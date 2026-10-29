//! Verus AST operations shared by safety checks, analysis, merge and Houdini.
use anyhow::{ensure, Context, Result};
use quote::ToTokens;
use serde::Serialize;
use std::collections::{BTreeMap, BTreeSet};
use syn_verus::{visit::Visit, visit_mut::VisitMut, Expr, File, Item, Stmt};

pub fn parse(code: &str) -> Result<File> {
    let mut file = syn_verus::parse_file(code).context("parse Rust/Verus source")?;
    let mut items = Vec::new();
    for item in file.items {
        if let Item::Macro(m) = &item {
            let path = text(&m.mac.path).replace(' ', "");
            if [
                "verus",
                "vstd::prelude::verus",
                "verus_builtin_macros::verus",
            ]
            .contains(&path.as_str())
            {
                let inner: File =
                    syn_verus::parse2(m.mac.tokens.clone()).context("parse verus! contents")?;
                items.extend(inner.items);
                continue;
            }
        }
        items.push(item);
    }
    file.items = items;
    Ok(file)
}

pub fn render(file: &File) -> String {
    crate::pretty::file(file)
}

pub fn formatted(code: &str) -> Result<String> {
    let original = parse(code)?;
    let mut output = render(&original);
    ensure!(
        parse(&output)? == original,
        "formatter changed the Verus AST"
    );
    if let Some(index) = code.rfind("\n// Score:") {
        output.push('\n');
        output.push_str(code[index..].trim_start());
        if !output.ends_with('\n') {
            output.push('\n');
        }
    }
    Ok(output)
}

fn text<T: ToTokens>(node: &T) -> String {
    node.to_token_stream().to_string()
}

fn proof_stmt(stmt: &Stmt) -> bool {
    // Existing assumptions stay structurally visible in the preservation check.
    if text(stmt)
        .split_whitespace()
        .any(|t| ["assume", "admit", "external_body"].contains(&t))
    {
        return false;
    }
    match stmt {
        Stmt::Local(l) => l.ghost.is_some() || l.tracked.is_some(),
        Stmt::Expr(Expr::Assert(_) | Expr::AssertForall(_), _) => true,
        Stmt::Expr(Expr::Unary(u), _) => matches!(u.op, syn_verus::UnOp::Proof(_)),
        _ => false,
    }
}

struct Erase;
impl VisitMut for Erase {
    fn visit_block_mut(&mut self, block: &mut syn_verus::Block) {
        block.stmts.retain(|s| !proof_stmt(s));
        syn_verus::visit_mut::visit_block_mut(self, block);
    }
    fn visit_expr_mut(&mut self, expr: &mut Expr) {
        match expr {
            Expr::While(w) => {
                w.invariant = None;
                w.invariant_except_break = None;
                w.invariant_ensures = None;
                w.ensures = None;
                w.decreases = None;
            }
            Expr::Loop(w) => {
                w.invariant = None;
                w.invariant_except_break = None;
                w.invariant_ensures = None;
                w.ensures = None;
                w.decreases = None;
            }
            Expr::ForLoop(w) => {
                w.invariant = None;
                w.decreases = None;
            }
            _ => {}
        }
        syn_verus::visit_mut::visit_expr_mut(self, expr);
    }
    fn visit_attributes_mut(&mut self, attrs: &mut Vec<syn_verus::Attribute>) {
        attrs.retain(|a| !sound_attribute(a));
    }
}

fn sound_attribute(a: &syn_verus::Attribute) -> bool {
    let t = text(a).replace(' ', "");
    [
        "#[trigger]",
        "#[verifier::nonlinear_arith]",
        "#[verifier::integer_ring]",
        "#[verifier::spinoff_prover]",
        "#[verifier::loop_isolation(false)]",
        "#[verifier::loop_isolation(true)]",
    ]
    .contains(&t.as_str())
        || t.starts_with("#[verifier::rlimit(")
}

#[derive(Default)]
struct Boundary {
    asserts: BTreeMap<String, usize>,
    attrs: BTreeSet<String>,
    macros: BTreeSet<String>,
    forbidden: Vec<String>,
}
impl<'a> Visit<'a> for Boundary {
    fn visit_expr(&mut self, e: &'a Expr) {
        match e {
            Expr::Assert(a) => *self.asserts.entry(text(&a.expr)).or_default() += 1,
            Expr::AssertForall(a) => *self.asserts.entry(text(a)).or_default() += 1,
            Expr::Assume(_) => self.forbidden.push("assume".into()),
            _ => {}
        }
        syn_verus::visit::visit_expr(self, e);
    }
    fn visit_attribute(&mut self, a: &'a syn_verus::Attribute) {
        if !sound_attribute(a) {
            self.attrs.insert(text(a));
        }
        syn_verus::visit::visit_attribute(self, a);
    }
    fn visit_macro(&mut self, m: &'a syn_verus::Macro) {
        self.macros.insert(text(m));
        syn_verus::visit::visit_macro(self, m);
    }
    fn visit_ident(&mut self, ident: &'a proc_macro2::Ident) {
        let name = ident.to_string();
        if [
            "assume",
            "admit",
            "assume_specification",
            "external_body",
            "external",
            "external_fn_specification",
            "external_type_specification",
            "axiom",
            "assume_new",
            "assume_init",
            "assume_type_invariant",
            "unimplemented",
            "todo",
            "unreachable_unchecked",
            "inline_air_stmt",
        ]
        .contains(&name.as_str())
        {
            self.forbidden.push(name);
        }
    }
}

/// A conservative syntactic preservation check, not a semantic equivalence proof.
/// Original specs/helpers are immutable; executable functions may gain ghost code.
pub fn check(original: &str, candidate: &str) -> Result<()> {
    let original = parse(original)?;
    let candidate = parse(candidate)?;
    let mut old = Boundary::default();
    old.visit_file(&original);
    let mut new = Boundary::default();
    new.visit_file(&candidate);
    old.forbidden.sort();
    new.forbidden.sort();
    ensure!(
        new.forbidden == old.forbidden,
        "introduced or removed trusted constructs: {:?}",
        new.forbidden
    );
    ensure!(
        new.attrs.is_subset(&old.attrs),
        "new non-allowlisted attributes"
    );
    ensure!(
        new.macros.is_subset(&old.macros),
        "new or modified opaque macro invocation"
    );
    ensure!(
        original.attrs == candidate.attrs && original.shebang == candidate.shebang,
        "file attributes changed"
    );
    for (assertion, count) in old.asserts {
        ensure!(
            new.asserts.get(&assertion).copied().unwrap_or(0) >= count,
            "original assertion removed or changed"
        );
    }
    let mut next = 0;
    for item in &candidate.items {
        if let Some(before) = original.items.get(next) {
            let same_name =
                matches!((before,item), (Item::Fn(a),Item::Fn(b)) if a.sig.ident == b.sig.ident);
            if same_name {
                let (Item::Fn(a), Item::Fn(b)) = (before, item) else {
                    unreachable!()
                };
                ensure!(
                    a.sig == b.sig,
                    "function signature or contract changed: {}\noriginal: {}\ncandidate: {}",
                    a.sig.ident,
                    text(&a.sig),
                    text(&b.sig)
                );
                let mut old_asserts = Boundary::default();
                old_asserts.visit_block(&a.block);
                let mut new_asserts = Boundary::default();
                new_asserts.visit_block(&b.block);
                for (expr, count) in old_asserts.asserts {
                    ensure!(
                        new_asserts.asserts.get(&expr).copied().unwrap_or(0) >= count,
                        "original assertion moved out of its function"
                    );
                }
                let mut a = a.clone();
                let mut b = b.clone();
                Erase.visit_attributes_mut(&mut a.attrs);
                Erase.visit_attributes_mut(&mut b.attrs);
                ensure!(
                    a.attrs == b.attrs && a.vis == b.vis,
                    "function metadata changed"
                );
                match a.sig.mode {
                    syn_verus::FnMode::Default | syn_verus::FnMode::Exec(_) => {
                        Erase.visit_block_mut(&mut a.block);
                        Erase.visit_block_mut(&mut b.block);
                        ensure!(
                            a.block == b.block,
                            "executable body changed: {}",
                            a.sig.ident
                        );
                    }
                    syn_verus::FnMode::Proof(_) => {
                        // Existing incomplete proof bodies may be completed, but no axioms.
                        ensure!(b.semi_token.is_none(), "proof declaration without body");
                        if text(&a.block).contains("unimplemented !") {
                            ensure!(
                                a.block == b.block,
                                "original unimplemented proof stub changed"
                            );
                        }
                        let mut trust = Boundary::default();
                        trust.visit_block(&a.block);
                        if !trust.forbidden.is_empty() {
                            ensure!(
                                a.block == b.block,
                                "proof body containing original trust assumptions changed"
                            );
                        }
                    }
                    _ => ensure!(a == b, "existing specification function changed"),
                }
                next += 1;
                continue;
            }
            if before == item {
                next += 1;
                continue;
            }
        }
        // New helpers must have bodies; changing/removing any existing item fails below.
        ensure!(
            matches!(item, Item::Fn(f) if matches!(f.sig.mode, syn_verus::FnMode::Proof(_) | syn_verus::FnMode::Spec(_) | syn_verus::FnMode::SpecChecked(_)) && f.semi_token.is_none()),
            "non-proof item added, removed or modified"
        );
    }
    ensure!(
        next == original.items.len(),
        "original items missing or reordered"
    );
    Ok(())
}

#[derive(Debug, Default, Serialize)]
pub struct Analysis {
    pub functions: Vec<String>,
    pub calls: BTreeSet<String>,
    pub types: BTreeSet<String>,
    pub loops: usize,
    pub nonlinear: bool,
    pub has_break: bool,
    pub array_writes: bool,
    pub loop_invariants: Vec<Vec<String>>,
    pub contracts: BTreeMap<String, String>,
    pub dependencies: BTreeMap<String, BTreeSet<String>>,
    pub proof_order: Vec<String>,
    pub loop_contexts: Vec<LoopContext>,
    pub proof_obligations: BTreeMap<String, Vec<String>>,
}
#[derive(Debug, Default, Serialize)]
pub struct LoopContext {
    condition: String,
    reads: BTreeSet<String>,
    writes: BTreeSet<String>,
    arrays: BTreeSet<String>,
    invariants: Vec<String>,
}
#[derive(Default)]
struct Access {
    reads: BTreeSet<String>,
    writes: BTreeSet<String>,
    arrays: BTreeSet<String>,
}
impl<'a> Visit<'a> for Access {
    fn visit_expr_path(&mut self, p: &'a syn_verus::ExprPath) {
        self.reads.insert(text(&p.path));
        syn_verus::visit::visit_expr_path(self, p);
    }
    fn visit_expr_assign(&mut self, e: &'a syn_verus::ExprAssign) {
        self.writes.insert(text(&e.left));
        syn_verus::visit::visit_expr_assign(self, e);
    }
    fn visit_expr_index(&mut self, e: &'a syn_verus::ExprIndex) {
        self.arrays.insert(text(&e.expr));
        syn_verus::visit::visit_expr_index(self, e);
    }
    fn visit_expr_method_call(&mut self, e: &'a syn_verus::ExprMethodCall) {
        if [
            "set", "push", "pop", "remove", "insert", "append", "clear", "extend",
        ]
        .contains(&e.method.to_string().as_str())
        {
            self.writes.insert(text(&e.receiver));
            self.arrays.insert(text(&e.receiver));
        }
        syn_verus::visit::visit_expr_method_call(self, e);
    }
}
fn loop_context(
    body: &syn_verus::Block,
    condition: String,
    inv: &Option<syn_verus::Invariant>,
) -> LoopContext {
    let mut access = Access::default();
    access.visit_block(body);
    LoopContext {
        condition,
        reads: access.reads,
        writes: access.writes,
        arrays: access.arrays,
        invariants: invariants(inv),
    }
}
fn split_obligation(e: &Expr, out: &mut Vec<String>) {
    if let Expr::Binary(b) = e {
        if matches!(b.op, syn_verus::BinOp::And(_)) {
            split_obligation(&b.left, out);
            split_obligation(&b.right, out);
            return;
        }
    }
    out.push(text(e));
}
impl<'a> Visit<'a> for Analysis {
    fn visit_item_fn(&mut self, f: &'a syn_verus::ItemFn) {
        self.functions.push(f.sig.ident.to_string());
        self.contracts.insert(f.sig.ident.to_string(), text(&f.sig));
        let mut local = Calls::default();
        local.visit_block(&f.block);
        self.dependencies.insert(f.sig.ident.to_string(), local.0);
        let mut obligations = Vec::new();
        if let Some(ensures) = &f.sig.spec.ensures {
            for expr in &ensures.exprs.exprs {
                split_obligation(expr, &mut obligations);
            }
        }
        self.proof_obligations
            .insert(f.sig.ident.to_string(), obligations);
        syn_verus::visit::visit_item_fn(self, f);
    }
    fn visit_type(&mut self, t: &'a syn_verus::Type) {
        self.types.insert(text(t));
        syn_verus::visit::visit_type(self, t);
    }
    fn visit_expr(&mut self, e: &'a Expr) {
        match e {
            Expr::While(w) => {
                self.loops += 1;
                self.loop_invariants.push(invariants(&w.invariant));
                self.loop_contexts
                    .push(loop_context(&w.body, text(&w.cond), &w.invariant));
            }
            Expr::Loop(w) => {
                self.loops += 1;
                self.loop_invariants.push(invariants(&w.invariant));
                self.loop_contexts
                    .push(loop_context(&w.body, "true".into(), &w.invariant));
            }
            Expr::ForLoop(w) => {
                self.loops += 1;
                self.loop_invariants.push(invariants(&w.invariant));
                self.loop_contexts
                    .push(loop_context(&w.body, text(&w.expr), &w.invariant));
            }
            Expr::Break(_) => self.has_break = true,
            Expr::Binary(b)
                if matches!(
                    b.op,
                    syn_verus::BinOp::Mul(_) | syn_verus::BinOp::Div(_) | syn_verus::BinOp::Rem(_)
                ) =>
            {
                self.nonlinear = true
            }
            Expr::Call(c) => {
                self.calls.insert(text(&c.func));
            }
            Expr::MethodCall(c) => {
                if c.method == "set" || c.method == "push" {
                    self.array_writes = true;
                }
                self.calls.insert(c.method.to_string());
            }
            _ => {}
        }
        syn_verus::visit::visit_expr(self, e);
    }
}
fn invariants(i: &Option<syn_verus::Invariant>) -> Vec<String> {
    i.as_ref()
        .map(|i| i.exprs.exprs.iter().map(text).collect())
        .unwrap_or_default()
}
#[derive(Default)]
struct Calls(BTreeSet<String>);
impl<'a> Visit<'a> for Calls {
    fn visit_expr_call(&mut self, c: &'a syn_verus::ExprCall) {
        self.0.insert(text(&c.func));
        syn_verus::visit::visit_expr_call(self, c);
    }
}
pub fn analyze(code: &str) -> Result<Analysis> {
    let mut a = Analysis::default();
    a.visit_file(&parse(code)?);
    fn order(
        name: &str,
        deps: &BTreeMap<String, BTreeSet<String>>,
        seen: &mut BTreeSet<String>,
        out: &mut Vec<String>,
    ) {
        if !seen.insert(name.to_string()) {
            return;
        }
        if let Some(d) = deps.get(name) {
            for child in d {
                if deps.contains_key(child) {
                    order(child, deps, seen, out);
                }
            }
        }
        out.push(name.to_string());
    }
    let mut seen = BTreeSet::new();
    for f in &a.functions {
        order(f, &a.dependencies, &mut seen, &mut a.proof_order);
    }
    Ok(a)
}

/// Deterministic counterparts of constant-bound and basic loop synthesis rules.
/// They are speculative annotations, never trusted without Verus verification.
pub fn augment(code: &str) -> Result<String> {
    struct Augment {
        bounds: Vec<Expr>,
    }
    impl Augment {
        fn inv(&self, inv: &mut Option<syn_verus::Invariant>, extra: Vec<Expr>) {
            let mut expressions = self.bounds.clone();
            expressions.extend(extra);
            if expressions.is_empty() {
                return;
            }
            if inv.is_none() {
                *inv = Some(syn_verus::parse_str("invariant true,").unwrap());
            }
            let inv = inv.as_mut().unwrap();
            let mut seen: BTreeSet<_> = inv.exprs.exprs.iter().map(text).collect();
            for e in expressions {
                if seen.insert(text(&e)) {
                    inv.exprs.exprs.push(e);
                }
            }
        }
    }
    impl VisitMut for Augment {
        fn visit_item_fn_mut(&mut self, f: &mut syn_verus::ItemFn) {
            let old = self.bounds.clone();
            self.bounds = f
                .sig
                .spec
                .requires
                .as_ref()
                .map(|r| {
                    r.exprs
                        .exprs
                        .iter()
                        .filter(|e| !text(*e).contains("old ("))
                        .cloned()
                        .collect()
                })
                .unwrap_or_default();
            syn_verus::visit_mut::visit_item_fn_mut(self, f);
            self.bounds = old;
        }
        fn visit_expr_mut(&mut self, e: &mut Expr) {
            match e {
                Expr::While(w) => {
                    let mut extra = Vec::new();
                    if let Expr::Binary(b) = w.cond.as_ref() {
                        if matches!(b.op, syn_verus::BinOp::Lt(_)) {
                            let bound = format!("{} <= {}", text(&b.left), text(&b.right));
                            if let Ok(e) = syn_verus::parse_str(&bound) {
                                extra.push(e);
                            }
                            if w.decreases.is_none() {
                                w.decreases = syn_verus::parse_str(&format!(
                                    "decreases {} - {},",
                                    text(&b.right),
                                    text(&b.left)
                                ))
                                .ok();
                            }
                        }
                    }
                    self.inv(&mut w.invariant, extra);
                }
                Expr::Loop(w) => self.inv(&mut w.invariant, Vec::new()),
                Expr::ForLoop(w) => self.inv(&mut w.invariant, Vec::new()),
                _ => {}
            }
            syn_verus::visit_mut::visit_expr_mut(self, e);
        }
    }
    let mut file = parse(code)?;
    Augment { bounds: Vec::new() }.visit_file_mut(&mut file);
    Ok(render(&file))
}

pub fn merge(left: &str, right: &str) -> Result<String> {
    // Both inputs are separately checked against the original by the caller.
    // Added proof statements need not match each other to merge invariants.
    let mut l = parse(left)?;
    let mut r = parse(right)?;
    Erase.visit_file_mut(&mut l);
    Erase.visit_file_mut(&mut r);
    for file in [&mut l, &mut r] {
        file.items.retain(|i|!matches!(i,Item::Fn(f) if matches!(f.sig.mode,syn_verus::FnMode::Proof(_)|syn_verus::FnMode::Spec(_)|syn_verus::FnMode::SpecChecked(_))));
    }
    ensure!(
        l == r,
        "cannot merge different executable programs or contracts"
    );
    let a = analyze(left)?;
    let b = analyze(right)?;
    ensure!(
        a.loop_invariants.len() == b.loop_invariants.len(),
        "loop count differs"
    );
    struct Merge {
        extra: Vec<Vec<String>>,
        index: usize,
    }
    impl Merge {
        fn invariant(&mut self, inv: &mut Option<syn_verus::Invariant>) {
            let extra = &self.extra[self.index];
            self.index += 1;
            if extra.is_empty() {
                return;
            }
            if inv.is_none() {
                *inv = Some(
                    syn_verus::parse_str::<syn_verus::Invariant>(&format!(
                        "invariant {},",
                        extra.join(",")
                    ))
                    .expect("validated invariant expressions"),
                );
            } else if let Some(inv) = inv {
                let mut seen: BTreeSet<String> = inv.exprs.exprs.iter().map(text).collect();
                for e in extra {
                    if seen.insert(e.clone()) {
                        inv.exprs
                            .exprs
                            .push(syn_verus::parse_str(e).expect("validated expression"));
                    }
                }
            }
        }
    }
    impl VisitMut for Merge {
        fn visit_expr_mut(&mut self, e: &mut Expr) {
            match e {
                Expr::While(w) => self.invariant(&mut w.invariant),
                Expr::Loop(w) => self.invariant(&mut w.invariant),
                Expr::ForLoop(w) => self.invariant(&mut w.invariant),
                _ => {}
            }
            syn_verus::visit_mut::visit_expr_mut(self, e);
        }
    }
    let mut file = parse(left)?;
    Merge {
        extra: b.loop_invariants,
        index: 0,
    }
    .visit_file_mut(&mut file);
    Ok(render(&file))
}

pub fn loop_isolation(code: &str) -> Result<String> {
    let mut file = parse(code)?;
    for item in &mut file.items {
        if let Item::Fn(f) = item {
            if matches!(
                f.sig.mode,
                syn_verus::FnMode::Exec(_) | syn_verus::FnMode::Default
            ) && !f
                .attrs
                .iter()
                .any(|a| text(a).replace(' ', "").contains("loop_isolation("))
            {
                f.attrs
                    .push(syn_verus::parse_quote!(#[verifier::loop_isolation(false)]));
            }
        }
    }
    Ok(render(&file))
}

/// Remove only AST invariant/assertion expressions at failed diagnostic spans.
/// The caller rechecks against the original input, so original assertions survive.
#[cfg(test)]
pub fn prune(code: &str, lines: &BTreeSet<usize>) -> Result<String> {
    prune_at(
        code,
        &lines
            .iter()
            .map(|line| (*line, 0, *line, usize::MAX))
            .collect(),
    )
}
pub fn prune_at(code: &str, lines: &BTreeSet<(usize, usize, usize, usize)>) -> Result<String> {
    use syn_verus::spanned::Spanned;
    struct Prune<'a>(&'a BTreeSet<(usize, usize, usize, usize)>);
    impl Prune<'_> {
        fn intersects<T: Spanned>(&self, e: &T) -> bool {
            let start = e.span().start();
            let end = e.span().end();
            self.0.iter().any(|(sl, sc, el, ec)| {
                (*sl, *sc) < (end.line, end.column) && (start.line, start.column) < (*el, *ec)
            })
        }
        fn invariant(&self, i: &mut Option<syn_verus::Invariant>) {
            if let Some(i) = i {
                i.exprs.exprs = i
                    .exprs
                    .exprs
                    .iter()
                    .filter(|e| !self.intersects(*e))
                    .cloned()
                    .collect();
                if i.exprs.exprs.is_empty() {
                    *i = syn_verus::parse_str("invariant true,").unwrap();
                }
            }
        }
    }
    impl VisitMut for Prune<'_> {
        fn visit_block_mut(&mut self, b: &mut syn_verus::Block) {
            b.stmts
                .retain(|s| !matches!(s,Stmt::Expr(Expr::Assert(a),_) if self.intersects(a)));
            syn_verus::visit_mut::visit_block_mut(self, b);
        }
        fn visit_expr_mut(&mut self, e: &mut Expr) {
            match e {
                Expr::While(w) => self.invariant(&mut w.invariant),
                Expr::Loop(w) => self.invariant(&mut w.invariant),
                Expr::ForLoop(w) => self.invariant(&mut w.invariant),
                _ => {}
            }
            syn_verus::visit_mut::visit_expr_mut(self, e);
        }
    }
    let mut file = parse(code)?;
    Prune(lines).visit_file_mut(&mut file);
    Ok(render(&file))
}

#[cfg(test)]
mod tests {
    use super::*;
    const INPUT:&str="use vstd::prelude::*; fn main(){} verus!{ fn count(n:u64)->(r:u64) requires n<100, ensures r==n, { let mut i=0; while i<n { i=i+1; } i } }";
    #[test]
    fn full_program_guard() {
        let good = INPUT.replace(
            "while i<n {",
            "while i<n invariant i<=n, { proof { assert(i<n); }",
        );
        check(INPUT, &good).unwrap();
        for bad in [
            good.replace("ensures r==n", "ensures true"),
            good.replace("i=i+1", "i=i+2"),
            good.replace("assert(i<n)", "assume(false)"),
            good.replace("fn count", "#[verifier::external_body] fn count"),
        ] {
            assert!(check(INPUT, &bad).is_err(), "accepted {bad}");
        }
        assert_eq!(analyze(&good).unwrap().loops, 1);
    }
    #[test]
    fn merge_and_prune() {
        let a = INPUT.replace("while i<n {", "while i<n invariant i<=n, {");
        let b = INPUT.replace("while i<n {", "while i<n invariant n<100, {");
        let c = merge(&a, &b).unwrap();
        check(INPUT, &c).unwrap();
        assert_eq!(analyze(&c).unwrap().loop_invariants[0].len(), 2);
        let p = prune(&a, &BTreeSet::from([1])).unwrap();
        check(INPUT, &p).unwrap();
        assert_eq!(analyze(&p).unwrap().loop_invariants[0], vec!["true"]);
    }
}

// Standard demonstration I/O in main is ordinary Rust, not an opaque proof escape.
fn generated_boundary(file: &File) -> Boundary {
    let mut boundary = Boundary::default();
    boundary.visit_file(file);
    let mut macros = BTreeSet::new();
    for item in &file.items {
        let mut local = Boundary::default();
        local.visit_item(item);
        for invocation in local.macros {
            let path = invocation.split('!').next().unwrap_or("").replace(' ', "");
            let ordinary_main_macro = matches!(item, Item::Fn(function) if function.sig.ident == "main")
                && [
                    "println",
                    "print",
                    "eprintln",
                    "eprint",
                    "assert",
                    "assert_eq",
                    "assert_ne",
                    "dbg",
                ]
                .iter()
                .any(|name| path == *name || path == format!("std::{name}"));
            if !ordinary_main_macro {
                macros.insert(invocation);
            }
        }
    }
    boundary.macros = macros;
    boundary
}

/// Generated programs have no trusted original: require explicit contracts and reject escape hatches.
pub fn generated_contracts(code: &str) -> Result<BTreeMap<String, String>> {
    let file = parse(code)?;
    let boundary = generated_boundary(&file);
    ensure!(
        boundary.forbidden.is_empty(),
        "generated program contains trusted constructs"
    );
    ensure!(
        boundary.attrs.is_empty() && boundary.macros.is_empty() && file.attrs.is_empty(),
        "generated program contains unsupported attributes or opaque macros"
    );
    ensure!(
        !text(&file).split_whitespace().any(|word| word == "unsafe"),
        "generated program must use safe Rust"
    );
    let mut contracts = BTreeMap::new();
    for item in &file.items {
        match item {
            Item::Use(_) => {}
            Item::Fn(function) => {
                ensure!(
                    function.semi_token.is_none(),
                    "generated function must have a body"
                );
                if matches!(
                    function.sig.mode,
                    syn_verus::FnMode::Default | syn_verus::FnMode::Exec(_)
                ) {
                    if function.sig.ident == "main" {
                        continue;
                    }
                    let post = function
                        .sig
                        .spec
                        .ensures
                        .as_ref()
                        .context("each generated executable function needs ensures")?;
                    ensure!(
                        post.exprs
                            .exprs
                            .iter()
                            .any(|expr| text(expr).replace(' ', "").trim_matches(['(', ')'])
                                != "true"),
                        "generated postcondition is empty or trivially true"
                    );
                    if let Some(pre) = &function.sig.spec.requires {
                        ensure!(
                            !pre.exprs
                                .exprs
                                .iter()
                                .any(|expr| text(expr).replace(' ', "").trim_matches(['(', ')'])
                                    == "false"),
                            "generated precondition is false"
                        );
                    }
                    ensure!(
                        contracts
                            .insert(function.sig.ident.to_string(), text(&function.sig))
                            .is_none(),
                        "duplicate generated function"
                    );
                } else if matches!(
                    function.sig.mode,
                    syn_verus::FnMode::Spec(_) | syn_verus::FnMode::SpecChecked(_)
                ) {
                    contracts.insert(format!("spec:{}", function.sig.ident), text(function));
                }
            }
            _ => anyhow::bail!(
                "natural-language generation currently supports free functions and imports"
            ),
        }
    }
    ensure!(
        contracts.keys().any(|key| !key.starts_with("spec:")),
        "generate at least one executable function with a postcondition"
    );
    Ok(contracts)
}

/// Erase proof annotations to compare a Verus candidate with the previously generated ordinary Rust AST.
pub fn executable_rust(code: &str) -> Result<String> {
    generated_contracts(code)?;
    let mut file = parse(code)?;
    file.items.retain(|item| match item {
        Item::Use(import) => !text(&import.tree).split_whitespace().any(|word| {
            word == "vstd" || word == "verus_builtin" || word == "verus_builtin_macros"
        }),
        Item::Fn(function) => matches!(
            function.sig.mode,
            syn_verus::FnMode::Default | syn_verus::FnMode::Exec(_)
        ),
        _ => false,
    });
    Erase.visit_file_mut(&mut file);
    for item in &mut file.items {
        if let Item::Fn(function) = item {
            function.attrs.clear();
            function.sig.erase_spec_fields();
            function.sig.mode = syn_verus::FnMode::Default;
            function.sig.spec.with = None;
            if let syn_verus::ReturnType::Type(_, tracked, name, _) = &mut function.sig.output {
                *tracked = None;
                *name = None;
            }
        }
    }
    Ok(format!("{}\n", text(&file)))
}

/// Canonical ordinary Rust AST used to freeze the generated executable implementation.
pub fn plain_rust_structure(code: &str) -> Result<String> {
    let mut file = syn_verus::parse_file(code).context("parse ordinary Rust")?;
    let mut boundary = Boundary::default();
    boundary.visit_file(&file);
    ensure!(
        boundary.forbidden.is_empty() && boundary.attrs.is_empty() && file.attrs.is_empty(),
        "ordinary Rust must not contain trust escapes or unsupported attributes"
    );
    ensure!(
        !text(&file)
            .split_whitespace()
            .any(|word| word == "unsafe" || word == "vstd"),
        "use safe standard Rust without Verus dependencies in the implementation stage"
    );
    let mut functions = 0;
    for item in &file.items {
        match item {
            Item::Use(_) => {}
            Item::Fn(function) => {
                ensure!(
                    matches!(function.sig.mode, syn_verus::FnMode::Default),
                    "expected ordinary Rust function"
                );
                ensure!(
                    text(&function.sig.spec).is_empty(),
                    "ordinary Rust must not contain contracts"
                );
                if function.sig.ident != "main" {
                    functions += 1;
                }
            }
            _ => anyhow::bail!("currently supports standalone functions and imports"),
        }
    }
    ensure!(functions > 0, "implement at least one non-main function");
    file.items.sort_by_key(text);
    Ok(text(&file))
}

/// The generated adapter contributes contracts, not immutable proof assertions.
pub fn specification_seed(code: &str) -> Result<String> {
    generated_contracts(code)?;
    let mut file = parse(code)?;
    file.items.retain(|item| !matches!(item, Item::Fn(function) if matches!(function.sig.mode, syn_verus::FnMode::Proof(_) | syn_verus::FnMode::ProofAxiom(_))));
    let mut main = None;
    file.items.retain(|item| {
        if matches!(item, Item::Fn(function) if function.sig.ident == "main") {
            main = Some(text(item));
            false
        } else {
            true
        }
    });
    for item in &mut file.items {
        if let Item::Fn(function) = item {
            if matches!(
                function.sig.mode,
                syn_verus::FnMode::Default | syn_verus::FnMode::Exec(_)
            ) {
                Erase.visit_block_mut(&mut function.block);
            }
        }
    }
    let mut output = render(&file);
    if let Some(main) = main {
        output.push_str(&main);
        output.push('\n');
    }
    Ok(output)
}
