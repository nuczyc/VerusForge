//! Whitespace-only printing for the Verus AST, without erasing specification tokens.
use proc_macro2::{Delimiter, Spacing, TokenStream, TokenTree};
use quote::ToTokens;
use syn_verus::{File, Item};

#[derive(Default)]
struct Writer {
    out: String,
    indent: usize,
}
impl Writer {
    fn trim(&mut self) {
        while self.out.ends_with(' ') {
            self.out.pop();
        }
    }
    fn newline(&mut self) {
        self.trim();
        if !self.out.ends_with('\n') {
            self.out.push('\n');
        }
    }
    fn space(&mut self) {
        if !self.out.is_empty()
            && !self
                .out
                .ends_with([' ', '\n', '(', '[', '.', ':', '!', '\'', '#'])
        {
            self.out.push(' ');
        }
    }
    fn text(&mut self, s: &str) {
        if self.out.is_empty() || self.out.ends_with('\n') {
            self.out.push_str(&"    ".repeat(self.indent));
        }
        self.out.push_str(s);
    }
    fn stream(&mut self, ts: TokenStream, inline: bool, signature: bool) {
        let tokens: Vec<_> = ts.into_iter().collect();
        let base = self.indent;
        let mut spec = false;
        let mut i = 0;
        while i < tokens.len() {
            match &tokens[i] {
                TokenTree::Ident(id) => {
                    let name = id.to_string();
                    if !inline
                        && [
                            "requires",
                            "ensures",
                            "recommends",
                            "returns",
                            "decreases",
                            "invariant",
                            "invariant_except_break",
                            "invariant_ensures",
                            "where",
                        ]
                        .contains(&name.as_str())
                    {
                        self.newline();
                        self.indent = base + 1;
                        self.text(&name);
                        self.newline();
                        self.indent = base + 2;
                        spec = true;
                    } else {
                        self.space();
                        self.text(&name);
                    }
                }
                TokenTree::Literal(l) => {
                    self.space();
                    self.text(&l.to_string());
                }
                TokenTree::Group(g) => match g.delimiter() {
                    Delimiter::Parenthesis | Delimiter::Bracket => {
                        if ![": ", "-> ", "= ", "if ", "while ", "return "]
                            .iter()
                            .any(|s| self.out.ends_with(s))
                        {
                            self.trim();
                        }
                        let (open, close) = if g.delimiter() == Delimiter::Parenthesis {
                            ("(", ")")
                        } else {
                            ("[", "]")
                        };
                        self.text(open);
                        self.stream(g.stream(), true, false);
                        self.trim();
                        self.text(close);
                    }
                    Delimiter::Brace => {
                        if spec {
                            self.newline();
                            self.indent = base;
                            spec = false;
                        } else {
                            self.space();
                        }
                        self.text("{");
                        if !g.stream().is_empty() {
                            if inline {
                                self.space();
                                self.stream(g.stream(), true, false);
                                self.space();
                            } else {
                                self.newline();
                                self.indent += 1;
                                self.stream(g.stream(), false, false);
                                self.newline();
                                self.indent -= 1;
                            }
                        }
                        self.text("}");
                        if !inline {
                            let next = tokens.get(i + 1);
                            if matches!(next,Some(TokenTree::Ident(id)) if id=="else") {
                                self.space();
                            } else if !matches!(next,Some(TokenTree::Punct(p)) if [';',',','.', '?'].contains(&p.as_char()))
                            {
                                self.newline();
                            }
                        }
                    }
                    Delimiter::None => self.stream(g.stream(), inline, signature),
                },
                TokenTree::Punct(p) => {
                    let mut op = p.as_char().to_string();
                    let mut joint = p.spacing() == Spacing::Joint;
                    while joint && i + 1 < tokens.len() {
                        if let TokenTree::Punct(next) = &tokens[i + 1] {
                            op.push(next.as_char());
                            joint = next.spacing() == Spacing::Joint;
                            i += 1;
                        } else {
                            break;
                        }
                    }
                    match op.as_str() {
                        "," => {
                            self.trim();
                            self.text(",");
                            if !inline && (spec || !signature) {
                                self.newline();
                            } else {
                                self.space();
                            }
                        }
                        ";" => {
                            self.trim();
                            self.text(";");
                            if inline {
                                self.space();
                            } else {
                                self.newline();
                            }
                        }
                        "." | "::" => {
                            self.trim();
                            self.text(&op);
                        }
                        ":" => {
                            self.trim();
                            self.text(": ");
                        }
                        "#" | "!" | "'" => {
                            self.trim();
                            self.text(&op);
                        }
                        _ => {
                            self.space();
                            self.text(&op);
                            self.space();
                        }
                    }
                }
            }
            i += 1;
        }
        self.indent = base;
    }
}

pub fn file(file: &File) -> String {
    let mut w = Writer::default();
    if let Some(shebang) = &file.shebang {
        w.text(shebang);
        w.newline();
    }
    for attr in &file.attrs {
        w.stream(attr.to_token_stream(), true, false);
        w.newline();
    }
    w.text("vstd::prelude::verus! {");
    w.newline();
    w.indent = 1;
    for (index, item) in file.items.iter().enumerate() {
        if index > 0 && matches!(item, Item::Fn(_)) {
            w.newline();
            w.out.push('\n');
        }
        if let Item::Fn(f) = item {
            for a in &f.attrs {
                w.stream(a.to_token_stream(), true, false);
                w.newline();
            }
            w.stream(f.vis.to_token_stream(), true, false);
            w.space();
            w.stream(f.sig.to_token_stream(), false, true);
            w.trim();
            if f.semi_token.is_some() {
                w.text(";");
                w.newline();
                continue;
            }
            if f.sig.spec.to_token_stream().is_empty() {
                w.space();
            } else {
                w.newline();
            }
            w.stream(f.block.to_token_stream(), false, false);
            if f.semi_token.is_some() {
                w.text(";");
            }
        } else {
            w.stream(item.to_token_stream(), false, false);
        }
        w.newline();
    }
    w.indent = 0;
    w.text("}");
    w.newline();
    w.out
}

#[cfg(test)]
mod tests {
    #[test]
    fn keeps_tuple_fields_inline_and_indents_the_body() {
        let code="use vstd::prelude::*; verus! {fn f()->(r:(u32,u32)) ensures r.0==1,r.1==2, {let x=1;(x,2)}}";
        let output = crate::syntax::formatted(code).unwrap();
        assert!(output.contains("(r: (u32, u32))"));
        assert!(output.contains("            r.0 == 1,"));
        assert!(output.contains("        let x = 1;"));
        assert!(output.contains("        (x, 2)"));
    }
    #[test]
    fn preserves_all_benchmark_asts() {
        use std::{fs, path::Path};
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../benchmarks/Verus-Bench");
        let mut count = 0;
        for suite in ["CloverBench", "Diffy", "MBPP", "Misc"] {
            for entry in fs::read_dir(root.join(suite).join("unverified")).unwrap() {
                let path = entry.unwrap().path();
                if path.extension().is_none_or(|s| s != "rs") {
                    continue;
                }
                let input = fs::read_to_string(&path).unwrap();
                let output = crate::syntax::formatted(&input)
                    .unwrap_or_else(|e| panic!("{}: {e:#}", path.display()));
                assert_eq!(
                    crate::syntax::parse(&input).unwrap(),
                    crate::syntax::parse(&output).unwrap(),
                    "{}",
                    path.display()
                );
                count += 1;
            }
        }
        assert_eq!(count, 150);
    }
}
