use anyhow::{bail, ensure, Result};

pub const SLOT: &str = "/* VERUSSEEK_PROOF */";

/// Restricted assertion expressions only. This is deliberately not a Verus parser.
/// Calls, paths, macros, assignments, strings, attributes and new declarations
/// cannot be introduced. The surrounding template is never model-controlled.
pub fn fill(template: &str, proof: &str) -> Result<String> {
    ensure!(
        template.matches(SLOT).count() == 1,
        "input must contain exactly one {SLOT}"
    );
    let mut tokens = Vec::new();
    let chars: Vec<char> = proof.chars().collect();
    let mut i = 0;
    while i < chars.len() {
        let c = chars[i];
        if c.is_ascii_whitespace() {
            i += 1;
            continue;
        }
        if c.is_ascii_alphanumeric() || c == '_' {
            let start = i;
            while i < chars.len() && (chars[i].is_ascii_alphanumeric() || chars[i] == '_') {
                i += 1;
            }
            tokens.push(chars[start..i].iter().collect::<String>());
        } else {
            ensure!(
                "()[];+-*/%<>=!&|".contains(c),
                "unsupported proof character: {c}"
            );
            let pair: String = chars[i..chars.len().min(i + 2)].iter().collect();
            if ["==", "!=", "<=", ">=", "&&", "||"].contains(&pair.as_str()) {
                tokens.push(pair);
                i += 2;
            } else {
                ensure!(
                    c != '=' && c != '&' && c != '|',
                    "assignment/references are forbidden"
                );
                tokens.push(c.to_string());
                i += 1;
            }
        }
    }
    let mut pos = 0;
    while pos < tokens.len() {
        ensure!(
            tokens[pos] == "assert" && tokens.get(pos + 1).map(String::as_str) == Some("("),
            "only assert(expression); is supported"
        );
        pos += 2;
        let start = pos;
        let mut stack = vec!["("];
        while pos < tokens.len() && !stack.is_empty() {
            let t = tokens[pos].as_str();
            match t {
                "(" | "[" => stack.push(t),
                ")" => ensure!(stack.pop() == Some("("), "unbalanced expression"),
                "]" => ensure!(stack.pop() == Some("["), "unbalanced expression"),
                ";" => bail!("statement inside assertion"),
                _ => {}
            }
            if t.chars()
                .next()
                .is_some_and(|c| c.is_ascii_alphabetic() || c == '_')
            {
                ensure!(
                    ![
                        "assume", "admit", "unsafe", "return", "break", "continue", "let", "fn",
                        "proof", "exec", "spec", "loop", "while", "if", "match", "as", "move",
                        "async", "await", "yield"
                    ]
                    .contains(&t),
                    "forbidden proof token: {t}"
                );
                ensure!(
                    tokens.get(pos + 1).map(String::as_str) != Some("("),
                    "function calls are forbidden inside assertions"
                );
                ensure!(
                    tokens.get(pos + 1).map(String::as_str) != Some("!"),
                    "macros are forbidden inside assertions"
                );
            }
            pos += 1;
        }
        ensure!(
            stack.is_empty() && pos > start + 1,
            "empty or unbalanced assertion"
        );
        ensure!(
            tokens.get(pos).map(String::as_str) == Some(";"),
            "assertion needs a semicolon"
        );
        pos += 1;
    }
    Ok(template.replacen(SLOT, proof, 1))
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn accepts_pure_assertions() {
        assert_eq!(
            fill(
                "before /* VERUSSEEK_PROOF */ after",
                "assert(x + 1 > x);\nassert(a[i] == 2);"
            )
            .unwrap(),
            "before assert(x + 1 > x);\nassert(a[i] == 2); after"
        );
    }
    #[test]
    fn rejects_boundary_bypasses() {
        for proof in [
            "assume(false);",
            "assert(assume(false));",
            "assert(x = 2);",
            "assert({return true});",
            "assert(foo());",
            "assert(foo::bar);",
            "assert(x); } fn evil() {}",
            "assert(include!(x));",
            "assert(unsafe);",
            "assert((x]);",
            "assert();",
            "assert(x); // comment",
            "assert(x); #[verifier::external_body]",
        ] {
            assert!(fill(SLOT, proof).is_err(), "accepted {proof}");
        }
        assert!(fill("no slot", "").is_err());
        assert!(fill(&format!("{SLOT}{SLOT}"), "").is_err());
    }
}
