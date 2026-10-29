use crate::process::Output;
use anyhow::Result;
use serde::{Deserialize, Serialize};
use serde_json::Value;
use std::{
    collections::BTreeSet,
    fs,
    path::{Path, PathBuf},
    process::Command,
};

#[derive(Debug, Clone, Copy, Eq, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ErrorKind {
    Precondition,
    Postcondition,
    InvariantFront,
    InvariantEnd,
    Decreases,
    Assertion,
    Overflow,
    Type,
    Sequence,
    Recommendation,
    UnexpectedProof,
    RustAssert,
    ExecInGhost,
    Other,
}
impl ErrorKind {
    pub fn legacy_name(self) -> &'static str {
        match self {
            Self::Precondition => "PreCondFail",
            Self::Postcondition => "PostCondFail",
            Self::InvariantFront => "InvFailFront",
            Self::InvariantEnd => "InvFailEnd",
            Self::Decreases => "DecFailEnd",
            Self::Assertion => "AssertFail",
            Self::Overflow => "ArithmeticFlow",
            Self::Type => "MismatchedType",
            Self::Recommendation => "RecommendNotMet",
            Self::UnexpectedProof => "UnxProofBlock",
            Self::RustAssert => "RustAssert",
            Self::ExecInGhost => "ExecinGhost",
            Self::Sequence | Self::Other => "Other",
        }
    }
    fn classify(message: &str) -> Self {
        if message.contains("before loop") {
            Self::InvariantFront
        } else if message.contains("end of loop") {
            Self::InvariantEnd
        } else if message.contains("precondition") {
            Self::Precondition
        } else if message.contains("postcondition") {
            Self::Postcondition
        } else if message.contains("decreases") {
            Self::Decreases
        } else if message.contains("overflow") || message.contains("underflow") {
            Self::Overflow
        } else if message.contains("recommendation not met") {
            Self::Recommendation
        } else if message.contains("unexpected proof block") {
            Self::UnexpectedProof
        } else if message.contains("panic is not supported") {
            Self::RustAssert
        } else if message.contains("cannot call function with mode exec") {
            Self::ExecInGhost
        } else if message.contains("assertion") || message.contains("split assertion") {
            Self::Assertion
        } else if message.contains("mismatched types")
            || message.contains("expected")
            || message.contains("cannot find")
        {
            Self::Type
        } else if message.contains("Seq") || message.contains("sequence") {
            Self::Sequence
        } else {
            Self::Other
        }
    }
}
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Diagnostic {
    pub kind: ErrorKind,
    pub message: String,
    pub lines: Vec<usize>,
    pub spans: Vec<(usize, usize, usize, usize)>,
    pub rendered: String,
}
#[derive(Debug, Clone, Copy, Serialize, Deserialize, Eq, PartialEq)]
pub struct Score {
    pub verified: u64,
    pub errors: u64,
    pub compilation_error: bool,
    pub diagnostics: usize,
}
impl Score {
    pub fn legacy_text(&self) -> String {
        format!(
            "Compilation Error: {}, Verified: {}, Errors: {}, Verus Errors: {}",
            if self.compilation_error {
                "True"
            } else {
                "False"
            },
            self.verified,
            self.errors,
            self.diagnostics
        )
    }
    pub fn rank(&self) -> (bool, u64, std::cmp::Reverse<u64>, std::cmp::Reverse<usize>) {
        (
            !self.compilation_error,
            self.verified,
            std::cmp::Reverse(self.errors),
            std::cmp::Reverse(self.diagnostics),
        )
    }
    pub fn good_repair(&self, old: &Self) -> bool {
        (!self.compilation_error || old.compilation_error) && self.verified >= old.verified
    }
}
#[derive(Debug, Clone, Serialize)]
pub struct Evaluation {
    pub success: bool,
    pub score: Score,
    pub diagnostics: Vec<Diagnostic>,
    pub process: Output,
}
impl Evaluation {
    pub fn parse(output: Output) -> Self {
        let value: Value = serde_json::from_str(&output.stdout).unwrap_or(Value::Null);
        let r = &value["verification-results"];
        let mut diagnostics = Vec::new();
        for line in output.stderr.lines() {
            if let Ok(v) = serde_json::from_str::<Value>(line) {
                if v["level"] != "error"
                    || v["message"]
                        .as_str()
                        .unwrap_or("")
                        .starts_with("aborting due")
                {
                    continue;
                }
                let message = v["message"].as_str().unwrap_or("").to_string();
                let lines = v["spans"]
                    .as_array()
                    .into_iter()
                    .flatten()
                    .filter(|s| s["is_primary"] == true)
                    .filter_map(|s| s["line_start"].as_u64().map(|x| x as usize))
                    .collect();
                diagnostics.push(Diagnostic {
                    kind: ErrorKind::classify(&message),
                    message,
                    lines,
                    spans: v["spans"]
                        .as_array()
                        .into_iter()
                        .flatten()
                        .filter(|s| s["is_primary"] == true)
                        .filter_map(|s| {
                            Some((
                                s["line_start"].as_u64()? as usize,
                                (s["column_start"].as_u64()? as usize).saturating_sub(1),
                                s["line_end"].as_u64()? as usize,
                                (s["column_end"].as_u64()? as usize).saturating_sub(1),
                            ))
                        })
                        .collect(),
                    rendered: v["rendered"].as_str().unwrap_or(line).to_string(),
                });
            }
        }
        let verified = r["verified"].as_u64().unwrap_or(0);
        let errors = r["errors"].as_u64().unwrap_or(999);
        let success = output.exit_code == Some(0)
            && !output.timed_out
            && diagnostics.is_empty()
            && r["success"] == true
            && errors == 0
            && verified > 0
            && r["is-verifying-entire-crate"] == true
            && r["encountered-error"] == false
            && r["encountered-vir-error"] == false;
        let compilation_error = r["encountered-vir-error"] == true
            || !r.is_object()
            || !r["verified"].is_u64()
            || !r["errors"].is_u64()
            || (verified == 0 && errors == 0)
            || (errors == 0 && output.exit_code != Some(0))
            || diagnostics
                .iter()
                .any(|d| matches!(d.kind, ErrorKind::Type));
        Self {
            success,
            score: Score {
                verified,
                errors,
                compilation_error,
                diagnostics: diagnostics.len(),
            },
            diagnostics,
            process: output,
        }
    }
    pub fn feedback(&self) -> String {
        format!(
            "Score: {:?}\nDiagnostics:\n{}\nRaw verifier output:\n{}",
            self.score,
            self.diagnostics
                .iter()
                .map(|d| d.rendered.as_str())
                .collect::<Vec<_>>()
                .join("\n"),
            self.process.stderr.chars().take(20_000).collect::<String>()
        )
    }
    pub fn prune_spans(&self) -> BTreeSet<(usize, usize, usize, usize)> {
        self.diagnostics
            .iter()
            .filter(|d| {
                matches!(
                    d.kind,
                    ErrorKind::InvariantFront | ErrorKind::InvariantEnd | ErrorKind::Assertion
                )
            })
            .flat_map(|d| d.spans.iter().copied())
            .collect()
    }
    /// Port of the original proof-expression cast repair. Every result must pass
    /// the original-program guard before evaluation/acceptance.
    pub fn type_fix(&self, code: &str) -> Option<String> {
        for line in self.process.stderr.lines() {
            let Ok(value) = serde_json::from_str::<Value>(line) else {
                continue;
            };
            if !value["message"]
                .as_str()
                .is_some_and(|m| m.contains("mismatched types"))
            {
                continue;
            }
            for span in value["spans"].as_array().into_iter().flatten() {
                if span["is_primary"] != true {
                    continue;
                }
                let label = span["label"].as_str().unwrap_or("");
                let Some(rest) = label.split("expected `").nth(1) else {
                    continue;
                };
                let expected = rest.split('`').next().unwrap_or("");
                if !["int", "nat", "u64", "u32", "usize", "i64", "i32"].contains(&expected) {
                    continue;
                }
                let start = span["byte_start"].as_u64()? as usize;
                let end = span["byte_end"].as_u64()? as usize;
                let expression = code.get(start..end)?;
                let mut fixed = code.to_string();
                fixed.replace_range(start..end, &format!("({expression} as {expected})"));
                return Some(fixed);
            }
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn proof_failure_is_not_compilation_failure() {
        let evaluation=Evaluation::parse(Output{exit_code:Some(1),timed_out:false,stdout:serde_json::json!({"verification-results":{"encountered-error":true,"encountered-vir-error":false,"success":false,"verified":1,"errors":1,"is-verifying-entire-crate":true}}).to_string(),stderr:String::new(),elapsed_ms:1});
        assert!(!evaluation.success);
        assert!(!evaluation.score.compilation_error);
        assert_eq!(evaluation.score.verified, 1);
    }
}
#[derive(Clone)]
pub struct Verifier {
    pub path: PathBuf,
    pub timeout: u64,
}
impl Verifier {
    pub fn file(&self, path: &Path) -> Result<Evaluation> {
        Ok(Evaluation::parse(crate::process::run(
            Command::new(&self.path).arg(path).args([
                "--output-json",
                "--error-format=json",
                "--multiple-errors",
                "5",
            ]),
            self.timeout,
        )?))
    }
    pub fn code(&self, code: &str) -> Result<Evaluation> {
        let file = tempfile::Builder::new()
            .prefix("verusseek_")
            .suffix(".rs")
            .tempfile()?;
        fs::write(file.path(), code)?;
        self.file(file.path())
    }
}
