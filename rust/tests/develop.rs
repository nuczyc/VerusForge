use serde_json::{json, Value};
use std::{fs, path::PathBuf, process::Command};

const RUST: &str =
    "pub fn max_of_two(a: u64, b: u64) -> u64 { if a >= b { a } else { b } } fn main() {}";
const PROOF: &str = "use vstd::prelude::*; verus! { pub fn max_of_two(a: u64, b: u64) -> (r: u64) ensures r >= a, r >= b, r == a || r == b, { if a >= b { a } else { b } } fn main() {} }";

fn run(responses: &[String], max_requests: usize) -> Option<(tempfile::TempDir, Value)> {
    let verus = std::env::var("VERUS_PATH").ok()?;
    let dir = tempfile::tempdir().unwrap();
    fs::write(
        dir.path().join("config.json"),
        json!({"max_requests":max_requests,"max_verifications":10,"timeout":20,"examples":null})
            .to_string(),
    )
    .unwrap();
    let mut command = Command::new(env!("CARGO_BIN_EXE_verusforge"));
    command.args(["develop", "--prompt", "Implement max_of_two for all u64 inputs; result is either argument and is at least both arguments."])
        .arg("--config").arg(dir.path().join("config.json"))
        .arg("--verus").arg(verus)
        .arg("--output-dir").arg(dir.path().join("run"));
    for (index, response) in responses.iter().enumerate() {
        let path = dir.path().join(format!("response-{index}.rs"));
        fs::write(&path, response).unwrap();
        command.arg("--replay").arg(path);
    }
    let output = command.output().unwrap();
    assert_ne!(
        output.status.code(),
        Some(2),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let report: Value =
        serde_json::from_slice(&fs::read(dir.path().join("run/report.json")).unwrap()).unwrap();
    assert_eq!(
        output.status.success(),
        report["verified"] == true,
        "{report}"
    );
    Some((dir, report))
}

#[test]
fn natural_language_generates_rust_before_verus_proves_the_same_implementation() {
    let Some((dir, report)) = run(&[RUST.into(), PROOF.into()], 6) else {
        return;
    };
    assert_eq!(report["verified"], true, "{report}");
    assert_eq!(report["rust_compiled"], true);
    assert_eq!(report["executable_preserved"], true);
    assert_eq!(report["requests"], 2);
    assert_eq!(report["final_verification"]["success"], true);
    assert_eq!(report["mode"], "replay");
    assert_eq!(report["usage"]["requests"], 0);
    assert_eq!(
        fs::read_to_string(dir.path().join("run/implementation.rs")).unwrap(),
        RUST
    );
    let proof = fs::read_to_string(dir.path().join("run/verified.rs")).unwrap();
    assert!(proof.contains("// Score:"));
    let output = Command::new(env!("CARGO_BIN_EXE_verusforge"))
        .arg("verify")
        .arg(dir.path().join("run/verified.rs"))
        .arg("--verus")
        .arg(std::env::var("VERUS_PATH").unwrap())
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn adapter_proof_assertions_are_not_trusted_as_immutable_rust_input() {
    let bad = PROOF.replace("{ if a >=", "{ assert(false); if a >=");
    let weak = PROOF.replace("r >= a, r >= b, r == a || r == b,", "true,");
    let Some((dir, report)) = run(&[RUST.into(), bad, weak, PROOF.into()], 6) else {
        return;
    };
    assert_eq!(report["verified"], true, "{report}");
    assert_eq!(report["requests"], 2);
    assert_eq!(report["proof_engine"]["verified"], true);
    assert!(!fs::read_to_string(dir.path().join("run/proof/input.rs"))
        .unwrap()
        .contains("assert(false)"));
    assert_eq!(
        fs::read_to_string(dir.path().join("run/implementation.rs")).unwrap(),
        RUST
    );
}

#[test]
fn a_verified_replacement_algorithm_cannot_substitute_for_the_generated_rust() {
    let replacement = PROOF
        .replace("r >= a, r >= b, r == a || r == b,", "r == b,")
        .replace("{ if a >= b { a } else { b } }", "{ b }");
    let Some((_, report)) = run(&[RUST.into(), replacement, PROOF.into()], 6) else {
        return;
    };
    assert_eq!(report["verified"], true, "{report}");
    assert_eq!(report["attempts"][1]["status"], "rejected");
    assert!(report["attempts"][1]["error"]
        .as_str()
        .unwrap()
        .contains("executable Rust changed"));
}

#[test]
fn trust_bypass_is_rejected_and_compile_only_is_not_verified() {
    let bypass = PROOF.replace("{ if a >=", "{ assume(false); if a >=");
    let Some((dir, report)) = run(&[RUST.into(), bypass], 6) else {
        return;
    };
    assert_eq!(report["verified"], false);
    assert_eq!(report["rust_compiled"], true);
    assert_eq!(report["verifications"], 0);
    assert!(!dir.path().join("run/verified.rs").exists());
    let Some((_, limited)) = run(&[RUST.into(), PROOF.into()], 1) else {
        return;
    };
    assert_eq!(limited["verified"], false);
    assert_eq!(limited["rust_compiled"], true);
    assert_eq!(limited["requests"], 1);
    assert_eq!(limited["status"], "unproved");
}

#[test]
fn natural_language_cli_accepts_a_text_file_but_rejects_conflicting_inputs() {
    let output = Command::new(env!("CARGO_BIN_EXE_verusforge"))
        .args(["develop", "--help"])
        .output()
        .unwrap();
    assert!(output.status.success());
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../requirements/nl2vbench/DAFNY2VERUS-COLLECTION_1/description.txt");
    let output = Command::new(env!("CARGO_BIN_EXE_verusforge"))
        .args(["develop", "--prompt", "task", "--request-file"])
        .arg(path)
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(2));
}

#[test]
fn preview_prints_requirements_without_loading_credentials_or_creating_outputs() {
    let dir = tempfile::tempdir().unwrap();
    let request = dir.path().join("description.txt");
    fs::write(&request, "预览任务：计算两个整数的最大值。\n").unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_verusforge"))
        .arg("develop")
        .arg("--request-file")
        .arg(&request)
        .arg("--preview")
        .arg("--api-config")
        .arg(dir.path().join("does-not-exist"))
        .arg("--config")
        .arg(dir.path().join("does-not-exist.json"))
        .arg("--output-dir")
        .arg(dir.path().join("must-not-exist"))
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(String::from_utf8(output.stdout)
        .unwrap()
        .contains("预览任务：计算两个整数的最大值。"));
    assert!(output.stderr.is_empty());
    assert!(!dir.path().join("must-not-exist").exists());
}

#[test]
fn generated_rust_with_demo_printing_is_compiled_and_handed_to_verusforge() {
    let rust = include_str!("../examples/min-max-demo.rs");
    let (function, main_body) = rust.split_once("fn main()").unwrap();
    let function = function.replace(
        "-> (u64, u64)",
        "-> (r: (u64, u64)) ensures r.0 <= r.1, r == (a, b) || r == (b, a),",
    );
    let proof = format!("use vstd::prelude::*; verus! {{ {function} }} fn main(){main_body}");
    let Some((dir, report)) = run(&[rust.into(), proof], 6) else {
        return;
    };
    assert_eq!(report["rust_compiled"], true, "{report}");
    assert_eq!(report["verified"], true, "{report}");
    assert_eq!(report["proof_engine"]["verified"], true);
    assert_eq!(
        report["proof_engine"]["final_verification"]["success"],
        true
    );
    assert_eq!(report["requests"], 2);
    assert_eq!(
        fs::read_to_string(dir.path().join("run/implementation.rs")).unwrap(),
        rust
    );
    assert!(fs::read_to_string(dir.path().join("run/verified.rs"))
        .unwrap()
        .contains("println"));
}
