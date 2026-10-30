use serde_json::{json, Value};
use std::{fs, path::PathBuf, process::Command};

fn root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}
fn run(input: &str, responses: &[String], config: Value) -> Option<(tempfile::TempDir, Value)> {
    let verus = std::env::var("VERUS_PATH").ok()?;
    let dir = tempfile::tempdir().unwrap();
    fs::write(dir.path().join("input.rs"), input).unwrap();
    fs::write(dir.path().join("config.json"), config.to_string()).unwrap();
    let mut command = Command::new(env!("CARGO_BIN_EXE_verusforge"));
    command
        .arg("synthesize")
        .arg(dir.path().join("input.rs"))
        .arg("--config")
        .arg(dir.path().join("config.json"))
        .arg("--verus")
        .arg(verus)
        .arg("--output-dir")
        .arg(dir.path().join("run"));
    for (i, response) in responses.iter().enumerate() {
        let file = dir.path().join(format!("response-{i}.rs"));
        fs::write(&file, response).unwrap();
        command.arg("--replay").arg(file);
    }
    let output = command.output().unwrap();
    let report: Value =
        serde_json::from_slice(&fs::read(dir.path().join("run/report.json")).unwrap()).unwrap();
    assert!(
        output.status.success(),
        "{}\n{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
        serde_json::to_string_pretty(&report).unwrap()
    );
    Some((dir, report))
}
fn config() -> Value {
    json!({"phases":1,"inference_retries":1,"candidates":1,"refinement_retries":0,"repair_steps":0,"houdini_steps":5,"enhanced":false,"loop_isolation":false,"max_requests":30,"timeout":10,"examples":null})
}

#[test]
fn complementary_candidates_are_merged_even_when_scores_tie() {
    let input="use vstd::prelude::*; fn main(){} verus!{fn f(n:u64)->(r:u64) requires n<100, ensures r==2*n, {let mut i=0; while i<n decreases n-i, {i=i+1;} let mut j=0; while j<n decreases n-j, {j=j+1;} i+j}}";
    let a = input
        .replace(
            "while i<n decreases",
            "while i<n invariant i<=n,n<100, decreases",
        )
        .replace(
            "while j<n decreases",
            "while j<n invariant n<100, decreases",
        );
    let b = input
        .replace(
            "while i<n decreases",
            "while i<n invariant n<100, decreases",
        )
        .replace(
            "while j<n decreases",
            "while j<n invariant j<=n,n<100, decreases",
        );
    let mut cfg = config();
    cfg["candidates"] = json!(2);
    if let Some((_, report)) = run(input, &[a, b], cfg) {
        assert!(report["events"]
            .as_array()
            .unwrap()
            .iter()
            .any(|e| e["stage"] == "selective_merge" && e["evaluation"]["success"] == true));
    }
}

#[test]
fn standard_refinement_chain_reaches_classified_postcondition_repair() {
    let input = fs::read_to_string(root().join("examples/count-input.rs")).unwrap();
    let good = fs::read_to_string(root().join("examples/count-proof.rs")).unwrap();
    let mut responses = vec![input.clone(); 6];
    responses.push(good);
    let mut cfg = config();
    cfg["refinement_retries"] = json!(1);
    cfg["repair_steps"] = json!(1);
    cfg["repair_candidates"] = json!(1);
    if let Some((_, report)) = run(&input, &responses, cfg) {
        let stages: Vec<&str> = report["events"]
            .as_array()
            .unwrap()
            .iter()
            .filter_map(|e| e["strategy"].as_str())
            .collect();
        assert_eq!(
            stages,
            vec![
                "generation.direct_inference",
                "generation.constantrefine_inference",
                "generation.arraylen_inference",
                "generation.arrayrefine_inference",
                "generation.condlooprefine_inference",
                "generation.proof_block_inference",
                "refinement.repair_postcond_error"
            ]
        );
    }
}

#[test]
fn best_candidate_is_inherited_and_reset_can_be_requested() {
    let input = fs::read_to_string(root().join("examples/count-input.rs")).unwrap();
    let good = fs::read_to_string(root().join("examples/count-proof.rs")).unwrap();
    let partial = good.replace("invariant i <= n, n < 100,", "invariant n < 100,");
    for inherit in [true, false] {
        let mut cfg = config();
        cfg["profile"] = json!("direct-repair");
        cfg["phases"] = json!(2);
        cfg["repair_steps"] = json!(1);
        cfg["repair_candidates"] = json!(1);
        cfg["inheritance"] = json!(inherit);
        if let Some((dir, report)) = run(&input, &[partial.clone(), good.clone()], cfg) {
            assert_eq!(report["phases"].as_array().unwrap().len(), 2);
            assert_eq!(
                fs::read_to_string(dir.path().join("run/phase-2-start.rs")).unwrap(),
                if inherit {
                    partial.clone()
                } else {
                    input.clone()
                }
            );
        }
    }
}

#[test]
fn proof_only_type_error_is_repaired_without_another_model_request() {
    let input = fs::read_to_string(root().join("examples/count-input.rs")).unwrap();
    let candidate = fs::read_to_string(root().join("examples/count-proof.rs"))
        .unwrap()
        .replace(
            "    let mut i = 0;",
            "    proof { let ghost z: int = n; assert(z == n as int); }\n    let mut i = 0;",
        );
    if let Some((_, report)) = run(&input, &[candidate], config()) {
        assert_eq!(report["requests"], 1);
        assert!(report["events"]
            .as_array()
            .unwrap()
            .iter()
            .any(|e| e["stage"] == "type_fix" && e["evaluation"]["success"] == true));
    }
}

#[test]
fn baseline_and_uniform_profiles_follow_their_own_paths() {
    let input = fs::read_to_string(root().join("examples/count-input.rs")).unwrap();
    let good = fs::read_to_string(root().join("examples/count-proof.rs")).unwrap();
    for profile in ["baseline", "uniform"] {
        let mut cfg = config();
        cfg["profile"] = json!(profile);
        cfg["baseline_retries"] = json!(2);
        if let Some((_, report)) = run(&input, &[good.clone()], cfg) {
            let strategy = report["events"]
                .as_array()
                .unwrap()
                .iter()
                .find_map(|e| e["strategy"].as_str())
                .unwrap();
            assert_eq!(
                strategy,
                if profile == "baseline" {
                    "generation.direct_full_inference"
                } else {
                    "generation.direct_inference_with_refinement"
                }
            );
        }
    }
}

#[test]
fn request_budget_stops_before_consuming_a_second_candidate() {
    let Ok(verus) = std::env::var("VERUS_PATH") else {
        return;
    };
    let input = fs::read_to_string(root().join("examples/count-input.rs")).unwrap();
    let good = fs::read_to_string(root().join("examples/count-proof.rs")).unwrap();
    let dir = tempfile::tempdir().unwrap();
    let mut cfg = config();
    cfg["candidates"] = json!(2);
    cfg["max_requests"] = json!(1);
    fs::write(dir.path().join("config.json"), cfg.to_string()).unwrap();
    fs::write(dir.path().join("first.rs"), &input).unwrap();
    fs::write(dir.path().join("second.rs"), good).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_verusforge"))
        .arg("synthesize")
        .arg(root().join("examples/count-input.rs"))
        .arg("--config")
        .arg(dir.path().join("config.json"))
        .arg("--verus")
        .arg(verus)
        .arg("--replay")
        .arg(dir.path().join("first.rs"))
        .arg("--replay")
        .arg(dir.path().join("second.rs"))
        .arg("--output-dir")
        .arg(dir.path().join("run"))
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(1));
    let report: Value =
        serde_json::from_slice(&fs::read(dir.path().join("run/report.json")).unwrap()).unwrap();
    assert_eq!(report["requests"], 1);
    assert_eq!(report["status"], "exhausted");
    assert!(!dir.path().join("run/verified.rs").exists());
}

#[cfg(unix)]
#[test]
fn api_protocol_adapter_feeds_real_verus_without_network() {
    api_fixture(false, 10, "protocol-fixture", 1, false);
}

#[cfg(unix)]
#[test]
fn truncated_candidate_continues_at_fixed_token_limit() {
    api_fixture(true, 10, "protocol-fixture", 1, false);
}

#[cfg(unix)]
#[test]
fn truncated_candidate_respects_request_budget() {
    api_fixture(true, 1, "protocol-fixture", 1, false);
}

#[cfg(unix)]
#[test]
fn batch_candidates_use_one_request_and_process_all_choices() {
    api_fixture(false, 1, "protocol-fixture", 5, false);
}

#[cfg(unix)]
#[test]
fn deepseek_uses_one_choice_and_disables_thinking() {
    api_fixture(false, 10, "deepseek-flash", 5, false);
}

#[cfg(unix)]
#[test]
fn empty_truncations_stop_before_refinement_or_later_phases() {
    api_fixture(true, 96, "deepseek-flash", 5, true);
}

#[cfg(unix)]
fn api_fixture(
    truncated: bool,
    budget: usize,
    model: &str,
    candidates: usize,
    always_truncated: bool,
) {
    use std::os::unix::fs::PermissionsExt;
    let Ok(verus) = std::env::var("VERUS_PATH") else {
        return;
    };
    let dir = tempfile::tempdir().unwrap();
    let bin = dir.path().join("bin");
    fs::create_dir(&bin).unwrap();
    let shim = bin.join("curl");
    fs::write(
        &shim,
        r#"#!/bin/sh
while [ "$#" -gt 0 ]; do
  case "$1" in
    --config) cp "$2" "$TEST_AUTH_CAPTURE"; shift 2 ;;
    --data-binary) cp "${2#@}" "$TEST_REQUEST_CAPTURE"; shift 2 ;;
    *) shift ;;
  esac
done
if [ "$TEST_ALWAYS_TRUNCATE" = "yes" ] || { [ "$TEST_TRUNCATE" = "yes" ] && [ ! -f "$TEST_REQUEST_CAPTURE.seen" ]; }; then
  touch "$TEST_REQUEST_CAPTURE.seen"
  printf '%s' '{"choices":[{"finish_reason":"length","message":{"content":""}}],"usage":{"prompt_tokens":7,"completion_tokens":8192}}'
else
  cat "$TEST_MODEL_RESPONSE"
fi
"#,
    )
    .unwrap();
    fs::set_permissions(&shim, fs::Permissions::from_mode(0o755)).unwrap();
    let good = fs::read_to_string(root().join("examples/count-proof.rs")).unwrap();
    let effective = if model.contains("deepseek") {
        1
    } else {
        candidates
    };
    let input = fs::read_to_string(root().join("examples/count-input.rs")).unwrap();
    let choices: Vec<_> = (0..effective).map(|i| json!({"finish_reason":"stop","message":{"content":if effective > 1 && i == 0 { input.clone() } else { good.clone() }}})).collect();
    fs::write(
        dir.path().join("response.json"),
        json!({"choices":choices,"usage":{"prompt_tokens":20,"completion_tokens":30}}).to_string(),
    )
    .unwrap();
    fs::write(
        dir.path().join("apikey"),
        format!("test-only-key\nhttps://example.test/v1\n{model}\n"),
    )
    .unwrap();
    let mut cfg = config();
    cfg["profile"] = json!("baseline");
    cfg["baseline_retries"] = json!(25);
    cfg["candidates"] = json!(candidates);
    if always_truncated {
        cfg["profile"] = json!("standard");
        cfg["phases"] = json!(3);
        cfg["inference_retries"] = json!(3);
        cfg["refinement_retries"] = json!(3);
        cfg["repair_steps"] = json!(10);
    }
    cfg["max_requests"] = json!(budget);
    fs::write(dir.path().join("config.json"), cfg.to_string()).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_verusforge"))
        .env(
            "PATH",
            format!("{}:{}", bin.display(), std::env::var("PATH").unwrap()),
        )
        .env("TEST_TRUNCATE", if truncated { "yes" } else { "no" })
        .env(
            "TEST_ALWAYS_TRUNCATE",
            if always_truncated { "yes" } else { "no" },
        )
        .env("TEST_AUTH_CAPTURE", dir.path().join("auth.txt"))
        .env("TEST_REQUEST_CAPTURE", dir.path().join("request.json"))
        .env("TEST_MODEL_RESPONSE", dir.path().join("response.json"))
        .arg("synthesize")
        .arg(root().join("examples/count-input.rs"))
        .arg("--api-config")
        .arg(dir.path().join("apikey"))
        .arg("--config")
        .arg(dir.path().join("config.json"))
        .arg("--verus")
        .arg(verus)
        .arg("--output-dir")
        .arg(dir.path().join("run"))
        .output()
        .unwrap();
    assert_eq!(
        output.status.success(),
        !(always_truncated || truncated && budget == 1),
        "{} {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let request: Value =
        serde_json::from_slice(&fs::read(dir.path().join("request.json")).unwrap()).unwrap();
    assert_eq!(request["model"], model);
    assert_eq!(request["n"], effective);
    if model.contains("deepseek") {
        assert_eq!(request["thinking"]["type"], "disabled");
    }
    assert_eq!(request["messages"][0]["role"], "system");
    assert!(!request["messages"][1]["content"]
        .as_str()
        .unwrap()
        .contains("RETRIEVED"));
    assert!(fs::read_to_string(dir.path().join("auth.txt"))
        .unwrap()
        .contains("Bearer test-only-key"));
    let report = fs::read_to_string(dir.path().join("run/report.json")).unwrap();
    assert!(!report.contains("test-only-key"));
    let report: Value = serde_json::from_str(&report).unwrap();
    assert_eq!(request["max_tokens"], 8192);
    if always_truncated {
        assert_eq!(report["status"], "output_truncated");
        assert_eq!(report["requests"], 3);
        assert_eq!(report["usage"]["completion_tokens"], 24576);
        assert_eq!(report["phases"].as_array().unwrap().len(), 1);
        assert!(!report["events"]
            .as_array()
            .unwrap()
            .iter()
            .any(|e| e["strategy"].as_str().is_some_and(|s| s.contains("refine"))));
    } else if truncated && budget == 1 {
        assert_eq!(report["status"], "exhausted");
        assert_eq!(report["requests"], 1);
        assert_eq!(report["usage"]["completion_tokens"], 8192);
    } else {
        assert_eq!(report["verified"], true);
        assert_eq!(report["requests"], if truncated { 2 } else { 1 });
        if effective > 1 {
            assert!(dir.path().join("run/0-0.rs").exists());
            assert!(dir.path().join("run/0-1.rs").exists());
        }
        assert_eq!(
            report["usage"]["prompt_tokens"],
            if truncated { 27 } else { 20 }
        );
        assert_eq!(
            report["usage"]["completion_tokens"],
            if truncated { 8222 } else { 30 }
        );
    }
}

#[test]
fn unsafe_generation_candidates_trigger_the_next_round() {
    let input = fs::read_to_string(root().join("examples/count-input.rs")).unwrap();
    let good = fs::read_to_string(root().join("examples/count-proof.rs")).unwrap();
    let unsafe_code = good.replace("ensures r == n", "ensures true");
    let mut cfg = config();
    cfg["candidates"] = json!(2);
    cfg["inference_retries"] = json!(3);
    if let Some((dir, report)) = run(&input, &[unsafe_code.clone(), unsafe_code, good], cfg) {
        assert_eq!(report["requests"], 3);
        let rounds: Vec<_> = report["events"]
            .as_array()
            .unwrap()
            .iter()
            .filter(|e| e["stage"] == "generation_round")
            .collect();
        assert_eq!(rounds.len(), 2);
        for name in ["0-0.rs", "0-1.rs", "1-0.rs"] {
            assert!(dir.path().join("run").join(name).is_file(), "{name}");
        }
    }
}

#[test]
fn benchmark_preserves_phase_files_intermediate_candidates_and_logs() {
    let Ok(verus) = std::env::var("VERUS_PATH") else {
        return;
    };
    let dir = tempfile::tempdir().unwrap();
    let inputs = dir.path().join("inputs");
    fs::create_dir(&inputs).unwrap();
    let input = fs::read_to_string(root().join("examples/count-input.rs")).unwrap();
    let good = fs::read_to_string(root().join("examples/count-proof.rs")).unwrap();
    fs::write(inputs.join("a_success.rs"), &input).unwrap();
    fs::write(inputs.join("b_failed.rs"), &input).unwrap();
    fs::write(dir.path().join("good.rs"), good).unwrap();
    fs::write(dir.path().join("failed.rs"), &input).unwrap();
    let manifest = json!({
        "a_success.rs": [dir.path().join("good.rs")],
        "b_failed.rs": [dir.path().join("failed.rs"), dir.path().join("failed.rs"), dir.path().join("failed.rs")]
    });
    fs::write(dir.path().join("manifest.json"), manifest.to_string()).unwrap();
    let mut cfg = config();
    cfg["phases"] = json!(3);
    cfg["houdini_steps"] = json!(0);
    fs::write(dir.path().join("config.json"), cfg.to_string()).unwrap();
    let result = dir.path().join("20261027-130000-clover");
    let output = Command::new(env!("CARGO_BIN_EXE_verusforge"))
        .args(["benchmark", "--name", "clover", "--root"])
        .arg(&inputs)
        .arg("--config")
        .arg(dir.path().join("config.json"))
        .arg("--replay-manifest")
        .arg(dir.path().join("manifest.json"))
        .arg("--verus")
        .arg(verus)
        .arg("--output-dir")
        .arg(&result)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(!result.join("task-000").exists());
    assert!(!result.join("a_success.rs").exists());
    assert!(result.join("1-a_success.rs").exists());
    assert!(!result.join("2-a_success.rs").exists());
    for phase in 1..=3 {
        let source = fs::read_to_string(result.join(format!("{phase}-b_failed.rs"))).unwrap();
        assert!(source.contains("// Score:"));
        assert!(source.contains("// Safe: True"));
        let log = fs::read_to_string(result.join(format!("{phase}-b_failed.time"))).unwrap();
        assert!(log.contains("Generation round 1/1"));
        let candidate =
            fs::read_to_string(result.join(format!("intermediate-{phase}-b_failed/0-0.rs")))
                .unwrap();
        assert!(candidate.contains("// Score:"));
        assert!(result
            .join(format!("intermediate-{phase}-b_failed/final.rs"))
            .exists());
        assert!(result
            .join(format!("intermediate-{phase}-b_failed/final-hdn.rs"))
            .exists());
    }
    let summary: Value =
        serde_json::from_slice(&fs::read(result.join("summary.json")).unwrap()).unwrap();
    assert_eq!(summary["verified"], 1);
    assert_eq!(summary["tasks"][0]["result"], "1-a_success.rs");
    assert_eq!(summary["tasks"][1]["result"], "3-b_failed.rs");
    assert_eq!(summary["tasks"][1]["requests"], 3);
    assert_eq!(summary["tasks"][1]["phases"].as_array().unwrap().len(), 3);
}

#[test]
fn named_suite_replay_resolves_dataset_paths_and_records_sources() {
    let Ok(verus) = std::env::var("VERUS_PATH") else {
        return;
    };
    let dir = tempfile::tempdir().unwrap();
    let inputs = dir
        .path()
        .join("benchmarks/Verus-Bench/CloverBench/unverified");
    fs::create_dir_all(&inputs).unwrap();
    fs::copy(
        root().join("examples/count-input.rs"),
        inputs.join("count.rs"),
    )
    .unwrap();
    let proof = dir.path().join("good.rs");
    fs::copy(root().join("examples/count-proof.rs"), &proof).unwrap();
    let manifest = json!({"CloverBench/unverified/count.rs": [&proof]});
    fs::write(dir.path().join("manifest.json"), manifest.to_string()).unwrap();
    fs::write(dir.path().join("config.json"), config().to_string()).unwrap();
    for (name, args) in [
        ("named", vec!["--name", "clover"]),
        ("all", vec![]),
        (
            "custom",
            vec!["--root", "benchmarks/Verus-Bench/CloverBench/unverified"],
        ),
    ] {
        let output = Command::new(env!("CARGO_BIN_EXE_verusforge"))
            .current_dir(dir.path())
            .arg("benchmark")
            .args(args)
            .args([
                "--config",
                "config.json",
                "--replay-manifest",
                "manifest.json",
                "--verus",
            ])
            .arg(&verus)
            .arg("--output-dir")
            .arg(name)
            .output()
            .unwrap();
        let report: Value =
            serde_json::from_slice(&fs::read(dir.path().join(name).join("summary.json")).unwrap())
                .unwrap();
        assert_eq!(report["tasks"][0]["status"], "verified", "{name}: {report}");
        assert!(output.status.success());
        assert_eq!(report["tasks"][0]["replay_sources"], json!([&proof]));
        assert_eq!(report["tasks"][0]["requests"], 1);
    }
}
