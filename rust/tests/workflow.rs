use std::{fs, path::PathBuf, process::Command};

fn root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

#[test]
fn replay_with_real_verus() {
    let Ok(verus) = std::env::var("VERUS_PATH") else {
        eprintln!("SKIP real-Verus test: VERUS_PATH is unset");
        return;
    };
    let tmp = tempfile::tempdir().unwrap();
    let run = tmp.path().join("replay");
    let output = Command::new(env!("CARGO_BIN_EXE_verusforge"))
        .arg("prove")
        .arg(root().join("examples/input.rs"))
        .arg("--output-dir")
        .arg(&run)
        .arg("--kb")
        .arg(root().join("examples/kb.json"))
        .arg("--verus")
        .arg(verus)
        .arg("--replay")
        .arg(root().join("examples/bad-proof.txt"))
        .arg("--replay")
        .arg(root().join("examples/good-proof.txt"))
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let report: serde_json::Value =
        serde_json::from_slice(&fs::read(run.join("report.json")).unwrap()).unwrap();
    assert_eq!(report["mode"], "replay");
    assert_eq!(report["attempts"][0]["verified"], false);
    assert_eq!(report["attempts"][1]["verified"], true);
    let verified = fs::read_to_string(run.join("verified.rs")).unwrap();
    let input = fs::read_to_string(root().join("examples/input.rs")).unwrap();
    assert_eq!(
        verified,
        input.replace(
            "/* VERUSFORGE_PROOF */",
            &fs::read_to_string(root().join("examples/good-proof.txt")).unwrap()
        )
    );
}

#[test]
fn whole_program_synthesis_and_contract_rejection() {
    let Ok(verus) = std::env::var("VERUS_PATH") else {
        return;
    };
    let tmp = tempfile::tempdir().unwrap();
    let input = root().join("examples/count-input.rs");
    let good = root().join("examples/count-proof.rs");
    let bad = tmp.path().join("unsafe.rs");
    fs::write(
        &bad,
        fs::read_to_string(&good)
            .unwrap()
            .replace("ensures r == n", "ensures true"),
    )
    .unwrap();
    let baseline = Command::new(env!("CARGO_BIN_EXE_verusforge"))
        .arg("verify")
        .arg(&input)
        .arg("--verus")
        .arg(&verus)
        .output()
        .unwrap();
    assert!(
        !baseline.status.success(),
        "fixture must require an invariant"
    );
    let run = tmp.path().join("synthesis");
    let output = Command::new(env!("CARGO_BIN_EXE_verusforge"))
        .arg("synthesize")
        .arg(input)
        .arg("--output-dir")
        .arg(&run)
        .arg("--config")
        .arg(root().join("tests/fixtures/config/smoke.json"))
        .arg("--verus")
        .arg(verus)
        .arg("--replay")
        .arg(bad)
        .arg("--replay")
        .arg(good)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let report: serde_json::Value =
        serde_json::from_slice(&fs::read(run.join("report.json")).unwrap()).unwrap();
    assert_eq!(report["verified"], true);
    assert_eq!(report["requests"], 2);
    assert!(report["events"]
        .as_array()
        .unwrap()
        .iter()
        .any(|e| e["safe"] == false));
    assert!(run.join("verified.rs").exists());
    let final_code = fs::read_to_string(run.join("final.rs")).unwrap();
    assert!(final_code.contains("// Score: Compilation Error: False, Verified:"));
    assert!(final_code.contains("Errors: 0, Verus Errors: 0"));
    assert!(final_code.ends_with("// Safe: True\n"));
    assert_eq!(
        fs::read_to_string(run.join("verified.rs")).unwrap(),
        final_code
    );
    assert!(String::from_utf8_lossy(&output.stderr).contains("Phase 1/1"));
}

#[test]
fn houdini_removes_failed_invariant_with_real_verus() {
    let Ok(verus) = std::env::var("VERUS_PATH") else {
        return;
    };
    let tmp = tempfile::tempdir().unwrap();
    let bad = tmp.path().join("bad-invariant.rs");
    fs::write(
        &bad,
        fs::read_to_string(root().join("examples/count-proof.rs"))
            .unwrap()
            .replace(
                "invariant i <= n, n < 100,",
                "invariant i <= n, n < 100, i < n,",
            ),
    )
    .unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_verusforge"))
        .arg("synthesize")
        .arg(root().join("examples/count-input.rs"))
        .arg("--config")
        .arg(root().join("tests/fixtures/config/smoke.json"))
        .arg("--verus")
        .arg(verus)
        .arg("--replay")
        .arg(bad)
        .arg("--output-dir")
        .arg(tmp.path().join("run"))
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{} {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let report: serde_json::Value =
        serde_json::from_slice(&fs::read(tmp.path().join("run/report.json")).unwrap()).unwrap();
    assert!(report["events"]
        .as_array()
        .unwrap()
        .iter()
        .any(
            |e| e["stage"].as_str().is_some_and(|s| s.contains("houdini"))
                && e["evaluation"]["success"] == true
        ));
}

#[test]
fn deterministic_loop_strategy_with_real_verus() {
    let Ok(verus) = std::env::var("VERUS_PATH") else {
        return;
    };
    let tmp = tempfile::tempdir().unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_verusforge"))
        .arg("synthesize")
        .arg(root().join("examples/count-input.rs"))
        .arg("--config")
        .arg(root().join("tests/fixtures/config/local.json"))
        .arg("--verus")
        .arg(verus)
        .arg("--local-only")
        .arg("--output-dir")
        .arg(tmp.path().join("run"))
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{} {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let report: serde_json::Value =
        serde_json::from_slice(&fs::read(tmp.path().join("run/report.json")).unwrap()).unwrap();
    assert_eq!(report["requests"], 0);
    assert_eq!(report["verified"], true);
}

#[test]
#[ignore = "requires local TCP listener permission; run explicitly outside a network-restricted sandbox"]
fn live_http_contract_with_real_verus() {
    use std::{
        io::{Read, Write},
        net::TcpListener,
        thread,
    };
    let Ok(verus) = std::env::var("VERUS_PATH") else {
        return;
    };
    let server = TcpListener::bind("127.0.0.1:0").unwrap();
    let address = server.local_addr().unwrap();
    server.set_nonblocking(true).unwrap();
    let worker = thread::spawn(move || {
        for proof in ["assert(x > 100);", "assert(x + 1 <= 100);"] {
            let start = std::time::Instant::now();
            let mut socket = loop {
                match server.accept() {
                    Ok((socket, _)) => break socket,
                    Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => {
                        assert!(start.elapsed().as_secs() < 20, "HTTP request never arrived");
                        thread::sleep(std::time::Duration::from_millis(10));
                    }
                    Err(e) => panic!("{e}"),
                }
            };
            socket
                .set_read_timeout(Some(std::time::Duration::from_secs(5)))
                .unwrap();
            let mut data = Vec::new();
            let mut buffer = [0u8; 8192];
            loop {
                let n = socket.read(&mut buffer).unwrap();
                assert!(n > 0);
                data.extend_from_slice(&buffer[..n]);
                let text = String::from_utf8_lossy(&data);
                if let Some((headers, body)) = text.split_once("\r\n\r\n") {
                    let length: usize = headers
                        .lines()
                        .find_map(|l| {
                            l.to_ascii_lowercase()
                                .strip_prefix("content-length:")
                                .map(|v| v.trim().parse().unwrap())
                        })
                        .unwrap();
                    if body.len() >= length {
                        break;
                    }
                }
            }
            let request = String::from_utf8(data).unwrap();
            assert!(request.contains("POST /v1/chat/completions"));
            assert!(request.contains("Authorization: Bearer test-only"));
            if proof.contains("<=") {
                assert!(request.contains("Previous proof"));
            }
            let body = serde_json::json!({"choices":[{"message":{"content":proof}}]}).to_string();
            write!(socket, "HTTP/1.1 200 OK\r\nContent-Type: application/json\r\nContent-Length: {}\r\nConnection: close\r\n\r\n{}", body.len(), body).unwrap();
        }
    });
    let tmp = tempfile::tempdir().unwrap();
    let run = tmp.path().join("live");
    let output = Command::new(env!("CARGO_BIN_EXE_verusforge"))
        .env("VERUSFORGE_API_KEY", "test-only")
        .env("NO_PROXY", "127.0.0.1")
        .arg("prove")
        .arg(root().join("examples/input.rs"))
        .arg("--output-dir")
        .arg(&run)
        .arg("--verus")
        .arg(verus)
        .args([
            "--model",
            "local-contract-test",
            "--api-base",
            &format!("http://{address}/v1"),
        ])
        .output()
        .unwrap();
    worker.join().unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let report: serde_json::Value =
        serde_json::from_slice(&fs::read(run.join("report.json")).unwrap()).unwrap();
    assert_eq!(report["mode"], "live");
    assert_eq!(report["attempts"][0]["verified"], false);
    assert_eq!(report["attempts"][1]["verified"], true);
}
