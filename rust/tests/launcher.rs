use std::process::{Command, Stdio};

#[test]
fn no_arguments_with_piped_input_prints_help_without_terminal_controls() {
    let output = Command::new(env!("CARGO_BIN_EXE_verusforge"))
        .stdin(Stdio::null())
        .output()
        .unwrap();
    assert!(output.status.success());
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("Usage:"));
    assert!(stdout.contains("benchmark"));
    assert!(!stdout.contains('\u{1b}'));
}

#[test]
fn direct_commands_bypass_the_welcome_screen() {
    for command in [
        "--help",
        "generate",
        "verify",
        "benchmark",
        "search",
        "config",
    ] {
        let mut process = Command::new(env!("CARGO_BIN_EXE_verusforge"));
        process.arg(command);
        if command != "--help" {
            process.arg("--help");
        }
        let output = process.stdin(Stdio::null()).output().unwrap();
        assert!(output.status.success(), "{command}");
        assert!(!output.stdout.contains(&0x1b), "{command}");
    }
}

#[test]
fn lexical_search_is_available_without_loading_api_credentials() {
    let output = Command::new(env!("CARGO_BIN_EXE_verusforge"))
        .args(["search", "assert", "--kb"])
        .arg(std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/kb.json"))
        .stdin(Stdio::null())
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let hits: serde_json::Value = serde_json::from_slice(&output.stdout).unwrap();
    assert!(hits.is_array());
}
