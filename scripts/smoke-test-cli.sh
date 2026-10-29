#!/usr/bin/env bash
set -euo pipefail
project_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$project_root"
source scripts/env-rust-local.sh
cargo run --locked -p verusseek-rs -- --help > /dev/null
cargo run --locked -p verusseek-rs -- benchmark --help > /dev/null
cargo run --locked -p verusseek-rs -- verify examples/quickstart/smoke.rs
printf '%s\n' 'VerusSeek-RS CLI smoke test: PASS'
