#!/usr/bin/env bash
set -euo pipefail
project_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$project_root"
source scripts/env-rust-local.sh
cargo run --locked -p verusforge -- --help > /dev/null
cargo run --locked -p verusforge -- benchmark --help > /dev/null
cargo run --locked -p verusforge -- verify examples/quickstart/smoke.rs
printf '%s\n' 'VerusForge CLI smoke test: PASS'
