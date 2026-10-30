#!/usr/bin/env bash
set -euo pipefail
project_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$project_root"
source scripts/env-rust-local.sh
exec cargo run --locked -p verusforge -- "$@"
