#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
VERUS_BIN="${VERUS_PATH:-verus}"
"$VERUS_BIN" "$ROOT/examples/quickstart/smoke.rs"
