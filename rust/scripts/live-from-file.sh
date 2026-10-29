#!/usr/bin/env bash
set -euo pipefail
set +x
project_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
credential_file="${1:-$project_root/apikey}"
if [[ ! -r "$credential_file" ]]; then
  echo 'API configuration file is not readable.' >&2
  exit 2
fi
credential_file="$(cd "$(dirname "$credential_file")" && pwd)/$(basename "$credential_file")"
cd "$project_root"
exec cargo run --locked -p verusseek-rs -- benchmark --api-config "$credential_file" \
  --config rust/config.benchmark.json
