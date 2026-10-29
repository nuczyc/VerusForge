#!/usr/bin/env bash
set -euo pipefail
project_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
fixture="$(mktemp -d)"
trap 'rm -rf "$fixture"' EXIT
mkdir -p "$fixture/scripts" "$fixture/.local" "$fixture/bin"
cp "$project_root/scripts/env-rust-local.sh" "$fixture/scripts/"
for name in cargo saved-verus explicit-verus; do
  printf '#!/usr/bin/env bash\nexit 0\n' > "$fixture/bin/$name"
  chmod +x "$fixture/bin/$name"
done
{
  printf 'export VERUS_PATH=%q\n' "$fixture/bin/saved-verus"
  printf 'export CARGO_HOME=%q\n' "$fixture/saved-cargo"
  printf 'export RUSTUP_HOME=%q\n' "$fixture/saved-rustup"
  printf 'export RUSTUP_TOOLCHAIN=1.91.0\n'
} > "$fixture/.local/env.sh"
(
  export PATH="$fixture/bin:$PATH"
  unset VERUS_PATH CARGO_HOME RUSTUP_HOME RUSTUP_TOOLCHAIN
  source "$fixture/scripts/env-rust-local.sh"
  [[ "$VERUS_PATH" == "$fixture/bin/saved-verus" ]]
  [[ "$CARGO_HOME" == "$fixture/saved-cargo" ]]
)
(
  export PATH="$fixture/bin:$PATH"
  export VERUS_PATH="$fixture/bin/explicit-verus"
  export CARGO_HOME="$fixture/custom cargo" RUSTUP_HOME="$fixture/custom rustup"
  export RUSTUP_TOOLCHAIN=custom-toolchain
  export VERUS_Z3_PATH="$fixture/custom-z3"
  source "$fixture/scripts/env-rust-local.sh"
  [[ "$VERUS_PATH" == "$fixture/bin/explicit-verus" ]]
  [[ "$CARGO_HOME" == "$fixture/custom cargo" ]]
  [[ "$RUSTUP_HOME" == "$fixture/custom rustup" ]]
  [[ "$RUSTUP_TOOLCHAIN" == custom-toolchain ]]
  [[ "$VERUS_Z3_PATH" == "$fixture/custom-z3" ]]
  [[ "$PATH" == "$CARGO_HOME/bin:"* ]]
)
(
  export PATH="$fixture/bin:$PATH"
  export VERUS_PATH="$fixture/missing-verus"
  if source "$fixture/scripts/env-rust-local.sh" 2>/dev/null; then
    echo 'Invalid explicit VERUS_PATH must fail instead of using a saved value' >&2
    exit 1
  fi
)
echo 'Environment priority regression checks: PASS'
