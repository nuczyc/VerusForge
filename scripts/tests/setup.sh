#!/usr/bin/env bash
# Isolated installer tests: downloads, rustup and compilation are replaced by fixtures.
set -euo pipefail
project_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
fixture="$(mktemp -d)"
trap 'rm -rf "$fixture"' EXIT
export SETUP_TEST_ROOT="$fixture"
mkdir -p "$fixture/bin" "$fixture/project with spaces/scripts" "$fixture/source/top/source/tools" "$fixture/source/top/tools"
cp "$project_root/scripts/setup.sh" "$project_root/scripts/run.sh" "$project_root/scripts/env-rust-local.sh" "$fixture/project with spaces/scripts/"
cat > "$fixture/bin/uname" <<'MOCK'
#!/usr/bin/env bash
case "$1" in -s) echo Linux;; -m) echo aarch64;; esac
MOCK
cat > "$fixture/bin/rustup" <<'MOCK'
#!/usr/bin/env bash
printf 'rustup %s\n' "$*" >> "$SETUP_TEST_ROOT/calls"
MOCK
cat > "$fixture/bin/cargo" <<'MOCK'
#!/usr/bin/env bash
printf 'cargo %s\n' "$*" >> "$SETUP_TEST_ROOT/calls"
if [[ "$*" == *'verify examples/quickstart/smoke.rs'* && -f "$SETUP_TEST_ROOT/fail" ]]; then exit 1; fi
MOCK
cat > "$fixture/bin/curl" <<'MOCK'
#!/usr/bin/env bash
printf 'download\n' >> "$SETUP_TEST_ROOT/calls"
while (($#)); do
  if [[ "$1" == -o ]]; then cp "$SETUP_TEST_ROOT/source.tar.gz" "$2"; exit; fi
  shift
done
exit 1
MOCK
cat > "$fixture/source/top/source/tools/get-z3.sh" <<'MOCK'
#!/usr/bin/env bash
printf '#!/usr/bin/env bash\nexit 0\n' > z3
chmod +x z3
MOCK
cat > "$fixture/source/top/tools/activate" <<'MOCK'
vargo() {
  printf 'build-verus\n' >> "$SETUP_TEST_ROOT/calls"
  mkdir -p target-verus/release
  printf '#!/usr/bin/env bash\necho MockVerus\n' > target-verus/release/verus
  chmod +x target-verus/release/verus
  cp z3 target-verus/release/z3
}
MOCK
chmod +x "$fixture/bin/"*
tar -czf "$fixture/source.tar.gz" -C "$fixture/source" top
(
  unset VERUS_PATH VERUS_Z3_PATH RUSTUP_TOOLCHAIN
  export PATH="$fixture/bin:$PATH"
  export CARGO_HOME="$fixture/cargo" RUSTUP_HOME="$fixture/rustup"
  cd "$fixture/project with spaces"
  # ARM64 takes the source-build path and produces a loadable, shell-escaped environment.
  bash scripts/setup.sh > "$fixture/output"
  [[ -f .local/env.sh ]]
  source scripts/env-rust-local.sh
  [[ -x "$VERUS_PATH" && -x "$VERUS_Z3_PATH" ]]
  [[ "$RUSTUP_TOOLCHAIN" == 1.91.0 ]]
  bash scripts/run.sh benchmark --name clover --limit 3
  # A fresh invocation loads the saved environment; no new download or Verus build.
  unset VERUS_PATH VERUS_Z3_PATH
  bash scripts/setup.sh > "$fixture/output"
  [[ "$(grep -c '^download$' "$fixture/calls")" == 1 ]]
  [[ "$(grep -c '^build-verus$' "$fixture/calls")" == 1 ]]
  grep -q '^cargo run --locked -p verusseek-rs -- benchmark --name clover --limit 3$' "$fixture/calls"
  # Failed verification cannot publish a successful installation environment.
  cp .local/env.sh "$fixture/previous-env"
  touch "$fixture/fail"
  if bash scripts/setup.sh > "$fixture/output" 2>&1; then echo 'Expected verification failure' >&2; exit 1; fi
  cmp .local/env.sh "$fixture/previous-env"
  if bash scripts/setup.sh --verus > "$fixture/output" 2>&1; then exit 1; fi
)
echo 'Setup regression checks: PASS'
