#!/usr/bin/env bash
set -euo pipefail

project_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
install_dir="$project_root/.local"
rust_version=1.91.0
verus_commit=6f528900ac664798daff003ab9548325fa1fb8c7
launch=0
if [[ -r "$install_dir/env.sh" && -z "${VERUS_PATH:-}" ]]; then
  source "$install_dir/env.sh"
fi
verus_override="${VERUS_PATH:-}"
usage() {
  cat <<'HELP'
Usage: bash scripts/setup.sh [--run] [--verus PATH]

Install dependencies, configure Rust 1.91.0 and Verus, build and verify a sample.
  --run         Open VerusSeek-RS after setup.
  --verus PATH  Use an existing Verus installation instead of building one.
  -h, --help    Show this help.
HELP
}
while (($#)); do
  case "$1" in
    --run) launch=1; shift ;;
    --verus)
      [[ $# -ge 2 && -n "$2" ]] || { echo '--verus requires a path' >&2; exit 2; }
      verus_override="$2"; shift 2 ;;
    -h|--help) usage; exit 0 ;;
    *) echo "Unknown option: $1" >&2; usage >&2; exit 2 ;;
  esac
done
case "$(uname -s):$(uname -m)" in
  Linux:x86_64|Linux:aarch64|Darwin:x86_64|Darwin:arm64) ;;
  *) echo 'Supported platforms: Linux x86_64/ARM64, macOS Intel/Apple Silicon. On Windows use WSL2.' >&2; exit 2 ;;
esac
mkdir -p "$install_dir"
setup_tmp="$(mktemp -d "$install_dir/setup.XXXXXX")"
trap 'rm -rf "$setup_tmp"' EXIT

# System package managers may request the usual administrator password.
missing=0
for dependency in curl git cc c++ make unzip tar pkg-config; do
  command -v "$dependency" >/dev/null 2>&1 || missing=1
done
if ((missing)); then
  echo '[1/5] Installing system dependencies...'
  if [[ "$(uname -s)" == Darwin ]]; then
    command -v brew >/dev/null 2>&1 || { echo 'Install Homebrew and Xcode Command Line Tools first.' >&2; exit 1; }
    xcode-select -p >/dev/null 2>&1 || { echo 'Run xcode-select --install, then retry.' >&2; exit 1; }
    brew install curl git make unzip pkg-config openssl
  else
    admin=()
    if [[ "$(id -u)" != 0 ]]; then
      command -v sudo >/dev/null 2>&1 || { echo 'Install curl git a C compiler make unzip tar pkg-config, then retry.' >&2; exit 1; }
      admin=(sudo)
    fi
    if command -v apt-get >/dev/null 2>&1; then
      "${admin[@]}" apt-get update
      "${admin[@]}" apt-get install -y ca-certificates curl git build-essential unzip tar pkg-config libssl-dev
    elif command -v dnf >/dev/null 2>&1; then
      "${admin[@]}" dnf install -y ca-certificates curl git gcc gcc-c++ make unzip tar pkgconf-pkg-config openssl-devel
    elif command -v pacman >/dev/null 2>&1; then
      "${admin[@]}" pacman -S --needed --noconfirm ca-certificates curl git base-devel unzip tar pkgconf openssl
    else
      echo 'Install curl git a C/C++ compiler make unzip tar pkg-config and OpenSSL development files, then retry.' >&2
      exit 1
    fi
  fi
else
  echo '[1/5] System dependencies available.'
fi

export CARGO_HOME="${CARGO_HOME:-$HOME/.cargo}"
export RUSTUP_HOME="${RUSTUP_HOME:-$HOME/.rustup}"
export PATH="$CARGO_HOME/bin:$PATH"
echo "[2/5] Configuring Rust $rust_version..."
if ! command -v rustup >/dev/null 2>&1; then
  curl --proto '=https' --tlsv1.2 -fSL --retry 3 https://sh.rustup.rs -o "$setup_tmp/rustup.sh"
  sh "$setup_tmp/rustup.sh" -y --profile minimal --no-modify-path --default-toolchain "$rust_version"
fi
if ! rustup run "$rust_version" rustc --version >/dev/null 2>&1; then
  rustup toolchain install "$rust_version" --profile minimal
fi
export RUSTUP_TOOLCHAIN="$rust_version"

verus_source="$install_dir/verus-source"
if [[ -n "$verus_override" ]]; then
  if [[ "$verus_override" != */* ]]; then
    verus_override="$(command -v "$verus_override")"
  fi
  [[ -x "$verus_override" ]] || { echo "Verus is not executable: $verus_override" >&2; exit 1; }
  verus_bin="$(cd "$(dirname "$verus_override")" && pwd)/$(basename "$verus_override")"
elif command -v verus >/dev/null 2>&1; then
  verus_bin="$(command -v verus)"
else
  verus_bin="$verus_source/source/target-verus/release/verus"
  if [[ ! -x "$verus_bin" || ! -f "$verus_source/.verusseek-build-complete" ]]; then
    echo '[3/5] Building Verus for this architecture (first installation can take a while)...'
    if [[ ! -d "$verus_source" ]]; then
      curl --proto '=https' --tlsv1.2 -fSL --retry 3 \
        "https://codeload.github.com/verus-lang/verus/tar.gz/$verus_commit" -o "$setup_tmp/verus.tar.gz"
      mkdir "$setup_tmp/verus-source"
      tar -xzf "$setup_tmp/verus.tar.gz" -C "$setup_tmp/verus-source" --strip-components=1
      mv "$setup_tmp/verus-source" "$verus_source"
    fi
    (
      cd "$verus_source"
      rustup toolchain install
      cd source
      if [[ ! -x z3 ]]; then
        bash tools/get-z3.sh
      fi
      # The upstream activation script defines a cargo function; keep it in this subshell.
      set +u
      source ../tools/activate
      set -u
      vargo build --release
    )
    touch "$verus_source/.verusseek-build-complete"
  fi
fi
export VERUS_PATH="$verus_bin"
if [[ -x "$(dirname "$verus_bin")/z3" ]]; then
  export VERUS_Z3_PATH="$(dirname "$verus_bin")/z3"
fi
echo "[3/5] Verus: $VERUS_PATH"
"$VERUS_PATH" --version

echo '[4/5] Building VerusSeek-RS...'
cd "$project_root"
cargo build --locked -p verusseek-rs

echo '[5/5] Verifying sample...'
cargo run --locked -p verusseek-rs -- verify examples/quickstart/smoke.rs

# Publish environment only after the complete installation has passed verification.
{
  printf '# Generated by scripts/setup.sh\n'
  printf 'export CARGO_HOME=%q\n' "$CARGO_HOME"
  printf 'export RUSTUP_HOME=%q\n' "$RUSTUP_HOME"
  printf 'export RUSTUP_TOOLCHAIN=%q\n' "$rust_version"
  printf 'export VERUS_PATH=%q\n' "$VERUS_PATH"
  if [[ -n "${VERUS_Z3_PATH:-}" ]]; then printf 'export VERUS_Z3_PATH=%q\n' "$VERUS_Z3_PATH"; fi
  printf 'export PATH="$CARGO_HOME/bin:$PATH"\n'
} > "$setup_tmp/env.sh"
mv "$setup_tmp/env.sh" "$install_dir/env.sh"
printf '\nSetup complete. Start with: bash scripts/run.sh\n'
if ((launch)); then
  bash scripts/run.sh
fi
