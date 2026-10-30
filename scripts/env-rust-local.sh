#!/usr/bin/env bash
# Load saved defaults while retaining caller-supplied toolchain settings.
_verusforge_load_environment() {
    local project_root name assignment
    local -a overrides=()
    project_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
    for name in CARGO_HOME RUSTUP_HOME RUSTUP_TOOLCHAIN VERUS_PATH VERUS_Z3_PATH; do
        if [[ -n "${!name:-}" ]]; then
            overrides+=("$name=${!name}")
        fi
    done
    if [[ -r "$project_root/.local/env.sh" ]]; then
        source "$project_root/.local/env.sh"
    fi
    for assignment in "${overrides[@]}"; do
        export "$assignment"
    done
    if [[ -n "${CARGO_HOME:-}" ]]; then
        export PATH="$CARGO_HOME/bin:$PATH"
    fi
    if ! command -v cargo >/dev/null 2>&1; then
        echo 'Run: bash scripts/setup.sh' >&2
        return 1
    fi
    if [[ -z "${VERUS_PATH:-}" ]]; then
        export VERUS_PATH="$(command -v verus || true)"
    fi
    if [[ ! -x "${VERUS_PATH:-}" ]] && ! command -v "${VERUS_PATH:-verus}" >/dev/null 2>&1; then
        echo 'Run: bash scripts/setup.sh (or set VERUS_PATH to an installed Verus)' >&2
        return 1
    fi
}
if _verusforge_load_environment; then
    unset -f _verusforge_load_environment
else
    unset -f _verusforge_load_environment
    return 1
fi
