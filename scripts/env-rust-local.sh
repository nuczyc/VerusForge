#!/usr/bin/env bash
# Source this optional helper on the current ARM64 development host.
_rustseek_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
_rustseek_native="${VERUSSEEK_NATIVE_ROOT:-$_rustseek_root/../../VerusSeek}"
if ! command -v cargo >/dev/null || [[ -z "${VERUS_PATH:-}" ]]; then
    if [[ -r "$_rustseek_native/scripts/env-native.sh" ]]; then
        source "$_rustseek_native/scripts/env-native.sh"
    else
        echo 'Configure Cargo and native VERUS_PATH, or set VERUSSEEK_NATIVE_ROOT.' >&2
        unset _rustseek_root _rustseek_native
        return 2
    fi
fi
# A writable copy of the existing registry was prepared for offline development.
if [[ -d /tmp/verusseek-rs-cargo/registry ]]; then
    export CARGO_HOME=/tmp/verusseek-rs-cargo
fi
unset _rustseek_root _rustseek_native
