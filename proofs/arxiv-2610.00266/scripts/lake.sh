#!/usr/bin/env bash
set -euo pipefail
root="$(cd "$(dirname "$0")/.." && pwd)"
case "$(uname -s)-$(uname -m)" in
 Linux-x86_64) compiler="$root/.toolchain/lean-4.24.0-linux/bin" ;;
 Darwin-arm64) compiler="$root/.toolchain/lean-4.24.0-darwin_aarch64/bin" ;;
 *) echo "Unsupported platform" >&2; exit 2 ;;
esac
export PATH="$compiler:$PATH" LC_ALL=C
cd "$root"
"$compiler/lean" --version | grep -q '797c613eb9b6d4ec95db23e3e00af9ac6657f24b'
exec "$compiler/lake" --no-cache "$@"
