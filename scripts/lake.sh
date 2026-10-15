#!/usr/bin/env bash
set -euo pipefail
repo_root="$(cd "$(dirname "$0")/.." && pwd)"
case "$(uname -s)-$(uname -m)" in
  Darwin-arm64) compiler_bin="$repo_root/.toolchain/lean-4.24.0-darwin_aarch64/bin" ;;
  Linux-x86_64) compiler_bin="$repo_root/.toolchain/lean-4.24.0-linux/bin" ;;
  *) compiler_bin="$repo_root/.toolchain/not-installed/bin" ;;
esac
if [[ -x "$compiler_bin/lake" ]]; then
  export PATH="$compiler_bin:$PATH"
fi
export LC_ALL=C
export MATHLIB_CACHE_DIR="$repo_root/.toolchain/mathlib-cache"
cd "$repo_root"
exec lake "$@"
