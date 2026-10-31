#!/bin/bash
# Lean Lab setup for any agent container: Codex, Jules, Gemini CLI, Grok Build.
# Tool-neutral twin of .claude/hooks/session-start.sh. Safe to run twice.
set -uo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
LAB="$ROOT/LeanLab"
export PATH="$HOME/.elan/bin:$PATH"
TC=$(sed 's/.*://' "$LAB/lean-toolchain")
VER=${TC#v}
TMP=$(mktemp -d)
df -h "$HOME" | tail -1
if ! command -v elan >/dev/null 2>&1; then
  curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o "$TMP/elan-init.sh"
  sh "$TMP/elan-init.sh" -y --default-toolchain none >/dev/null
fi
if [ ! -e "$HOME/.elan/toolchains/leanprover--lean4---$TC" ]; then
  if ! elan toolchain install "leanprover/lean4:$TC" 2>/dev/null; then
    python3 -c "import zstandard" 2>/dev/null || python3 -m pip install -q zstandard || python3 -m pip install -q --break-system-packages zstandard
    curl -sSfL -o "$TMP/lean.tar.zst" "https://github.com/leanprover/lean4/releases/download/$TC/lean-$VER-linux.tar.zst"
    python3 -I -c "
import zstandard, sys
with open(sys.argv[1],'rb') as f, open(sys.argv[2],'wb') as o: zstandard.ZstdDecompressor().copy_stream(f,o)
" "$TMP/lean.tar.zst" "$TMP/lean.tar"
    mkdir -p "$HOME/.elan/toolchains"; tar xf "$TMP/lean.tar" -C "$HOME/.elan/toolchains"; rm -f "$TMP/lean.tar"
    elan toolchain link "leanprover--lean4---$TC" "$HOME/.elan/toolchains/lean-$VER-linux"
  fi
fi
rm -rf "$TMP"
grep -q 'elan/bin' "$HOME/.bashrc" 2>/dev/null || echo 'export PATH="$HOME/.elan/bin:$PATH"' >> "$HOME/.bashrc"
cd "$LAB"
lake resolve-deps >/dev/null 2>&1 || true
if timeout 1200 lake exe cache get >/tmp/lean-cache-get.log 2>&1 || timeout 1200 lake exe cache get >>/tmp/lean-cache-get.log 2>&1; then
  echo "Mathlib cache: ok"
else
  echo "Mathlib cache: FAILED, see /tmp/lean-cache-get.log; do not build Mathlib from source" >&2
fi
df -h "$HOME" | tail -1
exit 0
