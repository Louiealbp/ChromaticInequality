#!/usr/bin/env bash
set -euo pipefail

# Build each genuine Lake module target sequentially, then the whole library
# and the independent Lean audit. Serial compilation bounds peak memory use.
script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
exec python3 "$script_dir/scripts/verify_project.py" --audit Audit.lean "$@"
