#!/usr/bin/env bash
set -euo pipefail

echo "=== Semantic agreement tests ==="
lake exe test-semantics

echo ""
echo "=== Example verification tests ==="
for f in Examples/*.ml; do
  printf "%-30s" "$f"
  if lake exe mica "$f" > /dev/null 2>&1; then
    echo "✓"
  else
    echo "✗"
    exit 1
  fi
done

echo ""
echo "All tests passed."
