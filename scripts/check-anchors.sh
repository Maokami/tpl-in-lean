#!/usr/bin/env bash
# ANCHOR 마커의 짝이 맞는지, 그리고 Answers/Exercises 두 트리의
# `@[exercise]` 태그 집합이 일치하는지 검사한다.
set -euo pipefail
cd "$(dirname "$0")/.."

fail=0

echo "== ANCHOR 짝 검사 =="
while IFS= read -r f; do
  opens=$(grep -c -- '-- ANCHOR: ' "$f" || true)
  closes=$(grep -c -- '-- ANCHOR_END: ' "$f" || true)
  if [ "$opens" != "$closes" ]; then
    echo "  ✖ $f : ANCHOR $opens 개, ANCHOR_END $closes 개"
    fail=1
  fi
done < <(find Reynolds -name '*.lean')
[ "$fail" = 0 ] && echo "  ✔ 이상 없음"

echo "== @[exercise] 태그 일치 검사 =="
tags () { grep -rho '@\[exercise "[^"]*"' "$1" 2>/dev/null | sed 's/.*"\(.*\)"/\1/' | sort; }
a=$(tags Reynolds/Answers)
e=$(tags Reynolds/Exercises)
if [ "$a" != "$e" ]; then
  echo "  ✖ Answers 와 Exercises 의 태그 집합이 다르다:"
  diff <(echo "$a") <(echo "$e") | sed 's/^/    /' || true
  fail=1
else
  echo "  ✔ 일치 ($(echo "$a" | grep -c . || true) 개)"
fi

exit "$fail"
