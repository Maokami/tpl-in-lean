#!/usr/bin/env bash
# 저장소 규약 검사:
#   1. ANCHOR 마커의 짝이 맞는가
#   2. ANCHOR 가 Answers 트리에만 있는가  (문서는 Answers 만 인용한다)
#   3. Answers / Exercises 의 @[exercise] 태그 집합이 일치하는가
#   4. 같은 exercise id 가 한 트리 안에서 중복되지 않는가
set -euo pipefail
cd "$(dirname "$0")/.."

fail=0

echo "== 1. ANCHOR 짝 검사 =="
while IFS= read -r f; do
  opens=$(grep -c -- '-- ANCHOR: ' "$f" || true)
  closes=$(grep -c -- '-- ANCHOR_END: ' "$f" || true)
  if [ "$opens" != "$closes" ]; then
    echo "  ✖ $f : ANCHOR $opens 개, ANCHOR_END $closes 개"
    fail=1
  fi
done < <(find Reynolds -name '*.lean')
[ "$fail" = 0 ] && echo "  ✔ 이상 없음"

echo "== 2. ANCHOR 는 Answers 트리 전용 =="
stray=$(grep -rln -- '-- ANCHOR' Reynolds/Exercises 2>/dev/null || true)
if [ -n "$stray" ]; then
  echo "  ✖ Exercises 트리에 ANCHOR 가 있다 (AGENTS.md §3.1):"
  echo "$stray" | sed 's/^/    /'
  fail=1
else
  echo "  ✔ 이상 없음"
fi

tags () { grep -rho '@\[exercise "[^"]*"' "$1" 2>/dev/null | sed 's/.*"\(.*\)"/\1/' | sort; }

echo "== 3. @[exercise] 태그 일치 =="
a=$(tags Reynolds/Answers)
e=$(tags Reynolds/Exercises)
if [ "$a" != "$e" ]; then
  echo "  ✖ Answers 와 Exercises 의 태그 집합이 다르다:"
  diff <(echo "$a") <(echo "$e") | sed 's/^/    /' || true
  fail=1
else
  n=$(echo "$a" | grep -c . || true)
  echo "  ✔ 일치 ($n 개)"
fi

echo "== 4. exercise id 중복 검사 =="
for tree in Answers Exercises; do
  dup=$(tags "Reynolds/$tree" | uniq -d)
  if [ -n "$dup" ]; then
    echo "  ✖ $tree 트리에 중복된 id:"
    echo "$dup" | sed 's/^/    /'
    fail=1
  fi
done
[ "$fail" = 0 ] && echo "  ✔ 이상 없음"

exit "$fail"
