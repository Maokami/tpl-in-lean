/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Exercises.Ch02.Syntax
public import Reynolds.Answers.Ch02.Notation
public import Reynolds.Exercises.Ch02.Semantics

/-!
# 2장 «단순 명령형 언어» — 연습 (Exercises)

1장에는 비종료가 없었다. `while` 이 들어오면서 의미 함수가 전함수로 정의되지 않고,
그것을 해결하려고 Scott 이 만든 것이 도메인 이론이다. Reynolds 는 §2.3~2.4 에서
그 최소한을 직접 만든다. 우리도 Mathlib 에서 꺼내 쓰지 않고 직접 만든 뒤,
다 만들고 나서 Mathlib 의 대응물과 대조한다.

## 읽는 순서
1. `Syntax.lean` — §2.1 추상 구문 (`BoolExp`, `Comm`)
2. `Notation.lean` — §2.1 구체 구문. 명령 DSL
3. `Semantics.lean` — §2.2 표시적 의미론. `while` 이 왜 벽인가

전체 설계는 [`docs/chapter-02.md`](../../docs/chapter-02.md).
-/
