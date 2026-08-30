/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Answers.Ch02.Syntax
public import Reynolds.Answers.Ch02.Notation
public import Reynolds.Answers.Ch02.Semantics
public import Reynolds.Answers.Ch02.Domain
public import Reynolds.Answers.Ch02.Domain.Lifting
public import Reynolds.Answers.Ch02.Domain.FunctionSpace
public import Reynolds.Answers.Ch02.Fixpoint

/-!
# 2장 «단순 명령형 언어» — 완성본 (Answers)

1장에는 비종료가 없었다. `while`이 들어오면 명령의 실행은 부분함수가 되지만, 의미 함수
자체는 `State V → SigmaBot V`라는 전함수로 표현한다. `none`이 결과 상태를 내지 않는
계산을 나타낸다. Reynolds는 이 의미 공간에 정보 순서를 주고, 연속 자기함수의 최소
고정점으로 `while`의 의미를 고른다. §2.3~2.4의 정의를 Mathlib에서 바로 가져오지 않고
직접 만든 뒤, 나중에 라이브러리의 대응물과 대조한다.

## 읽는 순서
1. `Syntax.lean` — §2.1 추상 구문 (`BoolExp`, `Comm`)
2. `Notation.lean` — §2.1 구체 구문. 명령 DSL
3. `Semantics.lean` — §2.2 표시적 의미론과 `while`의 풀기 방정식
4. `Domain.lean` — §2.3 사슬·프리도메인(predomain)·연속성

전체 설계는 [`docs/chapter-02.md`](../../docs/chapter-02.md).
-/
