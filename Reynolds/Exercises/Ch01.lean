/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Exercises.Ch01.Syntax
public import Reynolds.Exercises.Ch01.Semantics
public import Reynolds.Exercises.Ch01.Validity
public import Reynolds.Exercises.Ch01.FreeVars
public import Reynolds.Exercises.Ch01.Background
public import Reynolds.Exercises.Ch01.Depth.Algebra
public import Reynolds.Exercises.Ch01.Depth.SignatureFunctor

/-!
# 1장 «술어 논리» — 연습 (Exercises)

## 읽는 순서
1. `Background.lean` — **먼저 읽어라.** 책이 가정하고 넘어가는 것 (메타/객체 구분)
2. `Syntax.lean` — §1.1 추상 구문
3. `Semantics.lean` — §1.2 표시적 의미론
4. `Validity.lean` — §1.3 타당성과 추론, 건전성
5. `FreeVars.lean` — §1.4 자유 변수와 일치 정리
6. `Depth/Algebra.lean` — 심화 A (선택). 대수와 초기성
7. `Depth/SignatureFunctor.lean` — 심화 B (선택). 시그니처 함자와 Lambek
-/
