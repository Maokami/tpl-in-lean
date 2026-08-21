/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Answers.Ch01.Syntax
public import Reynolds.Answers.Ch01.Notation
public import Reynolds.Answers.Ch01.Realizations
public import Reynolds.Answers.Ch01.Semantics
public import Reynolds.Answers.Ch01.Validity
public import Reynolds.Answers.Ch01.FreeVars
public import Reynolds.Answers.Ch01.Substitution
public import Reynolds.Answers.Ch01.Ex
public import Reynolds.Answers.Ch01.Ex.Summation
public import Reynolds.Answers.Ch01.Background
public import Reynolds.Answers.Ch01.Depth.Algebra
public import Reynolds.Answers.Ch01.Depth.SignatureFunctor
public import Reynolds.Answers.Ch01.Depth.TermMonad

/-!
# 1장 «술어 논리» — 완성본 (Answers)

## 읽는 순서
1. `Background.lean` — **먼저 읽어라.** 책이 가정하고 넘어가는 것 (메타/객체 구분)
2. `Syntax.lean` — §1.1 추상 구문
3. `Notation.lean` — §1.1 구체 구문 (객체 언어 DSL)
4. `Semantics.lean` — §1.2 표시적 의미론
5. `Validity.lean` — §1.3 타당성과 추론, 건전성
6. `FreeVars.lean` — §1.4 자유 변수와 일치 정리
7. `Substitution.lean` — §1.4 치환, 명제 1.2~1.5
8. `Realizations.lean` — §1.1 실현 (연습 1.3)
9. `Ex.lean` — 책 연습문제 1.1~1.7
10. `Ex/Summation.lean` — 연습 1.5·1.6 (합 식). 축소판 언어로 따로 세운다
11. `Depth/Algebra.lean` — 심화 A (선택). 대수와 초기성
12. `Depth/SignatureFunctor.lean` — 심화 B (선택). 시그니처 함자와 Lambek
13. `Depth/TermMonad.lean` — 심화 A (선택). 치환은 bind 다
-/
