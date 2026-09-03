/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Exercises.Ch02.Syntax
public import Reynolds.Answers.Ch02.Notation
public import Reynolds.Exercises.Ch02.Semantics
public import Reynolds.Exercises.Ch02.Domain
public import Reynolds.Exercises.Ch02.Domain.Lifting
public import Reynolds.Exercises.Ch02.Domain.FunctionSpace
public import Reynolds.Exercises.Ch02.Fixpoint
public import Reynolds.Exercises.Ch02.Eval
public import Reynolds.Exercises.Ch02.Interpreter
public import Reynolds.Exercises.Ch02.FreeVars
public import Reynolds.Exercises.Ch02.Substitution
public import Reynolds.Exercises.Ch02.Sugar

/-!
# 2장 «단순 명령형 언어» — 연습 (Exercises)

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
5. `Domain/Lifting.lean` — §2.3 평평한 리프팅과 명제 2.4
6. `Domain/FunctionSpace.lean` — §2.3 함수 공간과 명제 2.2·2.3
7. `Fixpoint.lean` — §2.4 반복 사슬과 최소 고정점 정리
8. `Eval.lean` — §2.4 `while`의 표시적 의미
9. `Interpreter.lean` — §2.4 연료 해석기와 적합성
10. `FreeVars.lean` — §2.5 자유 변수 두 종류와 명제 2.6
11. `Substitution.lean` — §2.5 명령의 치환, 별칭, 지역 변수 이름 바꾸기
12. `Sugar.lean` — §2.6 `for` 명령과 세 가지 결함

## 책과의 차이

Reynolds는 §2.2~2.4의 의미 방정식, 도메인 이론, 최소 고정점을 이어서 전개한다. 이
저장소에서는 명세(`Semantics.lean`), 수학적 기반, 의미 함수, 실행 가능한 해석기를 별도
모듈로 나누고 각 경계를 정리로 연결한다.

전체 설계는 [`docs/chapter-02.md`](../../docs/chapter-02.md).
-/
