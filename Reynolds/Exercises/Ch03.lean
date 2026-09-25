/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Exercises.Ch03.Spec
public import Reynolds.Exercises.Ch03.Hoare
public import Reynolds.Exercises.Ch03.Soundness
public import Reynolds.Exercises.Ch03.Assign
public import Reynolds.Exercises.Ch03.Annot
public import Reynolds.Exercises.Ch03.Total
public import Reynolds.Exercises.Ch03.Derived

/-!
# 3장 «명세와 그 증명» — 연습 (Exercises)

1장은 단언이 언제 타당한지를, 2장은 명령이 무엇을 하는지를 정했다. 3장은 그 둘을 잇는다.
명령 앞뒤에 단언을 놓아 "이 상태에서 시작하면 저 상태로 끝난다" 를 말하고, 그런 주장을
증명하는 규칙을 세운다 — Hoare 논리다.

이 장은 새 대상을 거의 만들지 않는다. 명세의 뜻은 2장의 `Comm.eval` 위에 정의하고, 규칙의
건전성은 1·2장의 정리로 증명한다. 대입 공리는 명제 1.4, `while` 규칙은 Scott 귀납법,
변수 선언 규칙은 명제 1.1, 치환 규칙은 명제 2.7 (연습 2.8 의 약한 조건) 이다.

## 읽는 순서

1. `Spec.lean` — §3.1 명세의 뜻, 부분과 전체, 극한을 통과함
2. `Hoare.lean` — §3.2~3.6 부분 정확성의 추론 규칙, 결과 규칙의 두 반쪽, 첫 유도
3. `Soundness.lean` — §3.2~3.6 건전성 — 규칙마다 1·2장의 정리 하나
4. `Assign.lean` — §3.3 대입 공리는 왜 거꾸로인가 — Floyd 의 앞으로 가는 판과 힘이 같다
5. `Annot.lean` — §3.4 주석 명세, 검증 조건 생성기 `vcg` 와 그 건전성
6. `Total.lean` — §3.5 전체 정확성의 `while` 규칙 — 변항, 유령 변수, 정초 귀납
7. `Derived.lean` — §3.7 상수 규칙, 연언·선언, ∃ 규칙, 치환 규칙 (연습 2.8 의 약한 조건)

## 책과의 차이

책의 `{ }`·`[ ]` 는 Lean 에서 이미 다른 뜻이라 전각 괄호를 쓴다. 단언은 구문 판과 의미 판을
둘 다 둔다 — 규칙은 구문 판에, 불변식이 `Assert` 로 안 적히는 예제는 의미 판에.

전체 설계는 [`docs/chapter-03.md`](../../docs/chapter-03.md).
-/
