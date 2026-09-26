/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
import VersoManual
import Manual.Ch03.Spec
import Manual.Ch03.Rules
import Manual.Ch03.Annot
import Manual.Ch03.Derived
import Manual.Ch03.Examples
import Manual.Ch03.Wlp

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External

set_option verso.exampleProject ".."
set_option verso.exampleModule "Reynolds.Answers.Ch03.Spec"

#doc (Manual) "3장 명세와 그 증명" =>
%%%
tag := "ch03"
file := "ch03"
number := false
%%%

1장은 단언이 언제 참인지를 정했고, 2장은 명령이 무엇을 하는지를 정했다. 3장은 둘을
잇는다. 명령 앞뒤에 단언을 놓아 "이런 상태에서 시작하면 저런 상태로 끝난다"를 말하고,
그런 주장을 증명하는 규칙을 세운다. Hoare 논리다.

이 장은 새 대상을 거의 만들지 않는다. 명세의 뜻은 2장의 `Comm.eval` 위에 정의하고, 규칙의
건전성은 1·2장의 정리로 증명한다. 앞의 두 장에서 쌓은 것이 여기서 한꺼번에 쓰인다.

# 이 장에서 배우는 것
%%%
tag := "ch03-goals"
file := "ch03-goals"
number := false
%%%

* *부분 정확성과 전체 정확성* — 발산을 어떻게 세느냐가 두 명세의 유일한 차이다
* *건전성* — 규칙마다 앞 장의 정리 하나가 받친다. 대입 공리는 명제 1.4, `while` 규칙은
  Scott 귀납법, 변수 선언 규칙은 명제 1.1이다
* *불변식과 변항* — 반복을 증명할 때 사람이 골라야 하는 두 가지
* *검증 조건* — 주석 명세에서 확인할 함의들을 기계적으로 뽑아 내는 방법
* *상대 완전성* — 단언의 타당성을 오라클로 두면 타당한 명세가 모두 유도된다는 것, 그리고
  그 "조건부"가 어디서 오는지

# 앞 장의 정리가 쓰이는 곳
%%%
tag := "ch03-reuse"
file := "ch03-reuse"
number := false
%%%

: 명제 1.4 (치환 정리)

  대입 공리의 건전성. 1장 §1.4에서 포획을 피하는 치환을 애써 만든 것이 이 한 줄을 위해서였다.

: 명제 1.1 (일치 정리)

  변수 선언 규칙의 세 신선함 조건, 상수 규칙, 유령 변수.

: Scott 귀납법 (§2.4)

  `while` 규칙의 건전성, 그리고 wlp가 최대 고정점이라는 정리.

: 명제 2.6 (명령의 일치 정리)

  상수 규칙, ∃ 규칙, 전체 정확성 `while` 규칙.

: 연습 2.8 (약한 치환 정리)

  치환 규칙. 2장에서 조건을 약화한 연습이 3장의 규칙 하나를 위한 준비였다.

# 읽는 순서
%%%
tag := "ch03-order"
file := "ch03-order"
number := false
%%%

1. `Spec.lean` — §3.1 명세의 뜻
2. `Hoare.lean` — §3.2~3.6 추론 규칙
3. `Soundness.lean` — 규칙마다 건전성
4. `Assign.lean` — §3.3 대입 공리의 방향
5. `Annot.lean` — §3.4 주석 명세와 검증 조건
6. `Total.lean` — §3.5 전체 정확성의 `while` 규칙
7. `Derived.lean` — §3.7 더 많은 규칙
8. `Semantic.lean` — 의미 단언 위의 규칙
9. `Examples/Fib.lean`, `Examples/FastExp.lean` — §3.8, §3.9 예제
10. `Wlp.lean` — §3.10 최약 사전조건과 완전성

전부 `Reynolds/Answers/Ch03/` 아래에 있고, `Reynolds/Exercises/Ch03/`에는 같은 선언 순서에서
채울 자리만 `sorry`로 비어 있다. Exercises 트리는 앞 장의 _완성본_을 가져다 쓰므로 1·2장을
풀지 않아도 3장을 풀 수 있다.

{include 1 Manual.Ch03.Spec}

{include 1 Manual.Ch03.Rules}

{include 1 Manual.Ch03.Annot}

{include 1 Manual.Ch03.Derived}

{include 1 Manual.Ch03.Examples}

{include 1 Manual.Ch03.Wlp}
