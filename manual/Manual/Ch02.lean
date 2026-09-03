/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
import VersoManual
import Manual.Ch02.SyntaxSemantics
import Manual.Ch02.Domain
import Manual.Ch02.Fixpoint

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External

set_option verso.exampleProject ".."
set_option verso.exampleModule "Reynolds.Answers.Ch02.Syntax"

#doc (Manual) "2장 단순 명령형 언어" =>
%%%
tag := "ch02"
file := "ch02"
number := false
%%%

1장에서는 모든 구문의 뜻을 구문 트리에 대한 재귀로 정의할 수 있었다. 2장의 `while`은
유한한 구문 트리지만 실행은 끝나지 않을 수 있다. 구문의 유한성과 실행의 유한성이 처음으로
갈라지는 자리다.

명령 하나의 뜻은 상태를 새 상태로 보내는 함수다. 다만 항상 새 상태를 얻는 것은 아니므로
결과 타입에 `Option`을 붙인다.

```
State V → Option (State V)
```

`some σ'`는 `σ'`에서 끝났다는 정보이고 `none`은 결과 상태를 아직 얻지 못했다는 정보다.
이 장에서는 `none`을 실행 오류나 비결정적 결과와 섞지 않고 비종료의 근사로만 읽는다.

# 이 장에서 배우는 것
%%%
tag := "ch02-goals"
file := "ch02-goals"
number := false
%%%

* *부분 함수(partial function)* — 끝나지 않을 수 있는 명령을
  `State V → Option (State V)`라는 전함수로 표현하는 방법
* *풀기 방정식(unwinding equation)* — 반복문을 한 번 펼친 방정식과, 그 방정식만으로는
  뜻이 유일해지지 않는 이유
* *도메인 이론(domain theory)* — 계산의 유한 근사를 정보 순서로 비교하고 사슬의 극한으로
  합치는 방법
* *최소 고정점(least fixed point)* — 여러 방정식의 해 중 유한 근사에서 시작하는 해를
  고르는 원리
* *적합성(adequacy)* — 증명용 표시적 의미 `Comm.eval`과 실행용 연료 해석기 `Comm.run`이
  같은 종료 결과를 낸다는 정리

이 용어들은 서로 따로 놓인 정의가 아니다. `while`의 뜻을 정하려다 생긴 한 문제를
차례로 풀면서 필요해진다.

# 읽는 순서
%%%
tag := "ch02-order"
file := "ch02-order"
number := false
%%%

현재 구현된 §2.1~§2.4는 다음 순서로 읽는다.

1. `Syntax.lean` — §2.1 불 식과 명령의 추상 구문
2. `Notation.lean` — §2.1 명령을 Lean 안에서 쓰는 DSL
3. `Semantics.lean` — §2.2 불 식의 계산과 명령 의미의 명세
4. `Domain.lean` — §2.3 사슬, 프리도메인, 연속성
5. `Domain/Lifting.lean` — §2.3 `Option`에 평평한 정보 순서를 주는 방법
6. `Domain/FunctionSpace.lean` — §2.3 상태 변환 함수들의 점별 순서와 극한
7. `Fixpoint.lean` — §2.4 반복 사슬과 최소 고정점 정리
8. `Eval.lean` — §2.4 최소 고정점으로 정의한 `Comm.eval`
9. `Interpreter.lean` — §2.4 연료 해석기와 적합성

전부 `Reynolds/Answers/Ch02/` 아래에 있고, `Reynolds/Exercises/Ch02/`에는 같은 선언
순서에서 채울 자리만 `sorry`로 비어 있다. §2.5~§2.8의 파일은 설계 문서에는 있지만 아직
구현되지 않았다. 이 문서는 현재 코드가 있는 §2.4까지만 다룬다.

# 1장에서 2장으로 넘어가는 한 줄
%%%
tag := "ch02-transition"
file := "ch02-transition"
number := false
%%%

1장의 의미 함수는 구문 구조를 그대로 따라가면 끝났다. `while b do c`의 뜻을 같은 방식으로
쓰면 우변에 `while b do c`의 뜻이 다시 나타난다.

```
⟦while b do c⟧ σ
  = if ⟦b⟧ σ then ⟦c⟧ σ >>= ⟦while b do c⟧ else some σ
```

이 식은 반복문의 뜻이 만족해야 할 조건은 말하지만, 구문 트리의 더 작은 부분으로 내려가는
재귀 정의는 아니다. 실제로 이 조건을 만족하는 함수가 둘 이상 생긴다. 2장의 §2.2~§2.4는
그 비유일성에서 출발해, 정보 순서를 만들고, 유한 근사의 극한을 택해, 실행 가능한 해석기와
같은 종료 결과를 내는 뜻을 얻는 과정이다.

{include 1 Manual.Ch02.SyntaxSemantics}

{include 1 Manual.Ch02.Domain}

{include 1 Manual.Ch02.Fixpoint}
