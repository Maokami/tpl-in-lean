/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External

set_option verso.exampleProject ".."
set_option verso.exampleModule "Reynolds.Answers.Ch01.Syntax"

#doc (Manual) "들어가며" =>
%%%
tag := "intro"
file := "intro"
number := false
%%%


# 왜 Lean 인가
%%%
tag := "why-lean"
file := "why-lean"
number := false
%%%


Reynolds 의 책은 세 가지를 계속 반복한다: *구문을 정의하고*, *의미를 주고*,
*성질을 증명한다*. Lean 4 는 이 셋을 한 파일 안에서 할 수 있는 드문 도구다.

특히 §1.1 에서 눈에 띄는 일이 벌어진다. Reynolds 는 추상 구문에 세 조건을 손으로 부과한다 —
생성자가 단사일 것, 치역이 서로소일 것, 유한 생성일 것. Lean 에서는 `inductive` 선언
한 번이면 셋 다 딸려 온다:

```anchor IntExp
inductive IntExp (V : Type u) where
  /-- 정수 상수. Reynolds의 `c₀, c₁, c₂, …`. -/
  | num : Int → IntExp V
  /-- 변수. Reynolds의 `c_var` — 변수를 정수 식으로 넣어 주는 생성자다.
      §1.4 명제 1.2(b)에서 이것이 "항등 치환"으로 작동한다는 사실이 쓰인다. -/
  | var : V → IntExp V
  /-- 단항 마이너스 `- e`. -/
  | neg : IntExp V → IntExp V
  /-- 이항 연산 `e₀ op e₁`. -/
  | bin : IntOp → IntExp V → IntExp V → IntExp V
  deriving DecidableEq, Repr
```

위 코드 블록은 손으로 옮겨 적은 것이 아니다. 저장소의
`Reynolds/Answers/Ch01/Syntax.lean` 에서 *그대로 인용*한 것이고,
소스가 바뀌면 이 문서의 빌드가 실패한다.

# 저장소 구조
%%%
tag := "layout"
file := "layout"
number := false
%%%


: `Reynolds/Answers/ChNN/`

  완성본. 이 문서가 인용하는 대상이고, 설명은 전부 이쪽 docstring 에 있다.

: `Reynolds/Exercises/ChNN/`

  같은 구조에서 연습 지점만 `sorry` 로 비운 것. `scripts/gen-exercises.py` 가
  완성본에서 만들어 내므로 손으로 고치지 않는다.

: `ReynoldsTests/`

  `#guard` 단위 테스트. 완성본만 import 한다.

: `docs/`

  장별 형식화 설계와 [연습 푸는 법](https://github.com/Maokami/tpl-in-lean/blob/main/docs/solving-guide.md).

: `manual/`

  이 문서.

# 실습하는 법
%%%
tag := "how-to-practice"
file := "how-to-practice"
number := false
%%%


시작하기 전에 두 가지를 알아 두면 헤매지 않는다.

*`Ch01/Background.lean` 을 먼저 읽어라.* 연습이 하나도 없어서 지나치기 쉬운데,
책이 가정하고 넘어가는 메타 수준과 객체 수준의 구분을 여기서 다룬다.

*연습은 이름이 `Ex` 인 파일에만 있지 않다.* 책의 명제 증명이 본문 파일 안에 연습으로
들어 있고, 책 연습문제가 그 명제들을 쓴다. 장마다 [읽는 순서](--tag--ch01-order)를
따라가는 것이 그래서 권고가 아니라 요구다.

그다음은 이렇게 돈다.

1. `lake exe cache get` 으로 Mathlib 캐시를 받고 `lake build` (처음 한 번만)
2. `Reynolds/Exercises/` 에서 `sorry` 를 찾아 지우고 채운다
3. `lake exe grade` 로 확인한다
4. 막히거나 다 풀었으면 `Reynolds/Answers/` 의 같은 선언과 비교한다
