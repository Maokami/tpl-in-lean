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


Reynolds의 각 장은 대체로 같은 세 작업을 반복한다. 대상 언어의 구문을 정하고, 구문을
의미 공간으로 보내는 함수를 정의하고, 그 함수가 만족해야 할 성질을 증명한다. Lean에서는
구문 데이터, 실행 가능한 예제, 정리와 증명을 서로 참조하는 한 소스 트리에 둘 수 있다.

§1.1의 추상 구문부터 차이가 보인다. Reynolds는 생성자의 단사성, 같은 반송자로 가는
생성자 치역의 서로소성, 모든 구가 유한하게 생성된다는 조건을 명시한다. Lean의
`inductive` 선언은 이에 대응하는 no-confusion 원리와 재귀·귀납 원리를 함께 만든다.

```anchor IntExp
inductive IntExp (V : Type u) where
  /-- 정수 상수. Reynolds의 `c₀, c₁, c₂, …`를 음의 정수까지 일반화했다. -/
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


소스 파일을 읽을 때는 두 가지 순서 규칙이 있다.

*`Ch01/Background.lean`이 첫 읽기다.* 연습은 없지만, 책이 가정하고 넘어가는 메타 수준과
객체 수준의 구분을 여기서 다룬다.

*연습은 이름이 `Ex` 인 파일에만 있지 않다.* 책의 명제 증명이 본문 파일 안에 연습으로
들어 있고, 책 연습문제가 그 명제들을 사용한다. 처음에는 장마다
[읽는 순서](--tag--ch01-order)를 따라가야 필요한 정리들이 차례로 나타난다.

그다음은 이렇게 돈다.

1. `lake exe cache get` 으로 Mathlib 캐시를 받고 `lake build` (처음 한 번만)
2. `Reynolds/Exercises/` 에서 `sorry` 를 찾아 지우고 채운다
3. `lake exe grade` 로 확인한다
4. 막히거나 다 풀었으면 `Reynolds/Answers/` 의 같은 선언과 비교한다
