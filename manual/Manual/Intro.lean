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
%%%


# 왜 Lean 인가
%%%
tag := "why-lean"
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
%%%


| 디렉터리 | 내용 |
|---|---|
| `Reynolds/Answers/ChNN/` | 완성본. 이 문서가 인용하는 대상 |
| `Reynolds/Exercises/ChNN/` | 같은 구조, 연습 지점만 `sorry` |
| `ReynoldsTests/` | `#guard` 단위 테스트 |

# 실습하는 법
%%%
tag := "how-to-practice"
%%%


1. `Reynolds/Exercises/` 에서 `sorry` 를 찾아 지우고 채운다
2. `lake exe grade` 로 확인한다
3. `Reynolds/Answers/` 의 같은 선언과 비교한다
