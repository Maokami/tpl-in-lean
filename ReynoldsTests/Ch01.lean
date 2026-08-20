/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Answers.Ch01
-- `#guard` 는 **컴파일 시점에** 계산한다. 즉 meta 문맥이므로, 계산에 쓰이는 정의들이
-- meta 로도 보여야 한다. 이것이 `public meta import` 가 필요한 이유다.
public meta import Reynolds.Answers.Ch01
public meta import Mathlib.Data.Finset.Defs

/-!
# 1장 단위 테스트

**계산 가능한 것만** 여기서 테스트한다. 정리는 그 자체가 스펙이므로
테스트가 필요 없다 — `lake build` 가 통과하면 참이다.

`#guard` 는 실패하면 **빌드를 실패시킨다.** 그래서 CI 에 따로 붙일 것이 없다.

주의: `/-- … -/` docstring 은 선언에만 붙는다. `#guard` 같은 커맨드 앞에는 `--` 를 쓴다.
-/

public section

namespace Reynolds.Answers.Ch01

open Reynolds

-- `⟦x + 1⟧` — 모든 변수가 41인 상태에서.
#guard ⟦IntExp.bin .add (.var "x") (.num 1)⟧ₑ (State.const 41) == 42

-- 0으로 나누기 규약 (§1.2, §2.7). Lean 의 `Int` 는 `x / 0 = 0`.
#guard ⟦IntExp.bin .div (.var "x") (.num 0)⟧ₑ (State.const (7 : Int)) == 0

-- 단항 마이너스.
#guard ⟦IntExp.neg (.var "x")⟧ₑ (State.const (5 : Int)) == -5

-- 자유 변수 계산.
#guard (IntExp.bin .add (.var "x") (.bin .mul (.var "y") (.num 2)) : IntExp String).fv
        == ({"x", "y"} : Finset String)

-- 상수에는 자유 변수가 없다.
#guard (IntExp.num 3 : IntExp String).fv == (∅ : Finset String)

-- 일치 정리를 구체적인 상태에 적용해 본다: `x` 밖에서 상태가 달라도 값이 같다.
example :
    ⟦IntExp.var "x"⟧ₑ (fun v => if v == "x" then 7 else 1)
      = ⟦IntExp.var "x"⟧ₑ (fun v => if v == "x" then 7 else 99) := by
  apply coincidence_intExp
  intro w hw
  simp [IntExp.fv] at hw
  simp [hw]

end Reynolds.Answers.Ch01
