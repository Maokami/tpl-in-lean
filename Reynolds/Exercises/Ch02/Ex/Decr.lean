/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Exercises.Ch02.Ex

/-!
# 연습 2.3 — `while x ≠ 0 do x := x - 2` 의 닫힌 꼴

Reynolds 연습 2.3 에 대응한다.

## 이 연습이 장의 고리를 닫는다

이 반복문은 §2.2 에서 이미 나왔다. 거기서 풀기 방정식이 뜻을 **유일하게 정하지 못한다**는
것을 보이는 데 썼다 — `decrTrue` 와 `decrFake` 가 둘 다 방정식을 만족했다
(`unwinding_not_unique`).

§2.4 는 그 여러 해 중 **최소**를 고르기로 했다. 그러면 이 반복의 뜻은 정확히 무엇인가?
이 연습이 답한다.

```
⟦while x ≠ 0 do x := x - 2⟧ = decrTrue
```

§2.2 가 "둘 다 해다" 로 열어 둔 것을, §2.4 의 결정이 "그중 이것" 으로 닫는다.
`decrFake` 는 여전히 방정식의 해이지만 뜻은 아니다.

## 증명이 두 조각인 이유

최소 고정점이 어떤 구체적인 함수와 **같다**는 것은 양쪽 부등식이다.

- `⊑` — `decrTrue` 가 방정식을 만족하므로(§2.2 의 `unwindsDecr_true`) 최소성이 곧바로
  준다. 계산이 없다.
- `⊒` — 이쪽이 일이다. 끝나는 상태에서 반복이 **정말 끝난다**는 것을 보여야 하고,
  그것은 실제로 몇 바퀴 도는지를 세는 논증이다. `x` 가 한 바퀴마다 2 씩 줄므로
  `(x / 2).toNat` 이 정확히 하나 준다 — §2.6 의 정확 반복 정리, §2.8 의 `countLoop_eval`
  과 같은 측도 귀납이다.

끝나지 않는 상태에서는 `decrTrue` 가 `⊥` 라서 `⊒` 쪽이 공짜다. **`⊥` 가 아래에 있다는
것이 "증명할 것이 없다" 로 나타나는 자리**이고, 최소 고정점을 고른 값이 여기서 드러난다.

## 읽는 순서
`Ex.lean` 다음. §2.2 의 `decrTrue`·`unwindsDecr_true` 와 §2.4 의 `fix_least` 를 쓴다.
-/

@[expose] public section

namespace Reynolds.Exercises.Ch02.Ex

open Reynolds Reynolds.Exercises.Ch01 Reynolds.Exercises.Ch02

/-! ## 1. 프로그램과 그 풀기 방정식 -/

/-- §2.2 의 예제 반복문. 이제 구문으로 적는다. -/
def decrLoop : Comm String := ⟪ while x ≠ 0 do x := x - 2 ⟫ᶜ

/-- 본체의 뜻이 §2.2 의 `decrBody` 와 같다. -/
theorem decrLoop_body_eval :
    (Comm.assign "x" (.bin .sub (.var "x") (.num 2))).eval = decrBody := rfl

/-- 조건의 값. `Bool` 쪽과 `Prop` 쪽을 잇는다. -/
theorem decrLoop_cond (σ : State String) :
    ⟦(.cmp .ne (.var "x") (.num 0) : BoolExp String)⟧ᵇ σ = decide (σ "x" ≠ 0) := by
  by_cases h : σ "x" = 0 <;> simp [BoolExp.eval, IntExp.eval, Cmp.denoteBool, h]

/--
**이 반복의 뜻도 풀기 방정식을 만족한다.**

§2.2 는 `decrTrue` 와 `decrFake` 가 방정식의 해임을 보였다. 여기에 셋째 해가 있다 —
우리가 §2.4 에서 정의한 뜻 자체다. 이 연습이 묻는 것은 셋 중 어느 것이냐가 아니라,
**최소인 것이 무엇이냐**다.
-/
theorem unwindsDecr_eval : UnwindsDecr decrLoop.eval := by
  intro σ
  have hw : decrLoop.eval σ
      = if ⟦(.cmp .ne (.var "x") (.num 0) : BoolExp String)⟧ᵇ σ
        then Option.bind ((Comm.assign "x" (.bin .sub (.var "x") (.num 2))).eval σ) decrLoop.eval
        else some σ := Comm.eval_isSemantics.2.2.2.2.1 _ _ σ
  rw [hw, decrLoop_cond, decrLoop_body_eval]
  by_cases h0 : σ "x" = 0
  · rw [if_neg (by simp [h0]), if_neg (by simp [h0])]
  · rw [if_pos (by simp [h0]), if_pos (by simp [h0])]

/-! ## 2. 끝나는 상태에서는 정말 끝난다

여기가 이 연습의 계산이다. `x` 가 0 이상의 짝수면 반복이 `x / 2` 바퀴 돌고 멈춘다. -/

/--
**연습 2.3 — 끝나는 상태에서의 닫힌 꼴.**

`x` 가 0 이상의 짝수면 반복은 끝나고 `x` 가 0 이 된다.

측도는 `(σ x / 2).toNat` — 남은 바퀴 수다. 한 바퀴마다 `x` 가 2 씩 줄므로 정확히 하나
준다. §2.6 의 `forWhile_eq_fold`, §2.8 의 `countLoop_eval` 과 같은 모양이다.

`decrHalts` 가 한 걸음을 견딘다는 것(§2.2 의 `decrHalts_step`)이 귀납을 굴리는 연료다.
그것이 없으면 "끝나는 상태" 가 도중에 "안 끝나는 상태" 로 바뀌지 않는다는 보장이 없다.
-/
@[exercise "Ex 2.3" 3]
theorem decrLoop_eval_of_halts :
    ∀ (σ : State String), decrHalts σ → decrLoop.eval σ = some (σ["x" := (0 : Int)]) := by
  -- 먼저 볼 것: 바로 위 `unwindsDecr_eval` (완성본) 과 §2.2 의 `decrHalts_step`,
  --            `decr_step`, `State.subst_subst`, `State.subst_eq_self`.
  -- 힌트 1: 측도는 `(σ "x" / 2).toNat` — 남은 바퀴 수다. 한 바퀴마다 `x` 가 2 씩 줄므로
  --         정확히 하나 준다. §2.8 의 `countLoop_eval` 과 같은 모양이다.
  -- 힌트 2: 그 `Nat` 에 대한 보조 명제를 `have` 로 세우고 귀납한다.
  --         `σ` 는 귀납 뒤에 `intro` 해야 가설이 다음 상태에 쓰인다.
  -- 힌트 3: 0 이면 `decrHalts σ` 와 측도로부터 `σ "x" = 0` 이 나온다 (`omega`).
  --         조건이 거짓이고 `State.subst_eq_self` 가 끝낸다.
  -- 힌트 4: 아니면 `σ "x" ≠ 0` 이므로 한 걸음 간다. `decrHalts` 가 한 걸음을 견딘다는
  --         `decrHalts_step` 이 귀납을 굴리는 연료다.
  sorry


/-! ## 3. 최소 고정점이 곧 의도한 의미다 -/

/--
**`⟦while x ≠ 0 do x := x - 2⟧ = decrTrue`.**

§2.2 가 열어 둔 물음의 답이다. 두 방향이 아주 다르게 생겼다.

- `⊑` — `decrTrue` 가 방정식의 해이므로 최소성(`fix_least`)이 곧바로 준다. **계산이 없다.**
- `⊒` — 끝나는 상태에서는 위의 닫힌 꼴이 주고, 끝나지 않는 상태에서는 `decrTrue` 가
  `⊥` 라서 보일 것이 없다.

채점 연습이 아니다. `decrLoop_eval_of_halts` 가 이미 연습이라 비우면 비운 것끼리
의존한다 (연습 독립성 원칙, `AGENTS.md` §1-9).
-/
theorem decrLoop_eval : decrLoop.eval = decrTrue := by
  refine le_antisymm ?_ ?_
  · -- `decrTrue` 는 고정점이므로 최소성이 준다.
    refine fix_least (whileF_monotone _ _) (le_of_eq ?_)
    funext σ
    have hu := unwindsDecr_true σ
    unfold whileF
    rw [decrLoop_cond, decrLoop_body_eval, hu]
    by_cases h0 : σ "x" = 0
    · rw [if_neg (by simp [h0]), if_neg (by simp [h0])]
    · rw [if_pos (by simp [h0]), if_pos (by simp [h0])]
  · -- 끝나는 상태는 계산으로, 끝나지 않는 상태는 `⊥` 라서 공짜로.
    intro σ
    by_cases hh : decrHalts σ
    · rw [decrTrue, if_pos hh, decrLoop_eval_of_halts σ hh]
    · rw [decrTrue, if_neg hh]
      exact bot_le

/--
**`decrFake` 는 해이지만 뜻이 아니다.** §2.2 의 논의가 여기서 닫힌다.

방정식은 끝나지 않는 상태에서 아무것도 요구하지 않았다. 그 자리를 `⊥` 로 메우는 것이
최소 고정점의 선택이고, `decrFake` 처럼 999 를 채워 넣은 함수는 방정식을 만족하면서도
뜻은 아니다.
-/
theorem decrLoop_eval_ne_decrFake : decrLoop.eval ≠ decrFake := by
  intro hEq
  have h := congrFun hEq (State.const 1)
  rw [decrLoop_eval] at h
  have hnh : ¬ decrHalts (State.const 1 : State String) := by
    unfold decrHalts State.const
    omega
  rw [decrTrue, if_neg hnh, decrFake, if_neg hnh] at h
  exact absurd h (by simp)

/-! ## 4. 여기서 어디로 가나

구체적인 반복 하나의 뜻을 끝까지 계산해 보았다. 다음은 `while` **일반**에 대한 연습
2.5 다 — `while b do c` 와 `while b do (c; if b then c else skip)` 이 같은가. 양방향
`⊑` 인데, 한쪽은 이번처럼 `fix_least` 한 번으로 끝나고 다른 쪽은 근사열을 직접 따라가야
한다. -/

end Reynolds.Exercises.Ch02.Ex
