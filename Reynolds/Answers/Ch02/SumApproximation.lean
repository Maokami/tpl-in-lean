/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Answers.Ch02.Approximation
public import Reynolds.Answers.Ch02.Notation

/-!
# §2.4 합산 반복문의 유한 근사와 극한

Reynolds pp. 37–38의 명령은 `while x ≠ 0 do (x := x - 1; y := y + x)`다.
본체는 먼저 `x`를 줄인다. 따라서 처음 `x = 3`이면 `y`에 더하는 수는 `2, 1, 0`이다.
구체적인 입력에서 근사를 계산한 뒤, 모든 상태에 대한 닫힌 꼴을 증명한다.

`wₙ`은 조건을 `n`번까지 검사한다. `x = 3`이면 세 번 본체를 실행하고 네 번째 검사에서
끝나므로 `w₃`까지는 바닥, `w₄`부터 결과다. 처음 `x = 0`이어도 한 번은 검사해야 한다.
음수에서 시작하면 계속 작아져 0에 도달하지 않는다.

연습은 `0 ≤ x < n`이라는 유한 단계의 정확한 경계를 증명한다.
그 식에서 사슬의 극한을 구하는 증명은 완성 자료로 읽는다. 마지막 정리
`sumLoop_eval_closed`에는 유한 근사에 관한 미증명 가설이 남지 않는다.

읽는 순서: `Approximation.lean` → 이 파일 → `Interpreter.lean`.
-/

@[expose] public section

namespace Reynolds.Answers.Ch02.SumApproximation

open Reynolds Reynolds.Answers.Ch01

-- ANCHOR: sumLoop
/-- Reynolds p. 37의 본체. 감소한 뒤의 `x`를 `y`에 더한다. -/
def sumBody : Comm String := ⟪ x := x - 1; y := y + x ⟫ᶜ

/-- Reynolds pp. 37–38의 조건. 음수도 참이므로 단순히 `x > 0`으로 바꾸면 뜻이 달라진다. -/
def sumTest : BoolExp String := .cmp .ne (.var "x") (.num 0)

/-- Reynolds pp. 37–38의 합산 반복문. -/
def sumLoop : Comm String := .wh sumTest sumBody
-- ANCHOR_END: sumLoop

/-- 본체를 한 번 실행한 상태. 두 대입의 순서를 식에 드러낸다. -/
def sumStep (σ : State String) : State String :=
  σ["x" := σ "x" - 1]["y" := σ "y" + (σ "x" - 1)]

/-- `0 + 1 + ⋯ + (x-1)`의 정수 닫힌 꼴. 음수에서도 식 자체는 정의되지만 종료 조건은 별도다. -/
def triangle (x : Int) : Int := x * (x - 1) / 2

/-- 종료할 때의 전체 상태. `x`, `y` 이외의 변수는 원래 값을 유지한다. -/
def sumResult (σ : State String) : State String :=
  σ["x" := (0 : Int)]["y" := σ "y" + triangle (σ "x")]

-- ANCHOR: sumF
/-- 책 p. 37의 `F`. 본체 한 번의 계산을 쓴 뒤, 나머지 근사 `w`에 이어 붙인다. -/
def sumF (w : State String → SigmaBot String) (σ : State String) : SigmaBot String :=
  if σ "x" ≠ 0 then w (sumStep σ) else .some σ

/-- 책의 `Fⁿ(⊥)`. 이 예제의 본체에는 반복이 없으므로 이 함수는 직접 계산할 수 있다. -/
def sumApprox (n : ℕ) : State String → SigmaBot String :=
  sumF^[n] (fun _ ↦ .none)
-- ANCHOR_END: sumF

/-- 구문으로 쓴 본체의 뜻이 한 단계 상태 계산과 같다. -/
theorem sumBody_eval (σ : State String) : sumBody.eval σ = .some (sumStep σ) := by
  simp [sumBody, Comm.eval, IntExp.eval, IntOp.denote, Flat.bind, sumStep,
    State.subst_def, Function.update]

/-- 명령 의미론의 연산자와 손으로 정리한 `F`가 같다. -/
theorem sumF_eq_whileF : sumF = whileF sumTest sumBody.eval := by
  funext w σ
  simp [sumF, whileF, sumTest, BoolExp.eval, Cmp.denoteBool, IntExp.eval, sumBody_eval]

/-- `F`는 정보 순서에서 단조다. -/
theorem sumF_monotone : Monotone sumF := by
  rw [sumF_eq_whileF]
  exact whileF_monotone _ _

/-- 계산 가능한 근사값과 책의 실제 근사 명령을 잇는다. -/
theorem sumApprox_eq_approx_eval (n : ℕ) :
    sumApprox n = (Comm.approx sumTest sumBody n).eval := by
  rw [Comm.approx_eval_iterate, ← sumF_eq_whileF]
  rfl

/-- 합산 닫힌 꼴의 한 단계 관계. 나눗셈 전에 분자를 정리하여 정수 나눗셈의 의미를 보존한다. -/
theorem triangle_step (x : Int) : triangle x = (x - 1) + triangle (x - 1) := by
  unfold triangle
  have h : x * (x - 1) = (x - 1) * (x - 1 - 1) + (x - 1) * 2 := by ring
  rw [h, Int.add_mul_ediv_right _ _ (by decide : (2 : Int) ≠ 0)]
  omega

/-- 본체를 한 번 실행해도 최종 상태의 닫힌 꼴은 같다. -/
theorem sumResult_step (σ : State String) : sumResult (sumStep σ) = sumResult σ := by
  funext v
  by_cases hy : v = "y"
  · subst v
    simp only [sumResult, State.subst_self]
    simp only [sumStep, State.subst_def, Function.update_self,
      Function.update_of_ne (by decide : "x" ≠ "y")]
    rw [triangle_step (σ "x")]
    omega
  · by_cases hx : v = "x"
    · subst v
      simp [sumResult, State.subst_def, Function.update]
    · simp [sumResult, sumStep, State.subst_def, Function.update, hx, hy]

/-- `x = 0`이면 결과 닫힌 꼴은 입력 상태 그대로다. -/
theorem sumResult_zero (σ : State String) (hx : σ "x" = 0) : sumResult σ = σ := by
  funext v
  by_cases hy : v = "y"
  · subst v
    simp [sumResult, hx, triangle]
  · by_cases hv : v = "x"
    · subst v
      simp [sumResult, State.subst_def, Function.update, hx]
    · simp [sumResult, State.subst_def, Function.update, hv, hy]

-- ANCHOR: sumApprox_eq
/-- Reynolds pp. 37–38. 정확히 `0 ≤ x < n`일 때만 `n`번째 근사가 종료 결과를 갖는다. -/
@[exercise "§2.4 sum-approx" 3]
theorem sumApprox_eq (n : ℕ) (σ : State String) :
    sumApprox n σ = if 0 ≤ σ "x" ∧ σ "x" < (n : Int) then .some (sumResult σ) else .none := by
  induction n generalizing σ with
  | zero => simp [sumApprox]
  | succ n ih =>
      rw [sumApprox, Function.iterate_succ_apply']
      change sumF (sumApprox n) σ = _
      unfold sumF
      by_cases hx : σ "x" ≠ 0
      · rw [if_pos hx, ih]
        have hstep : sumStep σ "x" = σ "x" - 1 := by
          simp [sumStep, State.subst_def, Function.update]
        rw [hstep, sumResult_step]
        congr 1
        apply propext
        push_cast
        omega
      · have hz : σ "x" = 0 := by omega
        simp [hz, sumResult_zero σ hz]
-- ANCHOR_END: sumApprox_eq

/--
Reynolds p. 38의 극한 계산. 유한 근사의 식을 각 사슬 항에 대입하여 상계와 최소성을 보인다.
아래 최종 정리가 이 보조정리에 실제로 증명한 근사식을 넘긴다.
-/
theorem sumLoop_eval_of_approx
    (happrox : ∀ n σ, sumApprox n σ =
      if 0 ≤ σ "x" ∧ σ "x" < (n : Int) then .some (sumResult σ) else .none)
    (σ : State String) :
    sumLoop.eval σ = if 0 ≤ σ "x" then .some (sumResult σ) else .none := by
  change (iterChain (whileF_monotone sumTest sumBody.eval)).lub σ = _
  rw [Chain.lub_apply]
  let c := (iterChain (whileF_monotone sumTest sumBody.eval)).apply σ
  have hseq (n : ℕ) : c.seq n = sumApprox n σ := by
    change (whileF sumTest sumBody.eval)^[n] ⊥ σ = _
    rw [← sumF_eq_whileF]
    rfl
  by_cases hx : 0 ≤ σ "x"
  · rw [if_pos hx]
    apply le_antisymm
    · apply Chain.lub_le
      intro n
      rw [hseq, happrox]
      split <;> simp
    · have hn : σ "x" < (Int.toNat (σ "x") + 1 : ℕ) := by omega
      have h := c.le_lub (Int.toNat (σ "x") + 1)
      rw [hseq, happrox, if_pos ⟨hx, hn⟩] at h
      exact h
  · rw [if_neg hx]
    apply le_antisymm
    · apply Chain.lub_le
      intro n
      rw [hseq, happrox, if_neg (by omega)]
    · exact bot_le

-- ANCHOR: sumLoop_eval_closed
/--
Reynolds p. 38. 합산 반복문의 최소 고정점은 `x ≥ 0`에서만 종료하는 이 전체 상태 함수다.
유한 근사식은 `sumApprox_eq`로 증명했으므로 추가 가설이 없다.
이 정리는 그 연습에 의존하는 결론이며 별도 채점 연습으로 두지 않는다.
-/
theorem sumLoop_eval_closed (σ : State String) :
    sumLoop.eval σ = if 0 ≤ σ "x" then .some (sumResult σ) else .none :=
  sumLoop_eval_of_approx sumApprox_eq σ
-- ANCHOR_END: sumLoop_eval_closed

end Reynolds.Answers.Ch02.SumApproximation
