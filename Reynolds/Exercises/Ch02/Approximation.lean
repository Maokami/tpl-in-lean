/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Exercises.Ch02.Eval

/-!
# §2.4 근사 명령 `wₙ`과 의미 사슬

Reynolds pp. 36–37은 실제 명령을 차례로 만든다. `w₀`는 항상 발산하고,
`wₙ₊₁`은 조건이 참이면 본체를 한 번 실행한 뒤 `wₙ`으로 이어 간다.
따라서 명령 구문을 펼치는 단계와 의미 함수에 `F`를 적용하는 단계가 대응한다.

`wₙ`은 바깥 반복만 자른다. 본체 `c`의 뜻은 여전히 완전한 `c.eval`이다.
중첩된 반복에도 연료를 주는 `Comm.run n`과 단계마다 같은 것으로 보아서는 안 된다.
조건이 처음부터 거짓이어도 `w₀`는 발산하고 `w₁`부터 종료한다.

이 파일은 다음 합산 실습의 완성 자료다. `approx_eval_iterate`를 또 빈칸으로 만들면
그 뒤 실습이 미완성 정리에 의존하므로, 대응의 귀납 증명은 직접 읽도록 제공한다.
읽는 순서: `Eval.lean` → 이 파일 → `SumApproximation.lean`.
-/

@[expose] public section

namespace Reynolds.Exercises.Ch02

open Reynolds

universe u

variable {V : Type u} [DecidableEq V]

/-- Reynolds pp. 36–37의 `wₙ`. 본체의 반복은 건드리지 않고 바깥 반복만 `n`단계 펼친다. -/
def Comm.approx (b : BoolExp V) (c : Comm V) : ℕ → Comm V
  | 0 => .wh .tru .skip
  | n + 1 => .ite b (.seq c (Comm.approx b c n)) .skip

/-- 항상 참인 조건 아래에서 아무 변화 없이 반복하면 모든 입력에서 바닥이다. -/
theorem Comm.spin_eval : (.wh .tru .skip : Comm V).eval = ⊥ := by
  apply le_antisymm
  · exact Comm.eval_while_least (by intro σ; rfl)
  · exact bot_le

/-- Reynolds p. 37. 구문 근사의 뜻은 의미 연산자 `F`를 바닥에 `n`번 적용한 값이다. -/
theorem Comm.approx_eval_iterate (b : BoolExp V) (c : Comm V) (n : ℕ) :
    (Comm.approx b c n).eval = (whileF b c.eval)^[n] ⊥ := by
  induction n with
  | zero => exact Comm.spin_eval
  | succ n ih =>
      change whileF b c.eval (Comm.approx b c n).eval = _
      rw [ih, Function.iterate_succ_apply']

/-- `wₙ`의 의미는 정보 순서에서 증가한다. -/
theorem Comm.approx_eval_mono (b : BoolExp V) (c : Comm V) :
    Monotone (fun n ↦ (Comm.approx b c n).eval) := by
  intro m n hmn
  change (Comm.approx b c m).eval ≤ (Comm.approx b c n).eval
  rw [Comm.approx_eval_iterate, Comm.approx_eval_iterate]
  exact (iterChain (whileF_monotone b c.eval)).mono hmn

/-- 근사 명령들의 의미 사슬. 원소는 구문 `wₙ`을 해석한 함수다. -/
noncomputable def Comm.approxChain (b : BoolExp V) (c : Comm V) :
    Chain (State V → SigmaBot V) := iterChain (whileF_monotone b c.eval)

/-- 의미 반복으로 정의한 사슬의 각 항을 실제 명령 `wₙ`으로 읽는다. -/
theorem Comm.approxChain_seq (b : BoolExp V) (c : Comm V) (n : ℕ) :
    (Comm.approxChain b c).seq n = (Comm.approx b c n).eval :=
  (Comm.approx_eval_iterate b c n).symm

/-- Reynolds p. 37. `while`의 뜻은 근사 명령들의 의미 사슬의 극한이다. -/
theorem Comm.eval_while_eq_approx_lub (b : BoolExp V) (c : Comm V) :
    (Comm.wh b c).eval = (Comm.approxChain b c).lub := rfl

end Reynolds.Exercises.Ch02
