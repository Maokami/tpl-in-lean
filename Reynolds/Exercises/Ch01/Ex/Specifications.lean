/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Exercises.Ch01.Semantics
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Nat.Prime.Defs

/-!
# 연습 1.1·1.2의 채점 명세 (Reynolds p. 22)

이 파일은 학생이 만든 단언의 뜻을 확인하는 보조 자료다. 책의 정답 단언은 포함하지 않는다.
1.1의 구간 끝점을 매개변수로 열고 유한 집합의 원소 수로 명세한다. 책의 네 문장은 모두
참이어서 고정된 사례만 검사하면 `true`로 대신할 수 있기 때문이다.

1.2는 자연수 상태와 자연수 양화를 사용한다. 본문의 정수 의미론은 그대로 두고,
여기서만 상태 값을 정수로 올려 기존 정수 식 평가기에 전달한다.
허용 구문은 자연수 상수·변수·덧셈·곱셈이다. 이 조각은 네 문항을 모두 표현하면서
음수 값·나눗셈·나머지를 배제한다. 책보다 좁은 산술 조각을 쓰는 실습용 선택이다.
음수 상수나 뺄셈에 새로운 자연수 의미를 부여하는 것은 아니다.

읽는 순서: `Semantics.lean` → 이 파일 → `Ex.lean`.
-/

@[expose] public section

namespace Reynolds.Exercises.Ch01.Ex

open Reynolds

/-- 연습 1.1(p. 22)의 보조 명세. 두 끝점 사이에 있는 정수의 개수다. -/
noncomputable def intervalCount (lo hi : Int) : Nat := (Finset.Ioo lo hi).card

/-- 연습 1.2(p. 22)의 보조 자료. 음수·나눗셈·나머지 없는 자연수 산술 조각인지 검사한다. -/
def naturalArithmetic : IntExp String → Bool
  | .num n => decide (0 ≤ n)
  | .var _ => true
  | .bin .add e f | .bin .mul e f => naturalArithmetic e && naturalArithmetic f
  | .neg _ | .bin .sub _ _ | .bin .div _ _ | .bin .rem _ _ => false

/-- 연습 1.2(p. 22)의 보조 자료. 단언에 나타나는 모든 정수 식의 허용 구문을 확인한다. -/
def naturalSyntax : Assert String → Bool
  | .tru | .fls => true
  | .cmp _ e f => naturalArithmetic e && naturalArithmetic f
  | .not p | .quant _ _ p => naturalSyntax p
  | .bin _ p q => naturalSyntax p && naturalSyntax q

/-- 연습 1.2(p. 22)의 허용 산술은 자연수 상태에서 항상 음이 아닌 정수 값을 갖는다. -/
theorem naturalArithmetic_nonneg (e : IntExp String) (h : naturalArithmetic e = true)
    (σ : String → Nat) : 0 ≤ e.eval (fun v => (σ v : Int)) := by
  induction e with
  | num n => simpa [naturalArithmetic, IntExp.eval] using h
  | var v => exact Int.natCast_nonneg _
  | neg e ih => simp [naturalArithmetic] at h
  | bin op e f ihe ihf =>
      cases op with
      | add =>
          simp only [naturalArithmetic, Bool.and_eq_true] at h
          exact add_nonneg (ihe h.1) (ihf h.2)
      | mul =>
          simp only [naturalArithmetic, Bool.and_eq_true] at h
          exact mul_nonneg (ihe h.1) (ihf h.2)
      | sub | div | rem => simp [naturalArithmetic] at h

/--
연습 1.2(p. 22)의 자연수 범위 해석. 상태와 양화 변수가 모두 `Nat`이다.
비교식에서는 기존 정수 평가기를 사용한다. `naturalSyntax`가 참인 단언만 실습 답으로 받는다.
-/
def evalNat : Assert String → (String → Nat) → Prop
  | .tru, _ => True
  | .fls, _ => False
  | .cmp c e f, σ => c.denote (e.eval (fun v => (σ v : Int)))
      (f.eval (fun v => (σ v : Int)))
  | .not p, σ => ¬ evalNat p σ
  | .bin op p q, σ => op.denote (evalNat p σ) (evalNat q σ)
  | .quant .all v p, σ => ∀ n : Nat, evalNat p (Function.update σ v n)
  | .quant .ex v p, σ => ∃ n : Nat, evalNat p (Function.update σ v n)

/--
연습 1.2(c)(p. 22)의 수치상 최대 공약수 명세. 공약수 집합의 가장 큰 원소를 뜻한다.
`b = c = 0`이면 모든 자연수가 공약수이므로 최대가 없다. `Nat.gcd 0 0 = 0` 규약과 구별한다.
-/
def GreatestCommonDivisor (a b c : Nat) : Prop :=
  IsGreatest {d : Nat | d ∣ b ∧ d ∣ c} a

/-- 연습 1.2(c)(p. 22)의 경계: `(0,0)`의 공약수 집합에는 최대가 없다. -/
theorem no_greatestCommonDivisor_zero_zero (a : Nat) : ¬ GreatestCommonDivisor a 0 0 := by
  intro h
  have hle := h.2 (show a + 1 ∈ {d : Nat | d ∣ 0 ∧ d ∣ 0} from ⟨dvd_zero _, dvd_zero _⟩)
  omega

/-- 연습 1.2(p. 22)의 답 묶음. 허용 구문인 단언과 모든 자연수 상태에서의 의미 증명을 담는다. -/
def NatAnswer (meaning : (String → Nat) → Prop) :=
  {p : Assert String // naturalSyntax p = true ∧ ∀ σ, evalNat p σ ↔ meaning σ}

end Reynolds.Exercises.Ch01.Ex
