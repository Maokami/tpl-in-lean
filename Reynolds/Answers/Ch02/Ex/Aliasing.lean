/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Answers.Ch02.Ex.Unwind
-- `#guard`는 컴파일 시점에 계산한다 (AGENTS.md §10).
public meta import Reynolds.Answers.Ch02.Interpreter
public meta import Reynolds.Answers.Ch02.Notation
public meta import Reynolds.Answers.Ch02.Semantics
public meta import Reynolds.Prelude

/-!
# 연습 2.6 · 2.7 — 자유 변수와 별칭

Reynolds 연습 2.6 과 2.7 에 대응한다. 둘 다 §2.5 가 재료다.

## 연습 2.6 — 언제 두 명령의 순서를 바꿔도 되는가

## 조건

```
FV(c₀) ∩ FA(c₁) = ∅   그리고   FA(c₀) ∩ FV(c₁) = ∅
```

이면 `c₀; c₁` 과 `c₁; c₀` 의 뜻이 같다. 읽는 말로는 "한쪽이 **읽거나 쓰는** 변수를
다른 쪽이 **쓰지** 않는다" 다.

**한쪽만으로는 안 된다.** `FA(c₀) ∩ FA(c₁) = ∅` 만 요구하면 거짓이다 —
`c₀ = (x := y)`, `c₁ = (y := 0)` 은 쓰는 변수가 겹치지 않는데도 순서가 중요하다.
`FV` 쪽을 봐야 그 경우가 걸러진다.

반대로 `FA ⊆ FV` (§2.5) 이므로 위 조건은 `FA(c₀) ∩ FA(c₁) = ∅` 을 자동으로 포함한다.
둘 다 같은 변수에 쓰면 그 변수는 양쪽 `FV` 에도 있기 때문이다.

> Reynolds 의 책에는 `= ∅` 이 빠져 있다. 교집합만 적고 "서로소" 를 말로 남긴 것인데,
> 형식화에서는 그 말을 살려야 진술이 참이 된다.

## 비종료도 맞물린다

한쪽이 발산하면 다른 쪽을 먼저 돌려도 여전히 발산해야 한다. 그것이 명제 2.6(a) 의
일치 정리가 하는 일이다 — `c₁` 이 `c₀` 의 자유 변수를 건드리지 않으므로,
`c₁` 을 지난 상태에서 `c₀` 를 돌려도 종료 여부가 같다.

증명은 명제 2.6 의 **두 부분을 모두** 쓴다.

- (b) `eval_agree_outside_fa` — 한쪽을 지나도 다른 쪽의 자유 변수가 그대로다.
- (a) `coincidence_general` — 그러므로 다른 쪽의 결과가 같다.

## 연습 2.7 — 별칭에 안전한 계승

프로그램이 자기 변수가 **합쳐질 수 있다**는 것을 모른 채 쓰인다. §2.5 에서 보았듯
프로시저 호출이 두 인자를 같은 칸으로 묶으면 그런 일이 생긴다. 그래도 맞게 도는
계승 프로그램을 쓰는 것이 이 연습이다.

답은 `newvar` 다 — 입력을 **지역 변수에 찍어 두고** 그것으로 돈다. 그러면 출력 변수가
입력 변수와 합쳐져도 찍어 둔 값이 살아남는다.

## 읽는 순서
`Ex/Unwind.lean` 다음. §2.5 의 명제 2.6 과 치환이 재료다.
-/

-- 이 파일의 `#guard` 가 별칭이 계승을 어떻게 망가뜨리는지 보여 준다.
set_option linter.hashCommand false

@[expose] public section

namespace Reynolds.Answers.Ch02.Ex

open Reynolds Reynolds.Answers.Ch01 Reynolds.Answers.Ch02

universe u

variable {V : Type u} [DecidableEq V]

/-! ## 연습 2.6 — 순서 교환 -/

-- ANCHOR: seqComm
/--
**연습 2.6 — 서로 간섭하지 않는 두 명령은 순서를 바꿔도 된다.**

`h₀` 는 "`c₀` 가 읽거나 쓰는 것을 `c₁` 이 쓰지 않는다", `h₁` 은 그 반대다.

증명은 결과 네 갈래다. 한쪽만 발산하는 갈래에서 일치 정리가 "다른 순서로도 발산한다"
를 준다 — 비종료가 있는 언어에서 이 정리가 그냥 계산이 아닌 이유다.

둘 다 끝나는 갈래에서는 최종 상태를 변수마다 따진다. 세 경우로 갈린다.

- `w ∈ FA(c₀)` — `c₁` 은 `w` 를 안 건드리므로 양쪽 다 `c₀` 가 쓴 값이 남는다.
- `w ∈ FA(c₁)` — 대칭.
- 둘 다 아님 — 아무도 안 건드렸으므로 양쪽 다 `σ w` 다.
-/
@[exercise "Ex 2.6" 2]
theorem seq_comm (c₀ c₁ : Comm V)
    (h₀ : ∀ w ∈ c₀.fv, w ∉ c₁.fa) (h₁ : ∀ w ∈ c₀.fa, w ∉ c₁.fv) :
    (Comm.seq c₀ c₁).eval = (Comm.seq c₁ c₀).eval := by
  -- 대우를 미리 뒤집어 둔다.
  have h₁' : ∀ w ∈ c₁.fv, w ∉ c₀.fa := fun w hw hfa => h₁ w hfa hw
  funext σ
  change Option.bind (c₀.eval σ) c₁.eval = Option.bind (c₁.eval σ) c₀.eval
  rcases h0 : c₀.eval σ with _ | τ₀ <;> rcases hI : c₁.eval σ with _ | τ₁
  · rfl
  · -- `c₀` 만 발산한다. `c₁` 을 먼저 돌려도 `c₀` 는 여전히 발산한다.
    change (none : SigmaBot V) = c₀.eval τ₁
    have hag : ∀ w ∈ c₀.fv, σ w = τ₁ w := fun w hw =>
      (Comm.eval_agree_outside_fa c₁ σ τ₁ hI w (h₀ w hw)).symm
    have hc := Comm.coincidence_general c₀ c₀.fv (le_refl _) σ τ₁ hag
    rw [h0] at hc
    rcases hr : c₀.eval τ₁ with _ | τ
    · rfl
    · rw [hr] at hc; exact absurd hc (by simp)
  · -- `c₁` 만 발산한다. 대칭이다.
    change c₁.eval τ₀ = (none : SigmaBot V)
    have hag : ∀ w ∈ c₁.fv, σ w = τ₀ w := fun w hw =>
      (Comm.eval_agree_outside_fa c₀ σ τ₀ h0 w (h₁' w hw)).symm
    have hc := Comm.coincidence_general c₁ c₁.fv (le_refl _) σ τ₀ hag
    rw [hI] at hc
    rcases hr : c₁.eval τ₀ with _ | τ
    · rfl
    · rw [hr] at hc; exact absurd hc (by simp)
  · -- 둘 다 끝난다. 최종 상태를 변수마다 따진다.
    change c₁.eval τ₀ = c₀.eval τ₁
    -- `c₁` 을 `τ₀` 에서 돌린 것은 `σ` 에서 돌린 것과 `FV(c₁)` 위에서 같다.
    have hag₁ : ∀ w ∈ c₁.fv, σ w = τ₀ w := fun w hw =>
      (Comm.eval_agree_outside_fa c₀ σ τ₀ h0 w (h₁' w hw)).symm
    have hc₁ := Comm.coincidence_general c₁ c₁.fv (le_refl _) σ τ₀ hag₁
    rw [hI] at hc₁
    -- 대칭으로 `c₀` 쪽도.
    have hag₀ : ∀ w ∈ c₀.fv, σ w = τ₁ w := fun w hw =>
      (Comm.eval_agree_outside_fa c₁ σ τ₁ hI w (h₀ w hw)).symm
    have hc₀ := Comm.coincidence_general c₀ c₀.fv (le_refl _) σ τ₁ hag₀
    rw [h0] at hc₀
    rcases hr₁ : c₁.eval τ₀ with _ | ρ₁
    · rw [hr₁] at hc₁; exact absurd hc₁ (by simp)
    rcases hr₀ : c₀.eval τ₁ with _ | ρ₀
    · rw [hr₀] at hc₀; exact absurd hc₀ (by simp)
    rw [hr₁] at hc₁
    rw [hr₀] at hc₀
    -- `ρ₁` 과 `ρ₀` 가 같은 상태임을 변수마다 확인한다.
    refine congrArg some (funext fun w => ?_)
    by_cases hw₀ : w ∈ c₀.fa
    · -- `c₀` 가 쓴 변수. `c₁` 은 건드리지 않는다.
      have hwv₀ : w ∈ c₀.fv := Comm.fa_subset_fv c₀ hw₀
      have hw₁ : w ∉ c₁.fa := h₀ w hwv₀
      -- 왼쪽: `c₁` 이 `τ₀` 에서 `w` 를 안 건드렸다.
      have hl : ρ₁ w = τ₀ w := Comm.eval_agree_outside_fa c₁ τ₀ ρ₁ hr₁ w hw₁
      -- 오른쪽: `c₀` 의 결과가 `FV(c₀)` 위에서 `τ₀` 와 일치한다.
      have hr : τ₀ w = ρ₀ w := hc₀ w hwv₀
      rw [hl, hr]
    · by_cases hw₁ : w ∈ c₁.fa
      · -- `c₁` 이 쓴 변수. 대칭이다.
        have hwv₁ : w ∈ c₁.fv := Comm.fa_subset_fv c₁ hw₁
        have hl : τ₁ w = ρ₁ w := hc₁ w hwv₁
        have hr : ρ₀ w = τ₁ w := Comm.eval_agree_outside_fa c₀ τ₁ ρ₀ hr₀ w hw₀
        rw [← hl, hr]
      · -- 아무도 안 건드린 변수. 양쪽 다 `σ w` 다.
        have hl : ρ₁ w = τ₀ w := Comm.eval_agree_outside_fa c₁ τ₀ ρ₁ hr₁ w hw₁
        have hl' : τ₀ w = σ w := Comm.eval_agree_outside_fa c₀ σ τ₀ h0 w hw₀
        have hr : ρ₀ w = τ₁ w := Comm.eval_agree_outside_fa c₀ τ₁ ρ₀ hr₀ w hw₀
        have hr' : τ₁ w = σ w := Comm.eval_agree_outside_fa c₁ σ τ₁ hI w hw₁
        rw [hl, hl', hr, hr']
-- ANCHOR_END: seqComm

/-! ## 연습 2.7 — 별칭에 안전한 계승

두 프로그램을 나란히 둔다. 하나는 입력 변수를 직접 깎고, 하나는 지역 변수에 찍어 두고
그것을 깎는다. 별칭이 없으면 둘 다 맞다. 별칭이 생기면 갈린다. -/

-- ANCHOR: fact
/-- 순진한 계승. 입력 `x` 를 직접 깎고 답을 `y` 에 쌓는다. -/
def factNaive : Comm String := ⟪ y := 1; while x > 0 do (y := y × x; x := x - 1) ⟫ᶜ

/-- 별칭에 안전한 계승. 입력을 지역 변수 `t` 에 찍어 두고 그것을 깎는다. -/
def factSafe : Comm String :=
  ⟪ newvar t := x in (y := 1; while t > 0 do (y := y × t; t := t - 1)) ⟫ᶜ

-- 별칭이 없으면 둘 다 3! = 6 을 낸다.
#guard (factNaive.run 10 (State.const 3)).map (fun σ => σ "y") == some 6
#guard (factSafe.run 10 (State.const 3)).map (fun σ => σ "y") == some 6

/-- 입력과 출력을 같은 칸으로 묶는 이름 바꾸기. 단사가 아니다 — 이것이 별칭이다. -/
def aliasToZ : Ren String := fun w => if w = "x" then "z" else if w = "y" then "z" else w

/-- 별칭을 건 순진한 판. `z := 1; while z > 0 do (z := z × z; z := z - 1)` -/
def factNaiveAliased : Comm String := ⟪ z := 1; while z > 0 do (z := z × z; z := z - 1) ⟫ᶜ

/-- 별칭을 건 안전한 판. 지역 변수 `t` 는 합쳐지지 않으므로 그대로 남는다. -/
def factSafeAliased : Comm String :=
  ⟪ newvar t := z in (z := 1; while t > 0 do (z := z × t; t := t - 1)) ⟫ᶜ

/-- 치환이 정말 그 프로그램을 내놓는다. 구문 계산이라 `rfl` 이다. -/
theorem factNaive_alias_eq : factNaive /ᶜ aliasToZ = factNaiveAliased := rfl

/-- 안전한 판도 마찬가지다. `newvar` 의 결합자 `t` 는 `z` 와 겹치지 않아 그대로다. -/
theorem factSafe_alias_eq : factSafe /ᶜ aliasToZ = factSafeAliased := rfl

-- 별칭이 생기면 갈린다. 순진한 판은 0, 안전한 판은 6.
#guard (factNaiveAliased.run 10 (State.const 3)).map (fun σ => σ "z") == some 0
#guard (factSafeAliased.run 10 (State.const 3)).map (fun σ => σ "z") == some 6

/--
**연습 2.7 — 지역 변수가 별칭을 막는다.**

입력과 출력을 같은 칸으로 묶어 놓고 돌린다.

- 순진한 판은 `z := 1` 이 입력을 **덮어써서** 3 이 사라진다. 남은 것은 1 이고,
  한 바퀴 돌면 0 이 된다.
- 안전한 판은 `newvar t := z` 가 3 을 먼저 찍어 둔다. `z := 1` 이 입력을 덮어써도
  `t` 에 3 이 살아 있어 제대로 센다.

`newvar` 가 여기서 하는 일이 §2.5 의 이름 바꾸기 정리와 짝을 이룬다 — 지역 변수는
바깥 이름과 절대 합쳐지지 않으므로, 밖에서 무슨 별칭이 생기든 안쪽 계산이 지켜진다.

`while` 이 있으므로 `run` 으로 계산한 뒤 `run_sound` 로 표시적 의미에 옮긴다.
결과 상태를 손으로 적지 않으려고 `Option.map` 으로 `z` 만 뽑아 본다.
-/
@[exercise "Ex 2.7" 2]
theorem fact_alias_safe_vs_naive :
    (∃ τ, (factSafe /ᶜ aliasToZ).eval (State.const 3) = some τ ∧ τ "z" = 6)
      ∧ (∃ τ, (factNaive /ᶜ aliasToZ).eval (State.const 3) = some τ ∧ τ "z" = 0) := by
  constructor
  · rw [factSafe_alias_eq]
    have h : (factSafeAliased.run 4 (State.const 3)).map (fun σ => σ "z") = some 6 := by
      simp [factSafeAliased, Comm.run, restore, BoolExp.eval, IntExp.eval, IntOp.denote,
        Cmp.denoteBool, State.const, State.subst_def, Function.update]
    obtain ⟨τ, hτ, hs⟩ := Option.map_eq_some_iff.mp h
    exact ⟨τ, Comm.run_sound hτ, hs⟩
  · rw [factNaive_alias_eq]
    have h : (factNaiveAliased.run 2 (State.const 3)).map (fun σ => σ "z") = some 0 := by
      simp [factNaiveAliased, Comm.run, BoolExp.eval, IntExp.eval, IntOp.denote,
        Cmp.denoteBool, State.subst_def, Function.update]
    obtain ⟨τ, hτ, hs⟩ := Option.map_eq_some_iff.mp h
    exact ⟨τ, Comm.run_sound hτ, hs⟩
-- ANCHOR_END: fact

/-! ## 여기서 어디로 가나

연습 2.6 은 "언제 순서를 바꿔도 되는가" 를 `FV` 와 `FA` 로 답했고, 2.7 은 별칭을 막는
법이 지역 변수임을 보였다. 다음은 연습 2.8 이다 — 명제 2.7(치환 정리)의 단사 가정을
얼마나 약하게 할 수 있는가. 답의 실마리는 2.7 에 이미 있다: **읽기만 하는 변수는 합쳐도
된다.** 대입이 있는 자리에서만 이름의 수가 저장 공간의 수와 같아야 한다. -/

end Reynolds.Answers.Ch02.Ex
