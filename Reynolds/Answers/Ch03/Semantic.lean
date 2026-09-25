/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Answers.Ch03.Derived

/-!
# §3.8 준비 — 의미 단언 위의 규칙

§3.8 · §3.9 의 예제는 불변식에 `fib` 와 거듭제곱이 든다. 둘 다 `Assert` 로는 적을 수 없다
(적을 수는 있지만 괴델 부호화를 거쳐야 한다 — §3.10). 그래서 예제는 **의미 단언**
`State V → Prop` 위에서 간다 (§3.1 의 "둘 다" 결정).

이 파일은 `Hoare` 의 규칙들을 의미 판으로 다시 적는다. 대입 공리의 의미 판은 치환이 아니라
**상태 갱신**이다 — `Q (σ[v := ⟦e⟧ σ])`. 명제 1.4 가 그 둘이 같다고 말하므로, 구문 판에서
치환이 하던 일을 여기서는 갱신이 그대로 한다.

`while` 의 의미 판은 `Soundness.lean` 의 `wh_sound` 와 같은 Scott 귀납법이다. 그 연습을
풀었다면 같은 증명을 알아볼 것이다.
-/

@[expose] public section

namespace Reynolds.Answers.Ch03

open Reynolds Reynolds.Answers.Ch01 Reynolds.Answers.Ch02

universe u

variable {V : Type u} [DecidableEq V]

namespace PartialCorrectS

-- ANCHOR: semRules
/-- 대입 — 의미 판. 사후조건을 갱신된 상태에서 묻는다. -/
theorem assign (Q : State V → Prop) (v : V) (e : IntExp V) :
    PartialCorrectS (fun σ => Q (σ[v := ⟦e⟧ₑ σ])) (.assign v e) Q := by
  intro σ hq τ hτ
  obtain rfl := Option.some.inj hτ
  exact hq

/-- 순차 합성 — 의미 판. -/
theorem seq {P R Q : State V → Prop} {c₀ c₁ : Comm V}
    (h₀ : PartialCorrectS P c₀ R) (h₁ : PartialCorrectS R c₁ Q) :
    PartialCorrectS P (.seq c₀ c₁) Q := by
  intro σ hp τ hτ
  change Option.bind (⟦c₀⟧ᶜ σ) ⟦c₁⟧ᶜ = some τ at hτ
  rcases h : ⟦c₀⟧ᶜ σ with _ | ρ
  · rw [h] at hτ; simp at hτ
  · rw [h] at hτ
    exact h₁ ρ (h₀ σ hp ρ h) τ hτ

/-- 조건 — 의미 판. 조건을 단언으로 옮길 필요 없이 불 값 그대로 쓴다. -/
theorem ite {P Q : State V → Prop} {b : BoolExp V} {c₀ c₁ : Comm V}
    (h₀ : PartialCorrectS (fun σ => P σ ∧ ⟦b⟧ᵇ σ = true) c₀ Q)
    (h₁ : PartialCorrectS (fun σ => P σ ∧ ⟦b⟧ᵇ σ = false) c₁ Q) :
    PartialCorrectS P (.ite b c₀ c₁) Q := by
  intro σ hp τ hτ
  change (if ⟦b⟧ᵇ σ then ⟦c₀⟧ᶜ σ else ⟦c₁⟧ᶜ σ) = some τ at hτ
  cases hb : ⟦b⟧ᵇ σ
  · rw [hb] at hτ
    exact h₁ σ ⟨hp, hb⟩ τ hτ
  · rw [hb, if_pos rfl] at hτ
    exact h₀ σ ⟨hp, hb⟩ τ hτ

/-- 반복 — 의미 판. `I` 가 불변식. Scott 귀납법. -/
theorem wh {I : State V → Prop} {b : BoolExp V} {c : Comm V}
    (hbody : PartialCorrectS (fun σ => I σ ∧ ⟦b⟧ᵇ σ = true) c I) :
    PartialCorrectS I (.wh b c) (fun σ => I σ ∧ ⟦b⟧ᵇ σ = false) := by
  change Sat I (fix (whileF b ⟦c⟧ᶜ) (whileF_monotone b ⟦c⟧ᶜ)) _
  refine scott_induction (whileF_monotone b ⟦c⟧ᶜ)
    (P := fun w => Sat I w fun σ => I σ ∧ ⟦b⟧ᵇ σ = false)
    (fun d hd => Sat.admissible _ _ d hd) (Sat.bot _ _) ?_
  intro w hw σ hi τ hτ
  change (if ⟦b⟧ᵇ σ then Option.bind (⟦c⟧ᶜ σ) w else some σ) = some τ at hτ
  cases hb : ⟦b⟧ᵇ σ
  · rw [hb] at hτ
    obtain rfl := Option.some.inj hτ
    exact ⟨hi, hb⟩
  · rw [hb, if_pos rfl] at hτ
    rcases hc : ⟦c⟧ᶜ σ with _ | ρ
    · rw [hc] at hτ; simp at hτ
    · rw [hc] at hτ
      exact hw ρ (hbody σ ⟨hi, hb⟩ ρ hc) τ hτ

/-- 결과 규칙 — 의미 판. 전제가 술어 사이의 함의다. -/
theorem conseq {P P' Q Q' : State V → Prop} {c : Comm V}
    (hp : ∀ σ, P' σ → P σ) (h : PartialCorrectS P c Q) (hq : ∀ σ, Q σ → Q' σ) :
    PartialCorrectS P' c Q' :=
  fun σ h' τ hτ => hq τ (h σ (hp σ h') τ hτ)
-- ANCHOR_END: semRules

end PartialCorrectS

-- ANCHOR: semOfSyn
/-- 구문 판 명세는 의미 판 명세의 특수 경우다 — 정의 그대로 (§3.1). -/
theorem PartialCorrect.toS {p q : Assert V} {c : Comm V} (h : ｛p｝c｛q｝) :
    PartialCorrectS ⟦p⟧ₐ c ⟦q⟧ₐ :=
  h
-- ANCHOR_END: semOfSyn

end Reynolds.Answers.Ch03
