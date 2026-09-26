/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Answers.Ch03.Spec

/-!
# §3.3–§3.5 의미 단언 위의 규칙

Reynolds §3.3–§3.5의 대입(AS), 순차 합성(SQ), 조건(CD), 부분 반복(WHP)을 다룬다.

## 이 파일에서 다루는 것
부분·전체 정확성의 뜻을 직접 써서 AS·SQ·CD를 각각 한 연습으로 증명한다.
WHP는 Scott 귀납법으로 증명한다. 구문 규칙의 건전성은 이 정리들의 따름정리다.

## 핵심 아이디어
의미 단언은 `State V → Prop`다. 대입은 사후조건을 갱신된 상태에서 묻는다.
순차 합성에서는 가운데 상태를, 조건에서는 선택된 가지를 확인한다.
부분 정확성은 발산한 경우 의무가 없고, 전체 정확성은 종료 상태도 제시한다.

## 읽는 순서
`Spec.lean` → 이 파일 → `Hoare.lean` → `Soundness.lean`.

## 책과의 차이
구문 단언 대신 상태 술어를 사용한다. `fib`와 거듭제곱을 쓰는 예제에도 적용할 수 있다.
-/

@[expose] public section

namespace Reynolds.Answers.Ch03

open Reynolds Reynolds.Answers.Ch01 Reynolds.Answers.Ch02

universe u

variable {V : Type u} [DecidableEq V]

-- ANCHOR: asSound
-- ANCHOR: stmtAsSound
/-- AS (§3.3). 갱신된 상태에서 사후조건을 묻는 대입은 부분·전체 정확성을 함께 만족한다. -/
@[exercise "§3.3 as-sound" 1]
theorem as_sound (Q : State V → Prop) (v : V) (e : IntExp V) :
    PartialCorrectS (fun σ => Q (σ[v := ⟦e⟧ₑ σ])) (.assign v e) Q ∧
    TotalCorrectS (fun σ => Q (σ[v := ⟦e⟧ₑ σ])) (.assign v e) Q
-- ANCHOR_END: stmtAsSound
    := by
  constructor
  · intro σ hq τ hτ
    obtain rfl := Option.some.inj hτ
    exact hq
  · intro σ hq
    exact ⟨_, rfl, hq⟩
-- ANCHOR_END: asSound

-- ANCHOR: sqSound
-- ANCHOR: stmtSqSound
/-- SQ (§3.3). 가운데 조건을 공유하는 두 명령을 순서대로 실행한다. -/
@[exercise "§3.3 sq-sound" 1]
theorem sq_sound {P R Q : State V → Prop} {c₀ c₁ : Comm V} :
    (PartialCorrectS P c₀ R → PartialCorrectS R c₁ Q → PartialCorrectS P (.seq c₀ c₁) Q) ∧
    (TotalCorrectS P c₀ R → TotalCorrectS R c₁ Q → TotalCorrectS P (.seq c₀ c₁) Q)
-- ANCHOR_END: stmtSqSound
    := by
  constructor
  · intro h₀ h₁ σ hp τ hτ
    change Option.bind (⟦c₀⟧ᶜ σ) ⟦c₁⟧ᶜ = some τ at hτ
    rcases h : ⟦c₀⟧ᶜ σ with _ | ρ
    · rw [h] at hτ; simp at hτ
    · rw [h] at hτ
      exact h₁ ρ (h₀ σ hp ρ h) τ hτ
  · intro h₀ h₁ σ hp
    obtain ⟨ρ, hρ, hr⟩ := h₀ σ hp
    obtain ⟨τ, hτ, hq⟩ := h₁ ρ hr
    refine ⟨τ, ?_, hq⟩
    change Option.bind (⟦c₀⟧ᶜ σ) ⟦c₁⟧ᶜ = some τ
    rw [hρ]
    exact hτ
-- ANCHOR_END: sqSound

-- ANCHOR: cdSound
-- ANCHOR: stmtCdSound
/-- CD (§3.5). 참인 가지와 거짓인 가지의 정확성을 각각 확인한다. -/
@[exercise "§3.5 cd-sound" 1]
theorem cd_sound {P Q : State V → Prop} {b : BoolExp V} {c₀ c₁ : Comm V} :
    (PartialCorrectS (fun σ => P σ ∧ ⟦b⟧ᵇ σ = true) c₀ Q →
      PartialCorrectS (fun σ => P σ ∧ ⟦b⟧ᵇ σ = false) c₁ Q →
      PartialCorrectS P (.ite b c₀ c₁) Q) ∧
    (TotalCorrectS (fun σ => P σ ∧ ⟦b⟧ᵇ σ = true) c₀ Q →
      TotalCorrectS (fun σ => P σ ∧ ⟦b⟧ᵇ σ = false) c₁ Q →
      TotalCorrectS P (.ite b c₀ c₁) Q)
-- ANCHOR_END: stmtCdSound
    := by
  constructor
  · intro h₀ h₁ σ hp τ hτ
    change (if ⟦b⟧ᵇ σ then ⟦c₀⟧ᶜ σ else ⟦c₁⟧ᶜ σ) = some τ at hτ
    cases hb : ⟦b⟧ᵇ σ
    · rw [hb] at hτ
      exact h₁ σ ⟨hp, hb⟩ τ hτ
    · rw [hb, if_pos rfl] at hτ
      exact h₀ σ ⟨hp, hb⟩ τ hτ
  · intro h₀ h₁ σ hp
    cases hb : ⟦b⟧ᵇ σ
    · obtain ⟨τ, hτ, hq⟩ := h₁ σ ⟨hp, hb⟩
      exact ⟨τ, by change (if ⟦b⟧ᵇ σ then _ else _) = _; rw [hb]; exact hτ, hq⟩
    · obtain ⟨τ, hτ, hq⟩ := h₀ σ ⟨hp, hb⟩
      exact ⟨τ, by change (if ⟦b⟧ᵇ σ then _ else _) = _; rw [hb]; exact hτ, hq⟩
-- ANCHOR_END: cdSound

-- ANCHOR: whpSound
-- ANCHOR: stmtWhpSound
/-- WHP (§3.4). 불변식을 보존하는 본체에서 Scott 귀납법으로 반복의 부분 정확성을 얻는다. -/
@[exercise "§3.4 whp-sound" 3]
theorem PartialCorrectS.wh {I : State V → Prop} {b : BoolExp V} {c : Comm V}
    (hbody : PartialCorrectS (fun σ => I σ ∧ ⟦b⟧ᵇ σ = true) c I) :
    PartialCorrectS I (.wh b c) (fun σ => I σ ∧ ⟦b⟧ᵇ σ = false)
-- ANCHOR_END: stmtWhpSound
    := by
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

-- ANCHOR_END: whpSound

namespace PartialCorrectS

/-- AS의 부분 정확성 판. -/
theorem assign (Q : State V → Prop) (v : V) (e : IntExp V) :
    PartialCorrectS (fun σ => Q (σ[v := ⟦e⟧ₑ σ])) (.assign v e) Q :=
  (as_sound Q v e).1

/-- SQ의 부분 정확성 판. -/
theorem seq {P R Q : State V → Prop} {c₀ c₁ : Comm V}
    (h₀ : PartialCorrectS P c₀ R) (h₁ : PartialCorrectS R c₁ Q) :
    PartialCorrectS P (.seq c₀ c₁) Q := sq_sound.1 h₀ h₁

/-- CD의 부분 정확성 판. -/
theorem ite {P Q : State V → Prop} {b : BoolExp V} {c₀ c₁ : Comm V}
    (h₀ : PartialCorrectS (fun σ => P σ ∧ ⟦b⟧ᵇ σ = true) c₀ Q)
    (h₁ : PartialCorrectS (fun σ => P σ ∧ ⟦b⟧ᵇ σ = false) c₁ Q) :
    PartialCorrectS P (.ite b c₀ c₁) Q := cd_sound.1 h₀ h₁

/-- 결과 규칙 — 의미 판. 전제가 술어 사이의 함의다. -/
theorem conseq {P P' Q Q' : State V → Prop} {c : Comm V}
    (hp : ∀ σ, P' σ → P σ) (h : PartialCorrectS P c Q) (hq : ∀ σ, Q σ → Q' σ) :
    PartialCorrectS P' c Q' :=
  fun σ h' τ hτ => hq τ (h σ (hp σ h') τ hτ)

end PartialCorrectS

-- ANCHOR: semOfSyn
/-- 구문 판 명세는 의미 판 명세의 특수 경우다 — 정의 그대로 (§3.1). -/
theorem PartialCorrect.toS {p q : Assert V} {c : Comm V} (h : ｛p｝c｛q｝) :
    PartialCorrectS ⟦p⟧ₐ c ⟦q⟧ₐ :=
  h
-- ANCHOR_END: semOfSyn

end Reynolds.Answers.Ch03
