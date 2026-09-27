/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Answers.Ch03.Spec

/-!
# §3.3–§3.5 의미 단언 위의 규칙

Reynolds §3.3–§3.5의 대입(AS), 순차 합성(SQ), 조건(CD), 부분 반복(WHP), 전체 반복(WHT), 변수 선언(DC), 이름 바꾸기(RN)를 다룬다.

## 이 파일에서 다루는 것
부분·전체 정확성의 뜻을 직접 써서 AS·SQ·CD를 각각 한 연습으로 증명한다.
WHP는 Scott 귀납법, WHT는 변항의 자연수 상계에 대한 귀납법으로 증명한다. 구문 규칙의 건전성은 이 정리들의 따름정리다.

## 핵심 아이디어
의미 단언은 `State V → Prop`다. 대입은 사후조건을 갱신된 상태에서 묻는다.
순차 합성에서는 가운데 상태를, 조건에서는 선택된 가지를 확인한다.
부분 정확성은 발산한 경우 의무가 없고, 전체 정확성은 종료 상태도 제시한다.

## 읽는 순서
`Spec.lean` → 이 파일 → `Hoare.lean` → `Soundness.lean`.

## 책과의 차이
대부분의 규칙은 구문 단언 대신 상태 술어를 사용한다. `fib`와 거듭제곱 예제에도 적용할 수 있다.
**책과의 차이**: RN은 같은 명령 앞부분 뒤의 지역 선언 이름 바꾸기만 표현한다.
-/

@[expose] public section

namespace Reynolds.Answers.Ch03

open Reynolds Reynolds.Answers.Ch01 Reynolds.Answers.Ch02

universe u

variable {V : Type u} [DecidableEq V]

/-- DC의 앞부분 `s`를 명령 `c` 앞에 순서대로 붙인다. 빈 목록이면 `c`다. -/
def Comm.seqs : List (Comm V) → Comm V → Comm V
  | [], c => c
  | d :: ds, c => .seq d (Comm.seqs ds c)

/-- 명령 목록을 실행한 뒤 마지막 명령을 실행한다. -/
theorem Comm.eval_seqs (s : List (Comm V)) (c : Comm V) (σ : State V) :
    (Comm.seqs s c).eval σ = Flat.bind ((Comm.seqs s .skip).eval σ) c.eval := by
  induction s generalizing σ with
  | nil => rfl
  | cons d ds ih =>
    simp only [Comm.seqs, Comm.eval]
    rw [Flat.bind_assoc]
    congr 1
    funext ρ
    exact ih ρ

/-- 같은 의미의 명령은 같은 앞부분 뒤에서도 같은 의미를 갖는다. -/
theorem Comm.seqs_congr (s : List (Comm V)) {c c' : Comm V} (h : c.eval = c'.eval) :
    (Comm.seqs s c).eval = (Comm.seqs s c').eval := by
  funext σ
  rw [Comm.eval_seqs s c σ, Comm.eval_seqs s c' σ, h]

/-- §3.5 RN의 명령 앞부분 판. 초기값 식은 결합 범위 밖이므로 그대로 둔다.
책의 일반 RN 중 이 형태만 표현하며, 두 방향과 반복 적용을 허용한다. -/
inductive Comm.PrefixRename [HasFresh V] : Comm V → Comm V → Prop where
  /-- 지역 결합 이름을 신선한 이름으로 바꾼다. -/
  | forward (s : List (Comm V)) (v w : V) (e : IntExp V) (c : Comm V)
      (hfresh : w ∉ c.fv.erase v) :
      PrefixRename (seqs s (.newvar v e c))
        (seqs s (.newvar w e (c /ᶜ Function.update id v w)))
  /-- 같은 이름 바꾸기를 거꾸로 적용한다. -/
  | backward (s : List (Comm V)) (v w : V) (e : IntExp V) (c : Comm V)
      (hfresh : w ∉ c.fv.erase v) :
      PrefixRename (seqs s (.newvar w e (c /ᶜ Function.update id v w)))
        (seqs s (.newvar v e c))

-- ANCHOR: dcSound
-- ANCHOR: stmtDcSound
/-- DC (§3.5 p.67, 연습 3.9). 사후조건만 지역 변수를 무시하면 된다.
앞부분이 끝난 상태의 변수 값을 복원하므로 사전조건과 초기값에는 신선함을 요구하지 않는다. -/
@[exercise "Ex 3.9 dc-sound" 2]
theorem dc_sound (s : List (Comm V)) (P Q : State V → Prop)
    (v : V) (e : IntExp V) (c : Comm V)
    (hQ : ∀ (σ : State V) (n : Int), Q (σ[v := n]) ↔ Q σ) :
    (PartialCorrectS P (Comm.seqs s (.seq (.assign v e) c)) Q →
      PartialCorrectS P (Comm.seqs s (.newvar v e c)) Q) ∧
    (TotalCorrectS P (Comm.seqs s (.seq (.assign v e) c)) Q →
      TotalCorrectS P (Comm.seqs s (.newvar v e c)) Q)
-- ANCHOR_END: stmtDcSound
    := by
  constructor
  · intro h σ hp τ ht
    rw [Comm.eval_seqs] at ht
    obtain ⟨ρ, hρ, ht⟩ := Flat.bind_eq_some_iff.mp ht
    change Flat.map (fun τ => τ[v := ρ v]) (c.eval (ρ[v := e.eval ρ])) = .some τ at ht
    obtain ⟨υ, hυ, rfl⟩ := Flat.map_eq_some_iff.mp ht
    apply (hQ υ (ρ v)).mpr
    apply h σ hp υ
    rw [Comm.eval_seqs, hρ]
    exact hυ
  · intro h σ hp
    obtain ⟨τ, ht, hq⟩ := h σ hp
    rw [Comm.eval_seqs] at ht
    obtain ⟨ρ, hρ, ht⟩ := Flat.bind_eq_some_iff.mp ht
    refine ⟨τ[v := ρ v], ?_, (hQ τ (ρ v)).mpr hq⟩
    rw [Comm.eval_seqs, hρ]
    change Flat.map (fun τ => τ[v := ρ v]) (c.eval (ρ[v := e.eval ρ])) = _
    change c.eval (ρ[v := e.eval ρ]) = .some τ at ht
    rw [ht]
    rfl
-- ANCHOR_END: dcSound

-- ANCHOR: rnSound
-- ANCHOR: stmtRnSound
/-- RN (§3.5 p.68)의 명령 앞부분 판. §2.5의 지역 이름 바꾸기는 전체 상태의 의미를 보존한다. -/
@[exercise "§3.5 rn-sound" 2]
theorem rn_sound [HasFresh V] (p q : Assert V) {c c' : Comm V}
    (h : Comm.PrefixRename c c') :
    (PartialCorrect p c q → PartialCorrect p c' q) ∧
    (TotalCorrect p c q → TotalCorrect p c' q)
-- ANCHOR_END: stmtRnSound
    := by
  have heq : c.eval = c'.eval := by
    cases h with
    | forward s v w e c hfresh =>
      exact Comm.seqs_congr s (Comm.newvar_rename v w e c hfresh).symm
    | backward s v w e c hfresh =>
      exact Comm.seqs_congr s (Comm.newvar_rename v w e c hfresh)
  constructor <;> intro hc <;> simpa only [PartialCorrect, PartialCorrectS,
    TotalCorrect, TotalCorrectS, heq] using hc
-- ANCHOR_END: rnSound

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
    obtain rfl := Flat.some.inj hτ
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
    change Flat.bind (⟦c₀⟧ᶜ σ) ⟦c₁⟧ᶜ = Flat.some τ at hτ
    rcases h : ⟦c₀⟧ᶜ σ with _ | ρ
    · rw [h] at hτ; simp at hτ
    · rw [h] at hτ
      exact h₁ ρ (h₀ σ hp ρ h) τ hτ
  · intro h₀ h₁ σ hp
    obtain ⟨ρ, hρ, hr⟩ := h₀ σ hp
    obtain ⟨τ, hτ, hq⟩ := h₁ ρ hr
    refine ⟨τ, ?_, hq⟩
    change Flat.bind (⟦c₀⟧ᶜ σ) ⟦c₁⟧ᶜ = Flat.some τ
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
    change (if ⟦b⟧ᵇ σ then ⟦c₀⟧ᶜ σ else ⟦c₁⟧ᶜ σ) = Flat.some τ at hτ
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
  change (if ⟦b⟧ᵇ σ then Flat.bind (⟦c⟧ᶜ σ) w else Flat.some σ) = Flat.some τ at hτ
  cases hb : ⟦b⟧ᵇ σ
  · rw [hb] at hτ
    obtain rfl := Flat.some.inj hτ
    exact ⟨hi, hb⟩
  · rw [hb, if_pos rfl] at hτ
    rcases hc : ⟦c⟧ᶜ σ with _ | ρ
    · rw [hc] at hτ; simp at hτ
    · rw [hc] at hτ
      exact hw ρ (hbody σ ⟨hi, hb⟩ ρ hc) τ hτ

-- ANCHOR_END: whpSound

-- ANCHOR: whtSound
-- ANCHOR: stmtWhtSound
/--
WHT (§3.4). 본체가 불변식을 보존하고 정수 변항을 엄격히 줄이면 반복이 종료한다.
변항의 비음수 조건은 불변식과 반복 조건이 참인 상태에만 요구한다.
마지막 실행 뒤 조건이 거짓이면 변항은 음수여도 된다.

**책과의 차이**: 책 p64의 유령 변수 대신 본체 실행 전의 값을 `n : Int`로 고정한다.
구문 단언의 유령 변수 규칙은 `Total.lean`에서 이 정리의 따름정리로 얻는다.
-/
@[exercise "§3.4 wht-sound" 3]
theorem TotalCorrectS.wh {I : State V → Prop} {E : State V → Int}
    {b : BoolExp V} {c : Comm V}
    (hbody : ∀ n : Int, TotalCorrectS
      (fun σ => I σ ∧ ⟦b⟧ᵇ σ = true ∧ E σ = n) c (fun σ => I σ ∧ E σ < n))
    (hnonneg : ∀ σ, I σ → ⟦b⟧ᵇ σ = true → 0 ≤ E σ) :
    TotalCorrectS I (.wh b c) (fun σ => I σ ∧ ⟦b⟧ᵇ σ = false)
-- ANCHOR_END: stmtWhtSound
    := by
  have whileEq : ∀ σ : State V, ⟦Comm.wh b c⟧ᶜ σ
      = if ⟦b⟧ᵇ σ then Flat.bind (⟦c⟧ᶜ σ) ⟦Comm.wh b c⟧ᶜ else Flat.some σ :=
    fun σ => Comm.eval_isSemantics.2.2.2.2.1 _ _ σ
  have stop : ∀ σ, I σ → ⟦b⟧ᵇ σ = false →
      ∃ τ, ⟦Comm.wh b c⟧ᶜ σ = Flat.some τ ∧ I τ ∧ ⟦b⟧ᵇ τ = false := by
    intro σ hi hb
    exact ⟨σ, by rw [whileEq, hb]; rfl, hi, hb⟩
  -- 자연수 상계를 하나씩 줄인다. 변항 자체는 정수로 둔다.
  have key : ∀ (n : Nat) (σ : State V), I σ → E σ < n →
      ∃ τ, ⟦Comm.wh b c⟧ᶜ σ = Flat.some τ ∧ I τ ∧ ⟦b⟧ᵇ τ = false := by
    intro n
    induction n with
    | zero =>
      intro σ hi hlt
      cases hb : ⟦b⟧ᵇ σ
      · exact stop σ hi hb
      · have h0 := hnonneg σ hi hb
        omega
    | succ n ih =>
      intro σ hi hlt
      cases hb : ⟦b⟧ᵇ σ
      · exact stop σ hi hb
      · obtain ⟨ρ, hρ, hiρ, hdec⟩ := hbody (E σ) σ ⟨hi, hb, rfl⟩
        obtain ⟨τ, hτ, hpost⟩ := ih ρ hiρ (by omega)
        exact ⟨τ, by rw [whileEq, hb, if_pos rfl, hρ]; exact hτ, hpost⟩
  intro σ hi
  exact key ((E σ).toNat + 1) σ hi (by omega)
-- ANCHOR_END: whtSound

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
