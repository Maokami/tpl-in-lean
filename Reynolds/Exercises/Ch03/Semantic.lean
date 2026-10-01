/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Exercises.Ch03.Spec

/-!
# §3.3–§3.5 의미 단언 위의 규칙

Reynolds §3.3–§3.5의 대입(AS), 순차 합성(SQ), 조건(CD), 부분 반복(WHP), 전체 반복(WHT), 변수 선언(DC), 이름 바꾸기(RN)를 다룬다.

## 이 파일에서 다루는 것
부분·전체 정확성의 뜻을 직접 써서 AS·SQ·CD·SP·WC·CA·DA·CST를 독립 연습으로 증명한다.
CSP는 종료 전제가 없는 부분 정확성 규칙으로 증명한다.
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

namespace Reynolds.Exercises.Ch03

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

/-- DC (§3.5 p.67, 연습 3.9). 사후조건만 지역 변수를 무시하면 된다.
앞부분이 끝난 상태의 변수 값을 복원하므로 사전조건과 초기값에는 신선함을 요구하지 않는다. -/
@[exercise "Ex 3.9 dc-sound" 2]
theorem dc_sound (s : List (Comm V)) (P Q : State V → Prop)
    (v : V) (e : IntExp V) (c : Comm V)
    (hQ : ∀ (σ : State V) (n : Int), Q (σ[v := n]) ↔ Q σ) :
    (PartialCorrectS P (Comm.seqs s (.seq (.assign v e) c)) Q →
      PartialCorrectS P (Comm.seqs s (.newvar v e c)) Q) ∧
    (TotalCorrectS P (Comm.seqs s (.seq (.assign v e) c)) Q →
      TotalCorrectS P (Comm.seqs s (.newvar v e c)) Q) := by
  -- 힌트: `Comm.eval_seqs`로 앞부분을 분리하고 `Flat.bind_eq_some_iff`로 중간 상태를 꺼낸다.
  -- 복원에는 그 중간 상태의 값을 쓴다. `Flat.map_eq_some_iff`와 `hQ`를 적용한다.
  sorry


/-- RN (§3.5 p.68)의 명령 앞부분 판. §2.5의 지역 이름 바꾸기는 전체 상태의 의미를 보존한다. -/
@[exercise "§3.5 rn-sound" 2]
theorem rn_sound [HasFresh V] (p q : Assert V) {c c' : Comm V}
    (h : Comm.PrefixRename c c') :
    (PartialCorrect p c q → PartialCorrect p c' q) ∧
    (TotalCorrect p c q → TotalCorrect p c' q) := by
  -- 힌트: `Comm.newvar_rename`과 `Comm.seqs_congr`로 명령 의미의 등식을 얻는다.
  -- `PrefixRename`의 두 방향을 나눈 뒤 부분·전체 정확성의 정의에 등식을 쓴다.
  sorry


/-- AS (§3.3). 갱신된 상태에서 사후조건을 묻는 대입은 부분·전체 정확성을 함께 만족한다. -/
@[exercise "§3.3 as-sound" 1]
theorem as_sound (Q : State V → Prop) (v : V) (e : IntExp V) :
    PartialCorrectS (fun σ => Q (σ[v := ⟦e⟧ₑ σ])) (.assign v e) Q ∧
    TotalCorrectS (fun σ => Q (σ[v := ⟦e⟧ₑ σ])) (.assign v e) Q := by
  -- 힌트: 부분 판은 종료 상태를 맞추고, 전체 판은 갱신한 상태를 증인으로 준다.
  sorry


/-- SQ (§3.3). 가운데 조건을 공유하는 두 명령을 순서대로 실행한다. -/
@[exercise "§3.3 sq-sound" 1]
theorem sq_sound {P R Q : State V → Prop} {c₀ c₁ : Comm V} :
    (PartialCorrectS P c₀ R → PartialCorrectS R c₁ Q → PartialCorrectS P (.seq c₀ c₁) Q) ∧
    (TotalCorrectS P c₀ R → TotalCorrectS R c₁ Q → TotalCorrectS P (.seq c₀ c₁) Q) := by
  -- 힌트: 부분 판은 첫 명령의 결과를 나눈다. 전체 판은 두 종료 증인을 잇는다.
  sorry


/-- CD (§3.5). 참인 가지와 거짓인 가지의 정확성을 각각 확인한다. -/
@[exercise "§3.5 cd-sound" 1]
theorem cd_sound {P Q : State V → Prop} {b : BoolExp V} {c₀ c₁ : Comm V} :
    (PartialCorrectS (fun σ => P σ ∧ ⟦b⟧ᵇ σ = true) c₀ Q →
      PartialCorrectS (fun σ => P σ ∧ ⟦b⟧ᵇ σ = false) c₁ Q →
      PartialCorrectS P (.ite b c₀ c₁) Q) ∧
    (TotalCorrectS (fun σ => P σ ∧ ⟦b⟧ᵇ σ = true) c₀ Q →
      TotalCorrectS (fun σ => P σ ∧ ⟦b⟧ᵇ σ = false) c₁ Q →
      TotalCorrectS P (.ite b c₀ c₁) Q) := by
  -- 힌트: 각 성분에서 조건의 불 값을 나누고 해당 가지의 가정을 쓴다.
  sorry


/-- WHP (§3.4). 불변식을 보존하는 본체에서 Scott 귀납법으로 반복의 부분 정확성을 얻는다. -/
@[exercise "§3.4 whp-sound" 3]
theorem PartialCorrectS.wh {I : State V → Prop} {b : BoolExp V} {c : Comm V}
    (hbody : PartialCorrectS (fun σ => I σ ∧ ⟦b⟧ᵇ σ = true) c I) :
    PartialCorrectS I (.wh b c) (fun σ => I σ ∧ ⟦b⟧ᵇ σ = false) := by
  -- 힌트: Sat.admissible·Sat.bot과 Scott 귀납법을 쓴다. 한 바퀴에서는 본체의 종료 여부를 나눈다.
  sorry


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
    TotalCorrectS I (.wh b c) (fun σ => I σ ∧ ⟦b⟧ᵇ σ = false) := by
  -- 먼저 볼 것: `Comm.eval_isSemantics.2.2.2.2.1`, `Flat.bind_some`.
  -- 힌트 1: `E σ < n`인 상태의 종료를 `n : Nat`에 대한 귀납으로 보인다.
  -- 힌트 2: 조건이 거짓이면 즉시 종료한다. 참이면 비음수 조건과 엄격한 감소를 쓴다.
  -- 힌트 3: 본체 실행 전의 값을 `hbody (E σ)`에 넣는다. 마지막에는 상계
  --         `(E σ).toNat + 1`을 택한다. `omega`로 정수 부등식을 정리할 수 있다.
  sorry


/-- SP (§3.3 p.59). 더 강한 사전조건에서 원래 사전조건을 얻는다. -/
@[exercise "§3.3 sp-sound" 1]
theorem sp_sound {P P' Q : State V → Prop} {c : Comm V}
    (hp : ∀ σ, P' σ → P σ) :
    (PartialCorrectS P c Q → PartialCorrectS P' c Q) ∧
    (TotalCorrectS P c Q → TotalCorrectS P' c Q) := by
  -- 힌트: 사전조건의 함의를 적용한다.
  sorry


/-- WC (§3.3 p.59). 종료 상태에서 사후조건의 함의를 적용한다. -/
@[exercise "§3.3 wc-sound" 1]
theorem wc_sound {P Q Q' : State V → Prop} {c : Comm V}
    (hq : ∀ σ, Q σ → Q' σ) :
    (PartialCorrectS P c Q → PartialCorrectS P c Q') ∧
    (TotalCorrectS P c Q → TotalCorrectS P c Q') := by
  -- 힌트: 종료 상태에 사후조건의 함의를 적용한다.
  sorry


/-- CA (§3.5 p.68). 두 전체 명세의 종료 상태는 같은 명령의 결과이므로 같다. -/
@[exercise "§3.5 ca-sound" 2]
theorem ca_sound {P₀ P₁ Q₀ Q₁ : State V → Prop} {c : Comm V} :
    (PartialCorrectS P₀ c Q₀ → PartialCorrectS P₁ c Q₁ →
      PartialCorrectS (fun σ => P₀ σ ∧ P₁ σ) c (fun σ => Q₀ σ ∧ Q₁ σ)) ∧
    (TotalCorrectS P₀ c Q₀ → TotalCorrectS P₁ c Q₁ →
      TotalCorrectS (fun σ => P₀ σ ∧ P₁ σ) c (fun σ => Q₀ σ ∧ Q₁ σ)) := by
  -- 힌트: 전체 판의 두 종료 상태가 같음을 Flat.some.inj로 보인다.
  sorry


/-- DA (§3.5 p.68). 사전조건의 어느 성분이 참인지에 따라 그 명세를 사용한다. -/
@[exercise "§3.5 da-sound" 1]
theorem da_sound {P₀ P₁ Q₀ Q₁ : State V → Prop} {c : Comm V} :
    (PartialCorrectS P₀ c Q₀ → PartialCorrectS P₁ c Q₁ →
      PartialCorrectS (fun σ => P₀ σ ∨ P₁ σ) c (fun σ => Q₀ σ ∨ Q₁ σ)) ∧
    (TotalCorrectS P₀ c Q₀ → TotalCorrectS P₁ c Q₁ →
      TotalCorrectS (fun σ => P₀ σ ∨ P₁ σ) c (fun σ => Q₀ σ ∨ Q₁ σ)) := by
  -- 힌트: 사전조건의 선언을 경우로 나눈다.
  sorry


/-- CSP (§3.5 p.68). 명령이 쓰지 않는 자유 변수의 단언은 종료 시 보존된다.
명세 전제는 없으며, 발산해도 부분 정확성에는 문제가 없다. -/
@[exercise "§3.5 csp-sound" 2]
theorem csp_sound {p : Assert V} {c : Comm V} (hp : Disjoint c.fa p.fv) :
    PartialCorrect p c p := by
  -- 힌트: Comm.eval_agree_outside_fa와 coincidence_assert를 쓴다.
  sorry


/-- CST (§3.5 p.68). 전체 명세 전제에서 종료 상태를 얻고, 쓰이지 않는 단언을 보존한다.
부분 판도 함께 증명한다. 두 성분 모두 다른 연습의 답 없이 풀 수 있다. -/
@[exercise "§3.5 cst-sound" 2]
theorem cst_sound {P Q : State V → Prop} {r : Assert V} {c : Comm V}
    (hr : Disjoint c.fa r.fv) :
    (PartialCorrectS P c Q →
      PartialCorrectS (fun σ => P σ ∧ r.eval σ) c (fun σ => Q σ ∧ r.eval σ)) ∧
    (TotalCorrectS P c Q →
      TotalCorrectS (fun σ => P σ ∧ r.eval σ) c (fun σ => Q σ ∧ r.eval σ)) := by
  -- 힌트: 전제에서 종료 상태를 얻고 쓰이지 않는 단언을 보존한다.
  sorry


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

/-- 구문 판 명세는 의미 판 명세의 특수 경우다 — 정의 그대로 (§3.1). -/
theorem PartialCorrect.toS {p q : Assert V} {c : Comm V} (h : ｛p｝c｛q｝) :
    PartialCorrectS ⟦p⟧ₐ c ⟦q⟧ₐ :=
  h

end Reynolds.Exercises.Ch03
