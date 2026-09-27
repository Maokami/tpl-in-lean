/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Answers.Ch01.Ex.Summation

/-!
# 연습 1.5(c) — 합 식의 치환 정리

Reynolds 연습 1.5(c) (p. 23)는 자유 변수와 치환을 정의하면서 §1.4의 결합·치환
명제가 계속 성립하도록 요구한다. `Summation.lean`의 정의에 대해 그 의무를 확인한다.
상계와 하계는 바깥 상태에서, 본체는 결합 변수를 갱신한 상태에서 계산한다.

## 읽는 순서
`Summation.lean`의 자유 변수·치환·일치 정리 → 이 파일의 신선성 → 치환 정리.

## 연습의 전제
일치 정리도 별도 연습이므로 `hcoin`이라는 가설로 받는다. 따라서 그 연습을 아직
풀지 않아도 치환 정리를 독립적으로 풀 수 있다. 완성본에서는 `coincidence_sExp`를
이 가설에 넣으면 된다. 뒤의 한 변수 치환과 이름 바꾸기는 채점하지 않는 따름정리다.

**책과의 차이**: 본문의 단언 언어 전체를 바꾸지 않고, 합 식을 더한 정수 식 `SExp`의
성질을 증명한다. 양화 단언까지 확장한 언어와 연습 1.7의 구문적 α-동치는 다루지 않는다.
-/

@[expose] public section

namespace Reynolds.Answers.Ch01.Summation

open Reynolds Reynolds.Answers.Ch01 Cslib

universe u
variable {V : Type u} [DecidableEq V] [HasFresh V]

/-- 연습 1.5(c) (p. 23)의 지원 정리: 선택된 결합 변수는 포획 위험 집합 밖에 있다. -/
theorem SExp.newBinder_notMem (e : SExp V) (v : V) (δ : SSubst V) :
    e.newBinder v δ ∉ e.captureSet v δ := by
  unfold SExp.newBinder
  split
  · exact HasFresh.fresh_notMem _
  · assumption

/-- 연습 1.5(c) (p. 23)의 지원 정리: 실제 치환되는 식의 자유 변수를 포획하지 않는다. -/
theorem SExp.newBinder_notMem_fv {e : SExp V} {v w : V} {δ : SSubst V}
    (hw : w ∈ e.fv) (hne : w ≠ v) : e.newBinder v δ ∉ (δ w).fv := by
  intro hmem
  exact e.newBinder_notMem v δ
    (Finset.mem_biUnion.mpr ⟨w, Finset.mem_erase.mpr ⟨hne, hw⟩, hmem⟩)

/-- 연습 1.5(c) (p. 23): 명제 1.2(a)의 합 식 판. 자유 변수 위의 치환만 결과를 결정한다. -/
theorem subst_congr_sExp (e : SExp V) :
    ∀ δ δ' : SSubst V, (∀ w ∈ e.fv, δ w = δ' w) → e /ₜ δ = e /ₜ δ' := by
  induction e with
  | num n => intro _ _ _; rfl
  | var v => intro _ _ h; exact h v (by simp [SExp.fv])
  | neg e ih => intro δ δ' h; simp [SExp.subst, ih δ δ' h]
  | bin op a b iha ihb =>
      intro δ δ' h
      simp [SExp.subst,
        iha δ δ' (fun w hw => h w (by simp [SExp.fv, hw])),
        ihb δ δ' (fun w hw => h w (by simp [SExp.fv, hw]))]
  | sum v lo hi body ihlo ihhi ihbody =>
      intro δ δ' h
      have hcap : body.captureSet v δ = body.captureSet v δ' := by
        apply Finset.biUnion_congr rfl
        intro w hw
        rw [h w (by simp [SExp.fv, Finset.mem_erase.mp hw])]
      have hb : body.newBinder v δ = body.newBinder v δ' := by
        simp only [SExp.newBinder, hcap]
      have hlo := ihlo δ δ' (fun w hw => h w (by simp [SExp.fv, hw]))
      have hhi := ihhi δ δ' (fun w hw => h w (by simp [SExp.fv, hw]))
      simp only [SExp.subst, hb, hlo, hhi]
      congr 1
      apply ihbody
      intro w hw
      by_cases hwv : w = v
      · subst w; simp
      · simp [hwv, h w (by simp [SExp.fv, hwv, hw])]

/-- 연습 1.5(c) (p. 23): 명제 1.2(b)의 합 식 판. 항등 치환은 결합 변수도 바꾸지 않는다. -/
theorem subst_var_sExp (e : SExp V) : e /ₜ SExp.var = e := by
  induction e with
  | num n | var v => rfl
  | neg e ih => simp [SExp.subst, ih]
  | bin op a b iha ihb => simp [SExp.subst, iha, ihb]
  | sum v lo hi body ihlo ihhi ihbody =>
      have hcap : body.captureSet v SExp.var = body.fv.erase v := by
        simp [SExp.captureSet, SExp.fv]
      have hb : body.newBinder v SExp.var = v := by simp [SExp.newBinder, hcap]
      simp [SExp.subst, hb, ihlo, ihhi, ihbody]

/-- 연습 1.5(c) (p. 23): 명제 1.2(c)의 합 식 판. 치환되는 자유 발생의 자유 변수만 남는다. -/
theorem fv_subst_sExp (e : SExp V) (δ : SSubst V) :
    (e /ₜ δ).fv = e.fv.biUnion (fun w => (δ w).fv) := by
  induction e generalizing δ with
  | num n => simp [SExp.subst, SExp.fv]
  | var v => simp [SExp.subst, SExp.fv]
  | neg e ih => simpa [SExp.subst, SExp.fv] using ih δ
  | bin op a b iha ihb => simp [SExp.subst, SExp.fv, iha, ihb, Finset.union_biUnion]
  | sum v lo hi body ihlo ihhi ihbody =>
      have hbody :
          (body.fv.biUnion (fun w =>
            ((Function.update δ v (.var (body.newBinder v δ))) w).fv)).erase
            (body.newBinder v δ) = body.captureSet v δ := by
        ext x
        rw [Finset.mem_erase]
        constructor
        · rintro ⟨hx, hxbody⟩
          obtain ⟨w, hw, hmem⟩ := Finset.mem_biUnion.mp hxbody
          by_cases hwv : w = v
          · subst w
            simp only [Function.update_self, SExp.fv, Finset.mem_singleton] at hmem
            exact (hx hmem).elim
          · exact Finset.mem_biUnion.mpr
              ⟨w, Finset.mem_erase.mpr ⟨hwv, hw⟩, by simpa [hwv] using hmem⟩
        · intro hcap
          have hx : x ≠ body.newBinder v δ := by
            rintro rfl
            exact body.newBinder_notMem v δ hcap
          obtain ⟨w, hw, hmem⟩ := Finset.mem_biUnion.mp hcap
          exact ⟨hx, Finset.mem_biUnion.mpr ⟨w, (Finset.mem_erase.mp hw).2,
            by simpa [(Finset.mem_erase.mp hw).1] using hmem⟩⟩
      simp [SExp.subst, SExp.fv, ihlo, ihhi, ihbody, hbody,
        Finset.union_biUnion, SExp.captureSet]

-- ANCHOR: substitutionSExp
-- ANCHOR: stmtSubstitutionSExp
/--
연습 1.5(c) (p. 23): 명제 1.3 (§1.4)의 합 식 판.
치환한 구문을 평가하는 것과 치환 사상을 평가한 상태에서 원래 구문을 평가하는 것이 같다.
`hcoin`은 별도 일치 정리 연습의 결론이다. 가설로 받아 두 연습의 채점을 분리한다.
-/
@[exercise "Ex 1.5c-substitution" 3]
theorem substitution_sExp
    (hcoin : ∀ (e : SExp V) (σ σ' : State V),
      (∀ w ∈ e.fv, σ w = σ' w) → ⟦e⟧ₛ σ = ⟦e⟧ₛ σ') :
    ∀ (e : SExp V) (δ : SSubst V) (σ σ' : State V),
      (∀ w ∈ e.fv, σ w = ⟦δ w⟧ₛ σ') → ⟦e /ₜ δ⟧ₛ σ' = ⟦e⟧ₛ σ
-- ANCHOR_END: stmtSubstitutionSExp
    := by
  intro e
  induction e with
  | num n => intro _ _ _ _; rfl
  | var v => intro _ _ _ h; exact (h v (by simp [SExp.fv])).symm
  | neg e ih => intro δ σ σ' h; simp [SExp.subst, SExp.eval, ih δ σ σ' h]
  | bin op a b iha ihb =>
      intro δ σ σ' h
      simp [SExp.subst, SExp.eval,
        iha δ σ σ' (fun w hw => h w (by simp [SExp.fv, hw])),
        ihb δ σ σ' (fun w hw => h w (by simp [SExp.fv, hw]))]
  | sum v lo hi body ihlo ihhi ihbody =>
      intro δ σ σ' h
      have hlo := ihlo δ σ σ' (fun w hw => h w (by simp [SExp.fv, hw]))
      have hhi := ihhi δ σ σ' (fun w hw => h w (by simp [SExp.fv, hw]))
      simp only [SExp.subst, SExp.eval, hlo, hhi]
      refine Finset.sum_congr rfl fun k _ => ihbody _ _ _ ?_
      intro w hw
      by_cases hwv : w = v
      · subst w; simp [SExp.eval]
      · have hww := h w (by simp [SExp.fv, hwv, hw])
        have hfresh : body.newBinder v δ ∉ (δ w).fv :=
          SExp.newBinder_notMem_fv hw hwv
        have hc : ⟦δ w⟧ₛ (σ'[body.newBinder v δ := k]) = ⟦δ w⟧ₛ σ' := by
          apply hcoin
          intro x hx
          have hne : x ≠ body.newBinder v δ := by rintro rfl; exact hfresh hx
          simp [hne]
        simp [hwv, hc, hww]
-- ANCHOR_END: substitutionSExp

/-- 연습 1.5(c) (p. 23): 명제 1.4의 한 변수 치환 판. 나머지 변수는 그대로 둔다. -/
theorem substitution_single_sExp (e t : SExp V) (v : V) (σ : State V) :
    ⟦e /[v := t]⟧ₛ σ = ⟦e⟧ₛ (σ[v := ⟦t⟧ₛ σ]) := by
  apply substitution_sExp coincidence_sExp
  intro w _
  by_cases hw : w = v
  · subst w; simp
  · simp [hw, SExp.eval]

/--
연습 1.5(c) (p. 23): 명제 1.5의 합 식 판. 새 이름은 본체의 다른 자유 변수와 겹치지 않는다.
경계 식은 결합 범위 밖이므로 바꾸지 않는다. 새 이름이 경계 식에 나타나는 것은 허용된다.
-/
theorem renaming_sum (lo hi body : SExp V) (v fresh : V)
    (hfresh : fresh ∉ body.fv.erase v) (σ : State V) :
    ⟦SExp.sum fresh lo hi (body /[v := .var fresh])⟧ₛ σ =
      ⟦SExp.sum v lo hi body⟧ₛ σ := by
  simp only [SExp.eval]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [substitution_single_sExp]
  apply coincidence_sExp
  intro w hw
  by_cases hwv : w = v
  · subst w; simp [SExp.eval]
  · have hwf : w ≠ fresh := by
      rintro rfl
      exact hfresh (Finset.mem_erase.mpr ⟨hwv, hw⟩)
    simp [hwv, hwf]

end Reynolds.Answers.Ch01.Summation
