/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Answers.Ch03.Total

/-!
# 3장 대표 연습: 거짓 사전조건과 변수 치환

Reynolds 연습 3.5(p.79), 3.11(p.80)에 대응한다.

## 이 파일에서 다루는 것
- 모든 명령의 `[false] c [false]`를 추론 규칙으로 유도한다.
- 자유 변수 집합 위 단사인 이름 바꾸기가 전체 정확성을 보존함을 증명한다.
- 두 저장 공간을 합치면 타당했던 명세가 거짓이 되는 예를 계산한다.

## 읽는 순서
`Total.lean`을 읽고 2장의 `Comm.substitution_general`을 다시 확인한다.
첫 문제는 명령 구문에 대한 귀납이고, 두 번째는 이미 증명한 의미 정리의 적용이다.
두 연습은 서로의 답을 사용하지 않는다.

## 책과의 차이
없음. 3.11의 치환은 `Comm.subst`와 `Assert.subst`가 결합자의 포획을 회피하며,
단사성은 전체 변수 타입이 아니라 명세에 나타나는 유한 자유 변수 집합에만 요구한다.
-/

@[expose] public section

namespace Reynolds.Answers.Ch03

open Reynolds Reynolds.Answers.Ch01 Reynolds.Answers.Ch02

variable {V : Type*} [DecidableEq V] [HasFresh V]

-- ANCHOR: ex35
/--
연습 3.5. 사전조건 `false`를 만족하는 상태는 없지만, 여기서는 그 의미적 관찰에
그치지 않고 명령의 각 생성자마다 `HoareT`의 유도 나무를 구성한다.
반복의 불변식은 `false`, 변항은 `0`으로 잡는다.
-/
@[exercise "Ex 3.5" 2]
theorem ex_3_5 (c : Comm V) : HoareT .fls c .fls := by
  induction c with
  | «skip» => exact HoareT.skip .fls
  | assign v e =>
      exact HoareT.strengthen (fun _ h ↦ h.elim) (HoareT.assign .fls v e)
  | seq _ _ ih₀ ih₁ => exact HoareT.seq ih₀ ih₁
  | ite _ _ _ ih₀ ih₁ =>
      exact HoareT.ite (HoareT.strengthen (fun _ h ↦ h.1) ih₀)
        (HoareT.strengthen (fun _ h ↦ h.1) ih₁)
  | wh b c ih =>
      obtain ⟨z, hz⟩ := Cslib.fresh_exists (b.fv ∪ c.fv)
      refine HoareT.weaken (HoareT.wh (i := .fls) (e := .num 0) (z := z)
        (by simp [Assert.fv]) (fun h ↦ hz (Finset.mem_union_left _ h))
        (fun h ↦ hz (Finset.mem_union_right _ h)) (by simp [IntExp.fv])
        (fun _ h ↦ h.1.elim) ?_) (fun _ h ↦ h.1)
      exact HoareT.conseq (fun _ h ↦ h.1.1) ih (fun _ h ↦ h.elim)
  | «newvar» v e _ ih =>
      exact HoareT.newvar_comp (by simp [Assert.fv])
        (HoareT.strengthen (fun _ h ↦ h.elim) (HoareT.assign .fls v e)) ih
-- ANCHOR_END: ex35

-- ANCHOR: ex311
/--
연습 3.11. `FV(p) ∪ FV(c) ∪ FV(q)` 위에서 단사인 이름 바꾸기는 전체 정확성을
보존한다. 명제 2.7은 종료 여부도 보존하므로 새 실행의 종료 증인을 얻을 수 있다.
-/
@[exercise "Ex 3.11" 2]
theorem ex_3_11 {p q : Assert V} {c : Comm V} (δ : Ren V)
    (hinj : ∀ u ∈ p.fv ∪ c.fv ∪ q.fv, ∀ w ∈ p.fv ∪ c.fv ∪ q.fv,
      δ u = δ w → u = w)
    (h : ［p］c［q］) : ［p /ₛ δ.toSubst］(c /ᶜ δ)［q /ₛ δ.toSubst］ := by
  intro σ' hp
  have hpσ := (substitution_assert p δ.toSubst (fun w ↦ σ' (δ w)) σ'
    (fun _ _ ↦ rfl)).mp hp
  obtain ⟨τ, hc, hq⟩ := h _ hpσ
  have hag := Comm.substitution_general c δ (p.fv ∪ c.fv ∪ q.fv)
    (fun _ hw ↦ Finset.mem_union_left _ (Finset.mem_union_right _ hw)) hinj
    (fun w ↦ σ' (δ w)) σ' (fun _ _ ↦ rfl)
  rw [hc] at hag
  cases he : (c /ᶜ δ).eval σ' with
  | none => simp [he, AgreeVia] at hag
  | some τ' =>
      rw [he, AgreeVia.some_some] at hag
      exact ⟨τ', rfl, (substitution_assert q δ.toSubst τ τ'
        (fun w hw ↦ hag w (Finset.mem_union_right _ hw))).mpr hq⟩
-- ANCHOR_END: ex311

-- ANCHOR: ex311Counterexample
/-- 연습 3.11 반례의 이름 바꾸기. `x`, `y`를 같은 저장 공간 `y`로 보낸다. -/
def mergeXY : Ren String := fun w ↦ if w = "x" then "y" else w

/-- 연습 3.11의 단사 조건을 뺄 수 없다. `x := 1`은 `y = 0`을 보존하지만,
`x ↦ y`로 치환한 `y := 1`은 그 명세를 만족하지 않는다. -/
theorem ex_3_11_counterexample :
    ［⟪ y = 0 ⟫ₐ］⟪ x := 1 ⟫ᶜ［⟪ y = 0 ⟫ₐ］ ∧
    ¬ ［(⟪ y = 0 ⟫ₐ) /ₛ mergeXY.toSubst］(⟪ x := 1 ⟫ᶜ /ᶜ mergeXY)
      ［(⟪ y = 0 ⟫ₐ) /ₛ mergeXY.toSubst］ := by
  constructor
  · intro σ hp
    refine ⟨_, rfl, ?_⟩
    simpa [Assert.eval, IntExp.eval, State.subst_def, Function.update] using hp
  · intro h
    obtain ⟨τ, he, hq⟩ := h (fun _ ↦ 0) (by
      simp [Assert.subst, IntExp.subst, Ren.toSubst, mergeXY, Assert.eval, IntExp.eval,
        Cmp.denote])
    cases he
    simp [Assert.subst, IntExp.subst, Ren.toSubst, mergeXY, Assert.eval, IntExp.eval,
      State.subst_def, Function.update, Cmp.denote] at hq
-- ANCHOR_END: ex311Counterexample

end Reynolds.Answers.Ch03
