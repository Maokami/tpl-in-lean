/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Exercises.Ch03.Hoare

/-!
# §3.2–§3.5 건전성 — 규칙마다 1·2장의 정리 하나

`Hoare.lean` 의 규칙이 뜻(`Spec.lean`)에 대해 옳다는 것을 증명한다. 유도된 명세는 타당하다.

## 규칙마다 독립이다

AS·SQ·CD·SP·WC·CA·DA·CSP·CST·WHP·DC·RN은 `Semantic.lean`에서 각각 독립된 의미 판 연습으로 증명한다.
이 파일의 구문 판은 그 결과를 구문 단언에 적용한다. 기존 합성형 선언 API도 제공한다.
각 규칙이 앞 장의 어느 정리를 쓰는지는 다음과 같다.

- 대입 공리 — 명제 1.4 (`substitution_single`). **1장 §1.4 의 치환 정리가 이 한 줄을
  위해 있었다.**
- 순차 합성 — `Flat.bind`.
- 조건 — §2.2 의 `boolExp_eval_iff`.
- `while` — §2.4 의 **Scott 귀납법**. 허용 가능성은 §3.1 의 `Sat.admissible` 이다.
- DC — 복원과 사후조건의 지역성. 구문 판의 지역성은 명제 1.1에서 얻는다.
- RN — §2.5 `Comm.newvar_rename`의 명령 의미 등식.
- 결과 규칙 — §3.1 의 `PartialCorrect.conseq`.

`Hoare.sound` 자체는 `Hoare` 에 대한 구조적 귀납으로 위의 것들을 잇기만 한다.

## 읽는 순서
`Hoare.lean` → 이 파일 → `Assign.lean`.
-/

@[expose] public section

namespace Reynolds.Exercises.Ch03

open Reynolds Reynolds.Answers.Ch01 Reynolds.Answers.Ch02

universe u

variable {V : Type u} [DecidableEq V]

/-! ## 1. 규칙마다 건전성 -/

/-- `skip` 은 상태를 그대로 낸다. -/
theorem skip_sound (p : Assert V) : ｛p｝Comm.skip｛p｝ := by
  intro σ hp τ hτ
  change Flat.some σ = Flat.some τ at hτ
  obtain rfl := Flat.some.inj hτ
  exact hp

/--
**대입 공리의 건전성 — 명제 1.4 한 줄.**

대입 뒤의 상태는 `σ[v := ⟦e⟧ σ]` 이고, 거기서 `q` 가 참이라는 것은 `σ` 에서 `q/v→e` 가
참이라는 것과 같다. 그것이 `substitution_single` 이다.
-/
theorem assign_sound [HasFresh V] (q : Assert V) (v : V) (e : IntExp V) :
    ｛q /[v := e]｝(Comm.assign v e)｛q｝ := by
  intro σ hp
  exact (as_sound ⟦q⟧ₐ v e).1 σ ((substitution_single q v e σ).mp hp)


/-- **순차 합성의 건전성.** `c₀` 가 끝나면 `r`, 거기서 `c₁` 이 끝나면 `q`. 어느 쪽이든
발산하면 공허하다. -/
theorem seq_sound {p r q : Assert V} {c₀ c₁ : Comm V}
    (h₀ : ｛p｝c₀｛r｝) (h₁ : ｛r｝c₁｛q｝) : ｛p｝(Comm.seq c₀ c₁)｛q｝ := sq_sound.1 h₀ h₁


/-- **조건 규칙의 건전성.** 어느 가지로 갔는지가 곧 조건의 참·거짓이고, 그것을 단언으로
옮기는 것이 §2.2 의 `boolExp_eval_iff` 다. -/
theorem ite_sound {p q : Assert V} {b : BoolExp V} {c₀ c₁ : Comm V}
    (h₀ : ｛p ⋀ b.toAssert｝c₀｛q｝) (h₁ : ｛p ⋀ .not b.toAssert｝c₁｛q｝) :
    ｛p｝(Comm.ite b c₀ c₁)｛q｝ := by
  refine (cd_sound (P := ⟦p⟧ₐ) (Q := ⟦q⟧ₐ) (b := b) (c₀ := c₀) (c₁ := c₁)).1 ?_ ?_
  · intro σ hp
    exact h₀ σ ((Assert.eval_and _ _ _).mpr ⟨hp.1, (boolExp_eval_iff b σ).mpr hp.2⟩)
  · intro σ hp
    exact h₁ σ ((Assert.eval_and _ _ _).mpr
      ⟨hp.1, (Assert.eval_not _ _).mpr fun h => by
        have := (boolExp_eval_iff b σ).mp h
        simp [hp.2] at this⟩)


/--
**`while` 규칙의 건전성.** 의미 판 WHP를 구문 단언으로 옮긴다.

`PartialCorrectS.wh`가 Scott 귀납법으로 반복의 부분 정확성을 준다.
여기서는 `boolExp_eval_iff`로 본체의 전제와 반복의 사후조건을 구문 단언에 맞춘다.
-/
theorem wh_sound {i : Assert V} {b : BoolExp V} {c : Comm V}
    (hbody : ｛i ⋀ b.toAssert｝c｛i｝) : ｛i｝(Comm.wh b c)｛i ⋀ .not b.toAssert｝ := by
  have hsem : PartialCorrectS (fun σ => ⟦i⟧ₐ σ ∧ ⟦b⟧ᵇ σ = true) c ⟦i⟧ₐ := by
    intro σ hp
    exact hbody σ ((Assert.eval_and _ _ _).mpr ⟨hp.1, (boolExp_eval_iff b σ).mpr hp.2⟩)
  intro σ hi τ hτ
  obtain ⟨hiτ, hb⟩ := PartialCorrectS.wh hsem σ hi τ hτ
  exact (Assert.eval_and _ _ _).mpr
    ⟨hiτ, (Assert.eval_not _ _).mpr fun h => by
      have := (boolExp_eval_iff b τ).mp h
      simp [hb] at this⟩


/-- 기존 합성형 변수 선언 규칙의 건전성. 초기 단언을 AS·SQ로 만든 뒤 DC를 적용한다.
`p`와 `e`의 신선함은 이 제공 규칙의 조건이며, DC 자체는 `q`의 신선함만 요구한다. -/
theorem newvar_sound {p q : Assert V} {v : V} {e : IntExp V} {c : Comm V}
    (hp : v ∉ p.fv) (hq : v ∉ q.fv) (he : v ∉ e.fv)
    (h : ｛p ⋀ .cmp .eq (.var v) e｝c｛q｝) : ｛p｝(Comm.newvar v e c)｛q｝ := by
  apply (dc_sound [] p.eval q.eval v e c (Assert.eval_update_of_notMem hq)).1
  have hs := sq_sound.1 (as_sound (p ⋀ .cmp .eq (.var v) e).eval v e).1 h
  intro σ hpσ
  exact hs σ (newvar_init hp he σ hpσ)


/-! ## 2. 건전성 -/

/--
**건전성.** 유도된 명세는 타당하다.

`Hoare` 에 대한 구조적 귀납이고 절마다 위의 정리 하나다. 채점 연습이 아니다 — 각 절이
이미 연습이라 비우면 비운 것끼리 의존한다 (연습 독립성 원칙, `AGENTS.md` §1-9).
-/
theorem Hoare.sound [HasFresh V] {p q : Assert V} {c : Comm V} :
    Hoare p c q → ｛p｝c｛q｝ := by
  intro h
  induction h with
  | «skip» p => exact skip_sound p
  | assign q v e => exact assign_sound q v e
  | seq _ _ ih₀ ih₁ => exact seq_sound ih₀ ih₁
  | ite _ _ ih₀ ih₁ => exact ite_sound ih₀ ih₁
  | wh _ ih => exact wh_sound ih
  | dc s hq _ ih =>
    exact (dc_sound s _ _ _ _ _ (Assert.eval_update_of_notMem hq)).1 ih
  | rename hr _ ih => exact (rn_sound _ _ hr).1 ih
  | strengthen hp _ ih => exact (sp_sound hp).1 ih
  | weaken _ hq ih => exact (wc_sound hq).1 ih
  | conj _ _ ih₀ ih₁ => exact ca_sound.1 ih₀ ih₁
  | disj _ _ ih₀ ih₁ => exact da_sound.1 ih₀ ih₁
  | constancy hp => exact csp_sound hp

/-- `Hoare.lean` 의 두 유도가 이제 타당한 명세가 된다. §2.5 의 `swap_ok` 를 계산 없이 다시
얻은 셈이다. -/
example : ｛⟪ x = a ∧ y = b ⟫ₐ｝⟪ t := x; x := y; y := t ⟫ᶜ｛⟪ y = a ∧ x = b ⟫ₐ｝ :=
  swap_hoare.sound

/-! ## 3. 여기서 어디로 가나

건전성의 반대쪽 — 타당한 명세는 모두 유도되는가 — 는 (보충) `Wlp.lean` 의 최약 사전조건으로
답한다.
그 전에 `Assign.lean` 이 대입 공리의 방향을 따진다. -/

end Reynolds.Exercises.Ch03
