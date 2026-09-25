/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Answers.Ch03.Hoare

/-!
# §3.2~3.6 건전성 — 규칙마다 1·2장의 정리 하나

`Hoare.lean` 의 규칙이 뜻(`Spec.lean`)에 대해 옳다는 것을 증명한다. 유도된 명세는 타당하다.

## 규칙마다 독립이다

한 규칙의 건전성이 다른 규칙의 건전성에 기대지 않는다. 그래서 절마다 따로 정리로 두고
연습으로 낸다. 각각이 앞 장의 어느 정리 위에 서는지가 정해져 있다.

- 대입 공리 — 명제 1.4 (`substitution_single`). **1장 §1.4 의 치환 정리가 이 한 줄을
  위해 있었다.**
- 순차 합성 — `Option.bind`.
- 조건 — §2.2 의 `boolExp_eval_iff`.
- `while` — §2.4 의 **Scott 귀납법**. 허용 가능성은 §3.1 의 `Sat.admissible` 이다.
- 변수 선언 — 명제 1.1 (`coincidence_assert`) 세 번.
- 결과 규칙 — §3.1 의 `PartialCorrect.conseq`.

`Hoare.sound` 자체는 `Hoare` 에 대한 구조적 귀납으로 위의 것들을 잇기만 한다.

## 읽는 순서
`Hoare.lean` → 이 파일 → `Assign.lean`.
-/

@[expose] public section

namespace Reynolds.Answers.Ch03

open Reynolds Reynolds.Answers.Ch01 Reynolds.Answers.Ch02

universe u

variable {V : Type u} [DecidableEq V]

/-! ## 1. 규칙마다 건전성 -/

/-- `skip` 은 상태를 그대로 낸다. -/
theorem skip_sound (p : Assert V) : ｛p｝Comm.skip｛p｝ := by
  intro σ hp τ hτ
  change some σ = some τ at hτ
  obtain rfl := Option.some.inj hτ
  exact hp

-- ANCHOR: assignSound
/--
**대입 공리의 건전성 — 명제 1.4 한 줄.**

대입 뒤의 상태는 `σ[v := ⟦e⟧ σ]` 이고, 거기서 `q` 가 참이라는 것은 `σ` 에서 `q/v→e` 가
참이라는 것과 같다. 그것이 `substitution_single` 이다.
-/
@[exercise "§3.3 assign-sound" 1]
theorem assign_sound [HasFresh V] (q : Assert V) (v : V) (e : IntExp V) :
    ｛q /[v := e]｝(Comm.assign v e)｛q｝ := by
  intro σ hp τ hτ
  change some (σ[v := ⟦e⟧ₑ σ]) = some τ at hτ
  obtain rfl := Option.some.inj hτ
  exact (substitution_single q v e σ).mp hp
-- ANCHOR_END: assignSound

-- ANCHOR: seqSound
/-- **순차 합성의 건전성.** `c₀` 가 끝나면 `r`, 거기서 `c₁` 이 끝나면 `q`. 어느 쪽이든
발산하면 공허하다. -/
@[exercise "§3.3 seq-sound" 1]
theorem seq_sound {p r q : Assert V} {c₀ c₁ : Comm V}
    (h₀ : ｛p｝c₀｛r｝) (h₁ : ｛r｝c₁｛q｝) : ｛p｝(Comm.seq c₀ c₁)｛q｝ := by
  intro σ hp τ hτ
  change Option.bind (⟦c₀⟧ᶜ σ) ⟦c₁⟧ᶜ = some τ at hτ
  rcases h : ⟦c₀⟧ᶜ σ with _ | ρ
  · rw [h] at hτ; simp at hτ
  · rw [h] at hτ
    change ⟦c₁⟧ᶜ ρ = some τ at hτ
    exact h₁ ρ (h₀ σ hp ρ h) τ hτ
-- ANCHOR_END: seqSound

-- ANCHOR: iteSound
/-- **조건 규칙의 건전성.** 어느 가지로 갔는지가 곧 조건의 참·거짓이고, 그것을 단언으로
옮기는 것이 §2.2 의 `boolExp_eval_iff` 다. -/
@[exercise "§3.5 ite-sound" 1]
theorem ite_sound {p q : Assert V} {b : BoolExp V} {c₀ c₁ : Comm V}
    (h₀ : ｛p ⋀ b.toAssert｝c₀｛q｝) (h₁ : ｛p ⋀ .not b.toAssert｝c₁｛q｝) :
    ｛p｝(Comm.ite b c₀ c₁)｛q｝ := by
  intro σ hp τ hτ
  change (if ⟦b⟧ᵇ σ then ⟦c₀⟧ᶜ σ else ⟦c₁⟧ᶜ σ) = some τ at hτ
  by_cases hb : ⟦b⟧ᵇ σ = true
  · rw [if_pos hb] at hτ
    exact h₀ σ ((Assert.eval_and _ _ _).mpr ⟨hp, (boolExp_eval_iff b σ).mpr hb⟩) τ hτ
  · rw [if_neg hb] at hτ
    exact h₁ σ ((Assert.eval_and _ _ _).mpr
      ⟨hp, (Assert.eval_not _ _).mpr fun h => hb ((boolExp_eval_iff b σ).mp h)⟩) τ hτ
-- ANCHOR_END: iteSound

-- ANCHOR: whSound
/--
**`while` 규칙의 건전성 — Scott 귀납법.**

`⟦while b do c⟧` 는 `whileF b ⟦c⟧` 의 최소 고정점이다. 그 고정점이 "`i` 에서 출발해 끝나면
`i ∧ ¬b`" 를 만족한다는 것을 §2.4 의 `scott_induction` 으로 얻는다. 세 의무가 §3.1 에서
말한 것과 맞물린다.

- 허용 가능 — `Sat.admissible`. `⊥` 가 모든 사후조건을 만족한다는 것의 사슬 판.
- `⊥` — `Sat.bot`. 끝나지 않으므로 공허.
- 한 바퀴 — 조건이 참이면 본체가 `i` 를 지키고(전제) 나머지에 넘긴다(가설). 거짓이면 그
  자리에서 `i ∧ ¬b` 다.

명제 2.6, 명제 2.7 에 이어 Scott 귀납법을 세 번째 쓰는 자리다. 이번에는 성질이 두 상태의
관계가 아니라 한 상태의 술어라 더 단순하다.
-/
@[exercise "§3.5 wh-sound" 3]
theorem wh_sound {i : Assert V} {b : BoolExp V} {c : Comm V}
    (hbody : ｛i ⋀ b.toAssert｝c｛i｝) : ｛i｝(Comm.wh b c)｛i ⋀ .not b.toAssert｝ := by
  change Sat ⟦i⟧ₐ (fix (whileF b ⟦c⟧ᶜ) (whileF_monotone b ⟦c⟧ᶜ)) ⟦i ⋀ .not b.toAssert⟧ₐ
  refine scott_induction (whileF_monotone b ⟦c⟧ᶜ)
    (P := fun w => Sat ⟦i⟧ₐ w ⟦i ⋀ .not b.toAssert⟧ₐ) ?_ ?_ ?_
  · exact fun d hd => Sat.admissible _ _ d hd
  · exact Sat.bot _ _
  · intro w hw σ hi τ hτ
    change (if ⟦b⟧ᵇ σ then Option.bind (⟦c⟧ᶜ σ) w else some σ) = some τ at hτ
    by_cases hb : ⟦b⟧ᵇ σ = true
    · rw [if_pos hb] at hτ
      rcases hc : ⟦c⟧ᶜ σ with _ | ρ
      · rw [hc] at hτ; simp at hτ
      · rw [hc] at hτ
        change w ρ = some τ at hτ
        exact hw ρ (hbody σ ((Assert.eval_and _ _ _).mpr
          ⟨hi, (boolExp_eval_iff b σ).mpr hb⟩) ρ hc) τ hτ
    · rw [if_neg hb] at hτ
      obtain rfl := Option.some.inj hτ
      exact (Assert.eval_and _ _ _).mpr
        ⟨hi, (Assert.eval_not _ _).mpr fun h => hb ((boolExp_eval_iff b σ).mp h)⟩
-- ANCHOR_END: whSound

-- ANCHOR: newvarSound
/--
**변수 선언 규칙의 건전성 — 명제 1.1 세 번.**

`⟦newvar v := e in c⟧ σ = restore v σ (⟦c⟧ (σ[v := ⟦e⟧ σ]))` 다. 세 신선함 조건이 각각
다른 자리에서 쓰인다.

- `v ∉ FV(p)` — `v` 를 갱신해도 `p` 가 그대로 참이다.
- `v ∉ FV(e)` — `v` 를 갱신해도 `e` 의 값이 그대로라 안쪽에서 `v = e` 가 참이다.
- `v ∉ FV(q)` — `v` 를 복원해도 `q` 가 그대로 참이다.
-/
@[exercise "§3.6 newvar-sound" 2]
theorem newvar_sound {p q : Assert V} {v : V} {e : IntExp V} {c : Comm V}
    (hp : v ∉ p.fv) (hq : v ∉ q.fv) (he : v ∉ e.fv)
    (h : ｛p ⋀ .cmp .eq (.var v) e｝c｛q｝) : ｛p｝(Comm.newvar v e c)｛q｝ := by
  intro σ hpσ τ hτ
  change restore v σ (⟦c⟧ᶜ (σ[v := ⟦e⟧ₑ σ])) = some τ at hτ
  rcases hc : ⟦c⟧ᶜ (σ[v := ⟦e⟧ₑ σ]) with _ | ρ
  · rw [hc] at hτ; simp [restore] at hτ
  · rw [hc] at hτ
    simp only [restore, Option.map_some, Option.some.injEq] at hτ
    subst hτ
    -- 안쪽 사전조건. `p` 는 `v` 를 안 보고, `v = e` 는 갱신으로 참이다.
    have hp' : ⟦p⟧ₐ (σ[v := ⟦e⟧ₑ σ]) :=
      (coincidence_assert p σ _ fun w hw =>
        (State.subst_of_ne σ v w _ fun (hwv : w = v) => hp (hwv ▸ hw)).symm).mp hpσ
    have hv : ⟦Assert.cmp .eq (.var v) e⟧ₐ (σ[v := ⟦e⟧ₑ σ]) := by
      change (σ[v := ⟦e⟧ₑ σ]) v = ⟦e⟧ₑ (σ[v := ⟦e⟧ₑ σ])
      rw [State.subst_self]
      exact coincidence_intExp e σ _ fun w hw =>
        (State.subst_of_ne σ v w _ fun (hwv : w = v) => he (hwv ▸ hw)).symm
    -- 안쪽 결과에서 `q` 가 참이고, `v` 를 복원해도 `q` 는 `v` 를 안 보므로 그대로다.
    have hq' := h _ ((Assert.eval_and _ _ _).mpr ⟨hp', hv⟩) ρ hc
    exact (coincidence_assert q ρ (ρ[v := σ v]) fun w hw =>
      (State.subst_of_ne ρ v w _ fun (hwv : w = v) => hq (hwv ▸ hw)).symm).mp hq'
-- ANCHOR_END: newvarSound

/-! ## 2. 건전성 -/

-- ANCHOR: sound
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
  | «newvar» hp hq he _ ih => exact newvar_sound hp hq he ih
  | conseq hp _ hq ih => exact PartialCorrect.conseq hp ih hq
-- ANCHOR_END: sound

/-- `Hoare.lean` 의 두 유도가 이제 타당한 명세가 된다. §2.5 의 `swap_ok` 를 계산 없이 다시
얻은 셈이다. -/
example : ｛⟪ x = a ∧ y = b ⟫ₐ｝⟪ t := x; x := y; y := t ⟫ᶜ｛⟪ y = a ∧ x = b ⟫ₐ｝ :=
  swap_hoare.sound

/-! ## 3. 여기서 어디로 가나

건전성의 반대쪽 — 타당한 명세는 모두 유도되는가 — 는 §3.10 의 최약 사전조건으로 답한다.
그 전에 `Assign.lean` 이 대입 공리의 방향을 따진다. -/

end Reynolds.Answers.Ch03
