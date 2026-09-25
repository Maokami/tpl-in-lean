/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Exercises.Ch03.Hoare

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

namespace Reynolds.Exercises.Ch03

open Reynolds Reynolds.Exercises.Ch01 Reynolds.Exercises.Ch02

universe u

variable {V : Type u} [DecidableEq V]

/-! ## 1. 규칙마다 건전성 -/

/-- `skip` 은 상태를 그대로 낸다. -/
theorem skip_sound (p : Assert V) : ｛p｝Comm.skip｛p｝ := by
  intro σ hp τ hτ
  change some σ = some τ at hτ
  obtain rfl := Option.some.inj hτ
  exact hp

/--
**대입 공리의 건전성 — 명제 1.4 한 줄.**

대입 뒤의 상태는 `σ[v := ⟦e⟧ σ]` 이고, 거기서 `q` 가 참이라는 것은 `σ` 에서 `q/v→e` 가
참이라는 것과 같다. 그것이 `substitution_single` 이다.
-/
@[exercise "§3.3 assign-sound" 1]
theorem assign_sound [HasFresh V] (q : Assert V) (v : V) (e : IntExp V) :
    ｛q /[v := e]｝(Comm.assign v e)｛q｝ := by
  -- 먼저 볼 것: §1.4 의 `substitution_single` (명제 1.4). 이 정리가 전부다.
  -- 힌트 1: `intro σ hp τ hτ` 뒤 `hτ` 는 정의상 `some (σ[v := ⟦e⟧ₑ σ]) = some τ` 다.
  --         `change` 로 드러내고 `Option.some.inj` 로 `τ` 를 없앤다.
  -- 힌트 2: 남는 목표가 `⟦q⟧ₐ (σ[v := ⟦e⟧ₑ σ])` 이고 가정이 `⟦q /[v := e]⟧ₐ σ` 다.
  sorry


/-- **순차 합성의 건전성.** `c₀` 가 끝나면 `r`, 거기서 `c₁` 이 끝나면 `q`. 어느 쪽이든
발산하면 공허하다. -/
@[exercise "§3.3 seq-sound" 1]
theorem seq_sound {p r q : Assert V} {c₀ c₁ : Comm V}
    (h₀ : ｛p｝c₀｛r｝) (h₁ : ｛r｝c₁｛q｝) : ｛p｝(Comm.seq c₀ c₁)｛q｝ := by
  -- 힌트 1: `⟦c₀ ; c₁⟧ᶜ σ` 는 정의상 `Option.bind (⟦c₀⟧ᶜ σ) ⟦c₁⟧ᶜ` 다 (`change … at hτ`).
  -- 힌트 2: `rcases h : ⟦c₀⟧ᶜ σ with _ | ρ` 로 나눈다. `none` 이면 `hτ` 가 모순이고,
  --         `some ρ` 면 `h₀` 가 `⟦r⟧ₐ ρ` 를, `h₁` 이 `⟦q⟧ₐ τ` 를 준다.
  sorry


/-- **조건 규칙의 건전성.** 어느 가지로 갔는지가 곧 조건의 참·거짓이고, 그것을 단언으로
옮기는 것이 §2.2 의 `boolExp_eval_iff` 다. -/
@[exercise "§3.5 ite-sound" 1]
theorem ite_sound {p q : Assert V} {b : BoolExp V} {c₀ c₁ : Comm V}
    (h₀ : ｛p ⋀ b.toAssert｝c₀｛q｝) (h₁ : ｛p ⋀ .not b.toAssert｝c₁｛q｝) :
    ｛p｝(Comm.ite b c₀ c₁)｛q｝ := by
  -- 먼저 볼 것: §2.2 의 `boolExp_eval_iff`, 이 파일 위의 `Assert.eval_and` · `Assert.eval_not`.
  -- 힌트 1: `⟦if b then c₀ else c₁⟧ᶜ σ` 는 정의상 `if ⟦b⟧ᵇ σ then … else …` 다.
  -- 힌트 2: `by_cases hb : ⟦b⟧ᵇ σ = true` 로 나누고 `if_pos` / `if_neg` 로 가지를 고른다.
  -- 힌트 3: 각 가지의 사전조건 `p ⋀ …` 은 `hp` 와 `hb` 를 `boolExp_eval_iff` 로 합친 것이다.
  sorry


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
  -- 먼저 볼 것: §2.4 의 `scott_induction`, §3.1 의 `Sat.admissible` · `Sat.bot`,
  --            그리고 §2.5 의 `Comm.coincidence_general` — 같은 수법이다.
  -- 힌트 1: `⟦while b do c⟧ᶜ` 는 정의상 `fix (whileF b ⟦c⟧ᶜ) (whileF_monotone b ⟦c⟧ᶜ)` 다.
  --         목표를 `Sat ⟦i⟧ₐ (fix …) ⟦i ⋀ .not b.toAssert⟧ₐ` 로 `change` 한다.
  -- 힌트 2: `scott_induction (whileF_monotone b ⟦c⟧ᶜ) (P := fun w => Sat ⟦i⟧ₐ w ⟦…⟧ₐ)` 에
  --         세 의무를 준다 — 허용 가능(`Sat.admissible`), `⊥`(`Sat.bot`), 한 바퀴.
  -- 힌트 3: 한 바퀴에서 `whileF b ⟦c⟧ᶜ w σ` 를 `change` 로 펼치고, `⟦b⟧ᵇ σ = true` 로 나눈 뒤
  --         참이면 `rcases hc : ⟦c⟧ᶜ σ` — 본체가 끝난 상태에서 `hbody` 와 귀납 가설 `hw` 를 잇는다.
  sorry


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
  -- 먼저 볼 것: §1.4 의 `coincidence_assert` · `coincidence_intExp` (명제 1.1),
  --            `State.subst_self` · `State.subst_of_ne`.
  -- 힌트 1: `⟦newvar v := e in c⟧ᶜ σ` 는 정의상 `restore v σ (⟦c⟧ᶜ (σ[v := ⟦e⟧ₑ σ]))` 다.
  --         `rcases hc : ⟦c⟧ᶜ (σ[v := ⟦e⟧ₑ σ])` 로 나누고, `some ρ` 면
  --         `simp only [restore, Option.map_some, Option.some.injEq] at hτ` 로 `τ = ρ[v := σ v]`.
  -- 힌트 2: 안쪽 사전조건 두 조각 — `p` 는 `v` 를 안 보니 갱신해도 참(`hp`), `v = e` 는
  --         `State.subst_self` 와 `e` 가 `v` 를 안 본다는 것(`he`)으로.
  -- 힌트 3: 안쪽 결과 `⟦q⟧ₐ ρ` 에서 `v` 를 복원해도 `q` 는 `v` 를 안 본다(`hq`).
  sorry


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
  | «newvar» hp hq he _ ih => exact newvar_sound hp hq he ih
  | conseq hp _ hq ih => exact PartialCorrect.conseq hp ih hq

/-- `Hoare.lean` 의 두 유도가 이제 타당한 명세가 된다. §2.5 의 `swap_ok` 를 계산 없이 다시
얻은 셈이다. -/
example : ｛⟪ x = a ∧ y = b ⟫ₐ｝⟪ t := x; x := y; y := t ⟫ᶜ｛⟪ y = a ∧ x = b ⟫ₐ｝ :=
  swap_hoare.sound

/-! ## 3. 여기서 어디로 가나

건전성의 반대쪽 — 타당한 명세는 모두 유도되는가 — 는 §3.10 의 최약 사전조건으로 답한다.
그 전에 `Assign.lean` 이 대입 공리의 방향을 따진다. -/

end Reynolds.Exercises.Ch03
