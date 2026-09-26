/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Exercises.Ch03.Annot

/-!
# §3.5 전체 정확성의 `while` 규칙 — 변항

부분 정확성의 `while` 규칙은 끝나면 무엇이 참인지만 말한다. 끝난다는 것까지 말하려면
한 바퀴마다 **줄어드는 양**이 있어야 한다.

```
[ i ∧ b ∧ e = z ] c [ i ∧ e < z ]       i ∧ b ⇒ 0 ≤ e
-------------------------------------------------------   z ∉ FV(i) ∪ FV(b) ∪ FV(c) ∪ FV(e)
              [ i ] while b do c [ i ∧ ¬b ]
```

`e` 가 **변항**(variant)이다. 한 바퀴마다 줄고 0 아래로 못 내려가므로 무한히 돌 수 없다.
`z` 는 한 바퀴 시작 때의 `e` 값을 붙들어 두는 신선한 변수다 — "줄었다" 를 말하려면 전과
후를 비교해야 하고, 그러려면 전의 값을 어딘가에 기억해야 한다. **유령 변수**(§3.10)의 첫
등장이다. `z ∉ FV(c)` 가 필요한 이유는 명제 2.6(b) 다 — 본체가 `z` 를 안 건드려야 "전의 값"
이 살아남는다.

## 건전성은 Scott 귀납법이 아니라 정초 귀납이다

§3.1 에서 말했듯 "끝난다" 는 극한으로 올라가지 않는다 — 사슬의 모든 항이 발산해도 극한은
발산한다. 그러니 `while` 이 끝난다는 증명은 단계를 세는 측도 위의 귀납이어야 하고, 그
측도가 변항이다. 2장에서 구체적인 루프의 값을 계산할 때 쓴 수법(§2.6 `forWhile_eq_fold`,
§2.8 `countLoop_eval`, 연습 2.3·2.5)이 정확히 이것이다 — 그때는 측도를 손으로 잡았고, 이제는
규칙이 측도를 인자로 받는다.

## 나머지 규칙은 종료를 그대로 물려준다

전체 정확성 체계 `HoareT` 는 `Hoare` 와 `wh` 규칙만 다르다. 나머지 규칙의 건전성은 부분 판과
같은 논증에 "끝난다" 를 얹은 것이다.

## 읽는 순서
`Annot.lean` → 이 파일.
-/

@[expose] public section

namespace Reynolds.Exercises.Ch03

open Reynolds Reynolds.Answers.Ch01 Reynolds.Answers.Ch02

universe u

variable {V : Type u} [DecidableEq V]

/-! ## 1. 준비 — 불 식을 단언으로 읽어도 자유 변수는 같다 -/

/-- `b.toAssert` 의 자유 변수는 `b` 의 자유 변수다. 절이 그대로 옮겨지므로. -/
theorem BoolExp.fv_toAssert (b : BoolExp V) : b.toAssert.fv = b.fv := by
  induction b with
  | tru | fls => rfl
  | cmp c e₀ e₁ => rfl
  | not b ih => simp [BoolExp.toAssert, Assert.fv, BoolExp.fv, ih]
  | bin op b₀ b₁ ih₀ ih₁ => simp [BoolExp.toAssert, Assert.fv, BoolExp.fv, ih₀, ih₁]

/-! ## 2. 규칙 -/

/-- 전체 정확성의 추론 체계. `wh` 만 `Hoare` 와 다르다. -/
inductive HoareT [HasFresh V] : Assert V → Comm V → Assert V → Prop where
  | skip (p : Assert V) : HoareT p .skip p
  | assign (q : Assert V) (v : V) (e : IntExp V) :
      HoareT (q /[v := e]) (.assign v e) q
  | seq {p r q : Assert V} {c₀ c₁ : Comm V} :
      HoareT p c₀ r → HoareT r c₁ q → HoareT p (.seq c₀ c₁) q
  | ite {p q : Assert V} {b : BoolExp V} {c₀ c₁ : Comm V} :
      HoareT (p ⋀ b.toAssert) c₀ q → HoareT (p ⋀ .not b.toAssert) c₁ q →
      HoareT p (.ite b c₀ c₁) q
  /-- 반복. `i` 가 불변식, `e` 가 변항, `z` 가 한 바퀴 시작의 `e` 값을 붙드는 유령 변수. -/
  | wh {i : Assert V} {b : BoolExp V} {c : Comm V} {e : IntExp V} {z : V}
      (hzi : z ∉ i.fv) (hzb : z ∉ b.fv) (hzc : z ∉ c.fv) (hze : z ∉ e.fv)
      (hnonneg : Stronger (i ⋀ b.toAssert) (.cmp .le (.num 0) e)) :
      HoareT (i ⋀ b.toAssert ⋀ .cmp .eq e (.var z)) c (i ⋀ .cmp .lt e (.var z)) →
      HoareT i (.wh b c) (i ⋀ .not b.toAssert)
  | newvar {p q : Assert V} {v : V} {e : IntExp V} {c : Comm V}
      (hp : v ∉ p.fv) (hq : v ∉ q.fv) (he : v ∉ e.fv) :
      HoareT (p ⋀ .cmp .eq (.var v) e) c q → HoareT p (.newvar v e c) q
  | conseq {p p' q q' : Assert V} {c : Comm V} :
      Stronger p' p → HoareT p c q → Stronger q q' → HoareT p' c q'

/-- 전제 강화. -/
theorem HoareT.strengthen [HasFresh V] {p p' q : Assert V} {c : Comm V}
    (hp : Stronger p' p) (h : HoareT p c q) : HoareT p' c q :=
  HoareT.conseq hp h (Stronger.refl q)

/-- 결론 약화. -/
theorem HoareT.weaken [HasFresh V] {p q q' : Assert V} {c : Comm V}
    (h : HoareT p c q) (hq : Stronger q q') : HoareT p c q' :=
  HoareT.conseq (Stronger.refl p) h hq

/-! ## 3. 규칙마다 건전성 — 종료를 얹는다 -/

theorem skipT_sound (p : Assert V) : ［p］Comm.skip［p］ :=
  fun σ hp => ⟨σ, rfl, hp⟩

theorem assignT_sound [HasFresh V] (q : Assert V) (v : V) (e : IntExp V) :
    ［q /[v := e]］(Comm.assign v e)［q］ :=
  fun σ hp => ⟨_, rfl, (substitution_single q v e σ).mp hp⟩

theorem seqT_sound {p r q : Assert V} {c₀ c₁ : Comm V}
    (h₀ : ［p］c₀［r］) (h₁ : ［r］c₁［q］) : ［p］(Comm.seq c₀ c₁)［q］ := by
  intro σ hp
  obtain ⟨ρ, hρ, hr⟩ := h₀ σ hp
  obtain ⟨τ, hτ, hq⟩ := h₁ ρ hr
  refine ⟨τ, ?_, hq⟩
  change Option.bind (⟦c₀⟧ᶜ σ) ⟦c₁⟧ᶜ = some τ
  rw [hρ]
  exact hτ

theorem iteT_sound {p q : Assert V} {b : BoolExp V} {c₀ c₁ : Comm V}
    (h₀ : ［p ⋀ b.toAssert］c₀［q］) (h₁ : ［p ⋀ .not b.toAssert］c₁［q］) :
    ［p］(Comm.ite b c₀ c₁)［q］ := by
  intro σ hp
  by_cases hb : ⟦b⟧ᵇ σ = true
  · obtain ⟨τ, hτ, hq⟩ := h₀ σ ((Assert.eval_and _ _ _).mpr ⟨hp, (boolExp_eval_iff b σ).mpr hb⟩)
    refine ⟨τ, ?_, hq⟩
    change (if ⟦b⟧ᵇ σ then ⟦c₀⟧ᶜ σ else ⟦c₁⟧ᶜ σ) = some τ
    rw [if_pos hb]; exact hτ
  · obtain ⟨τ, hτ, hq⟩ := h₁ σ ((Assert.eval_and _ _ _).mpr
      ⟨hp, (Assert.eval_not _ _).mpr fun h => hb ((boolExp_eval_iff b σ).mp h)⟩)
    refine ⟨τ, ?_, hq⟩
    change (if ⟦b⟧ᵇ σ then ⟦c₀⟧ᶜ σ else ⟦c₁⟧ᶜ σ) = some τ
    rw [if_neg hb]; exact hτ

/--
**전체 정확성 `while` 규칙의 건전성 — 정초 귀납.**

측도는 `n` 으로, "`⟦e⟧ σ < n` 인 모든 `σ` 에서 루프가 끝난다" 를 `n` 에 대한 귀납으로 보인다.

- `n = 0` — 조건이 참이면 `0 ≤ e` 인데 `e < 0` 이라 모순. 거짓이면 그 자리에서 끝난다.
- `n + 1` — 조건이 참이면 유령 변수에 지금의 `e` 값을 적어 둔 상태 `σ[z := ⟦e⟧ σ]` 에서
  본체를 돌린다 (전제). 본체는 `z` 를 안 건드리므로 (명제 2.6(b)) 끝난 상태에서 `e < ⟦e⟧ σ`,
  곧 측도가 줄었고, 귀납 가설이 나머지를 끝낸다. 마지막으로 `σ` 와 `σ[z := …]` 는 `z` 를 뺀
  모든 곳에서 같으니 루프의 결과도 그렇다 (명제 2.6(a)) — `z` 는 사후조건에 없다.

명제 2.6 의 (a)·(b) 가 둘 다 들고, 그것이 규칙에 `z ∉ FV(c)` 가 붙는 이유다.
-/
@[exercise "§3.5 whT-sound" 3]
theorem whT_sound {i : Assert V} {b : BoolExp V} {c : Comm V} {e : IntExp V} {z : V}
    (hzi : z ∉ i.fv) (hzb : z ∉ b.fv) (hzc : z ∉ c.fv) (hze : z ∉ e.fv)
    (hnonneg : Stronger (i ⋀ b.toAssert) (.cmp .le (.num 0) e))
    (hbody : ［i ⋀ b.toAssert ⋀ .cmp .eq e (.var z)］c［i ⋀ .cmp .lt e (.var z)］) :
    ［i］(Comm.wh b c)［i ⋀ .not b.toAssert］ := by
  -- 먼저 볼 것: §2.8 `countLoop_eval` 의 측도 귀납, §2.5 의 `Comm.coincidence_general` (명제
  --            2.6(a)) 와 `Comm.eval_agree_outside_fa` (명제 2.6(b)), `Comm.fa_subset_fv`,
  --            `BoolExp.fv_coincidence`, 이 파일 위의 `BoolExp.fv_toAssert`.
  -- 힌트 1: `Comm.eval_isSemantics.2.2.2.2.1` 로 풀기 방정식 `whileEq` 를 꺼낸다.
  -- 힌트 2: "`⟦e⟧ σ < n` 인 모든 `σ` 에서 끝난다" 를 `n : Nat` 에 대한 귀납으로. 마지막에
  --         `n := (⟦e⟧ σ).toNat + 1` 을 넣는다 (`omega`).
  -- 힌트 3: `n = 0` — 조건이 참이면 `hnonneg` 와 모순, 거짓이면 그 자리에서 끝.
  -- 힌트 4: `n + 1`, 조건 참 — 본체를 `σ[z := ⟦e⟧ₑ σ]` 에서 돌린다 (`hbody`). 사전조건 세 조각은
  --         명제 1.1 (`coincidence_assert` · `coincidence_intExp` · `BoolExp.fv_coincidence`).
  --         끝난 상태 `ρ` 에서 `ρ z = ⟦e⟧ σ` (명제 2.6(b)) 이므로 측도가 줄어 귀납 가설이 든다.
  -- 힌트 5: 그렇게 얻은 `⟦while⟧ (σ[z := …]) = some τ'` 를 `⟦while⟧ σ` 로 옮긴다 — 명제 2.6(a) 를
  --         `S := (Comm.wh b c).fv ∪ (i ⋀ .not b.toAssert).fv` 에 적용하면 결과가 `S` 에서
  --         일치하고, 사후조건은 `S` 만 본다 (`coincidence_assert`).
  sorry


theorem newvarT_sound {p q : Assert V} {v : V} {e : IntExp V} {c : Comm V}
    (hp : v ∉ p.fv) (hq : v ∉ q.fv) (he : v ∉ e.fv)
    (h : ［p ⋀ .cmp .eq (.var v) e］c［q］) : ［p］(Comm.newvar v e c)［q］ := by
  intro σ hpσ
  have hp' : ⟦p⟧ₐ (σ[v := ⟦e⟧ₑ σ]) :=
    (coincidence_assert p σ _ fun w hw =>
      (State.subst_of_ne σ v w _ fun (hwv : w = v) => hp (hwv ▸ hw)).symm).mp hpσ
  have hv : ⟦Assert.cmp .eq (.var v) e⟧ₐ (σ[v := ⟦e⟧ₑ σ]) := by
    change (σ[v := ⟦e⟧ₑ σ]) v = ⟦e⟧ₑ (σ[v := ⟦e⟧ₑ σ])
    rw [State.subst_self]
    exact coincidence_intExp e σ _ fun w hw =>
      (State.subst_of_ne σ v w _ fun (hwv : w = v) => he (hwv ▸ hw)).symm
  obtain ⟨ρ, hρ, hqρ⟩ := h _ ((Assert.eval_and _ _ _).mpr ⟨hp', hv⟩)
  refine ⟨ρ[v := σ v], ?_, ?_⟩
  · change restore v σ (⟦c⟧ᶜ (σ[v := ⟦e⟧ₑ σ])) = some (ρ[v := σ v])
    rw [hρ]; rfl
  · exact (coincidence_assert q ρ (ρ[v := σ v]) fun w hw =>
      (State.subst_of_ne ρ v w _ fun (hwv : w = v) => hq (hwv ▸ hw)).symm).mp hqρ

/-! ## 4. 건전성 -/

/-- **전체 정확성의 건전성.** 유도된 명세는 타당하고, 게다가 끝난다. -/
theorem HoareT.sound [HasFresh V] {p q : Assert V} {c : Comm V} :
    HoareT p c q → ［p］c［q］ := by
  intro h
  induction h with
  | «skip» p => exact skipT_sound p
  | assign q v e => exact assignT_sound q v e
  | seq _ _ ih₀ ih₁ => exact seqT_sound ih₀ ih₁
  | ite _ _ ih₀ ih₁ => exact iteT_sound ih₀ ih₁
  | wh hzi hzb hzc hze hnonneg _ ih => exact whT_sound hzi hzb hzc hze hnonneg ih
  | «newvar» hp hq he _ ih => exact newvarT_sound hp hq he ih
  | conseq hp _ hq ih => exact TotalCorrect.conseq hp ih hq

/-- 전체 정확성의 유도는 부분 정확성의 명세도 준다 (§3.1 `TotalCorrect.toPartial` 과 같은
논증). -/
theorem HoareT.toPartial [HasFresh V] {p q : Assert V} {c : Comm V} (h : HoareT p c q) :
    ｛p｝c｛q｝ := by
  intro σ hp τ hτ
  obtain ⟨τ', hτ', hq⟩ := h.sound σ hp
  obtain rfl := Option.some.inj (hτ.symm.trans hτ')
  exact hq

/-! ## 5. 백까지 세기, 끝난다

§2.8 의 `countLoop` 다. 불변식 `x ≤ 100`, 변항 `100 - x`, 유령 변수 `z`. 본체의 전제는 대입
공리와 `omega` 하나로 닫힌다. -/

/-- `[x ≤ 100] while x < 100 do x := x + 1 [x = 100]`. -/
theorem countTo100_total :
    HoareT (⟪ x ≤ 100 ⟫ₐ) ⟪ while x < 100 do x := x + 1 ⟫ᶜ (⟪ x = 100 ⟫ₐ) := by
  refine HoareT.weaken (HoareT.wh (e := ⟪ 100 - x ⟫ₑ) (z := "z") ?_ ?_ ?_ ?_ ?_ ?_) ?_
  · simp [Assert.fv, IntExp.fv]
  · simp [BoolExp.fv, IntExp.fv]
  · simp [Comm.fv, IntExp.fv]
  · simp [IntExp.fv]
  · intro σ h
    simp [BoolExp.toAssert, Assert.eval, IntExp.eval, IntOp.denote, Cmp.denote, LogOp.denote] at h ⊢
    omega
  · refine HoareT.strengthen ?_ (HoareT.assign _ "x" _)
    intro σ h
    simp [BoolExp.toAssert, Assert.subst, IntExp.subst, Assert.eval, IntExp.eval, IntOp.denote,
      Cmp.denote, LogOp.denote, Function.update] at h ⊢
    omega
  · intro σ h
    simp [BoolExp.toAssert, Assert.eval, IntExp.eval, Cmp.denote, LogOp.denote] at h ⊢
    omega

/-- 그러니 §2.8 에서 계산으로 얻은 것을 규칙만으로 다시 얻는다 — 그리고 이번에는 끝난다는 것까지. -/
example : ［⟪ x ≤ 100 ⟫ₐ］⟪ while x < 100 do x := x + 1 ⟫ᶜ［⟪ x = 100 ⟫ₐ］ :=
  countTo100_total.sound

/-! ## 6. 여기서 어디로 가나

`z` 가 사전조건에만 나오고 프로그램은 건드리지 않는 변수 — 유령 변수 — 라는 것이 §3.7 의 상수
규칙과 ∃ 규칙, §3.10 의 논의로 이어진다. -/

end Reynolds.Exercises.Ch03
