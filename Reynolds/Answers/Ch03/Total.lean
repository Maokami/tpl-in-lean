/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Answers.Ch03.Annot

/-!
# §3.4 전체 정확성의 `while` 규칙 — 변항

부분 정확성의 `while` 규칙은 끝나면 무엇이 참인지만 말한다. 끝난다는 것까지 말하려면
한 바퀴마다 **줄어드는 양**이 있어야 한다.

```
[ i ∧ b ∧ e = z ] c [ i ∧ e < z ]       i ∧ b ⇒ 0 ≤ e
-------------------------------------------------------   z ∉ FV(i) ∪ FV(b) ∪ FV(c) ∪ FV(e)
              [ i ] while b do c [ i ∧ ¬b ]
```

`e`가 **변항**(variant)이다. 본체가 시작할 때 비음수이고 매번 엄격히 줄므로 무한히 돌 수 없다.
마지막 실행 뒤 조건이 거짓이면 `e`가 음수가 되어도 된다.
`z`는 본체 실행 전의 `e` 값을 기억하는 **유령 변수**(§3.4)다. 명세에는 나타나지만
명령에는 자유롭게 나타나지 않는다. `z ∉ FV(c)`에서 명제 2.6(b)는 본체가 `z`에 저장한
값을 보존함을, 명제 2.6(a)는 `z`를 바꾼 입력의 본체 결과를 원래 입력의 실행에
옮길 수 있음을 준다. 값을 보존하는 데만 필요한 `z ∉ FA(c)`보다 강한 조건이다.

## 건전성은 Scott 귀납법이 아니라 정초 귀납이다

§3.1 에서 보았듯 전체 정확성은 극한을 통과하지만, `⊥` 에서는 사전조건을 만족하는
상태의 종료를 보일 수 없다. Scott 귀납법의 시작 조건이 막히므로 `while` 이 끝난다는
증명에는 단계를 세는 측도 위의 귀납이 필요하고, 그
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

namespace Reynolds.Answers.Ch03

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

-- ANCHOR: hoareT
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
  | dc (s : List (Comm V)) {p q : Assert V} {v : V} {e : IntExp V} {c : Comm V}
      (hq : v ∉ q.fv) :
      HoareT p (Comm.seqs s (.seq (.assign v e) c)) q →
      HoareT p (Comm.seqs s (.newvar v e c)) q
  /-- RN: 앞부분 뒤의 지역 결합 이름을 어느 방향으로든 바꾼다. -/
  | rename {p q : Assert V} {c c' : Comm V} :
      Comm.PrefixRename c c' → HoareT p c q → HoareT p c' q
  /-- 결과 규칙. 사전조건을 강화하고 사후조건을 약화한다. -/
  | conseq {p p' q q' : Assert V} {c : Comm V} :
      Stronger p' p → HoareT p c q → Stronger q q' → HoareT p' c q'
-- ANCHOR_END: hoareT

/-- 전제 강화. -/
theorem HoareT.strengthen [HasFresh V] {p p' q : Assert V} {c : Comm V}
    (hp : Stronger p' p) (h : HoareT p c q) : HoareT p' c q :=
  HoareT.conseq hp h (Stronger.refl q)

/-- 결론 약화. -/
theorem HoareT.weaken [HasFresh V] {p q q' : Assert V} {c : Comm V}
    (h : HoareT p c q) (hq : Stronger q q') : HoareT p c q' :=
  HoareT.conseq (Stronger.refl p) h hq

/-- 대입 뒤 본체의 유도에서 빈 앞부분의 DC로 변수 선언을 얻는다. -/
theorem HoareT.newvar_comp [HasFresh V] {p r q : Assert V} {v : V}
    {e : IntExp V} {c : Comm V} (hq : v ∉ q.fv)
    (ha : HoareT p (.assign v e) r) (hc : HoareT r c q) :
    HoareT p (.newvar v e c) q :=
  HoareT.dc [] hq (HoareT.seq ha hc)

/-- 기존 합성형 선언 API. AS·SQ·DC로 유도되며 `p`, `e`의 신선함은 초기 단언에만 쓰인다. -/
theorem HoareT.newvar [HasFresh V] {p q : Assert V} {v : V}
    {e : IntExp V} {c : Comm V} (hp : v ∉ p.fv) (hq : v ∉ q.fv) (he : v ∉ e.fv)
    (h : HoareT (p ⋀ .cmp .eq (.var v) e) c q) : HoareT p (.newvar v e c) q := by
  refine HoareT.newvar_comp hq (HoareT.strengthen ?_ (HoareT.assign _ v e)) h
  intro σ hpσ
  exact (substitution_single _ v e σ).mpr (newvar_init hp he σ hpσ)

/-! ## 3. 규칙마다 건전성 — 종료를 얹는다 -/

theorem skipT_sound (p : Assert V) : ［p］Comm.skip［p］ :=
  fun σ hp => ⟨σ, rfl, hp⟩

/-- AS의 전체 정확성 성분을 구문 치환 명세로 옮긴다. -/
theorem assignT_sound [HasFresh V] (q : Assert V) (v : V) (e : IntExp V) :
    ［q /[v := e]］(Comm.assign v e)［q］ := by
  intro σ hp
  exact (as_sound ⟦q⟧ₐ v e).2 σ ((substitution_single q v e σ).mp hp)

/-- SQ의 전체 정확성 성분을 구문 명세에 적용한다. -/
theorem seqT_sound {p r q : Assert V} {c₀ c₁ : Comm V}
    (h₀ : ［p］c₀［r］) (h₁ : ［r］c₁［q］) : ［p］(Comm.seq c₀ c₁)［q］ := sq_sound.2 h₀ h₁

/-- CD의 전체 정확성 성분에서 불 조건을 구문 단언으로 옮긴다. -/
theorem iteT_sound {p q : Assert V} {b : BoolExp V} {c₀ c₁ : Comm V}
    (h₀ : ［p ⋀ b.toAssert］c₀［q］) (h₁ : ［p ⋀ .not b.toAssert］c₁［q］) :
    ［p］(Comm.ite b c₀ c₁)［q］ := by
  refine (cd_sound (P := ⟦p⟧ₐ) (Q := ⟦q⟧ₐ) (b := b) (c₀ := c₀) (c₁ := c₁)).2 ?_ ?_
  · intro σ hp
    exact h₀ σ ((Assert.eval_and _ _ _).mpr ⟨hp.1, (boolExp_eval_iff b σ).mpr hp.2⟩)
  · intro σ hp
    exact h₁ σ ((Assert.eval_and _ _ _).mpr
      ⟨hp.1, (Assert.eval_not _ _).mpr fun h => by
        have := (boolExp_eval_iff b σ).mp h
        simp [hp.2] at this⟩)

-- ANCHOR: whTSound
/--
§3.4 WHT의 구문 판. 신선한 변수 `z`에 본체 실행 전 변항을 기록해 의미 판에 전달한다.

`z`를 바꾼 상태에서 얻은 본체의 결과를 명제 2.6(a)로 원래 입력의 실행에 옮긴다.
명제 2.6(b)는 본체가 `z`를 바꾸지 않아 변항의 전후 값을 비교할 수 있음을 보인다.
종료를 보이는 귀납법은 `TotalCorrectS.wh`가 맡는다.
-/
theorem whT_sound {i : Assert V} {b : BoolExp V} {c : Comm V} {e : IntExp V} {z : V}
    (hzi : z ∉ i.fv) (hzb : z ∉ b.fv) (hzc : z ∉ c.fv) (hze : z ∉ e.fv)
    (hnonneg : Stronger (i ⋀ b.toAssert) (.cmp .le (.num 0) e))
    (hbody : ［i ⋀ b.toAssert ⋀ .cmp .eq e (.var z)］c［i ⋀ .cmp .lt e (.var z)］) :
    ［i］(Comm.wh b c)［i ⋀ .not b.toAssert］ := by
  have hbodyS : ∀ n : Int, TotalCorrectS
      (fun σ => ⟦i⟧ₐ σ ∧ ⟦b⟧ᵇ σ = true ∧ ⟦e⟧ₑ σ = n) c
      (fun σ => ⟦i⟧ₐ σ ∧ ⟦e⟧ₑ σ < n) := by
    intro n σ ⟨hi, hb, he⟩
    have hi' : ⟦i⟧ₐ (σ[z := n]) :=
      (coincidence_assert i σ _ fun w hw =>
        (State.subst_of_ne σ z w n fun h => hzi (h ▸ hw)).symm).mp hi
    have hb' : ⟦b⟧ᵇ (σ[z := n]) = true :=
      (BoolExp.fv_coincidence b σ _ fun w hw =>
        (State.subst_of_ne σ z w n fun h => hzb (h ▸ hw)).symm).symm.trans hb
    have he' : ⟦e⟧ₑ (σ[z := n]) = n :=
      (coincidence_intExp e σ _ fun w hw =>
        (State.subst_of_ne σ z w n fun h => hze (h ▸ hw)).symm).symm.trans he
    have hpre : ⟦i ⋀ b.toAssert ⋀ .cmp .eq e (.var z)⟧ₐ (σ[z := n]) := by
      refine (Assert.eval_and _ _ _).mpr
        ⟨(Assert.eval_and _ _ _).mpr ⟨hi', (boolExp_eval_iff b _).mpr hb'⟩, ?_⟩
      change ⟦e⟧ₑ (σ[z := n]) = (σ[z := n]) z
      rw [State.subst_self]
      exact he'
    obtain ⟨ρ', hρ', hpost⟩ := hbody _ hpre
    obtain ⟨hiρ', hdec⟩ := (Assert.eval_and _ _ _).mp hpost
    change ⟦e⟧ₑ ρ' < ρ' z at hdec
    have hz : ρ' z = n := by
      rw [Comm.eval_agree_outside_fa c _ ρ' hρ' z fun h => hzc (Comm.fa_subset_fv c h)]
      exact State.subst_self σ z n
    -- 유령 변수를 바꾸지 않은 입력에서의 본체 결과로 불변식과 변항 값을 옮긴다.
    have hag := Comm.coincidence_general c ((c.fv ∪ i.fv) ∪ e.fv)
      (fun w hw => Finset.mem_union_left _ (Finset.mem_union_left _ hw))
      σ (σ[z := n]) (fun w hw =>
        (State.subst_of_ne σ z w n fun h => by
          subst h
          rcases Finset.mem_union.mp hw with hci | he
          · rcases Finset.mem_union.mp hci with hc | hi
            · exact hzc hc
            · exact hzi hi
          · exact hze he).symm)
    rw [hρ'] at hag
    cases hρ : ⟦c⟧ᶜ σ with
    | none => rw [hρ] at hag; simp [AgreeOn] at hag
    | some ρ =>
      rw [hρ] at hag
      change ∀ w ∈ (c.fv ∪ i.fv) ∪ e.fv, ρ w = ρ' w at hag
      refine ⟨ρ, rfl, ?_, ?_⟩
      · exact (coincidence_assert i ρ ρ' fun w hw =>
          hag w (Finset.mem_union_left _ (Finset.mem_union_right _ hw))).mpr hiρ'
      · rw [coincidence_intExp e ρ ρ' fun w hw => hag w (Finset.mem_union_right _ hw)]
        exact hz ▸ hdec
  have hnonnegS : ∀ σ, ⟦i⟧ₐ σ → ⟦b⟧ᵇ σ = true → 0 ≤ ⟦e⟧ₑ σ := by
    intro σ hi hb
    exact hnonneg σ ((Assert.eval_and _ _ _).mpr ⟨hi, (boolExp_eval_iff b σ).mpr hb⟩)
  intro σ hi
  obtain ⟨τ, hτ, hiτ, hbτ⟩ := TotalCorrectS.wh hbodyS hnonnegS σ hi
  refine ⟨τ, hτ, (Assert.eval_and _ _ _).mpr ⟨hiτ, (Assert.eval_not _ _).mpr ?_⟩⟩
  intro hb
  have := (boolExp_eval_iff b τ).mp hb
  simp [hbτ] at this
-- ANCHOR_END: whTSound

theorem newvarT_sound {p q : Assert V} {v : V} {e : IntExp V} {c : Comm V}
    (hp : v ∉ p.fv) (hq : v ∉ q.fv) (he : v ∉ e.fv)
    (h : ［p ⋀ .cmp .eq (.var v) e］c［q］) : ［p］(Comm.newvar v e c)［q］ := by
  apply (dc_sound [] p.eval q.eval v e c (Assert.eval_update_of_notMem hq)).2
  have hs := sq_sound.2 (as_sound (p ⋀ .cmp .eq (.var v) e).eval v e).2 h
  intro σ hpσ
  exact hs σ (newvar_init hp he σ hpσ)

/-! ## 4. 건전성 -/

-- ANCHOR: soundT
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
  | dc s hq _ ih =>
    exact (dc_sound s _ _ _ _ _ (Assert.eval_update_of_notMem hq)).2 ih
  | rename hr _ ih => exact (rn_sound _ _ hr).2 ih
  | conseq hp _ hq ih => exact TotalCorrect.conseq hp ih hq
-- ANCHOR_END: soundT

/-- 전체 정확성의 유도는 부분 정확성의 명세도 준다 (§3.1 `TotalCorrect.toPartial` 과 같은
논증). -/
theorem HoareT.toPartial [HasFresh V] {p q : Assert V} {c : Comm V} (h : HoareT p c q) :
    ｛p｝c｛q｝ := by
  intro σ hp τ hτ
  obtain ⟨τ', hτ', hq⟩ := h.sound σ hp
  obtain rfl := Flat.some.inj (hτ.symm.trans hτ')
  exact hq

/-! ## 5. 백까지 세기, 끝난다

§2.8 의 `countLoop` 다. 불변식 `x ≤ 100`, 변항 `100 - x`, 유령 변수 `z`. 본체의 전제는 대입
공리와 `omega` 하나로 닫힌다. -/

-- ANCHOR: countT
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
-- ANCHOR_END: countT

/-! ## 6. 여기서 어디로 가나

`z` 가 사전조건에만 나오고 프로그램은 건드리지 않는 변수 — 유령 변수 — 라는 것이 §3.7 의 상수
규칙과 ∃ 규칙, §3.10 의 논의로 이어진다. -/

end Reynolds.Answers.Ch03
