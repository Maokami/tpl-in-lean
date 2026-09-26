/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External

set_option verso.exampleProject ".."
-- 긴 증명을 인용하는 쪽이라 하이라이트 재구성이 기본 한도를 넘는다.
set_option maxHeartbeats 1000000
set_option verso.exampleModule "Reynolds.Answers.Ch03.Annot"

#doc (Manual) "§3.4~3.5 주석 명세와 전체 정확성" =>
%%%
tag := "ch03-annot"
file := "ch03-annot"
number := false
%%%

유도 나무는 금방 커진다. Reynolds는 그것을 명령 사이사이에 단언을 끼워 넣은 _주석
명세_(annotated specification)로 줄여 적는다. 규칙이 스스로 정하지 못하는 것은 두 가지뿐이다.
순차 합성의 _이음매_와 반복의 _불변식_이다. 나머지는 규칙이 계산한다.

# 주석 명령
%%%
tag := "ch03-annot-syntax"
file := "ch03-annot-syntax"
number := false
%%%

사람이 적어야 하는 것만 붙인 구문을 둔다. 주석을 지우면 명령이 된다.

```anchor annot (module := Reynolds.Answers.Ch03.Annot)
/-- 주석 명령. 이음매(`seq` 의 가운데)와 불변식(`wh` 의 첫 인자)만 사람이 적는다. -/
inductive Annot (V : Type u) where
  | assign : V → IntExp V → Annot V
  | skip
  /-- `a₀ ; {r} a₁` — 가운데가 이음매. -/
  | seq : Annot V → Assert V → Annot V → Annot V
  | ite : BoolExp V → Annot V → Annot V → Annot V
  /-- `while b do {i} a` — `i` 가 불변식. -/
  | wh : Assert V → BoolExp V → Annot V → Annot V
  | newvar : V → IntExp V → Annot V → Annot V

/-- 주석을 지우면 명령이다. -/
def Annot.erase : Annot V → Comm V
  | .assign v e     => .assign v e
  | .skip           => .skip
  | .seq a₀ _ a₁    => .seq a₀.erase a₁.erase
  | .ite b a₀ a₁    => .ite b a₀.erase a₁.erase
  | .wh _ b a       => .wh b a.erase
  | .newvar v e a   => .newvar v e a.erase
```

# 검증 조건 생성기
%%%
tag := "ch03-vcg"
file := "ch03-vcg"
number := false
%%%

사후조건에서 _뒤로_ 가며 사전조건을 계산하고, 도중에 확인해야 할 함의들을 모은다.
대입 공리가 거꾸로 가기 때문에 계산도 거꾸로 간다.

```anchor vcg (module := Reynolds.Answers.Ch03.Annot)
/-- 검증 조건 생성기. `(사전조건, 확인할 함의들)`. -/
def Annot.vcg [HasFresh V] : Annot V → Assert V → Assert V × List (Assert V × Assert V)
  | .assign v e, q   => (q /[v := e], [])
  | .skip, q         => (q, [])
  | .seq a₀ r a₁, q  => ((a₀.vcg r).1, (r, (a₁.vcg q).1) :: ((a₀.vcg r).2 ++ (a₁.vcg q).2))
  | .ite b a₀ a₁, q  =>
      (.bin .and (.bin .imp b.toAssert (a₀.vcg q).1) (.bin .imp (.not b.toAssert) (a₁.vcg q).1),
        (a₀.vcg q).2 ++ (a₁.vcg q).2)
  | .wh i b a, q     =>
      (i, (i ⋀ b.toAssert, (a.vcg i).1) :: (i ⋀ .not b.toAssert, q) :: (a.vcg i).2)
  | .newvar v e a, q => (.quant .all v (.bin .imp (.cmp .eq (.var v) e) (a.vcg q).1), (a.vcg q).2)
```

: 대입

  사후조건에 치환을 건다. 확인할 것은 없다.

: 순차 합성

  이음매 `r`이 뒤쪽 명령의 사전조건보다 강해야 한다. 이것이 검증 조건 하나다.

: 조건

  `(b ⇒ p₀) ∧ (¬b ⇒ p₁)`. 확인할 것은 없다.

: 반복

  사전조건은 불변식이다. `i ∧ b`가 본체의 사전조건보다 강한지, `i ∧ ¬b`가 사후조건보다
  강한지를 확인해야 한다.

: 변수 선언

  `∀ v. v = e ⇒ p`. 결합자를 `∀`로 가두면 바깥 단언에 새지 않는다.

검증 조건이 전부 타당하면 `Hoare` 유도가 있다(`Annot.vcg_sound`). Dafny나 Why3 같은 검증
도구가 하는 일의 축소판이다. 맞바꾸기에 주석을 달면 남는 일은 치환을 펼치는 것뿐이다.

```anchor swapAnnot (module := Reynolds.Answers.Ch03.Annot)
/-- 주석 붙은 맞바꾸기. 이음매가 Reynolds §3.4 의 주석 그대로다. -/
def swapAnnot : Annot String :=
  .seq (.assign "t" ⟪ x ⟫ₑ) (⟪ t = a ∧ y = b ⟫ₐ)
    (.seq (.assign "x" ⟪ y ⟫ₑ) (⟪ t = a ∧ x = b ⟫ₐ) (.assign "y" ⟪ t ⟫ₑ))

/-- 주석을 지우면 §2.5 의 `swap` 이다. -/
theorem swapAnnot_erase : swapAnnot.erase = swap := rfl

/-- 검증 조건 두 개와 맨 앞의 함의 하나. 셋 다 치환을 펼치면 항등이다. -/
theorem swap_hoare' : Hoare (⟪ x = a ∧ y = b ⟫ₐ) swap (⟪ y = a ∧ x = b ⟫ₐ) := by
  rw [← swapAnnot_erase]
  refine Hoare.strengthen ?_ (Annot.vcg_sound swapAnnot _ ⟨trivial, trivial, trivial⟩ ?_)
  · intro σ h
    simpa [swapAnnot, Annot.vcg, Assert.subst, IntExp.subst, Assert.eval, IntExp.eval,
      Cmp.denote, LogOp.denote, Function.update] using h
  · intro vc hvc σ h
    simp only [swapAnnot, Annot.vcg, List.nil_append, List.append_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hvc
    rcases hvc with rfl | rfl <;>
      simpa [Assert.subst, IntExp.subst, Assert.eval, IntExp.eval, Cmp.denote, LogOp.denote,
        Function.update] using h
```

# 전체 정확성 — 변항
%%%
tag := "ch03-total"
file := "ch03-total"
number := false
%%%

전체 정확성 체계는 `while` 규칙만 다르다. 끝난다는 것을 말하려면 한 바퀴마다 _줄어드는
양_, 곧 변항(variant)이 있어야 한다.

```anchor hoareT (module := Reynolds.Answers.Ch03.Total)
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
```

`z`는 한 바퀴를 시작할 때의 `e` 값을 붙들어 두는 _유령 변수_다. "줄었다"는 전과 후의
비교이므로 전의 값을 어딘가에 기억해야 한다. `z ∉ FV(c)`는 본체가 그 기억을 건드리지
않는다는 조건이다.

§3.1에서 보았듯 "반드시 끝난다"는 극한을 통과하지 않는다. 그래서 건전성 증명은 Scott
귀납법이 아니라 측도 위의 정초 귀납이다. 2장에서 구체적인 루프의 값을 계산할 때 손으로
잡던 측도를 이제는 규칙이 인자로 받는다.

```anchor whTSound (module := Reynolds.Answers.Ch03.Total)
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
  have whileEq : ∀ τ : State V, ⟦Comm.wh b c⟧ᶜ τ
      = if ⟦b⟧ᵇ τ then Option.bind (⟦c⟧ᶜ τ) ⟦Comm.wh b c⟧ᶜ else some τ :=
    fun τ => Comm.eval_isSemantics.2.2.2.2.1 _ _ τ
  -- 조건이 거짓이면 그 자리에서 끝난다.
  have stop : ∀ σ, ⟦i⟧ₐ σ → ¬ ⟦b⟧ᵇ σ = true →
      ∃ τ, ⟦Comm.wh b c⟧ᶜ σ = some τ ∧ ⟦i ⋀ .not b.toAssert⟧ₐ τ := fun σ hi hb =>
    ⟨σ, by rw [whileEq σ, if_neg hb],
      (Assert.eval_and _ _ _).mpr
        ⟨hi, (Assert.eval_not _ _).mpr fun h => hb ((boolExp_eval_iff b σ).mp h)⟩⟩
  -- `z` 를 뺀 곳에서 같은 두 상태는 `b` 를 같게 계산한다.
  have hbz : ∀ σ, ⟦b⟧ᵇ (σ[z := ⟦e⟧ₑ σ]) = ⟦b⟧ᵇ σ := fun σ =>
    (BoolExp.fv_coincidence b σ _ fun w hw =>
      (State.subst_of_ne σ z w _ fun (h : w = z) => hzb (h ▸ hw)).symm).symm
  have key : ∀ (n : Nat) (σ : State V), ⟦i⟧ₐ σ → ⟦e⟧ₑ σ < n →
      ∃ τ, ⟦Comm.wh b c⟧ᶜ σ = some τ ∧ ⟦i ⋀ .not b.toAssert⟧ₐ τ := by
    intro n
    induction n with
    | zero =>
      intro σ hi hlt
      by_cases hb : ⟦b⟧ᵇ σ = true
      · exfalso
        have h0 := hnonneg σ ((Assert.eval_and _ _ _).mpr ⟨hi, (boolExp_eval_iff b σ).mpr hb⟩)
        change (0 : Int) ≤ ⟦e⟧ₑ σ at h0
        omega
      · exact stop σ hi hb
    | succ n ih =>
      intro σ hi hlt
      by_cases hb : ⟦b⟧ᵇ σ = true
      · -- 유령 변수에 지금의 `e` 값을 적어 두고 본체를 돌린다.
        have hpre : ⟦i ⋀ b.toAssert ⋀ .cmp .eq e (.var z)⟧ₐ (σ[z := ⟦e⟧ₑ σ]) := by
          refine (Assert.eval_and _ _ _).mpr ⟨(Assert.eval_and _ _ _).mpr ⟨?_, ?_⟩, ?_⟩
          · exact (coincidence_assert i σ _ fun w hw =>
              (State.subst_of_ne σ z w _ fun (h : w = z) => hzi (h ▸ hw)).symm).mp hi
          · exact (boolExp_eval_iff b _).mpr ((hbz σ).trans hb)
          · change ⟦e⟧ₑ (σ[z := ⟦e⟧ₑ σ]) = (σ[z := ⟦e⟧ₑ σ]) z
            rw [State.subst_self]
            exact (coincidence_intExp e σ _ fun w hw =>
              (State.subst_of_ne σ z w _ fun (h : w = z) => hze (h ▸ hw)).symm).symm
        obtain ⟨ρ, hρ, hpost⟩ := hbody _ hpre
        obtain ⟨hiρ, hlt'⟩ := (Assert.eval_and _ _ _).mp hpost
        change ⟦e⟧ₑ ρ < ρ z at hlt'
        -- 본체는 `z` 를 안 건드린다 (명제 2.6(b)). 그러니 `ρ z` 는 시작 때의 `⟦e⟧ σ` 다.
        have hz : ρ z = ⟦e⟧ₑ σ := by
          rw [Comm.eval_agree_outside_fa c _ ρ hρ z fun h => hzc (Comm.fa_subset_fv c h)]
          exact State.subst_self σ z _
        -- 측도가 줄었다. 귀납 가설이 `ρ` 에서 루프를 끝낸다.
        obtain ⟨τ', hτ', hqτ'⟩ := ih ρ hiρ (by omega)
        have hloop : ⟦Comm.wh b c⟧ᶜ (σ[z := ⟦e⟧ₑ σ]) = some τ' := by
          rw [whileEq, if_pos ((hbz σ).trans hb), hρ]
          exact hτ'
        -- `σ` 와 `σ[z := …]` 는 `z` 를 뺀 모든 곳에서 같다. 루프의 결과도 그렇다 (명제 2.6(a)).
        have hag := Comm.coincidence_general (Comm.wh b c)
          ((Comm.wh b c).fv ∪ (i ⋀ .not b.toAssert).fv) Finset.subset_union_left
          σ (σ[z := ⟦e⟧ₑ σ]) fun w hw =>
            (State.subst_of_ne σ z w _ fun (h : w = z) => by
              subst h
              rcases Finset.mem_union.mp hw with h₁ | h₁
              · rcases Finset.mem_union.mp h₁ with h₂ | h₂
                · exact hzb h₂
                · exact hzc h₂
              · rw [Assert.fv, Assert.fv, BoolExp.fv_toAssert] at h₁
                rcases Finset.mem_union.mp h₁ with h₂ | h₂
                · exact hzi h₂
                · exact hzb h₂).symm
        rw [hloop] at hag
        rcases hτ : ⟦Comm.wh b c⟧ᶜ σ with _ | τ
        · rw [hτ] at hag; simp [AgreeOn] at hag
        · rw [hτ] at hag
          change ∀ w ∈ _, τ w = τ' w at hag
          exact ⟨τ, rfl, (coincidence_assert _ τ τ' fun w hw =>
            hag w (Finset.mem_union_right _ hw)).mpr hqτ'⟩
      · exact stop σ hi hb
  intro σ hi
  exact key ((⟦e⟧ₑ σ).toNat + 1) σ hi (by omega)
```

명제 2.6의 두 반쪽이 모두 쓰인다. (b)는 본체가 `z`를 건드리지 않음을, (a)는 `z`만 다른 두
시작 상태에서 루프의 결과가 사후조건이 보는 변수들 위에서 같음을 준다.

§2.8의 백까지 세기를 규칙만으로 유도하면, 이번에는 끝난다는 것까지 얻는다.

```anchor countT (module := Reynolds.Answers.Ch03.Total)
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
```
