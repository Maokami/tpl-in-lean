/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Answers.Ch02.Ex.Aliasing

/-!
# 연습 2.8 — 명제 2.7 의 조건을 얼마나 약하게 할 수 있나

Reynolds 연습 2.8 에 대응한다.

## 지금 조건과 실마리

§2.5 의 치환 정리(명제 2.7)는 `δ` 가 `S` **전체에서** 단사일 것을 요구했다.

```
∀ u ∈ S, ∀ w ∈ S, δ u = δ w → u = w
```

그런데 연습 2.7 이 이미 실마리를 주었다 — **읽기만 하는 변수는 합쳐도 된다.** 별칭이
해가 되는 것은 한쪽에 **쓸** 때뿐이다. `z := x + y` 에서 `x` 와 `y` 를 같은 칸으로 묶어도
읽는 값이 같으므로 결과가 안 변한다.

그래서 약한 조건은 이것이다.

```
∀ u ∈ FA(c), ∀ w ∈ S, δ u = δ w → u = w
```

"`δ` 가 **대입되는 변수들을 나머지로부터 갈라 놓는다**". 읽기 전용 변수끼리는 마음껏
합쳐도 된다. `FA(c) ⊆ FV(c) ⊆ S` 이므로 원래 조건이 이것을 포함하고, 따라서 명제 2.7 은
약한 판의 따름정리가 된다.

## 증명에서 무엇이 걸리는가

원래 증명에서 단사성이 실제로 쓰이는 자리는 둘뿐이다.

1. **`assign` 절** — 대입되는 `v` 와 다른 `w` 에 대해 `δ v ≠ δ w` 가 필요하다.
   `v ∈ FA` 이므로 약한 조건이 그대로 준다.
2. **`newvar` 절의 `hfa'`** — 치환된 명령이 어떤 이름에 대입하지 **않는다**를 보이는
   자리다. 원래 증명은 여기서

   ```
   (c /ᶜ δ).fa ⊆ (c /ᶜ δ).fv ⊆ (FV c).image δ
   ```

   로 올라가 버려서 `FV` 위의 단사성을 요구하게 된다. **그 어림이 너무 거칠다.**

## 반을 차지하는 관찰

치환된 명령이 대입하는 이름은 정확히 **원래 대입하던 이름들의 상**이다.

```
(c /ᶜ δ).fa ⊆ (FA c).image δ
```

이 더 날카로운 보조정리를 먼저 얻으면, `hfa'` 가 `FA` 위의 단사성만 쓰게 되고 약한
조건으로 증명이 그대로 돌아간다. **필요한 것이 이 보조정리라는 것을 알아채는 것이
이 연습의 절반이다.**

## 읽는 순서
`Ex/Aliasing.lean` 다음. §2.5 의 `Comm.substitution_general` 을 곁에 두고 비교하며 읽으면
어디가 달라졌는지 보인다.
-/

@[expose] public section

namespace Reynolds.Answers.Ch02.Ex

open Reynolds Reynolds.Answers.Ch01 Reynolds.Answers.Ch02

universe u

variable {V : Type u} [DecidableEq V]

/-! ## 1. 더 날카로운 어림

§2.5 의 `Comm.fv_subst_subset` 은 "치환된 명령의 **자유 변수**는 원래 자유 변수의 상
안에 있다" 였다. 여기서는 **대입되는 변수**에 대해 같은 것을 말한다. 더 작은 집합이라
더 강한 진술이고, 약한 조건이 통하는 이유가 바로 이것이다. -/

-- ANCHOR: faSubstSubset
/--
**치환된 명령이 대입하는 이름은 원래 대입하던 이름들의 상 안에 있다.**

```
(c /ᶜ δ).fa ⊆ (FA c).image δ
```

`newvar` 절만 볼 것이 있다. 치환된 본문이 새 결합자 `vn` 에 대입할 수는 있지만 그것은
지워지고, `vn` 이 아닌 이름은 원래 결합자 `v` 가 아닌 변수에서 온 것이므로 `erase v`
쪽에 남는다. **새 결합자의 신선함이 필요 없다** — 지워지는 쪽이라 저절로 맞는다.
-/
theorem Comm.fa_subst_subset [HasFresh V] :
    ∀ (c : Comm V) (δ : Ren V), (c /ᶜ δ).fa ⊆ c.fa.image δ := by
  intro c
  induction c with
  | assign v e => intro δ; simp [Comm.subst, Comm.fa]
  | «skip» => intro δ; simp [Comm.subst, Comm.fa]
  | seq c₀ c₁ ih₀ ih₁ =>
      intro δ
      simpa [Comm.subst, Comm.fa, Finset.image_union] using
        Finset.union_subset_union (ih₀ δ) (ih₁ δ)
  | ite b c₀ c₁ ih₀ ih₁ =>
      intro δ
      simpa [Comm.subst, Comm.fa, Finset.image_union] using
        Finset.union_subset_union (ih₀ δ) (ih₁ δ)
  | wh b c ih => intro δ; simpa [Comm.subst, Comm.fa] using ih δ
  | «newvar» v e c ih =>
      intro δ
      simp only [Comm.subst, Comm.fa]
      intro w hw
      obtain ⟨hwne, hwmem⟩ := Finset.mem_erase.mp hw
      obtain ⟨u, hu, huw⟩ := Finset.mem_image.mp (ih _ hwmem)
      by_cases huv : u = v
      · rw [huv, Function.update_self] at huw
        exact absurd huw.symm hwne
      · rw [Function.update_of_ne huv] at huw
        exact Finset.mem_image.mpr ⟨u, Finset.mem_erase.mpr ⟨huv, hu⟩, huw⟩
-- ANCHOR_END: faSubstSubset

/-! ## 2. 약한 조건의 치환 정리 -/

-- ANCHOR: substWeak
/--
**연습 2.8 — 명제 2.7, 약한 조건 판.**

단사성을 `S` 전체가 아니라 **`FA(c)` 에서만** 요구한다.

```
∀ u ∈ FA(c), ∀ w ∈ S, δ u = δ w → u = w
```

읽기만 하는 변수끼리는 합쳐도 된다. 별칭이 해가 되는 것은 한쪽에 **쓸** 때뿐이기 때문이다.

증명은 §2.5 의 `Comm.substitution_general` 과 뼈대가 같고 두 자리만 다르다.

- `assign` 절 — 대입되는 `v` 가 `FA` 에 있으므로 약한 조건이 그대로 쓰인다.
- `newvar` 절 — `hfa'` 에서 `Comm.fa_subst_subset` 을 쓴다. 원래 증명이 `FV` 로 올라가
  버리던 자리이고, 거기가 강한 조건을 요구하던 유일한 이유였다.

나머지 절은 조건을 부분 명령으로 좁혀 넘기기만 한다 — `FA(c₀) ⊆ FA(c₀; c₁)` 처럼.
-/
@[exercise "Ex 2.8" 3]
theorem Comm.substitution_weak [HasFresh V] :
    ∀ (c : Comm V) (δ : Ren V) (S : Finset V), c.fv ⊆ S →
      (∀ u ∈ c.fa, ∀ w ∈ S, δ u = δ w → u = w) →
      ∀ σ σ' : State V, (∀ w ∈ S, σ w = σ' (δ w)) →
      AgreeVia δ S (c.eval σ) ((c /ᶜ δ).eval σ') := by
  intro c
  induction c with
  | assign v e =>
      intro δ S hS hinj σ σ' h
      have he : ⟦e /ₑ δ.toSubst⟧ₑ σ' = ⟦e⟧ₑ σ :=
        substitution_intExp e δ.toSubst σ σ' fun w hw =>
          h w (hS (by simp [Comm.fv, hw]))
      change AgreeVia δ S (some (σ[v := ⟦e⟧ₑ σ])) (some (σ'[δ v := ⟦e /ₑ δ.toSubst⟧ₑ σ']))
      rw [AgreeVia.some_some, he]
      intro w hw
      by_cases hwv : w = v
      · subst hwv; simp
      · -- 여기가 약한 조건이 쓰이는 자리다. `v` 는 대입되는 변수이므로 `FA` 에 있다.
        have hδ : δ w ≠ δ v := fun hEq =>
          hwv ((hinj v (by simp [Comm.fa]) w hw hEq.symm).symm)
        simp [hwv, hδ, h w hw]
  | «skip» =>
      intro δ S _ _ σ σ' h
      exact h
  | seq c₀ c₁ ih₀ ih₁ =>
      intro δ S hS hinj σ σ' h
      have hS₀ : c₀.fv ⊆ S := le_trans Finset.subset_union_left hS
      have hS₁ : c₁.fv ⊆ S := le_trans Finset.subset_union_right hS
      have hinj₀ : ∀ u ∈ c₀.fa, ∀ w ∈ S, δ u = δ w → u = w := fun u hu =>
        hinj u (by simp [Comm.fa, hu])
      have hinj₁ : ∀ u ∈ c₁.fa, ∀ w ∈ S, δ u = δ w → u = w := fun u hu =>
        hinj u (by simp [Comm.fa, hu])
      change AgreeVia δ S (Option.bind (c₀.eval σ) c₁.eval)
        (Option.bind ((c₀ /ᶜ δ).eval σ') (c₁ /ᶜ δ).eval)
      have h₀ := ih₀ δ S hS₀ hinj₀ σ σ' h
      rcases h₀₁ : c₀.eval σ with _ | τ <;> rcases h₀₂ : (c₀ /ᶜ δ).eval σ' with _ | τ'
      · simp
      · rw [h₀₁, h₀₂] at h₀; exact absurd h₀ (by simp)
      · rw [h₀₁, h₀₂] at h₀; exact absurd h₀ (by simp)
      · rw [h₀₁, h₀₂] at h₀
        exact ih₁ δ S hS₁ hinj₁ τ τ' h₀
  | ite b c₀ c₁ ih₀ ih₁ =>
      intro δ S hS hinj σ σ' h
      have hinj₀ : ∀ u ∈ c₀.fa, ∀ w ∈ S, δ u = δ w → u = w := fun u hu =>
        hinj u (by simp [Comm.fa, hu])
      have hinj₁ : ∀ u ∈ c₁.fa, ∀ w ∈ S, δ u = δ w → u = w := fun u hu =>
        hinj u (by simp [Comm.fa, hu])
      have hb : ⟦b /ᵇ δ.toSubst⟧ᵇ σ' = ⟦b⟧ᵇ σ :=
        substitution_boolExp b δ.toSubst σ σ' fun w hw =>
          h w (hS (by simp [Comm.fv, hw]))
      change AgreeVia δ S (if ⟦b⟧ᵇ σ then _ else _) (if ⟦b /ᵇ δ.toSubst⟧ᵇ σ' then _ else _)
      rw [hb]
      by_cases hbσ : ⟦b⟧ᵇ σ
      · simp only [if_pos hbσ]
        exact ih₀ δ S (le_trans (le_trans Finset.subset_union_left
          Finset.subset_union_right) (by simpa [Comm.fv, Finset.union_assoc] using hS))
          hinj₀ σ σ' h
      · simp only [if_neg hbσ]
        exact ih₁ δ S (le_trans Finset.subset_union_right hS) hinj₁ σ σ' h
  | wh b c ihc =>
      intro δ S hS hinj σ σ' h
      have hSb : b.fv ⊆ S := le_trans Finset.subset_union_left hS
      have hSc : c.fv ⊆ S := le_trans Finset.subset_union_right hS
      have hinjc : ∀ u ∈ c.fa, ∀ w ∈ S, δ u = δ w → u = w := fun u hu =>
        hinj u (by simpa [Comm.fa] using hu)
      have hfm : Monotone (whileF b c.eval) := whileF_monotone b c.eval
      have hgm : Monotone (whileF (b /ᵇ δ.toSubst) ((c /ᶜ δ).eval)) :=
        whileF_monotone _ _
      have key : ∀ n, ∀ σ σ' : State V, (∀ w ∈ S, σ w = σ' (δ w)) →
          AgreeVia δ S ((whileF b c.eval)^[n] ⊥ σ)
            ((whileF (b /ᵇ δ.toSubst) ((c /ᶜ δ).eval))^[n] ⊥ σ') := by
        intro n
        induction n with
        | zero => intro σ σ' _; exact AgreeVia.none_none
        | succ n ih =>
            intro σ σ' hσσ'
            rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
            have hb : ⟦b /ᵇ δ.toSubst⟧ᵇ σ' = ⟦b⟧ᵇ σ :=
              substitution_boolExp b δ.toSubst σ σ' fun w hw => hσσ' w (hSb hw)
            change AgreeVia δ S (if ⟦b⟧ᵇ σ then _ else _)
              (if ⟦b /ᵇ δ.toSubst⟧ᵇ σ' then _ else _)
            rw [hb]
            by_cases hbσ : ⟦b⟧ᵇ σ
            · simp only [if_pos hbσ]
              have hbody := ihc δ S hSc hinjc σ σ' hσσ'
              rcases h₁ : c.eval σ with _ | τ <;> rcases h₂ : (c /ᶜ δ).eval σ' with _ | τ'
              · simp
              · rw [h₁, h₂] at hbody; exact absurd hbody (by simp)
              · rw [h₁, h₂] at hbody; exact absurd hbody (by simp)
              · rw [h₁, h₂] at hbody
                exact ih τ τ' hbody
            · simp only [if_neg hbσ]
              exact hσσ'
      exact AgreeVia.admissible δ S (iterChain hfm) (iterChain hgm)
        (fun n => key n σ σ' h)
  | «newvar» v e c ih =>
      intro δ S hS hinj σ σ' h
      set vn := c.newBinder v δ with hvn
      set δ' := Function.update δ v vn with hδ'
      have herase : c.fv.erase v ⊆ S := le_trans Finset.subset_union_right hS
      have he : ⟦e /ₑ δ.toSubst⟧ₑ σ' = ⟦e⟧ₑ σ :=
        substitution_intExp e δ.toSubst σ σ' fun w hw =>
          h w (hS (by simp [Comm.fv, hw]))
      have hS' : c.fv ⊆ insert v c.fv := Finset.subset_insert _ _
      have hvn_ne : ∀ w ∈ c.fv, w ≠ v → vn ≠ δ w := by
        intro w hw hwv; rw [hvn]; exact Comm.newBinder_ne hw hwv
      -- 약한 조건을 안쪽으로 넘긴다. 결합자 `v` 는 `vn` 의 신선함이 지켜 준다.
      have hinj' : ∀ u ∈ c.fa, ∀ w ∈ insert v c.fv, δ' u = δ' w → u = w := by
        intro u hu w hw huw
        have hufv : u ∈ c.fv := Comm.fa_subset_fv c hu
        by_cases huv : u = v <;> by_cases hwv : w = v
        · rw [huv, hwv]
        · have hw' : w ∈ c.fv := (Finset.mem_insert.mp hw).resolve_left hwv
          rw [huv, hδ', Function.update_self, Function.update_of_ne hwv] at huw
          exact absurd huw (hvn_ne w hw' hwv)
        · rw [hwv, hδ', Function.update_self, Function.update_of_ne huv] at huw
          exact absurd huw.symm (hvn_ne u hufv huv)
        · have hw' : w ∈ c.fv := (Finset.mem_insert.mp hw).resolve_left hwv
          rw [hδ', Function.update_of_ne huv, Function.update_of_ne hwv] at huw
          exact hinj u (Finset.mem_erase.mpr ⟨huv, hu⟩) w
            (herase (Finset.mem_erase.mpr ⟨hwv, hw'⟩)) huw
      have hupd : ∀ w ∈ insert v c.fv,
          σ[v := ⟦e⟧ₑ σ] w = σ'[vn := ⟦e⟧ₑ σ] (δ' w) := by
        intro w hw
        by_cases hwv : w = v
        · rw [hwv, hδ', Function.update_self]
          simp
        · have hw' : w ∈ c.fv := by
            rcases Finset.mem_insert.mp hw with h' | h'
            · exact absurd h' hwv
            · exact h'
          have hne : δ w ≠ vn := fun hEq => Comm.newBinder_ne hw' hwv hEq.symm
          rw [State.subst_of_ne _ _ _ _ hwv, hδ', Function.update_of_ne hwv,
            State.subst_of_ne _ _ _ _ hne]
          exact h w (herase (Finset.mem_erase.mpr ⟨hwv, hw'⟩))
      have hinner := ih δ' (insert v c.fv) hS' hinj' _ _ hupd
      -- 여기가 두 번째 자리다. 더 날카로운 어림이 `FA` 위의 단사성만 쓰게 한다.
      have hfa' : ∀ z ∈ S, δ z ≠ vn → (z = v ∨ z ∉ c.fv) → δ z ∉ (c /ᶜ δ').fa := by
        intro z hzS hzvn hz hmem
        obtain ⟨u, hu, huz⟩ := Finset.mem_image.mp (Comm.fa_subst_subset c δ' hmem)
        by_cases huv : u = v
        · rw [huv, hδ', Function.update_self] at huz
          exact hzvn huz.symm
        · rw [hδ', Function.update_of_ne huv] at huz
          have huz' : u = z :=
            hinj u (Finset.mem_erase.mpr ⟨huv, hu⟩) z hzS huz
          rcases hz with hzv | hznotc
          · exact huv (huz'.trans hzv)
          · exact hznotc (huz' ▸ Comm.fa_subset_fv c hu)
      change AgreeVia δ S (restore v σ (c.eval (σ[v := ⟦e⟧ₑ σ])))
        (restore vn σ' ((c /ᶜ δ').eval (σ'[vn := ⟦e /ₑ δ.toSubst⟧ₑ σ'])))
      rw [he]
      rcases h₁ : c.eval (σ[v := ⟦e⟧ₑ σ]) with _ | τ
        <;> rcases h₂ : (c /ᶜ δ').eval (σ'[vn := ⟦e⟧ₑ σ]) with _ | τ'
      · simp [restore]
      · rw [h₁, h₂] at hinner; exact absurd hinner (by simp)
      · rw [h₁, h₂] at hinner; exact absurd hinner (by simp)
      · rw [h₁, h₂] at hinner
        simp only [restore, Option.map_some]
        rw [AgreeVia.some_some]
        intro w hw
        by_cases hwv : w = v
        · have hvS : v ∈ S := hwv ▸ hw
          rw [hwv]
          simp only [State.subst_self]
          by_cases hδv : δ v = vn
          · rw [hδv]
            simp only [State.subst_self]
            rw [← hδv]
            exact h v hvS
          · rw [State.subst_of_ne _ _ _ _ hδv,
              Comm.eval_agree_outside_fa _ _ _ h₂ (δ v) (hfa' v hvS hδv (Or.inl rfl)),
              State.subst_of_ne _ _ _ _ hδv]
            exact h v hvS
        · rw [State.subst_of_ne _ _ _ _ hwv]
          by_cases hwc : w ∈ c.fv
          · have hτ := hinner w (Finset.mem_insert_of_mem hwc)
            rw [hδ', Function.update_of_ne hwv] at hτ
            have hne : δ w ≠ vn := fun hEq => Comm.newBinder_ne hwc hwv hEq.symm
            rw [State.subst_of_ne _ _ _ _ hne]
            exact hτ
          · have hτ : τ w = σ w := by
              have hwfa : w ∉ c.fa := fun hmem => hwc (Comm.fa_subset_fv c hmem)
              rw [Comm.eval_agree_outside_fa _ _ _ h₁ w hwfa,
                State.subst_of_ne _ _ _ _ hwv]
            by_cases hδw : δ w = vn
            · rw [hδw]
              simp only [State.subst_self]
              rw [hτ, ← hδw]
              exact h w hw
            · rw [State.subst_of_ne _ _ _ _ hδw,
                Comm.eval_agree_outside_fa _ _ _ h₂ (δ w) (hfa' w hw hδw (Or.inr hwc)),
                State.subst_of_ne _ _ _ _ hδw, hτ]
              exact h w hw
-- ANCHOR_END: substWeak

/--
**원래 명제 2.7 이 따름정리가 된다.** `FA(c) ⊆ FV(c) ⊆ S` 이므로 강한 조건이 약한
조건을 포함한다.
-/
theorem Comm.substitution_general_of_weak [HasFresh V] (c : Comm V) (δ : Ren V)
    (S : Finset V) (hS : c.fv ⊆ S)
    (hinj : ∀ u ∈ S, ∀ w ∈ S, δ u = δ w → u = w)
    (σ σ' : State V) (h : ∀ w ∈ S, σ w = σ' (δ w)) :
    AgreeVia δ S (c.eval σ) ((c /ᶜ δ).eval σ') :=
  Comm.substitution_weak c δ S hS
    (fun u hu => hinj u (hS (Comm.fa_subset_fv c hu))) σ σ' h

/-! ## 3. 약화가 실제 이득인가

새 조건이 옛 조건보다 진짜로 약한지 확인한다. 읽기만 하는 두 변수를 합치는 예에서
약한 조건은 성립하고 강한 조건은 깨진다. -/

-- ANCHOR: weakGain
/-- `z := x + y` — `x` 와 `y` 를 읽기만 하고 `z` 에만 쓴다. -/
def sumProg : Comm String := ⟪ z := x + y ⟫ᶜ

/-- `x` 와 `y` 를 같은 칸 `w` 로 합치는 이름 바꾸기. 단사가 아니다. -/
def mergeReads : Ren String := fun v => if v = "x" then "w" else if v = "y" then "w" else v

/--
**약화가 이득이다.** 읽기만 하는 두 변수를 합쳐도 약한 조건은 살아 있다.

- 강한 조건은 깨진다 — `x ≠ y` 인데 둘 다 `w` 로 간다.
- 약한 조건은 성립한다 — 대입되는 변수는 `z` 하나뿐이고, `z` 는 `w` 와 겹치지 않는다.

그러므로 `z := x + y` 에 이 별칭을 걸어도 치환 정리가 여전히 적용된다. 실제로
`z := w + w` 는 전제(`σ x = σ' w` 이고 `σ y = σ' w`) 아래에서 같은 값을 낸다 —
읽는 두 자리가 원래도 같은 값이었기 때문이다.
-/
theorem mergeReads_weak_ok :
    (∀ u ∈ sumProg.fa, ∀ w ∈ sumProg.fv, mergeReads u = mergeReads w → u = w)
      ∧ ¬ (∀ u ∈ sumProg.fv, ∀ w ∈ sumProg.fv, mergeReads u = mergeReads w → u = w) := by
  constructor
  · decide
  · intro hstrong
    have := hstrong "x" (by decide) "y" (by decide) (by decide)
    exact absurd this (by decide)
-- ANCHOR_END: weakGain

/-! ## 여기서 어디로 가나

연습 2.6·2.7·2.8 로 자유 변수와 별칭 쪽이 끝났다. 남은 것은 `for` 쪽이다 —
연습 2.9(제어 변수가 구간 밖으로 나가지 않는 `for`)와 2.10(`dotwice` 디슈가링의 종료성).
§2.6 에서 만든 `forV3` 와 정확 반복 정리가 재료다. -/

end Reynolds.Answers.Ch02.Ex
