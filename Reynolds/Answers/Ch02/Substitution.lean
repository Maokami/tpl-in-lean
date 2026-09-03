/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Answers.Ch02.FreeVars
public import Reynolds.Answers.Ch02.Notation
public import Reynolds.Answers.Ch01.Substitution

/-!
# §2.5 치환 (2) — 명령의 치환과 별칭

Reynolds §2.5 후반부에 대응한다. `FreeVars.lean` 이 전반부다.

## 명령의 치환은 변수를 변수로만 보낸다

1장의 치환 사상은 `⟨var⟩ → ⟨intexp⟩` 였다 — 변수 자리에 임의의 식을 넣을 수 있었다.
명령에서는 그것이 불가능하다. `x := e` 의 왼쪽과 `newvar v := e in c` 의 결합자는
**변수 자리**라서, `x` 를 `x + 1` 로 보내는 치환은 `x + 1 := e` 라는, 구문에 없는 것을
만들어 낸다. 그래서 명령의 치환 사상은 `⟨var⟩ → ⟨var⟩` 로 줄어든다.

형식화에서는 이 제약이 저절로 지켜진다. `Comm.subst` 의 타입에 `Ren V := V → V` 를
받게 하면, 변수 아닌 것을 넣는 치환은 아예 적을 수 없다.

## 치환 정리에 조건이 붙는다

1장의 치환 정리(명제 1.3)는 아무 치환 사상에나 성립했다. 명령 판(명제 2.7)에는
**단사(injective)** 가정이 붙는다. 서로 다른 두 변수가 같은 변수로 가면 — 이것이
**별칭(aliasing)** 이다 — 원래 프로그램에서 서로 다른 저장 공간이던 것이 치환 후에는
같은 공간이 되고, 한쪽에 쓴 값이 다른 쪽을 덮어쓴다. 읽기만 하는 식에서는 두 이름이
같은 값을 가리켜도 문제가 없지만, **쓰기가 있는 순간 이름의 수가 곧 공간의 수다.**

이 파일의 `swap` 예제가 그것을 실행해서 보인다. 세 변수로 맞바꾸기를 하는 프로그램에서
임시 변수를 `y` 와 별칭으로 만들면, 맞바꾸기가 망가진다.

## 읽는 순서
`FreeVars.lean` → 이 파일. 이후는 §2.6 (문법 설탕).

## 책과의 차이

- Reynolds 는 새 결합자를 "어떤 표준 순서에서 첫 번째" 로 정하고, 여기서는 1장과 같이
  `HasFresh.fresh` 로 뽑는다. 증명이 쓰는 성질은 신선함뿐이라 결론은 같다.
- 명제 2.7 은 1장 명제 1.3 처럼 상태 두 개를 잇는 형태로 적었고, 명제 2.6(a) 와 같은
  이유로 집합을 `S ⊇ FV(c)` 로 일반화해서 증명한다.
- `newvar` 결합자의 이름 바꾸기(α-변환)가 뜻을 보존한다는 것은 명제 2.7 의
  따름정리로 마지막 절에 두었다. 1장 명제 1.5 의 명령 판이다.
-/

@[expose] public section

namespace Reynolds.Answers.Ch02

open Reynolds Reynolds.Answers.Ch01

universe u

variable {V : Type u} [DecidableEq V]

/-! ## 1. 이름 바꾸기 사상

`Ren V` 는 명령이 감당할 수 있는 유일한 종류의 치환이다. 정수 식·불 식 쪽에는
1장의 일반 치환(`Subst V`)이 그대로 있으므로, 둘을 잇는 다리 `Ren.toSubst` 를 둔다. -/

-- ANCHOR: Ren
/--
명령의 치환 사상. Reynolds 의 `Δ = ⟨var⟩ → ⟨var⟩`.

1장의 `Subst V = V → IntExp V` 와 달리 변수를 **변수로만** 보낸다. 대입의 왼쪽과
`newvar` 의 결합자가 변수 자리이기 때문이다 — 타입이 반칙을 막는다.
-/
abbrev Ren (V : Type u) := V → V

/-- 이름 바꾸기를 1장의 일반 치환으로 읽는다. `w ↦ var (δ w)`. -/
def Ren.toSubst (δ : Ren V) : Subst V := fun w => .var (δ w)
-- ANCHOR_END: Ren

omit [DecidableEq V] in
@[simp] theorem Ren.toSubst_apply (δ : Ren V) (w : V) : δ.toSubst w = .var (δ w) := rfl

omit [DecidableEq V] in
/-- 항등 이름 바꾸기는 1장의 항등 치환이다. -/
theorem Ren.toSubst_id : Ren.toSubst (id : Ren V) = IntExp.var := rfl

/-- 이름 바꾸기 뒤의 자유 변수는 상(image)이다. 명제 1.2(c) 의 특수형인데,
`δ w` 가 변수 하나라 `biUnion` 이 `image` 로 줄어든다. -/
theorem IntExp.fv_rename (e : IntExp V) (δ : Ren V) :
    (e /ₑ δ.toSubst).fv = e.fv.image δ := by
  induction e with
  | num n => simp [IntExp.subst, IntExp.fv]
  | var v => simp [IntExp.subst, IntExp.fv]
  | neg e ih => simpa [IntExp.subst, IntExp.fv] using ih
  | bin op e₀ e₁ ih₀ ih₁ =>
      simp [IntExp.subst, IntExp.fv, ih₀, ih₁, Finset.image_union]

/-! ## 2. 불 식의 치환

조건 `b` 는 읽기만 하므로 1장의 일반 치환이 그대로 통한다. 양화사를 뺀 단언이라
`Assert.subst` 에서 양화사 절만 지운 모양이다. -/

/-- `b /ᵇ δ` — 불 식에 대한 동시 치환. 결합자가 없어 훑으며 갈아 끼우면 된다. -/
def BoolExp.subst : BoolExp V → Subst V → BoolExp V
  | .tru,          _ => .tru
  | .fls,          _ => .fls
  | .cmp c e₀ e₁,  δ => .cmp c (e₀ /ₑ δ) (e₁ /ₑ δ)
  | .not b,        δ => .not (b.subst δ)
  | .bin op b₀ b₁, δ => .bin op (b₀.subst δ) (b₁.subst δ)

@[inherit_doc BoolExp.subst]
scoped infixl:80 " /ᵇ " => BoolExp.subst

omit [DecidableEq V] in
/-- 불 식 판 명제 1.2(b) — 항등 치환은 구문을 바꾸지 않는다. -/
theorem BoolExp.subst_var (b : BoolExp V) : b /ᵇ IntExp.var = b := by
  induction b with
  | tru | fls => rfl
  | cmp c e₀ e₁ => simp [BoolExp.subst, subst_var_intExp]
  | not b ih => simp [BoolExp.subst, ih]
  | bin op b₀ b₁ ih₀ ih₁ => simp [BoolExp.subst, ih₀, ih₁]

/-- 불 식 판 명제 1.2(c) 의 특수형 — 이름 바꾸기 뒤의 자유 변수는 상이다. -/
theorem BoolExp.fv_rename (b : BoolExp V) (δ : Ren V) :
    (b /ᵇ δ.toSubst).fv = b.fv.image δ := by
  induction b with
  | tru | fls => simp [BoolExp.subst, BoolExp.fv]
  | cmp c e₀ e₁ => simp [BoolExp.subst, BoolExp.fv, IntExp.fv_rename, Finset.image_union]
  | not b ih => simpa [BoolExp.subst, BoolExp.fv] using ih
  | bin op b₀ b₁ ih₀ ih₁ =>
      simp [BoolExp.subst, BoolExp.fv, ih₀, ih₁, Finset.image_union]

-- ANCHOR: boolSubst
/--
**치환 정리, 불 식 판.** 구문을 먼저 바꾸고 평가하는 것과, 치환 사상을 먼저 평가해
상태를 만들고 거기서 평가하는 것이 같다.

명제 1.3 의 정수 식 판(`substitution_intExp`)을 절마다 이어 붙인다 —
`BoolExp.fv_coincidence` 가 일치 정리에서 했던 것과 같은 일이다.
-/
@[exercise "§2.5 bool-subst" 1]
theorem substitution_boolExp :
    ∀ (b : BoolExp V) (δ : Subst V) (σ σ' : State V),
      (∀ w ∈ b.fv, σ w = ⟦δ w⟧ₑ σ') → ⟦b /ᵇ δ⟧ᵇ σ' = ⟦b⟧ᵇ σ := by
  intro b
  induction b with
  | tru => intro _ _ _ _; rfl
  | fls => intro _ _ _ _; rfl
  | cmp c e₀ e₁ =>
      intro δ σ σ' h
      have h₀ := substitution_intExp e₀ δ σ σ' fun w hw => h w (by simp [BoolExp.fv, hw])
      have h₁ := substitution_intExp e₁ δ σ σ' fun w hw => h w (by simp [BoolExp.fv, hw])
      simp [BoolExp.subst, BoolExp.eval, h₀, h₁]
  | not b ih => intro δ σ σ' h; simp [BoolExp.subst, BoolExp.eval, ih δ σ σ' h]
  | bin op b₀ b₁ ih₀ ih₁ =>
      intro δ σ σ' h
      have h₀ := ih₀ δ σ σ' fun w hw => h w (by simp [BoolExp.fv, hw])
      have h₁ := ih₁ δ σ σ' fun w hw => h w (by simp [BoolExp.fv, hw])
      simp [BoolExp.subst, BoolExp.eval, h₀, h₁]
-- ANCHOR_END: boolSubst

/-! ## 3. 새 결합 변수 고르기

`newvar v := e in c` 에 `δ` 를 적용할 때 `v` 를 그대로 두면, 본문의 다른 자유 변수가
`δ` 로 가서 `v` 와 겹칠 수 있다 — 1장 양화사의 포획과 같은 문제다. 피해야 할 집합을
모으고 그 밖에서 새 이름을 뽑는다. `δ w` 가 변수 하나라 집합이 상으로 줄어든다. -/

/-- `newvar v` 를 `δ` 로 치환할 때 새 결합자가 피해야 할 변수들.
본문의 자유 변수 중 `v` 아닌 것들이 `δ` 로 가서 되는 이름 전부다. -/
def Comm.captureSet (c : Comm V) (v : V) (δ : Ren V) : Finset V :=
  (c.fv.erase v).image δ

/-- 새 결합 변수. `v` 자체가 안전하면 그대로 쓰고, 아니면 `HasFresh` 로 새로 뽑는다. -/
def Comm.newBinder [HasFresh V] (c : Comm V) (v : V) (δ : Ren V) : V :=
  if v ∈ c.captureSet v δ then Cslib.HasFresh.fresh (c.captureSet v δ) else v

/-- 새 결합 변수는 어느 분기를 타든 피해야 할 집합 밖에 있다. -/
theorem Comm.newBinder_notMem [HasFresh V] (c : Comm V) (v : V) (δ : Ren V) :
    c.newBinder v δ ∉ c.captureSet v δ := by
  unfold Comm.newBinder
  split
  · exact Cslib.HasFresh.fresh_notMem _
  · assumption

/-- `w` 가 본문의 자유 변수이고 `v` 가 아니면, 새 결합자는 `δ w` 와 다르다. -/
theorem Comm.newBinder_ne [HasFresh V] {c : Comm V} {v w : V} {δ : Ren V}
    (hw : w ∈ c.fv) (hne : w ≠ v) : c.newBinder v δ ≠ δ w := by
  intro h
  exact c.newBinder_notMem v δ
    (Finset.mem_image.mpr ⟨w, Finset.mem_erase.mpr ⟨hne, hw⟩, h.symm⟩)

/-! ## 4. 명령의 치환 -/

-- ANCHOR: commSubst
/--
`c /ᶜ δ` — 명령에 대한 동시 이름 바꾸기.

대입의 왼쪽은 `δ v` 로, 오른쪽 식과 조건 식은 1장의 치환으로 처리한다.
`newvar` 절은 1장의 양화사 절과 같은 수법이다 — 결합자를 새 이름으로 바꾸고,
치환 사상 쪽에서도 `v` 를 새 이름으로 보내도록 고친다.
-/
def Comm.subst [HasFresh V] : Comm V → Ren V → Comm V
  | .assign v e,   δ => .assign (δ v) (e /ₑ δ.toSubst)
  | .skip,         _ => .skip
  | .seq c₀ c₁,    δ => .seq (c₀.subst δ) (c₁.subst δ)
  | .ite b c₀ c₁,  δ => .ite (b /ᵇ δ.toSubst) (c₀.subst δ) (c₁.subst δ)
  | .wh b c,       δ => .wh (b /ᵇ δ.toSubst) (c.subst δ)
  | .newvar v e c, δ =>
      .newvar (c.newBinder v δ) (e /ₑ δ.toSubst)
        (c.subst (Function.update δ v (c.newBinder v δ)))
-- ANCHOR_END: commSubst

@[inherit_doc Comm.subst]
scoped infixl:80 " /ᶜ " => Comm.subst

-- ANCHOR: substId
/--
**항등 이름 바꾸기는 명령을 바꾸지 않는다.** 명제 1.2(b) 의 명령 판.

`newvar` 절에서는 피해야 할 집합이 `FV(c) \ {v}` 로 줄어들어 `v` 가 안전하고,
결합자가 그대로 남는다. 그 다음 `id` 를 `v` 자리에서 `v` 로 덮어써도 `id` 라는 것을
함수 외연성으로 확인하면 귀납 가설이 이어진다.
-/
@[exercise "§2.5 subst-id" 2]
theorem Comm.subst_id [HasFresh V] : ∀ c : Comm V, c /ᶜ id = c := by
  intro c
  induction c with
  | assign v e => simp [Comm.subst, Ren.toSubst_id, subst_var_intExp]
  | «skip» => rfl
  | seq c₀ c₁ ih₀ ih₁ => simp [Comm.subst, ih₀, ih₁]
  | ite b c₀ c₁ ih₀ ih₁ =>
      simp [Comm.subst, Ren.toSubst_id, BoolExp.subst_var, ih₀, ih₁]
  | wh b c ih => simp [Comm.subst, Ren.toSubst_id, BoolExp.subst_var, ih]
  | «newvar» v e c ih =>
      have hbind : c.newBinder v id = v := by
        simp [Comm.newBinder, Comm.captureSet, Finset.image_id]
      have hupd : Function.update (id : Ren V) v v = id := by
        funext w; by_cases hwv : w = v <;> simp [hwv]
      simp [Comm.subst, hbind, hupd, Ren.toSubst_id, subst_var_intExp, ih]
-- ANCHOR_END: substId

/-- **치환 뒤의 자유 변수는 상 안에 있다.** 명제 1.2(c) 의 명령 판.

등식이 아니라 포함인 것은 `newvar` 때문이다 — 새 결합자를 지우는 자리에서
한쪽 방향만 남는다. 명제 2.7 의 증명에는 이 방향이면 충분하다. -/
theorem Comm.fv_subst_subset [HasFresh V] :
    ∀ (c : Comm V) (δ : Ren V), (c /ᶜ δ).fv ⊆ c.fv.image δ := by
  intro c
  induction c with
  | assign v e =>
      intro δ
      simp [Comm.subst, Comm.fv, IntExp.fv_rename, Finset.image_insert]
  | «skip» => intro δ; simp [Comm.subst, Comm.fv]
  | seq c₀ c₁ ih₀ ih₁ =>
      intro δ
      simpa [Comm.subst, Comm.fv, Finset.image_union] using
        Finset.union_subset_union (ih₀ δ) (ih₁ δ)
  | ite b c₀ c₁ ih₀ ih₁ =>
      intro δ
      simp only [Comm.subst, Comm.fv, Finset.image_union, BoolExp.fv_rename]
      exact Finset.union_subset_union (Finset.union_subset_union (le_refl _) (ih₀ δ)) (ih₁ δ)
  | wh b c ih =>
      intro δ
      simp only [Comm.subst, Comm.fv, Finset.image_union, BoolExp.fv_rename]
      exact Finset.union_subset_union (le_refl _) (ih δ)
  | «newvar» v e c ih =>
      intro δ
      simp only [Comm.subst, Comm.fv, Finset.image_union, IntExp.fv_rename]
      refine Finset.union_subset_union (le_refl _) ?_
      -- 지워진 새 결합자 쪽. `δ'` 의 상에서 새 결합자가 아닌 것은 `δ` 의 상이다.
      intro w hw
      obtain ⟨hwne, hwmem⟩ := Finset.mem_erase.mp hw
      obtain ⟨u, hu, huw⟩ := Finset.mem_image.mp (ih _ hwmem)
      by_cases huv : u = v
      · subst huv
        rw [Function.update_self] at huw
        exact absurd huw.symm hwne
      · rw [Function.update_of_ne huv] at huw
        exact Finset.mem_image.mpr ⟨u, Finset.mem_erase.mpr ⟨huv, hu⟩, huw⟩

/-! ## 5. `AgreeVia` — 이름 바꾸기를 사이에 둔 "같다"

명제 2.6 의 `AgreeOn` 은 두 결과를 같은 이름끼리 비교했다. 여기서는 원래 프로그램의
`w` 를 치환된 프로그램의 `δ w` 와 비교해야 하므로, 사상을 사이에 둔 판이 필요하다. -/

-- ANCHOR: agreeVia
/-- `δ` 를 사이에 둔 `S` 위에서의 일치. 원래 결과의 `w` 값과 치환된 결과의 `δ w` 값을
비교한다. `δ = id` 로 두면 `AgreeOn` 이다. -/
def AgreeVia (δ : Ren V) (S : Finset V) : SigmaBot V → SigmaBot V → Prop
  | none,   none    => True
  | some τ, some τ' => ∀ w ∈ S, τ w = τ' (δ w)
  | _,      _       => False
-- ANCHOR_END: agreeVia

omit [DecidableEq V] in
@[simp] theorem AgreeVia.none_none {δ : Ren V} {S : Finset V} :
    AgreeVia δ S none none := trivial

omit [DecidableEq V] in
@[simp] theorem AgreeVia.some_some {δ : Ren V} {S : Finset V} {τ τ' : State V} :
    AgreeVia δ S (some τ) (some τ') ↔ ∀ w ∈ S, τ w = τ' (δ w) := Iff.rfl

omit [DecidableEq V] in
@[simp] theorem AgreeVia.none_some {δ : Ren V} {S : Finset V} {τ : State V} :
    ¬ AgreeVia δ S none (some τ) := fun h => h

omit [DecidableEq V] in
@[simp] theorem AgreeVia.some_none {δ : Ren V} {S : Finset V} {τ : State V} :
    ¬ AgreeVia δ S (some τ) none := fun h => h

omit [DecidableEq V] in
/--
**`AgreeVia` 는 극한을 통과한다.**

증명이 `AgreeOn.admissible` 과 글자까지 거의 같다 — 평평함 논증은 두 상태를 잇는
관계의 **내용**을 보지 않는다. 극한이 결정되는 단계까지 내려가서 단계별 가정을 읽을
뿐이다. 그 연습을 풀었다면 이것은 복습이다. 사슬이 둘로 늘어난 것만 다르다 —
이번에는 왼쪽과 오른쪽이 서로 다른 프로그램의 반복 사슬이다.
-/
theorem AgreeVia.admissible (δ : Ren V) (S : Finset V)
    (d d' : Chain (State V → SigmaBot V)) {σ σ' : State V}
    (h : ∀ n, AgreeVia δ S (d.seq n σ) (d'.seq n σ')) :
    AgreeVia δ S (d.lub σ) (d'.lub σ') := by
  rw [Chain.lub_apply, Chain.lub_apply]
  rcases hσ : (d.apply σ).lub with _ | τ
  · -- 왼쪽 극한이 `⊥` — 왼쪽 사슬이 전부 `⊥` 였고, 일치가 오른쪽도 전부 `⊥` 로 만든다.
    have hall : ∀ n, d'.seq n σ' = none := by
      intro n
      have hn := (d.apply σ).le_lub n
      rw [hσ] at hn
      simp only [Option.le_none_iff, Chain.apply_seq] at hn
      have := h n
      rw [hn] at this
      rcases hn' : d'.seq n σ' with _ | τ'
      · rfl
      · rw [hn'] at this; exact absurd this (by simp)
    have : (d'.apply σ').lub ≤ none :=
      (d'.apply σ').lub_le fun n => by rw [Chain.apply_seq, hall n]
    simp only [Option.le_none_iff] at this
    rw [this]
    simp
  · -- 왼쪽 극한이 상태 — 결정 시점 둘의 최댓값에서 두 극한을 함께 읽는다.
    obtain ⟨k, hk⟩ := (d.apply σ).flat_lub_mem_range
    rw [hσ] at hk
    rcases hσ' : (d'.apply σ').lub with _ | τ'
    · -- 오른쪽만 `⊥` 일 수는 없다.
      have hk' : d'.seq k σ' = none := by
        have hn := (d'.apply σ').le_lub k
        rw [hσ'] at hn
        simpa using hn
      have := h k
      rw [show d.seq k σ = some τ from hk, hk'] at this
      exact absurd this (by simp)
    · obtain ⟨k', hk'⟩ := (d'.apply σ').flat_lub_mem_range
      rw [hσ'] at hk'
      have hm : d.seq (max k k') σ = some τ :=
        Chain.flat_stabilizes (c := d.apply σ) hk (max k k') (le_max_left _ _)
      have hm' : d'.seq (max k k') σ' = some τ' :=
        Chain.flat_stabilizes (c := d'.apply σ') hk' (max k k') (le_max_right _ _)
      have := h (max k k')
      rw [hm, hm'] at this
      exact this

/-! ## 6. 명제 2.7 — 치환 정리

원래 프로그램을 `σ` 에서, 치환된 프로그램을 `σ'` 에서 돌린다. 두 상태가 `δ` 를 사이에
두고 일치하면 — `σ w = σ' (δ w)` — 두 결과도 그렇게 일치한다.

가정이 둘 붙는다.

- **`S ⊇ FV(c)` 로의 일반화.** 명제 2.6(a) 와 똑같은 이유다 — `seq` 케이스에서
  `c₀` 의 귀납 가설이 주는 일치가 `FV(c₀)` 위뿐이면 `c₁` 이 읽는 나머지를 잇지 못한다.
- **`S` 위에서의 단사.** 1장에는 없던 가정이다. 왜 필요한지는 §7 의 반례가 보인다 —
  대입이 있는 언어에서 두 이름이 하나로 합쳐지면 저장 공간도 하나로 합쳐진다.

`while` 케이스는 명제 2.6(a) 보다 한 단계 어렵다. 왼쪽과 오른쪽이 **서로 다른**
연산자의 최소 고정점이라 `scott_induction` 하나로는 안 되고, 두 반복 사슬
`Fⁿ(⊥)`, `Gⁿ(⊥)` 을 나란히 세워 단계별로 관계를 증명한 뒤 `AgreeVia.admissible` 로
극한에 올린다. -/

-- ANCHOR: prop27
/--
**명제 2.7 (치환 정리), 강화판** — `δ` 가 `S ⊇ FV(c)` 위에서 단사이고 두 입력이
`δ` 를 사이에 두고 `S` 위에서 일치하면, 두 결과도 그렇게 일치한다.

채점 연습이 아니다. 증명이 명제 1.3, 명제 2.6, Scott 귀납법 위에 서 있고 그중 여럿이
이미 연습이라, 비우면 비운 것끼리 의존한다 (연습 독립성 원칙). `newvar` 절이 이 절의
심장이니 완성본으로 읽어 두라 — 새 결합자의 신선함과 단사 가정이 각각 어느 등식을
지키는지가 그 절에 다 있다.
-/
theorem Comm.substitution_general [HasFresh V] :
    ∀ (c : Comm V) (δ : Ren V) (S : Finset V), c.fv ⊆ S →
      (∀ u ∈ S, ∀ w ∈ S, δ u = δ w → u = w) →
      ∀ σ σ' : State V, (∀ w ∈ S, σ w = σ' (δ w)) →
      AgreeVia δ S (c.eval σ) ((c /ᶜ δ).eval σ') := by
  intro c
  induction c with
  | assign v e =>
      intro δ S hS hinj σ σ' h
      have hv : v ∈ S := hS (by simp [Comm.fv])
      have he : ⟦e /ₑ δ.toSubst⟧ₑ σ' = ⟦e⟧ₑ σ :=
        substitution_intExp e δ.toSubst σ σ' fun w hw =>
          h w (hS (by simp [Comm.fv, hw]))
      change AgreeVia δ S (some (σ[v := ⟦e⟧ₑ σ])) (some (σ'[δ v := ⟦e /ₑ δ.toSubst⟧ₑ σ']))
      rw [AgreeVia.some_some, he]
      intro w hw
      by_cases hwv : w = v
      · subst hwv; simp
      · have hδ : δ w ≠ δ v := fun hEq => hwv (hinj w hw v hv hEq)
        simp [hwv, hδ, h w hw]
  | «skip» =>
      intro δ S _ _ σ σ' h
      exact h
  | seq c₀ c₁ ih₀ ih₁ =>
      intro δ S hS hinj σ σ' h
      have hS₀ : c₀.fv ⊆ S := le_trans Finset.subset_union_left hS
      have hS₁ : c₁.fv ⊆ S := le_trans Finset.subset_union_right hS
      change AgreeVia δ S (Option.bind (c₀.eval σ) c₁.eval)
        (Option.bind ((c₀ /ᶜ δ).eval σ') (c₁ /ᶜ δ).eval)
      have h₀ := ih₀ δ S hS₀ hinj σ σ' h
      rcases h₀₁ : c₀.eval σ with _ | τ <;> rcases h₀₂ : (c₀ /ᶜ δ).eval σ' with _ | τ'
      · simp
      · rw [h₀₁, h₀₂] at h₀; exact absurd h₀ (by simp)
      · rw [h₀₁, h₀₂] at h₀; exact absurd h₀ (by simp)
      · rw [h₀₁, h₀₂] at h₀
        exact ih₁ δ S hS₁ hinj τ τ' h₀
  | ite b c₀ c₁ ih₀ ih₁ =>
      intro δ S hS hinj σ σ' h
      have hb : ⟦b /ᵇ δ.toSubst⟧ᵇ σ' = ⟦b⟧ᵇ σ :=
        substitution_boolExp b δ.toSubst σ σ' fun w hw =>
          h w (hS (by simp [Comm.fv, hw]))
      change AgreeVia δ S (if ⟦b⟧ᵇ σ then _ else _) (if ⟦b /ᵇ δ.toSubst⟧ᵇ σ' then _ else _)
      rw [hb]
      by_cases hbσ : ⟦b⟧ᵇ σ
      · simp only [if_pos hbσ]
        exact ih₀ δ S (le_trans (le_trans Finset.subset_union_left
          Finset.subset_union_right) (by simpa [Comm.fv, Finset.union_assoc] using hS))
          hinj σ σ' h
      · simp only [if_neg hbσ]
        exact ih₁ δ S (le_trans Finset.subset_union_right hS) hinj σ σ' h
  | wh b c ihc =>
      intro δ S hS hinj σ σ' h
      have hSb : b.fv ⊆ S := le_trans Finset.subset_union_left hS
      have hSc : c.fv ⊆ S := le_trans Finset.subset_union_right hS
      -- 두 반복 사슬을 나란히 세운다.
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
              have hbody := ihc δ S hSc hinj σ σ' hσσ'
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
      -- 새 결합자와 고쳐진 치환 사상.
      set vn := c.newBinder v δ with hvn
      set δ' := Function.update δ v vn with hδ'
      have herase : c.fv.erase v ⊆ S := le_trans Finset.subset_union_right hS
      have he : ⟦e /ₑ δ.toSubst⟧ₑ σ' = ⟦e⟧ₑ σ :=
        substitution_intExp e δ.toSubst σ σ' fun w hw =>
          h w (hS (by simp [Comm.fv, hw]))
      -- 안쪽은 `insert v c.fv` 위에서 돌린다.
      have hS' : c.fv ⊆ insert v c.fv := Finset.subset_insert _ _
      -- 새 결합자는 본문의 다른 자유 변수가 `δ` 로 가서 되는 이름과 겹치지 않는다.
      have hvn_ne : ∀ w ∈ c.fv, w ≠ v → vn ≠ δ w := by
        intro w hw hwv; rw [hvn]; exact Comm.newBinder_ne hw hwv
      have hinj' : ∀ u ∈ insert v c.fv, ∀ w ∈ insert v c.fv, δ' u = δ' w → u = w := by
        intro u hu w hw huw
        by_cases huv : u = v <;> by_cases hwv : w = v
        · rw [huv, hwv]
        · have hw' : w ∈ c.fv := (Finset.mem_insert.mp hw).resolve_left hwv
          rw [huv, hδ', Function.update_self, Function.update_of_ne hwv] at huw
          exact absurd huw (hvn_ne w hw' hwv)
        · have hu' : u ∈ c.fv := (Finset.mem_insert.mp hu).resolve_left huv
          rw [hwv, hδ', Function.update_self, Function.update_of_ne huv] at huw
          exact absurd huw.symm (hvn_ne u hu' huv)
        · have hu' : u ∈ c.fv := (Finset.mem_insert.mp hu).resolve_left huv
          have hw' : w ∈ c.fv := (Finset.mem_insert.mp hw).resolve_left hwv
          rw [hδ', Function.update_of_ne huv, Function.update_of_ne hwv] at huw
          exact hinj u (herase (Finset.mem_erase.mpr ⟨huv, hu'⟩)) w
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
      -- `δ z ∉ FA(c /ᶜ δ')` 를 두 자리에서 쓴다. 공통 인수를 뽑아 둔다.
      have hfa' : ∀ z ∈ S, δ z ≠ vn → (z = v ∨ z ∉ c.fv) → δ z ∉ (c /ᶜ δ').fa := by
        intro z hzS hzvn hz hmem
        have hsub : (c /ᶜ δ').fa ⊆ c.fv.image δ' :=
          le_trans (Comm.fa_subset_fv _) (Comm.fv_subst_subset c δ')
        obtain ⟨u, hu, huz⟩ := Finset.mem_image.mp (hsub hmem)
        by_cases huv : u = v
        · subst huv
          rw [hδ', Function.update_self] at huz
          exact hzvn huz.symm
        · rw [hδ', Function.update_of_ne huv] at huz
          -- `δ u = δ z`, 둘 다 `S` 에 있으므로 단사가 `u = z` 를 준다. 그런데 `z` 는
          -- `v` 이거나 `c` 의 자유 변수가 아니다 — 어느 쪽이든 `u` 와 모순이다.
          have huz' : u = z :=
            hinj u (herase (Finset.mem_erase.mpr ⟨huv, hu⟩)) z hzS huz
          rcases hz with hzv | hznotc
          · exact huv (huz'.trans hzv)
          · exact hznotc (huz' ▸ hu)
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
        · -- 복원 자리. 왼쪽은 `σ v` 로 돌아왔다. 오른쪽은 `δ v` 가 `vn` 인지로 갈린다.
          have hvS : v ∈ S := hwv ▸ hw
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
          · -- 본문이 관리한 변수. 안쪽 일치가 바로 잇는다.
            have hτ := hinner w (Finset.mem_insert_of_mem hwc)
            rw [hδ', Function.update_of_ne hwv] at hτ
            have hne : δ w ≠ vn := fun hEq => Comm.newBinder_ne hwc hwv hEq.symm
            rw [State.subst_of_ne _ _ _ _ hne]
            exact hτ
          · -- 본문 밖 변수. 양쪽 다 입력이 그대로 흘러나온 값이다 (명제 2.6(b)).
            have hτ : τ w = σ w := by
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
-- ANCHOR_END: prop27

/-- **명제 2.7, Reynolds 의 진술** — `S := FV(c)` 로 둔 판. -/
theorem Comm.substitution [HasFresh V] (c : Comm V) (δ : Ren V)
    (hinj : ∀ u ∈ c.fv, ∀ w ∈ c.fv, δ u = δ w → u = w)
    (σ σ' : State V) (h : ∀ w ∈ c.fv, σ w = σ' (δ w)) :
    AgreeVia δ c.fv (c.eval σ) ((c /ᶜ δ).eval σ') :=
  Comm.substitution_general c δ c.fv (le_refl _) hinj σ σ' h

/-! ## 7. 별칭 — 단사 가정은 뺄 수 없다

세 변수로 맞바꾸기를 하는 고전적인 프로그램에 이름 바꾸기를 걸어 본다.
단사인 이름 바꾸기는 명제 2.7 이 지켜 주지만, `t` 와 `y` 를 같은 변수로 보내는 —
별칭을 만드는 — 이름 바꾸기는 프로그램의 행동 자체를 바꾼다. -/

-- ANCHOR: swap
/-- 임시 변수 `t` 를 거쳐 `x` 와 `y` 를 맞바꾼다. -/
def swap : Comm String := ⟪ t := x; x := y; y := t ⟫ᶜ

/--
**맞바꾸기는 맞바꾼다.** `while` 이 없으므로 `Comm.eval` 이 정의 등식만으로 끝까지
계산되고, 결과 상태에서 `x` 와 `y` 를 읽으면 된다.
-/
@[exercise "§2.5 swap" 1]
theorem swap_ok (σ : State String) :
    ∃ τ, swap.eval σ = some τ ∧ τ "x" = σ "y" ∧ τ "y" = σ "x" := by
  refine ⟨_, rfl, ?_, ?_⟩ <;> simp [IntExp.eval, State.subst_def, Function.update]
-- ANCHOR_END: swap

-- ANCHOR: alias
/-- `t ↦ y` — 임시 변수를 `y` 와 겹치게 만드는 이름 바꾸기. `t` 와 `y` 가 같은 곳으로
가므로 단사가 아니다. -/
def aliasTY : Ren String := fun w => if w = "t" then "y" else w

/--
별칭이 생긴 맞바꾸기 `y := x; x := y; y := y` 는 맞바꾸지 못한다 —
`t` 자리에 들어온 `y` 가 첫 대입에서 덮어써져, **두 변수 모두 옛 `x` 값**이 된다.
-/
theorem swap_aliased_eval (σ : State String) :
    ∃ τ, (swap /ᶜ aliasTY).eval σ = some τ ∧ τ "x" = σ "x" ∧ τ "y" = σ "x" := by
  refine ⟨_, rfl, ?_, ?_⟩ <;>
    simp [aliasTY, IntExp.eval, IntExp.subst, Ren.toSubst, State.subst_def, Function.update]

/--
**단사 가정을 빼면 명제 2.7 은 거짓이다.**

증인: `swap` 에 `aliasTY` 를 걸고, `δ` 를 사이에 둔 일치를 만족하는 입력쌍에서 돌린다.
원래 쪽은 `x` 가 옛 `y` 값 `1` 이 되고, 별칭 쪽은 `x` 가 옛 `x` 값 `0` 그대로다.
`AgreeVia` 가 두 값을 같다고 주장하는 순간 `1 = 0` 이 나온다.

읽기만 있는 1장에서는 두 이름이 한 값을 가리켜도 아무 일이 없었다. 대입이 생기는
순간 이름의 수가 곧 저장 공간의 수가 되고, 이름을 합치는 치환은 공간을 합쳐 버린다.
-/
theorem substitution_needs_injective :
    ¬ (∀ (c : Comm String) (δ : Ren String) (σ σ' : State String),
        (∀ w ∈ c.fv, σ w = σ' (δ w)) →
        AgreeVia δ c.fv (c.eval σ) ((c /ᶜ δ).eval σ')) := by
  intro hclaim
  -- σ' 는 x = 0, y = 1. σ 는 같은 값에 t 만 1 — `δ t = y` 이므로 `σ t = σ' y` 여야 한다.
  have h := hclaim swap aliasTY
    ((State.const 0)["y" := (1 : Int)]["t" := (1 : Int)])
    ((State.const 0)["y" := (1 : Int)])
    (by
      intro w hw
      have hcases : w = "t" ∨ w = "x" ∨ w = "y" := by
        simpa [swap, Comm.fv, IntExp.fv, or_comm, or_assoc, or_left_comm] using hw
      rcases hcases with rfl | rfl | rfl <;> simp [aliasTY, State.const])
  obtain ⟨τ, hτ, hτx, -⟩ := swap_ok ((State.const 0)["y" := (1 : Int)]["t" := (1 : Int)])
  obtain ⟨τ', hτ', hτ'x, -⟩ := swap_aliased_eval ((State.const 0)["y" := (1 : Int)])
  rw [hτ, hτ'] at h
  have hx := (AgreeVia.some_some.mp h) "x" (by simp [swap, Comm.fv, IntExp.fv])
  -- τ "x" = τ' (aliasTY "x") = τ' "x" 인데, 왼쪽은 1 이고 오른쪽은 0 이다.
  rw [hτx, show aliasTY "x" = "x" from rfl, hτ'x] at hx
  simp [State.const] at hx
-- ANCHOR_END: alias

/-! ## 8. 따름정리 — 지역 변수의 이름은 뜻이 아니다

명제 2.7 의 첫 수확이다. `newvar` 의 결합자를 신선한 이름으로 바꿔도 명령의 뜻이
그대로다 — 1장 명제 1.5(이름 바꾸기 정리)의 명령 판이고, "결합 변수는 이름이 아니라
자리"라는 원칙이 명령형 언어에서도 성립한다는 확인이다.

이름 바꾸기 `v ↦ vnew` 는 단사다 — 신선함이 `vnew` 를 본문의 다른 자유 변수와
갈라놓기 때문이다. 그래서 명제 2.7 이 적용되고, 별칭 걱정 없이 결론을 얻는다. -/

-- ANCHOR: newvarRename
/--
**지역 변수 이름 바꾸기.** `vnew ∉ FV(c) \ {v}` 이면

```
⟦newvar vnew := e in (c / v ↦ vnew)⟧ = ⟦newvar v := e in c⟧
```

초기값 `e` 는 결합 범위 밖이라 그대로다. 증명은 명제 2.7 에 `δ := id[v ↦ vnew]` 를
넣고, 복원(restore) 단계에서 어긋나는 두 변수 `v` 와 `vnew` 를 명제 2.6(b) 로 맞춘다.
-/
theorem Comm.newvar_rename [HasFresh V] (v vnew : V) (e : IntExp V) (c : Comm V)
    (hfresh : vnew ∉ c.fv.erase v) :
    (Comm.newvar vnew e (c /ᶜ Function.update id v vnew)).eval
      = (Comm.newvar v e c).eval := by
  by_cases hvv : vnew = v
  · -- 같은 이름으로 바꾸는 경우 — 치환이 항등이라 구문부터 같다.
    have hid : Function.update (id : Ren V) v vnew = id := by
      funext w
      by_cases hwv : w = v
      · simp [hwv, hvv, Function.update_self]
      · simp [Function.update_of_ne hwv]
    rw [hid, Comm.subst_id, hvv]
  · funext σ
    set δ₀ : Ren V := Function.update id v vnew with hδ₀
    have hδ₀v : δ₀ v = vnew := by rw [hδ₀]; exact Function.update_self ..
    have hδ₀ne : ∀ w, w ≠ v → δ₀ w = w := fun w hw => by
      simp [hδ₀, Function.update_of_ne hw]
    have hnotc : vnew ∉ c.fv := fun hmem =>
      hfresh (Finset.mem_erase.mpr ⟨hvv, hmem⟩)
    -- 명제 2.7 을 `S := insert v c.fv` 에서 적용한다.
    have hinj : ∀ u ∈ insert v c.fv, ∀ w ∈ insert v c.fv, δ₀ u = δ₀ w → u = w := by
      intro u hu w hw huw
      by_cases huv : u = v <;> by_cases hwv : w = v
      · rw [huv, hwv]
      · rw [huv, hδ₀v] at huw
        rw [hδ₀ne w hwv] at huw
        have hw' : w ∈ c.fv := by
          rcases Finset.mem_insert.mp hw with h' | h'
          · exact absurd h' hwv
          · exact h'
        exact absurd (huw ▸ hw') hnotc
      · rw [hwv, hδ₀v] at huw
        rw [hδ₀ne u huv] at huw
        have hu' : u ∈ c.fv := by
          rcases Finset.mem_insert.mp hu with h' | h'
          · exact absurd h' huv
          · exact h'
        exact absurd (huw ▸ hu') hnotc
      · rw [hδ₀ne u huv, hδ₀ne w hwv] at huw
        exact huw
    have hagree : ∀ w ∈ insert v c.fv,
        σ[v := ⟦e⟧ₑ σ] w = σ[vnew := ⟦e⟧ₑ σ] (δ₀ w) := by
      intro w hw
      by_cases hwv : w = v
      · rw [hwv, hδ₀v]; simp
      · have hw' : w ∈ c.fv := by
          rcases Finset.mem_insert.mp hw with h' | h'
          · exact absurd h' hwv
          · exact h'
        have hwnew : w ≠ vnew := fun hEq => hnotc (hEq ▸ hw')
        rw [hδ₀ne w hwv, State.subst_of_ne _ _ _ _ hwv, State.subst_of_ne _ _ _ _ hwnew]
    have hmain := Comm.substitution_general c δ₀ (insert v c.fv)
      (Finset.subset_insert _ _) hinj _ _ hagree
    -- `z ∉ FA(c /ᶜ δ₀)` 판정. 복원 단계에서 두 번 쓴다.
    have hfa' : ∀ z, z ≠ vnew → (z = v ∨ z ∉ c.fv) → z ∉ (c /ᶜ δ₀).fa := by
      intro z hzn hz hmem
      have hsub : (c /ᶜ δ₀).fa ⊆ c.fv.image δ₀ :=
        le_trans (Comm.fa_subset_fv _) (Comm.fv_subst_subset c δ₀)
      obtain ⟨u, hu, huz⟩ := Finset.mem_image.mp (hsub hmem)
      by_cases huv : u = v
      · rw [huv, hδ₀v] at huz; exact hzn huz.symm
      · rw [hδ₀ne u huv] at huz
        rcases hz with hzv | hznotc
        · exact huv (huz.trans hzv)
        · exact hznotc (huz ▸ hu)
    -- 양변을 복원까지 펼친다. 초기값 `e` 는 결합 범위 밖이라 왼쪽도 그대로 `e` 다.
    change restore vnew σ ((c /ᶜ δ₀).eval (σ[vnew := ⟦e⟧ₑ σ]))
      = restore v σ (c.eval (σ[v := ⟦e⟧ₑ σ]))
    rcases h₁ : c.eval (σ[v := ⟦e⟧ₑ σ]) with _ | τ
      <;> rcases h₂ : (c /ᶜ δ₀).eval (σ[vnew := ⟦e⟧ₑ σ]) with _ | τ'
    · rfl
    · rw [h₁, h₂] at hmain; exact absurd hmain (by simp)
    · rw [h₁, h₂] at hmain; exact absurd hmain (by simp)
    · rw [h₁, h₂] at hmain
      simp only [restore, Option.map_some, Option.some.injEq]
      funext u
      by_cases hun : u = vnew
      · -- 복원된 `vnew`. 오른쪽에서는 본문이 `vnew` 를 안 건드렸다 (명제 2.6(b)).
        have hufa : vnew ∉ c.fa := fun hmem => hnotc (Comm.fa_subset_fv c hmem)
        rw [hun]
        simp only [State.subst_self]
        rw [State.subst_of_ne _ _ _ _ hvv,
          Comm.eval_agree_outside_fa _ _ _ h₁ vnew hufa,
          State.subst_of_ne _ _ _ _ hvv]
      · rw [State.subst_of_ne _ _ _ _ hun]
        by_cases huv : u = v
        · -- 복원된 `v`. 왼쪽에서는 본문이 `v` 를 안 건드렸다.
          have hvne : v ≠ vnew := fun hEq => hvv hEq.symm
          rw [huv]
          simp only [State.subst_self]
          rw [Comm.eval_agree_outside_fa _ _ _ h₂ v (hfa' v hvne (Or.inl rfl)),
            State.subst_of_ne _ _ _ _ hvne]
        · rw [State.subst_of_ne _ _ _ _ huv]
          by_cases huc : u ∈ c.fv
          · -- 본문의 자유 변수. 명제 2.7 의 일치가 바로 잇는다.
            have := hmain u (Finset.mem_insert_of_mem huc)
            rw [hδ₀ne u huv] at this
            exact this.symm
          · -- 아무도 안 건드린 변수. 양쪽 다 입력값 그대로다.
            have hufa : u ∉ c.fa := fun hmem => huc (Comm.fa_subset_fv c hmem)
            rw [Comm.eval_agree_outside_fa _ _ _ h₁ u hufa,
              Comm.eval_agree_outside_fa _ _ _ h₂ u (hfa' u hun (Or.inr huc)),
              State.subst_of_ne _ _ _ _ huv, State.subst_of_ne _ _ _ _ hun]
-- ANCHOR_END: newvarRename

/-! ## 9. 여기서 어디로 가나

§2.5 가 닫혔다. 자유 변수가 읽기와 쓰기로 갈라졌고(`FreeVars.lean`), 치환은 변수를
변수로만 보내되 단사일 때만 뜻을 보존하며, 지역 변수의 이름은 뜻이 아니라는 것까지
확인했다. 별칭은 여기서 처음 이빨을 보였을 뿐이다 — 프로시저와 배열이 생기면
치환이 아니라 **호출**이 별칭을 만들고, 그때 다시 온다.

다음은 §2.6 이다. `for` 명령을 새 구문이 아니라 이미 있는 구문으로 **번역**해서
정의한다 — 문법 설탕(syntactic sugar)의 첫 사례이고, 제어 변수에 대입하지 말라는
제약이 `FA` 로 적힌다. -/

end Reynolds.Answers.Ch02
