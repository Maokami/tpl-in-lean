/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Answers.Ch02.Domain.Lifting

/-!
# §2.3 도메인과 연속 함수 (3) — 함수 공간

Reynolds §2.3의 함수 공간과 명제 2.2·2.3에 대응한다.

## 왜 함수 공간이 필요한가

`while`의 뜻은 함수 `Σ → Σ⊥`다. §2.4의 최소 고정점 정리는 도메인 위의 연속 함수에 대한
정리이므로, 그 함수들이 사는 `Σ → Σ⊥` 전체가 도메인이어야 정리를 쓸 수 있다.

두 층으로 만든다.

1. **전체 함수 공간** `α → β` — 점별(pointwise) 순서. `β`가 프리도메인이면 이쪽도
   프리도메인이다. 사슬의 극한은 자리마다 따로 잰 극한이다. `Σ → Σ⊥`가 여기 해당한다.
2. **연속 함수 공간** `[P → P']` — Reynolds의 명제 2.2. 연속 함수들만 모아도
   프리도메인이고, 점별 극한이 다시 연속이라는 것이 증명의 전부다.

2장의 최소 고정점 정리에는 1만 있어도 된다. 2를 함께 만들어 두는 이유는 10장부터다.
고차 함수가 들어오면 `⟦τ → σ⟧` 자체가 연속 함수 공간이어야 하고, 그때 명제 2.2가
타입의 뜻을 정의하는 재료가 된다.

## 읽는 순서

`Domain/Lifting.lean` → 이 파일 → `../Fixpoint.lean`

## 책과의 차이

Reynolds는 함수 공간을 수학적 구성으로 설명한다. 여기서는 전체 함수 공간에는 Mathlib의
점별 순서를 사용하고, 연속 함수 공간은 `Cont` 구조로 따로 표현한다.
-/

@[expose] public section

namespace Reynolds.Answers.Ch02

open Reynolds

universe u v

variable {α : Type u} {β : Type v}

/-! ## 1. 점별 순서와 점별 극한

`α → β`의 순서는 Mathlib의 Pi 인스턴스다: `f ⊑ g ⟺ ∀ x, f x ⊑ g x`.
`β`가 `Σ⊥`처럼 평평하면 이것이 Reynolds가 §2.3 끝에서 말하는 바로 그 순서가 된다.
아래 `pi_flat_le_iff`로 확인한다. -/

/-- 함수 사슬을 한 자리에서 본 사슬. `n ↦ fₙ x`. -/
def Chain.apply [Preorder β] (c : Chain (α → β)) (x : α) : Chain β :=
  ⟨fun n => c.seq n x, fun _ _ h => c.mono h x⟩

@[simp] theorem Chain.apply_seq [Preorder β] (c : Chain (α → β)) (x : α) (n : ℕ) :
    (c.apply x).seq n = c.seq n x := rfl

-- ANCHOR: piPredomain
/--
함수 공간은 점별로 프리도메인이다. 사슬의 극한은 자리마다 따로 잰 극한이다.

```
(⨆ₙ fₙ) x  =  ⨆ₙ (fₙ x)
```

상계·최소 확인은 모두 "자리 `x`를 고정하고 `β` 쪽 성질을 쓴다"로 내려간다.
-/
noncomputable instance piPredomain [PartialOrder β] [Predomain β] : Predomain (α → β) where
  lub c := fun x => (c.apply x).lub
  lub_isLUB c := by
    constructor
    · rintro _ ⟨n, rfl⟩ x
      exact (c.apply x).le_lub n
    · intro g hg x
      exact (c.apply x).lub_le fun n => hg ⟨n, rfl⟩ x
-- ANCHOR_END: piPredomain

/-- 점별 극한의 정의를 꺼내 쓰는 다리. -/
theorem Chain.lub_apply [PartialOrder β] [Predomain β] (c : Chain (α → β)) (x : α) :
    c.lub x = (c.apply x).lub := rfl

/--
**Reynolds 가 §2.3 끝에서 하는 말** — `Σ → Σ⊥` 의 순서를 풀어 쓰면 이렇다.

`f ⊑ g` ⟺ 모든 `σ` 에 대해, `f σ = ⊥` 이거나 `f σ = g σ`.

`g` 는 `f` 가 내는 결과를 전부 그대로 내고, `f` 가 `⊥` 인 자리 일부에서 추가로 종료할 수
있다. 정보가 늘어나는 순서다. `Semantics.lean` 의 `decrTrue` 와 `decrFake` 로 돌아가면,
`decrTrue ⊑ decrFake` 이고 — 진짜 뜻이 두 해 중 **아래쪽**이라는 §2.2 의 직관이
이 순서에서 문장이 된다.
-/
theorem pi_flat_le_iff {V : Type u} {f g : State V → SigmaBot V} :
    f ≤ g ↔ ∀ σ, f σ = none ∨ f σ = g σ := Iff.rfl

/-! ## 2. 명제 2.3 — 연속 함수를 만드는 부품

항등·상수·합성. §2.4에서 `while`의 함수 연산자가 연속임을 보일 때 이 셋을 조립한다. -/

section Prop23

variable {γ : Type v} [PartialOrder α] [PartialOrder β] [PartialOrder γ]

/-- 항등 함수는 연속이다. 상이 곧 원래 값 목록이라 확인할 것이 없다. -/
theorem continuous_id [Predomain α] : Continuous (id : α → α) := by
  intro c
  simpa using c.isLUB

/-- 상수 함수는 연속이다. 상이 한 점 `{b}` 로 무너지고, 한 점의 극한은 그 점이다. -/
theorem continuous_const [Predomain α] (b : β) : Continuous (fun _ : α => b) := by
  intro c
  have : (fun _ : α => b) '' Set.range c.seq = {b} :=
    Set.Nonempty.image_const (Set.range_nonempty _) b
  rw [this]
  exact isLUB_singleton

/-- 연속 함수는 사슬의 극한을 옮긴 사슬의 극한으로 보낸다. 극한의 유일성으로 등식이 된다. -/
theorem Continuous.map_lub [Predomain α] [Predomain β] {f : α → β} (hf : Continuous f)
    (c : Chain α) : f c.lub = (c.map hf.monotone).lub := by
  have h₂ := (c.map hf.monotone).isLUB
  rw [Chain.range_map] at h₂
  exact (hf c).unique h₂

-- ANCHOR: Continuous.comp
/--
**명제 2.3 — 연속 함수의 합성은 연속이다.**

`g` 의 연속성을 옮긴 사슬 `c.map` 에 적용하면 상이 `(g ∘ f) '' …` 로 접히고,
남는 것은 `g (f (⨆c)) = g (⨆ c.map)` 뿐이다. `f` 의 연속성이 그 안쪽 등식을 준다.
-/
@[exercise "Prop 2.3" 2]
theorem Continuous.comp [Predomain α] [Predomain β]
    {g : β → γ} {f : α → β} (hg : Continuous g) (hf : Continuous f) :
    Continuous (g ∘ f) := by
  intro c
  have hmap := hg (c.map hf.monotone)
  rw [Chain.range_map, ← Set.image_comp] at hmap
  have : (g ∘ f) c.lub = g ((c.map hf.monotone).lub) := by
    simp [Function.comp, hf.map_lub c]
  rw [this]
  exact hmap
-- ANCHOR_END: Continuous.comp

end Prop23

/-! ## 3. 명제 2.2 — 연속 함수 공간

연속 함수만 모은 `[P → P']`도 프리도메인이라는 주장이다. 전체 함수 공간은 §1에서
끝났으므로, 남은 것은 딱 하나다 — **연속 함수들의 점별 극한이 다시 연속인가.**

Reynolds 의 증명은 극한을 두 번 바꾸는 계산이다.

```
h(⨆ᵢ xᵢ) = ⨆ₙ fₙ(⨆ᵢ xᵢ) = ⨆ₙ ⨆ᵢ fₙ(xᵢ) = ⨆ᵢ ⨆ₙ fₙ(xᵢ) = ⨆ᵢ h(xᵢ)
```

Lean 에서는 `⨆` 를 등식으로 다루는 대신 "양쪽이 서로의 상계다" 를 오간다.
`le_lub` 와 `lub_le` 둘만으로 네 단계가 전부 지나간다.
-/

/-- 연속 함수 공간 `[P → P']`. Reynolds 의 표기다. -/
structure Cont (α : Type u) (β : Type v)
    [PartialOrder α] [PartialOrder β] [Predomain α] where
  /-- 함수 자체. -/
  toFun : α → β
  /-- 연속성. -/
  continuous : Continuous toFun

namespace Cont

variable [PartialOrder α] [PartialOrder β] [Predomain α]

@[ext] theorem ext {f g : Cont α β} (h : f.toFun = g.toFun) : f = g := by
  cases f; cases g; simpa using h

/-- 순서는 전체 함수 공간에서 물려받는다 — 점별이다. -/
instance partialOrder : PartialOrder (Cont α β) where
  le f g := f.toFun ≤ g.toFun
  le_refl _ := le_refl _
  le_trans _ _ _ h₁ h₂ := le_trans h₁ h₂
  le_antisymm _ _ h₁ h₂ := ext (le_antisymm h₁ h₂)

theorem le_def {f g : Cont α β} : f ≤ g ↔ f.toFun ≤ g.toFun := Iff.rfl

/-- 연속 함수 사슬에서 함수만 남긴 사슬. -/
def Chain.toFuns (c : Chain (Cont α β)) : Chain (α → β) :=
  ⟨fun n => (c.seq n).toFun, fun _ _ h => c.mono h⟩

@[simp] theorem Chain.toFuns_seq (c : Chain (Cont α β)) (n : ℕ) :
    (Chain.toFuns c).seq n = (c.seq n).toFun := rfl

variable [Predomain β]

-- ANCHOR: lub_continuous
/--
**명제 2.2 의 핵심 — 연속 함수들의 점별 극한은 연속이다.**

극한 바꾸기를 `le_lub` / `lub_le` 로 옮기면 두 단계다.

- `h(⨆d)` 아래에서: `fₙ(⨆d)` 는 연속성으로 `⨆ᵢ fₙ(dᵢ)` 이고, 각 `fₙ(dᵢ) ⊑ h(dᵢ) ⊑ b`.
- `h(dᵢ)` 들은 단조성으로 전부 `h(⨆d)` 아래에 있다.
-/
@[exercise "Prop 2.2" 3]
theorem lub_continuous (c : Chain (Cont α β)) :
    Continuous ((Chain.toFuns c).lub) := by
  have hmono : Monotone ((Chain.toFuns c).lub) := by
    intro x y hxy
    rw [Chain.lub_apply, Chain.lub_apply]
    exact Chain.lub_le fun n =>
      le_trans ((c.seq n).continuous.monotone hxy) (((Chain.toFuns c).apply y).le_lub n)
  intro d
  constructor
  · -- 상계: 단조성 그대로.
    rintro _ ⟨x, ⟨i, rfl⟩, rfl⟩
    exact hmono (d.le_lub i)
  · -- 최소: 극한을 두 번 벗긴다. 바깥은 n, 안쪽은 i.
    intro b hb
    rw [Chain.lub_apply]
    refine Chain.lub_le fun n => ?_
    -- n 번째 함수를 극한 상태에서 잰 값이다. 연속성으로 안쪽 극한을 벗긴다.
    change (c.seq n).toFun d.lub ≤ b
    rw [(c.seq n).continuous.map_lub d]
    refine Chain.lub_le fun i => ?_
    -- fₙ(dᵢ) ⊑ h(dᵢ) ⊑ b
    change (c.seq n).toFun (d.seq i) ≤ b
    refine le_trans (((Chain.toFuns c).apply (d.seq i)).le_lub n) ?_
    exact hb ⟨d.seq i, ⟨i, rfl⟩, rfl⟩
-- ANCHOR_END: lub_continuous

/--
**명제 2.2 — 연속 함수 공간은 프리도메인이다.**

극한은 점별 극한이고, 그것이 연속이라는 사실이 위의 `lub_continuous` 다.
상계·최소 확인은 전체 함수 공간의 것을 그대로 통과시킨다.
-/
noncomputable instance predomain : Predomain (Cont α β) where
  lub c := ⟨(Chain.toFuns c).lub, lub_continuous c⟩
  lub_isLUB c := by
    constructor
    · rintro _ ⟨n, rfl⟩
      exact fun x => ((Chain.toFuns c).apply x).le_lub n
    · intro g hg x
      exact ((Chain.toFuns c).apply x).lub_le fun n => hg ⟨n, rfl⟩ x

/-- `P'` 가 도메인이면 `[P → P']` 도 도메인이다. 최소원은 상수 `⊥` 함수다. -/
noncomputable instance orderBot [OrderBot β] : OrderBot (Cont α β) where
  bot := ⟨fun _ => ⊥, continuous_const ⊥⟩
  bot_le _ := fun _ => bot_le

end Cont

/-! ## 4. §2.4로 이어지는 함수 공간

`Σ → Σ⊥`는 점별 인스턴스로 도메인이다. §2.4는 이 공간에서 `while`의 함수 연산자가
연속임을 보이고, `⊥, F(⊥), F(F(⊥)), …`의 극한으로 `⟦while b do c⟧`를 정의한다. -/

end Reynolds.Answers.Ch02
