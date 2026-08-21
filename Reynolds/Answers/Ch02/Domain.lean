/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Init
public import Reynolds.Meta.Exercise
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.Bounds.Basic

/-!
# §2.3 도메인과 연속 함수 (1) — 순서를 만든다

Reynolds §2.3 에 대응한다. 분량이 있어서 둘로 나눈다. 이 파일은 순서 구조와 연속성,
그리고 **단조와 연속이 다른 것**이라는 사실까지 간다. 리프팅과 함수 공간은 다음 파일이다.

## 왜 이 절이 필요한가

`Semantics.lean` 에서 `while x ≠ 0 do x := x - 2` 의 풀기 방정식을 만족하는 함수가
둘이라는 것을 증명했다. 하나는 끝나지 않는 상태에서 `⊥` 를 내고, 다른 하나는 없는 답을
지어냈다. 방정식은 둘을 구별하지 못한다.

뜻으로 삼아야 할 것은 앞쪽이다. **계산이 알려 주지 않는 것을 의미 함수가 알려 주면 안 된다.**
그 원칙을 "아무 주장도 하지 않는 쪽이 아래" 라는 **순서**로 만들면, 여러 해 중 가장 아래에
있는 것을 고르는 일이 된다. 이 파일이 그 순서를 만든다.

## Mathlib 에 있는데 왜 직접 만드나

Mathlib 에 `OmegaCompletePartialOrder` 가 있다. 그런데 §2.3 은 **그것을 만드는 절**이다.
꺼내 쓰면 이 절이 통째로 사라진다.

다만 완비 격자(complete lattice)처럼 Mathlib 이 이미 갖춘 것에서 예비도메인이 따라 나오는
경로는 인스턴스 하나로 열어 둔다. 멱집합 도메인이 그 경로로 들어온다.
직접 만든 것과 Mathlib 대응물의 대조표는 `MathlibBridge.lean` 에 따로 둘 것이다.

## 이 파일에서 다루는 것
- 사슬(chain) — 가산 증가 열
- 예비도메인(predomain)과 도메인(domain)
- 연속(continuous) 함수, 그리고 연속이면 단조라는 것
- **명제 2.1** — 단조 함수가 언제 연속인가
- **단조인데 연속이 아닌 함수** — 이 절의 핵심

## 읽는 순서
`Semantics.lean` → 이 파일 → `Domain/Lifting.lean` (다음 PR)
-/

@[expose] public section

namespace Reynolds.Answers.Ch02

open Reynolds

universe u v

/-! ## 1. 사슬

Reynolds 의 정의를 그대로 옮긴다.

> *"A chain is a countably infinite increasing sequence x₀ ⊑ x₁ ⊑ x₂ ⊑ ⋯"*

책은 "엄밀히는 가산 사슬이지만 다른 종류는 다루지 않으므로 그냥 사슬이라 부른다" 고 한다.
더 일반적인 유향 집합(directed set)으로 정의하는 방식도 있고, Reynolds 도 §2.3 에서
언급하지만 쓰지는 않는다. -/

-- ANCHOR: chain
/--
사슬(chain) — 증가하는 가산 열.

`Monotone` 은 Mathlib 의 것이다. `∀ m n, m ≤ n → seq m ≤ seq n` 이고,
Reynolds 의 `x₀ ⊑ x₁ ⊑ ⋯` 와 같은 말이다 (이웃한 것만 비교해도 되지만 Lean 에서는
전순서 판이 다루기 편하다).
-/
structure Chain (α : Type u) [Preorder α] where
  /-- 열 자체. -/
  seq : ℕ → α
  /-- 증가한다. -/
  mono : Monotone seq
-- ANCHOR_END: chain

variable {α : Type u} {β : Type v}

/-- 한 점에 머무는 사슬. 어떤 원소든 사슬로 볼 수 있다는 뜻이다. -/
def Chain.const [Preorder α] (x : α) : Chain α := ⟨fun _ => x, monotone_const⟩

/--
`x ⊑ y` 일 때 `x, y, y, y, …` 인 사슬.

두 원소만 비교하고 싶을 때 쓴다. 아래 `Continuous.monotone` 이 이 사슬 하나로 증명된다.
-/
def Chain.step [Preorder α] {x y : α} (h : x ≤ y) : Chain α where
  seq n := if n = 0 then x else y
  mono m n hmn := by
    by_cases hm : m = 0
    · subst hm
      by_cases hn : n = 0
      · subst hn; simp
      · simp [hn, h]
    · have hn : n ≠ 0 := by omega
      simp [hm, hn]

@[simp] theorem Chain.step_zero [Preorder α] {x y : α} (h : x ≤ y) :
    (Chain.step h).seq 0 = x := rfl

@[simp] theorem Chain.step_succ [Preorder α] {x y : α} (h : x ≤ y) (n : ℕ) :
    (Chain.step h).seq (n + 1) = y := rfl

/-- `x, y, y, …` 인 사슬이 훑는 값은 `x` 와 `y` 둘뿐이다. -/
theorem Chain.range_step [Preorder α] {x y : α} (h : x ≤ y) :
    Set.range (Chain.step h).seq = {x, y} := by
  ext z
  constructor
  · rintro ⟨n, rfl⟩
    cases n with
    | zero => exact Or.inl rfl
    | succ k => exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

/-! ## 2. 예비도메인과 도메인

Reynolds 는 용어가 저자마다 다르다는 것을 §2.3 에서 직접 경고한다. 우리는 그의 용어를 쓴다.

- **예비도메인(predomain)** — 모든 사슬이 최소 상계를 갖는 부분 순서 집합
- **도메인(domain)** — 최소원 `⊥` 이 있는 예비도메인

Gunter 와 Winskel 은 앞의 것을 complete partial order 라 부르고, Tennent 는 뒤의 것을
domain 이라 부른다. 이름이 겹치므로 논문을 읽을 때는 정의를 확인해야 한다. -/

-- ANCHOR: predomain
/--
예비도메인(predomain) — 모든 사슬이 최소 상계를 갖는 부분 순서 집합.

**`PartialOrder` 를 확장하지 않고 인스턴스 인자로 받는다.** 확장하면 Mathlib 이 이미
순서를 주는 타입에서 순서 경로가 둘이 되어 다이아몬드가 생긴다. 인자로 받으면 순서는
언제나 원래 것 하나다.
-/
class Predomain (α : Type u) [PartialOrder α] where
  /-- 사슬의 최소 상계. Reynolds 의 `⨆ᵢ xᵢ`. -/
  lub : Chain α → α
  /-- 그 값이 실제로 최소 상계다. -/
  lub_isLUB (c : Chain α) : IsLUB (Set.range c.seq) (lub c)
-- ANCHOR_END: predomain

/--
도메인(domain) — 최소원(least element)을 가진 예비도메인. Reynolds §2.3.

클래스를 새로 만들지 않고 인스턴스 셋을 함께 요구하는 것으로 쓴다.
`Domain` 을 클래스로 만들면 `OrderBot` 을 이미 갖춘 타입에서 최소원 경로가 둘이 되어
다이아몬드가 생긴다.

`[OrderBot α]` 는 이 별칭 자체에서는 쓰이지 않는다. 도메인이라는 말이 무엇을 더 요구하는지를
**타입에 적어 두려고** 받는 것이고, `Domain α` 라고 쓰는 순간 Lean 이 그 인스턴스를 찾는다.
린터에는 그 사정을 따로 알려 준다.
-/
@[nolint unusedArguments]
abbrev Domain (α : Type u) [PartialOrder α] [OrderBot α] := Predomain α

/-- `c.lub` 로 쓸 수 있게 한다. Reynolds 의 `⨆ᵢ xᵢ` 에 해당한다. -/
def Chain.lub [PartialOrder α] [Predomain α] (c : Chain α) : α := Predomain.lub c

theorem Chain.isLUB [PartialOrder α] [Predomain α] (c : Chain α) :
    IsLUB (Set.range c.seq) c.lub := Predomain.lub_isLUB c

/-- 사슬의 각 항은 극한 아래에 있다. -/
theorem Chain.le_lub [PartialOrder α] [Predomain α] (c : Chain α) (n : ℕ) :
    c.seq n ≤ c.lub := c.isLUB.1 ⟨n, rfl⟩

/-- 모든 항보다 위에 있으면 극한보다 위에 있다. -/
theorem Chain.lub_le [PartialOrder α] [Predomain α] {c : Chain α} {b : α}
    (h : ∀ n, c.seq n ≤ b) : c.lub ≤ b :=
  c.isLUB.2 (by rintro _ ⟨n, rfl⟩; exact h n)

/-! ### 완비 격자는 예비도메인이다

Mathlib 이 완비 격자를 주는 타입은 그대로 예비도메인이 된다. 사슬의 극한이 `⨆` 다.
Reynolds 가 드는 예 중 **멱집합 도메인** `𝒫 S` 가 이 경로로 들어온다. -/

/-- 완비 격자에서 예비도메인 인스턴스. 우선순위를 낮춰 직접 만든 인스턴스가 먼저 잡히게 한다. -/
instance (priority := 100) Predomain.ofCompleteLattice [CompleteLattice α] : Predomain α where
  lub c := ⨆ n, c.seq n
  lub_isLUB _ := isLUB_iSup

/-! ## 3. 연속

Reynolds 의 정의다. 함수가 사슬의 극한을 보존한다.

```
f (⨆ᵢ xᵢ) = ⨆ᵢ f(xᵢ)
```

Lean 에서는 오른쪽이 존재한다고 가정하지 않고 **`f (⨆ xᵢ)` 가 상의 최소 상계다** 라고
쓴다. 그러면 공역이 예비도메인인지와 무관하게 진술이 서고, 극한의 유일성에서 위 등식이 따라온다. -/

-- ANCHOR: continuous
/--
연속(continuous) — 사슬의 극한을 상의 극한으로 보낸다.

단조성을 가정하지 않았는데도 아래 `Continuous.monotone` 이 나온다. 연속이 단조보다
**진짜로 강한** 조건이라는 것이 §2.3 의 요점이고, 이 파일 §5 의 반례가 그것을 보인다.
-/
def Continuous [PartialOrder α] [PartialOrder β] [Predomain α] (f : α → β) : Prop :=
  ∀ c : Chain α, IsLUB (f '' Set.range c.seq) (f c.lub)
-- ANCHOR_END: continuous

section ContinuousBasic
variable [PartialOrder α] [PartialOrder β] [Predomain α]

/--
**연속이면 단조다.**

`x ⊑ y` 를 보이려면 `x, y, y, …` 인 사슬 하나면 된다. 그 사슬의 극한이 `y` 이므로
연속성이 `f y` 가 `{f x, f y}` 의 상계라고 말해 주고, 상계라는 것이 곧 `f x ⊑ f y` 다.

Reynolds 는 연속성을 단조 함수에 대해서만 정의하지만, 이렇게 두면 가정이 하나 줄어든다.
-/
@[exercise "§2.3 continuous-monotone" 2]
theorem Continuous.monotone {f : α → β} (hf : Continuous f) : Monotone f := by
  intro x y hxy
  have h := hf (Chain.step hxy)
  -- 이 사슬의 극한은 `y` 다. 극한은 유일하므로 그것을 먼저 확인한다.
  have hlub : (Chain.step hxy).lub = y := by
    refine (Chain.step hxy).isLUB.unique ?_
    rw [Chain.range_step]
    constructor
    · rintro z (rfl | rfl)
      · exact hxy
      · exact le_refl z
    · intro b hb; exact hb (by simp)
  rw [hlub, Chain.range_step] at h
  exact h.1 ⟨x, by simp, rfl⟩

end ContinuousBasic

section ChainMap
variable [Preorder α] [Preorder β]

/-- 단조 함수는 사슬을 사슬로 보낸다. 명제 2.1 을 쓰려면 이것이 먼저 있어야 한다. -/
def Chain.map (c : Chain α) {f : α → β} (hf : Monotone f) : Chain β :=
  ⟨f ∘ c.seq, hf.comp c.mono⟩

@[simp] theorem Chain.map_seq (c : Chain α) {f : α → β} (hf : Monotone f) (n : ℕ) :
    (c.map hf).seq n = f (c.seq n) := rfl

/-- 옮긴 사슬이 훑는 값은 원래 사슬이 훑는 값의 상이다. -/
theorem Chain.range_map (c : Chain α) {f : α → β} (hf : Monotone f) :
    Set.range (c.map hf).seq = f '' Set.range c.seq := by
  ext z
  simp only [Set.mem_range, Set.mem_image, Chain.map_seq]
  constructor
  · rintro ⟨n, rfl⟩; exact ⟨c.seq n, ⟨n, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨n, rfl⟩, rfl⟩; exact ⟨n, rfl⟩

end ChainMap

/-! ## 4. 명제 2.1 — 단조 함수가 언제 연속인가

Reynolds 의 명제 2.1 이다. 단조 함수에 대해서는 연속성의 한쪽 방향이 공짜이므로,
확인할 것이 나머지 한쪽뿐이다.

단조 함수 `f` 와 사슬 `c` 에 대해 `⨆ᵢ f(xᵢ) ⊑ f(⨆ᵢ xᵢ)` 는 언제나 성립한다.
각 `xᵢ ⊑ ⨆ xᵢ` 이므로 `f(xᵢ) ⊑ f(⨆ xᵢ)` 이고, 따라서 오른쪽이 상계다.

**반대 방향이 연속성의 전부다.** -/

-- ANCHOR: prop21
/--
**명제 2.1** — 단조 함수가 연속일 필요충분조건.

`f (⨆ᵢ xᵢ) ⊑ ⨆ᵢ f(xᵢ)` 한 방향만 확인하면 된다. 나머지는 단조성에서 나온다.

이 진술이 §2.4 에서 실제로 쓰인다. 어떤 함수가 연속임을 보일 때마다 부등식 하나만
확인하게 되고, 그것이 증명 분량을 절반으로 줄인다.
-/
@[exercise "Prop 2.1" 3]
theorem continuous_iff_le [PartialOrder α] [PartialOrder β] [Predomain α] [Predomain β]
    {f : α → β} (hf : Monotone f) :
    Continuous f ↔ ∀ c : Chain α, f c.lub ≤ (c.map hf).lub := by
  constructor
  · -- 연속이면 `f c.lub` 가 상의 극한이고, 극한은 유일하다.
    intro hc c
    have h₁ := hc c
    have h₂ := (c.map hf).isLUB
    rw [Chain.range_map] at h₂
    exact le_of_eq (h₁.unique h₂)
  · intro hle c
    -- 상을 옮긴 사슬이 훑는 값으로 바꿔 놓고 시작한다.
    rw [(c.range_map hf).symm]
    constructor
    · -- 상계. 각 항에 단조성을 쓴다.
      rintro _ ⟨n, rfl⟩
      exact hf (c.le_lub n)
    · -- 최소. 가정한 부등식을 옮긴 사슬의 극한과 이어 붙인다.
      intro b hb
      exact le_trans (hle c) (Chain.lub_le fun n => hb ⟨n, rfl⟩)
-- ANCHOR_END: prop21

/-! ## 5. 단조인데 연속이 아닌 함수

§2.3 의 핵심이다. 두 조건이 정말로 다르다는 것을 반례로 보인다.

Reynolds 는 수직 자연수 `ℕ⊤` 에서 두 점 도메인으로 가는 함수를 든다. `f x = (x = ∞)`
이면 `0 ⊑ 1 ⊑ 2 ⊑ ⋯` 의 극한이 `∞` 이므로 `f(⨆ xᵢ)` 는 참인데, 각 `f(xᵢ)` 는 거짓이라
`⨆ f(xᵢ)` 는 거짓이다.

여기서는 같은 이야기를 **멱집합 도메인**으로 옮긴다. Mathlib 이 `Set ℕ` 에 완비 격자를
주므로 예비도메인이 공짜로 따라오고, `ℕ⊤` 처럼 형변환 보조정리를 뒤질 일이 없다.
`ℕ⊤` 판을 직접 써 보는 것은 좋은 연습이다.

사슬은 `{k | k < n}` 이다. 앞자리부터 하나씩 채워 가는 열이고, 극한이 `ℕ` 전체다.
`f s = (s = ℕ)` 는 극한에서만 참이 된다. -/

/-- 시작 구간 `{k | k < n}` 으로 이루어진 사슬. 극한이 `ℕ` 전체다. -/
def initSegs : Chain (Set ℕ) where
  seq n := {k | k < n}
  mono m n hmn := by
    intro k hk
    exact lt_of_lt_of_le hk hmn

/-- 이 사슬의 극한은 `ℕ` 전체다. `k` 는 `{j | j < k+1}` 에 들어 있다. -/
theorem initSegs_lub : initSegs.lub = Set.univ := by
  refine le_antisymm (le_top) ?_
  intro k _
  exact initSegs.le_lub (k + 1) (by simp [initSegs])

-- ANCHOR: notContinuous
/--
**단조인데 연속이 아닌 함수가 있다.**

`f s = (s = ℕ)` 이 그런 함수다. 단조인 이유는 `s = ℕ` 이고 `s ⊆ t` 면 `t = ℕ` 이기 때문이다.

연속이 아닌 이유는 이렇다. 시작 구간의 사슬은 극한이 `ℕ` 이므로 `f` 를 먹이면 참이 된다.
그런데 사슬의 **각 항**은 유한한 시작 구간이라 `f` 를 먹이면 전부 거짓이다.
상이 `{거짓}` 뿐인데 그 최소 상계가 참일 수는 없다.

Reynolds 가 이 반례를 드는 이유는, 의미 함수가 단조이기만 해서는 부족하다는 것이다.
§2.4 의 최소 고정점 정리는 연속성을 요구하고, 그 요구가 공짜가 아니라는 것을 여기서 확인한다.
-/
@[exercise "§2.3 not-continuous" 2]
theorem exists_monotone_not_continuous :
    ∃ f : Set ℕ → Prop, Monotone f ∧ ¬ Continuous f := by
  refine ⟨fun s => s = Set.univ, ?_, ?_⟩
  · -- 단조. `Prop` 의 순서는 함의다.
    intro s t hst hs
    exact Set.eq_univ_of_univ_subset (hs ▸ hst)
  · intro hc
    have h := hc initSegs
    rw [initSegs_lub] at h
    -- 극한에서는 참이다.
    have htrue : (Set.univ : Set ℕ) = Set.univ := rfl
    -- 그런데 상은 전부 거짓이라 `False` 도 상계다.
    have hub : False ∈ upperBounds ((fun s : Set ℕ => s = Set.univ) '' Set.range initSegs.seq) := by
      rintro P ⟨s, ⟨n, rfl⟩, rfl⟩ hs
      -- `{k | k < n} = ℕ` 이면 `n < n` 이 된다.
      have : n ∈ initSegs.seq n := hs ▸ Set.mem_univ n
      simp [initSegs] at this
    exact (h.2 hub) htrue
-- ANCHOR_END: notContinuous

/-! ## 6. 여기서 어디로 가나

순서와 연속성이 생겼다. 아직 없는 것이 둘이다.

- **리프팅** `P⊥` — `Σ⊥` 를 도메인으로 만드는 구성. `Option` 에 순서를 얹는 일이다.
- **함수 공간** `P → P'` — `Σ → Σ⊥` 가 도메인이어야 `while` 의 뜻을 그 안에서 찾는다.

둘 다 다음 파일에서 만든다. 그것까지 있으면 §2.4 의 최소 고정점 정리를 증명할 수 있고,
`Semantics.lean` 이 남겨 둔 `Comm.eval` 을 드디어 정의하게 된다. -/

end Reynolds.Answers.Ch02
