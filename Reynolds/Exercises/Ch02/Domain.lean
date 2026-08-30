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
# §2.3 도메인과 연속 함수 (1) — 사슬과 연속성

Reynolds §2.3 에 대응한다. 분량이 있어서 둘로 나눈다. 이 파일은 근사 순서에서 사슬의
최소 상계를 정의하고, 사슬의 극한을 보존하는 함수가 단조 함수보다 좁은 부류임을 보인다.
리프팅과 함수 공간은 다음 파일에서 다룬다.

## 왜 이 절이 필요한가

`Semantics.lean`에서는 같은 `while` 풀기 방정식을 만족하면서 비종료 입력에서 서로 다른
값을 내는 두 함수를 만들었다. 그 둘을 구분하려면 의미가 제공하는 정보량을 비교해야 한다.
Reynolds의 `x ⊑ y`는 수치 오차가 아니라 "`y`가 `x`가 주는 정보를 모두 포함한다"는
근사 관계다. 비종료 `⊥`를 가장 아래에 놓으면, 계산 근사가 진행되면서 정보가 늘어나는
과정을 증가 사슬로 표현할 수 있다.

## Mathlib 에 있는데 왜 직접 만드나

Mathlib 에는 이미 `OmegaCompletePartialOrder`가 있다. 이 절의 학습 대상은 완성된 API를
사용하는 법이 아니라, 가산 증가 사슬과 최소 상계에서 그 구조를 직접 조립하는 과정이다.

다만 완비 격자(complete lattice)처럼 Mathlib 이 이미 갖춘 것에서
프리도메인(predomain)이 따라 나오는
경로는 인스턴스 하나로 열어 둔다. 멱집합 도메인이 그 경로로 들어온다.
직접 만든 것과 Mathlib 대응물의 대조표는 `MathlibBridge.lean` 에 따로 둘 것이다.

## 이 파일에서 다루는 것
- 사슬(chain) — 가산 증가 열
- 프리도메인과 도메인(domain)
- 연속(continuous) 함수, 그리고 연속이면 단조라는 것
- 명제 2.1 — 단조 함수의 연속성을 확인하는 부등식
- 단조이지만 연속이 아닌 함수

## 읽는 순서
`Semantics.lean` → 이 파일 → `Domain/Lifting.lean` (다음 PR)
-/

@[expose] public section

namespace Reynolds.Exercises.Ch02

open Reynolds

universe u v

/-! ## 1. 사슬

Reynolds 의 정의를 그대로 옮긴다.

> *"A chain is a countably infinite increasing sequence x₀ ⊑ x₁ ⊑ x₂ ⊑ ⋯"*

책은 "엄밀히는 가산 사슬이지만 다른 종류는 다루지 않으므로 그냥 사슬이라 부른다" 고 한다.
더 일반적인 유향 집합(directed set)으로 정의하는 방식도 있고, Reynolds 도 §2.3 에서
언급하지만 쓰지는 않는다. -/

/--
사슬(chain) — 증가하는 가산 열.

`Monotone` 은 Mathlib 의 것이다. `∀ m n, m ≤ n → seq m ≤ seq n` 이고,
Reynolds 의 `x₀ ⊑ x₁ ⊑ ⋯` 를 모든 지수 쌍에 대해 적은 형태다. 이웃한 항에 대한
부등식만으로도 유도할 수 있지만, 이후 증명에서는 이 전이 폐쇄된 형태가 바로 쓰인다.
-/
structure Chain (α : Type u) [Preorder α] where
  /-- 열 자체. -/
  seq : ℕ → α
  /-- 증가한다. -/
  mono : Monotone seq

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

/-! ## 2. 프리도메인과 도메인

Reynolds 는 용어가 저자마다 다르다는 것을 §2.3 에서 직접 경고한다. 우리는 그의 용어를 쓴다.

- **프리도메인** — 모든 사슬이 최소 상계를 갖는 부분 순서 집합
- **도메인(domain)** — 최소원 `⊥` 이 있는 프리도메인

Gunter 와 Winskel 은 앞의 것을 complete partial order 라 부르고, Tennent 는 뒤의 것을
domain 이라 부른다. 이름이 겹치므로 논문을 읽을 때는 정의를 확인해야 한다. -/

/--
프리도메인 — 모든 사슬이 최소 상계를 갖는 부분 순서 집합.

**`PartialOrder` 를 확장하지 않고 인스턴스 인자로 받는다.** 확장하면 Mathlib 이 이미
순서를 주는 타입에서 순서 경로가 둘이 되어 다이아몬드가 생긴다. 인자로 받으면 순서는
언제나 원래 것 하나다.
-/
class Predomain (α : Type u) [PartialOrder α] where
  /-- 사슬의 최소 상계. Reynolds 의 `⨆ᵢ xᵢ`. -/
  lub : Chain α → α
  /-- 그 값이 실제로 최소 상계다. -/
  lub_isLUB (c : Chain α) : IsLUB (Set.range c.seq) (lub c)

/--
도메인(domain) — 최소원(least element)을 가진 프리도메인. Reynolds §2.3.

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

/-! ### 완비 격자는 프리도메인이다

Mathlib 이 완비 격자를 주는 타입은 그대로 프리도메인이 된다. 사슬의 극한이 `⨆` 다.
Reynolds 가 드는 예 중 **멱집합 도메인** `𝒫 S` 가 이 경로로 들어온다. -/

/-- 완비 격자에서 프리도메인 인스턴스. 우선순위를 낮춰 직접 만든 인스턴스가 먼저 잡히게 한다. -/
instance (priority := 100) Predomain.ofCompleteLattice [CompleteLattice α] : Predomain α where
  lub c := ⨆ n, c.seq n
  lub_isLUB _ := isLUB_iSup

/-! ## 3. 연속

Reynolds 의 정의다. 함수가 사슬의 극한을 보존한다.

```
f (⨆ᵢ xᵢ) = ⨆ᵢ f(xᵢ)
```

Lean 에서는 오른쪽이 존재한다고 가정하지 않고 **`f (⨆ xᵢ)` 가 상의 최소 상계다** 라고
쓴다. 그러면 공역이 프리도메인인지와 무관하게 진술이 서고, 극한의 유일성에서 위 등식이 따라온다. -/

/--
연속(continuous) — 사슬의 극한을 함수상의 극한으로 보낸다.

Reynolds는 단조 함수에 대해 이 보존 조건을 정의한다. 여기서는 보존 조건만 적고
`x, y, y, …` 사슬을 이용해 단조성을 정리로 유도한다. 공역도 프리도메인일 때는
Reynolds의 두 조건과 같은 함수 부류를 표현한다. 다만 이 정의 자체는 공역의 모든 사슬에
최소 상계가 있다고 가정하지 않고, 각 상 사슬의 최소 상계가 `f c.lub`라고 직접 요구한다.
-/
def Continuous [PartialOrder α] [PartialOrder β] [Predomain α] (f : α → β) : Prop :=
  ∀ c : Chain α, IsLUB (f '' Set.range c.seq) (f c.lub)

section ContinuousBasic
variable [PartialOrder α] [PartialOrder β] [Predomain α]

/--
연속이면 단조다.

`x ⊑ y` 를 보이려면 `x, y, y, …` 인 사슬 하나면 된다. 그 사슬의 극한이 `y` 이므로
연속성이 `f y` 가 `{f x, f y}` 의 상계라고 말해 주고, 상계라는 것이 곧 `f x ⊑ f y` 다.

Reynolds는 단조성을 먼저 요구한 뒤 극한 보존을 덧붙인다. 이 정리는 현재 정의에서
그 첫 조건이 이미 따라옴을 보인다.
-/
@[exercise "§2.3 continuous-monotone" 2]
theorem Continuous.monotone {f : α → β} (hf : Continuous f) : Monotone f := by
  -- 힌트 1: `x ⊑ y` 를 보이는 데 필요한 사슬은 `Chain.step hxy` 하나다 (`x, y, y, …`).
  -- 힌트 2: 그 사슬의 극한이 `y` 임을 먼저 세워라. 극한은 유일하므로
  --         `Chain.isLUB.unique` 로 보인다. `Chain.range_step` 이 훑는 값을 `{x, y}` 로 준다.
  -- 힌트 3: 연속성이 주는 `IsLUB` 의 **상계** 부분만 쓰면 끝난다.
  sorry

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

Reynolds의 명제 2.1은 극한을 사슬의 항으로 포함하지 않는 "흥미로운 사슬"에 대해서만
아래 부등식을 확인해도 된다고 말한다. 이 파일은 흥미로운 사슬이라는 보조 개념을 정의하지
않고 모든 사슬에 대해 같은 부등식을 요구한다. 이 형태도 연속성과 필요충분하고 §2.4에서
바로 쓰기 편하지만, 흥미롭지 않은 사슬에 대한 조건이 단조성에서 자동이라는 Reynolds의
추가 축약까지 형식화한 것은 아니다.

단조 함수 `f` 와 사슬 `c` 에 대해 `⨆ᵢ f(xᵢ) ⊑ f(⨆ᵢ xᵢ)` 는 언제나 성립한다.
각 `xᵢ ⊑ ⨆ xᵢ` 이므로 `f(xᵢ) ⊑ f(⨆ xᵢ)` 이고, 따라서 오른쪽이 상계다.

따라서 반대 부등식만 보이면 두 값이 같아지고 극한 보존이 성립한다. -/

/--
**명제 2.1** — 단조 함수가 연속일 필요충분조건.

`f (⨆ᵢ xᵢ) ⊑ ⨆ᵢ f(xᵢ)` 한 방향만 확인하면 된다. 나머지는 단조성에서 나온다.

이 진술은 연속성 목표를 이미 성립하는 단조 방향과 별도로 증명해야 하는 한 방향으로
분해한다. §2.4에서 함수들의 연속성을 합성할 때 이 형태를 사용한다.

**책과의 차이**: Reynolds의 진술은 이 부등식을 흥미로운 사슬에만 요구한다. 여기서는
`Interesting` 술어를 추가하지 않고 모든 `Chain`에 요구하는 동치 형태를 쓴다.
-/
@[exercise "Prop 2.1" 3]
theorem continuous_iff_le [PartialOrder α] [PartialOrder β] [Predomain α] [Predomain β]
    {f : α → β} (hf : Monotone f) :
    Continuous f ↔ ∀ c : Chain α, f c.lub ≤ (c.map hf).lub := by
  -- 힌트 1: 두 방향 다 `Chain.range_map` 으로 상과 옮긴 사슬을 오간다.
  -- 힌트 2: (→) 극한은 유일하다. 같은 집합의 최소 상계 둘이면 같은 값이다.
  -- 힌트 3: (←) 상계 쪽은 `hf (c.le_lub n)` 한 줄이다. 최소 쪽에서 가정한 부등식을 쓴다.
  sorry


/-! ## 5. 단조인데 연속이 아닌 함수

단조성은 각 두 점의 순서를 보존하지만, 연속성은 무한히 진행되는 근사의 극한까지 보존한다.
아래 반례는 두 요구가 갈라지는 사슬을 하나 구성한다.

Reynolds 는 수직 자연수 `ℕ⊤` 에서 두 점 도메인으로 가는 함수를 든다. `f x = (x = ∞)`
이면 `0 ⊑ 1 ⊑ 2 ⊑ ⋯` 의 극한이 `∞` 이므로 `f(⨆ xᵢ)` 는 참인데, 각 `f(xᵢ)` 는 거짓이라
`⨆ f(xᵢ)` 는 거짓이다.

여기서는 같은 논증을 멱집합 도메인 `Set ℕ`으로 옮긴다. Reynolds의 수직 자연수 예와
대상은 다르지만, 유한 근사에서는 거짓이고 극한에서만 참이 되는 관찰을 쓴다는 구조는 같다.
Mathlib이 `Set ℕ`에 완비 격자를 주므로 이 파일에서 정의한 프리도메인 인스턴스도 바로 얻는다.

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

/--
단조인데 연속이 아닌 함수가 있다.

`f s = (s = ℕ)` 이 그런 함수다. 단조인 이유는 `s = ℕ` 이고 `s ⊆ t` 면 `t = ℕ` 이기 때문이다.

연속이 아닌 이유는 이렇다. 시작 구간의 사슬은 극한이 `ℕ` 이므로 `f` 를 먹이면 참이 된다.
그런데 사슬의 **각 항**은 유한한 시작 구간이라 `f` 를 먹이면 전부 거짓이다.
상이 `{거짓}` 뿐인데 그 최소 상계가 참일 수는 없다.

이 반례는 단조성이 유한한 비교마다 정보를 보존해도 가산 근사의 극한에서 새 정보를
갑자기 만들 수 있음을 보인다. §2.4의 Kleene 사슬 계산에서 `f (⨆ xᵢ)`를
`⨆ f(xᵢ)`로 옮기려면 이 점프를 막는 연속성이 필요하다.
-/
@[exercise "§2.3 not-continuous" 2]
theorem exists_monotone_not_continuous :
    ∃ f : Set ℕ → Prop, Monotone f ∧ ¬ Continuous f := by
  -- 먼저 볼 것: 바로 위의 `initSegs` 와 `initSegs_lub`. 둘 다 완성되어 있다.
  -- 힌트 1: `f s = (s = Set.univ)` 를 쓴다. `Prop` 의 순서는 함의다.
  -- 힌트 2: 연속이라고 가정하고 `initSegs` 를 먹인 뒤, 상이 전부 거짓임을 보여라.
  --         그러면 `False` 도 상계이므로 최소 상계가 참일 수 없다.
  -- 힌트 3: `{k | k < n} = ℕ` 이면 `n < n` 이 된다.
  sorry


/-! ## 6. 다음에 필요한 두 구성

최소 고정점 정리를 명령 의미에 적용하려면 아직 두 가지 인스턴스가 필요하다.

- **리프팅** `P⊥` — `Σ⊥` 를 도메인으로 만드는 구성. `Option` 에 순서를 얹는 일이다.
- **함수 공간** `P → P'` — `Σ → Σ⊥` 가 도메인이어야 `while` 의 뜻을 그 안에서 찾는다.

`Domain/Lifting.lean` 이 앞의 것을, `Domain/FunctionSpace.lean` 이 뒤의 것을 만든다.
그러면 `State V → SigmaBot V` 위에서 `while`의 함수자를 만들고 §2.4의 최소 고정점
정리를 적용할 수 있다. -/

end Reynolds.Exercises.Ch02
