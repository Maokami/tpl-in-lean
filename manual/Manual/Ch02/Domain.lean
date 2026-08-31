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
set_option verso.exampleModule "Reynolds.Answers.Ch02.Domain"

#doc (Manual) "§2.3 도메인과 연속 함수" =>
%%%
tag := "ch02-domain"
file := "ch02-domain"
number := false
%%%

# 결과를 값이 아니라 정보로 비교한다
%%%
tag := "ch02-information-order"
file := "ch02-information-order"
number := false
%%%

§2.2에서 같은 풀기 방정식을 만족하는 함수가 둘 이상 생겼다. 이 중 계산의 뜻으로 삼을
함수를 고르려면 후보를 비교할 기준이 필요하다.

`SigmaBot V = Option (State V)`에는 평평한 순서(flat order)를 준다.

```
none   ⊑ none
none   ⊑ some σ
some σ ⊑ some σ
```

서로 다른 두 종료 상태는 비교하지 않는다. `some σ ⊑ some σ'`이면 `σ = σ'`다.
이 순서는 “더 큰 수”나 “더 좋은 상태”를 말하지 않는다. `none`보다 `some σ`가 위인
이유는 계산 결과에 관한 정보가 하나 늘었기 때문이다.

상태 변환 함수의 순서는 이 순서를 입력마다 적용한다.

```
f ⊑ g  ↔  ∀ σ, f σ ⊑ g σ
```

따라서 `g`가 `f`보다 위라는 말은, `f`가 이미 내던 종료 결과를 바꾸지 않으면서
`f`가 `none`이던 입력 중 일부에서 결과를 더 낼 수 있다는 뜻이다.

# 사슬은 유한 근사를 차례로 놓은 것이다
%%%
tag := "ch02-chain"
file := "ch02-chain"
number := false
%%%

계산을 0단계, 1단계, 2단계로 점점 더 오래 허용하면 정보가 줄지 않는 열을 얻는다.
이런 증가 열을 사슬(chain)이라 부른다.

```anchor Chain (module := Reynolds.Answers.Ch02.Domain)
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
```

`seq n`은 `n`번째 근사이고 `mono`는 나중 근사가 앞선 근사의 정보를 잃지 않는다는
증거다. 이 정의가 요구하는 것은 가산 열 하나다. 임의의 유향 집합을 쓰는 더 일반적인
도메인 이론과는 범위가 다르다.

사슬 전체를 하나의 값으로 합칠 때는 최소 상한(least upper bound)을 쓴다.

: 상계(upper bound)

  사슬의 모든 항보다 위에 있는 값이다.

: 최소 상한

  모든 상계보다 아래에 있는 상계다. 사슬이 쌓아 온 정보만 합치고, 갑자기 새 정보를
  보태지 않은 값이다.

# 프리도메인은 모든 사슬의 극한을 제공한다
%%%
tag := "ch02-predomain"
file := "ch02-predomain"
number := false
%%%

`Predomain`은 각 사슬에 최소 상한을 골라 주고, 그 선택이 실제 최소 상한임을 증명으로
묶는다.

```anchor Predomain (module := Reynolds.Answers.Ch02.Domain)
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
```

이 저장소의 `Domain α`는 프리도메인에 최소원 `⊥`이 추가된 경우다. Lean에서는
`Predomain α`와 `OrderBot α`를 함께 요구하는 축약 이름으로 둔다. 최소 고정점의 유한
근사를 시작하려면 아무 종료 정보도 없는 `⊥`이 필요하다.

Mathlib에는 이미 더 일반적인 순서론 구조가 있지만, 이 절에서는 Reynolds의 정의와 증명을
따라가기 위해 작은 `Chain`과 `Predomain`을 직접 만든다. 라이브러리 대응물을 가져와
정리를 한 줄로 끝내면 §2.3의 학습 대상이 사라진다.

# 연속성은 극한에서 정보가 갑자기 생기지 않게 한다
%%%
tag := "ch02-continuity"
file := "ch02-continuity"
number := false
%%%

단조 함수는 두 근사 사이의 순서를 보존한다. 연속 함수는 여기서 더 나아가, 사슬을 끝까지
합친 뒤 함수를 적용한 값이 각 근사에 함수를 적용해 합친 값과 맞도록 한다.

```anchor Continuous (module := Reynolds.Answers.Ch02.Domain)
/--
연속(continuous) — 사슬의 극한을 함수상의 극한으로 보낸다.

Reynolds는 단조 함수에 대해 이 보존 조건을 정의한다. 여기서는 보존 조건만 적고
`x, y, y, …` 사슬을 이용해 단조성을 정리로 유도한다. 공역도 프리도메인일 때는
Reynolds의 두 조건과 같은 함수 부류를 표현한다. 다만 이 정의 자체는 공역의 모든 사슬에
최소 상계가 있다고 가정하지 않고, 각 상 사슬의 최소 상계가 `f c.lub`라고 직접 요구한다.
-/
def Continuous [PartialOrder α] [PartialOrder β] [Predomain α] (f : α → β) : Prop :=
  ∀ c : Chain α, IsLUB (f '' Set.range c.seq) (f c.lub)
```

이 정의는 등식 하나를 직접 쓰지 않는다. `f c.lub`가 `f`를 사슬의 각 항에 적용해 얻은
값들의 최소 상한이라고 말한다. 공역 전체에 `Predomain` 인스턴스를 요구하지 않고도
해당 상의 극한 보존을 표현하기 위해서다.

현재 정의에서는 연속성으로부터 단조성을 증명한다. `x ⊑ y`일 때
`x, y, y, …`라는 사슬을 만들면, 그 극한은 `y`다. 연속성이 이 사슬의 상에 대해
`f x ⊑ f y`를 준다.

명제 2.1은 연속성 증명에서 확인할 방향을 줄여 준다.

```anchor continuous_iff_le (module := Reynolds.Answers.Ch02.Domain)
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
```

단조성만으로 충분하지 않은 이유는 무한한 극한에서만 새 정보를 내는 함수가 있기 때문이다.

# 단조지만 연속이 아닌 함수
%%%
tag := "ch02-monotone-counterexample"
file := "ch02-monotone-counterexample"
number := false
%%%

자연수의 유한 시작 구간을 하나씩 늘리는 사슬을 생각한다.

```
∅ ⊆ {0} ⊆ {0, 1} ⊆ {0, 1, 2} ⊆ ⋯
```

이 사슬의 극한은 자연수 전체다. `f s = (s = ℕ)`로 두면 각 유한 근사에서 `f s`는
거짓이고, 극한에서만 참이다.

```anchor exists_monotone_not_continuous (module := Reynolds.Answers.Ch02.Domain)
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
```

Reynolds는 수직 자연수 `ℕ⊤`을 사용한다. 이 저장소는 Mathlib의 완비 격자 인스턴스를
활용할 수 있는 `Set ℕ`으로 같은 구조의 반례를 옮겼다. 유한 근사에서는 보이지 않던 정보가
극한에서만 생긴다는 논점은 같다.

# `Option` 사슬의 극한
%%%
tag := "ch02-flat-domain"
file := "ch02-flat-domain"
number := false
%%%

평평한 `Option α` 사슬은 계속 `none`으로 남거나, 어느 시점에 `some a`가 나온 뒤
그 값으로 고정된다. 서로 다른 두 `some` 값은 비교되지 않으므로, 증가 사슬 안에서 종료
결과가 다른 값으로 바뀔 수 없다.

`flatPredomain`은 이 관찰을 프리도메인 인스턴스로 만든다. “언젠가 `some a`가 나오는가”는
일반적으로 판정할 수 없어서 극한 선택에 `Classical.choice`를 쓴다. 이 정의가
`noncomputable`인 것은 실행기의 결함이 아니다. 임의의 계산이 언젠가 끝나는지를 극한
함수가 계산해 준다면 정지 문제를 풀 수 있기 때문이다.

`Monotone.continuous_of_lub_mem` 정리는 평평한 정의역에서 단조 함수가 연속임을 보인다.
평평한 사슬의 극한은 새 값이 아니라 사슬이 실제로 지나간 값이므로, 극한에서 갑자기 생길
정보가 없다.

# 상태 변환 함수의 극한은 입력마다 잰다
%%%
tag := "ch02-function-space"
file := "ch02-function-space"
number := false
%%%

`while`의 후보 의미는 함수 `State V → SigmaBot V`다. 최소 고정점 정리를 이 함수들
사이에서 쓰려면 함수 공간 자체에도 사슬의 극한이 있어야 한다.

````anchor piPredomain (module := Reynolds.Answers.Ch02.Domain.FunctionSpace)
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
````

`(⨆ₙ fₙ) σ`는 입력 `σ` 하나를 고정한 뒤 결과들의 평평한 사슬을 합친 값이다.
어떤 입력에서는 3단계에 종료 결과가 나타나고, 다른 입력에서는 100단계에 나타나도 된다.
함수 공간의 극한은 그 차이를 입력마다 보존한다.

명제 2.2는 연속 함수들만 모은 공간도 프리도메인임을, 명제 2.3은 항등·상수·합성으로
연속 함수를 조립할 수 있음을 보인다. 2장의 `while`에는 전체 함수 공간의 점별 극한이
직접 쓰이고, 연속 함수 공간은 이후 고차 함수의 타입 의미에서 다시 필요해진다.
