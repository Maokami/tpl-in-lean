/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Answers.Ch02.Domain
public import Reynolds.Answers.Ch02.Semantics
public import Reynolds.Answers.Ch02.Domain.Flat

/-!
# §2.3 도메인과 연속 함수 (2) — 리프팅

Reynolds §2.3 의 리프팅 `P⊥` 에 대응한다. `Semantics.lean` 의 `Σ⊥ = Option (State V)` 에
순서를 얹어 도메인으로 만드는 것이 목표다.

## 어떤 순서인가

Reynolds 가 §2.3 끝에서 `Σ → Σ⊥` 의 순서를 이렇게 설명한다.

> `f ⊑ g` ⟺ 모든 `σ` 에 대해 `f σ = ⊥` 이거나 `f σ = g σ`.

정보가 늘어나는 순서다. `g` 는 `f` 와 같은 결과를 주되 더 많은 초기 상태에서 종료할 수 있다.
이 문장을 원소 하나 수준으로 내리면 `Σ⊥` 의 순서가 나온다.

```
x ⊑ y  ⟺  x = ⊥ 이거나 x = y
```

`⊥` 만 모든 것 아래에 있고, 나머지는 서로 비교되지 않는다. 이런 도메인을
**평평한 도메인(flat domain)** 이라고 부른다.

## 책과의 차이

Reynolds 의 리프팅은 임의의 예비도메인 `P` 에 `⊥` 를 더하는 일반 구성이다. 여기서는
`P` 의 순서를 쓰지 않는 판 — 집합을 이산(discrete)으로 보고 `⊥` 를 더하는 것 — 만 만든다.
2장에서 실제로 쓰는 것이 `Σ⊥` 하나이고, `Σ` 에는 애초에 순서가 없기 때문이다.

이 선택에는 이유가 하나 더 있다. `State V = V → Int` 에는 Mathlib 이 이미 점별 순서를
붙여 놓았다. 일반 리프팅을 `Option` 위의 인스턴스로 만들면 그 순서가 딸려 들어와서,
`some σ₁ ⊑ some σ₂` 가 "상태끼리 점별로 비교" 라는 **엉뚱한 뜻**이 된다. 상태는 정보의
조각이 아니라 결과 전체이므로 서로 비교되면 안 된다. 순서를 아예 받지 않는 평평한 정의가
그 사고를 원천에서 막는다.

Mathlib 의 `WithBot α` 도 같은 표현(`Option α`)에 순서를 얹지만, 안쪽 순서를 이어받는
쪽이라 여기서는 맞지 않는다.

## 읽는 순서
`Domain.lean` → 이 파일 → `Domain/FunctionSpace.lean`
-/

@[expose] public section

namespace Reynolds.Answers.Ch02

open Reynolds

universe u v

variable {α : Type u} {β : Type v}

/-! ## 1. 평평한 순서 — 어디에 있나

순서 인스턴스 자체는 `Domain/Flat.lean` 에 있다. `Option` 이 두 트리가 공유하는
루트 타입이라, 인스턴스를 이 파일에 두면 연습 트리에 복제되면서 두 벌이 되기 때문이다
(그쪽 파일 첫머리에 사정을 적어 두었다).

```
x ⊑ y  ⟺  x = ⊥ 이거나 x = y
```

이 파일은 그 순서 위의 이야기 — 사슬이 멈춘다는 것과 리프팅이 예비도메인이라는 것 — 만 다룬다.
-/


/-! ## 2. 평평한 사슬은 멈춘다

평평한 순서에서 사슬이 할 수 있는 일이 별로 없다. `⊥` 에 머물다가, 한 번 값을 내면
그 값에서 영원히 멈춘다. 값을 바꾸는 것은 순서가 허락하지 않는다.

이 관찰이 리프팅의 모든 증명을 짧게 만든다. -/

/-- 사슬이 한 번 `some a` 가 되면 그 뒤로는 계속 `some a` 다. -/
theorem Chain.flat_stabilizes {c : Chain (Option α)} {n : ℕ} {a : α}
    (h : c.seq n = some a) : ∀ m, n ≤ m → c.seq m = some a := by
  intro m hnm
  rcases c.mono hnm with h' | h'
  · rw [h] at h'; exact absurd h' (by simp)
  · rw [← h', h]

-- ANCHOR: flatPredomain
open Classical in
/--
`Σ⊥` 는 예비도메인이다 — 리프팅 구성의 본체.

사슬의 극한은 둘 중 하나다. 끝까지 `⊥` 면 `⊥`, 어디선가 `some a` 가 나왔으면 그 `a` 다
(뒤로는 값이 바뀔 수 없으므로 `a` 는 하나뿐이다).

"어디선가 값이 나왔는가" 는 판정할 수 없는 물음이라 `Classical.choice` 로 고른다.
극한이 계산되지 않는 것은 결함이 아니라 주제 그 자체다 — 극한을 계산할 수 있다면
정지 문제가 풀린다.

(문서 주석이 선언에 직접 붙어야 해서 `open Classical in` 이 이 주석 앞에 있다.)
-/
noncomputable instance flatPredomain : Predomain (Option α) where
  lub c :=
    if h : ∃ n a, c.seq n = some a then some h.choose_spec.choose else none
  lub_isLUB c := by
    by_cases h : ∃ n a, c.seq n = some a
    · simp only [dif_pos h]
      set A := h.choose_spec.choose with hA
      have hNA : c.seq h.choose = some A := h.choose_spec.choose_spec
      constructor
      · -- 상계. 각 항은 아직 `⊥` 이거나 이미 그 값이다.
        rintro _ ⟨m, rfl⟩
        rcases le_total h.choose m with hm | hm
        · simp [Chain.flat_stabilizes hNA m hm]
        · have hle := c.mono hm
          rw [hNA] at hle
          exact hle
      · -- 최소. 다른 상계도 `some A` 위에 있어야 하는데, 평평해서 같을 수밖에 없다.
        intro b hb
        have hb' := hb ⟨h.choose, rfl⟩
        rw [hNA] at hb'
        simp only [Option.some_le_iff] at hb'
        rw [hb']
    · -- 값이 한 번도 나오지 않았다. 극한은 `⊥` 다.
      simp only [dif_neg h]
      simp only [not_exists] at h
      constructor
      · rintro _ ⟨m, rfl⟩
        rcases hm : c.seq m with _ | a
        · simp
        · exact absurd hm (h m a)
      · intro _ _; simp
-- ANCHOR_END: flatPredomain

/-! ## 3. 평평한 도메인에서 연속은 공짜다

Reynolds 가 §2.3 에서 지나가며 말하는 사실이다. 평평한 사슬은 멈추므로 극한이 사슬
**안에** 있다. 그러면 단조 함수는 자동으로 극한을 보존한다.

이 사실을 일반화해서 증명해 둔다 — "극한이 값 목록 안에 있으면 단조로 충분하다".
§2.4 에서 `Σ⊥` 로 가는 함수들의 연속성을 확인할 때 이 정리 하나로 끝나는 경우가 많다. -/

/-- 평평한 사슬의 극한은 사슬이 실제로 지나간 값이다. -/
theorem Chain.flat_lub_mem_range (c : Chain (Option α)) : c.lub ∈ Set.range c.seq := by
  rcases hl : c.lub with _ | a
  · -- 극한이 `⊥` 다. 첫 항도 `⊥` 여야 한다 — 아니면 극한이 `⊥` 위에 있어야 하니까.
    refine ⟨0, ?_⟩
    have h0 := c.le_lub 0
    rw [hl] at h0
    simpa using h0
  · -- 극한이 `some a` 다. 어느 항이 그 값을 내야 한다.
    by_contra hne
    -- 모든 항이 `some a` 가 아니라면, "some a 가 나온 자리를 none 으로 봐도" 상계가 된다.
    -- 실제로는 더 간단하다: 모든 항이 ⊥ 이거나 some a 인데, some a 인 항이 없다는 뜻이므로
    -- 모든 항이 ⊥ 이고, 그러면 ⊥ 이 상계라서 극한 some a ≤ ⊥ — 모순.
    have hall : ∀ n, c.seq n = none := by
      intro n
      have hn := c.le_lub n
      rw [hl] at hn
      rcases hn with h | h
      · exact h
      · exact absurd (⟨n, h⟩ : (some a : Option α) ∈ Set.range c.seq) hne
    have := c.lub_le (b := none) fun n => by rw [hall n]
    rw [hl] at this
    simp at this

-- ANCHOR: monotoneContinuous
/--
극한이 사슬 안에 있으면 단조 함수는 연속이다.

상계 쪽은 단조성 그대로다. 최소 쪽이 요점이다 — 극한이 `c.seq N` 이면 `f c.lub` 자체가
상의 원소라서, 상의 어떤 상계도 그 위에 있다.

`Domain.lean` 의 반례(`f s = (s = ℕ)`)와 나란히 놓으면 그림이 완성된다. 멱집합 도메인은
극한이 사슬 밖에 있을 수 있어 단조로 부족했고, 평평한 도메인은 극한이 언제나 안에 있어
단조로 충분하다.
-/
@[exercise "§2.3 flat-continuous" 2]
theorem Monotone.continuous_of_lub_mem [PartialOrder α] [PartialOrder β] [Predomain α]
    {f : α → β} (hf : Monotone f)
    (hmem : ∀ c : Chain α, c.lub ∈ Set.range c.seq) : Continuous f := by
  intro c
  constructor
  · rintro _ ⟨x, ⟨n, rfl⟩, rfl⟩
    exact hf (c.le_lub n)
  · intro b hb
    obtain ⟨N, hN⟩ := hmem c
    exact hb ⟨c.seq N, ⟨N, rfl⟩, by rw [hN]⟩
-- ANCHOR_END: monotoneContinuous

/-- 평평한 도메인 판. `Σ⊥` 를 정의역으로 갖는 단조 함수는 전부 연속이다. -/
theorem Monotone.flat_continuous [PartialOrder β] {f : Option α → β} (hf : Monotone f) :
    Continuous f :=
  Monotone.continuous_of_lub_mem hf Chain.flat_lub_mem_range

/-! ## 4. 명제 2.4 — 리프팅된 함수들

`Semantics.lean` 에서 이미 만난 두 구성에 순서의 언어를 입힌다.

| Reynolds | §2.2 에서 | 하는 일 |
|---|---|---|
| `ι` | `some` | 값을 `Σ⊥` 로 들여보낸다 |
| `f⊥⊥` | `liftBot f` = `Option.bind · f` | `⊥` 는 `⊥` 로, 값은 `f` 로 |

명제 2.4 의 핵심 주장은 **유일성**이다. `g : Σ⊥ → Σ⊥` 가 순(strict)이고 — `⊥` 를 `⊥` 로
보내고 — 값에서 `f` 와 같다면, `g` 는 `f⊥⊥` 일 수밖에 없다. 정의역이 `⊥` 아니면 값이라
다른 자리가 없기 때문이다. -/

/-- `f⊥⊥` 는 순(strict)이다 — `⊥` 를 `⊥` 로 보낸다. -/
theorem liftBot_none {V : Type u} (f : State V → SigmaBot V) : liftBot f none = none := rfl

/-- `f⊥⊥` 는 값에서 `f` 다. -/
theorem liftBot_some {V : Type u} (f : State V → SigmaBot V) (σ : State V) :
    liftBot f (some σ) = f σ := rfl

-- ANCHOR: prop24
/--
**명제 2.4 — `f⊥⊥` 는 `f` 의 유일한 순 확장이다.**

`⊥` 에서 `⊥` 를 내고 값에서 `f` 와 같은 함수는 `liftBot f` 하나뿐이다.
증명은 정의역을 두 가지로 나누면 끝난다 — `Σ⊥` 에는 `⊥` 와 값밖에 없다.
-/
@[exercise "Prop 2.4" 2]
theorem liftBot_unique {V : Type u} {f : State V → SigmaBot V} {g : SigmaBot V → SigmaBot V}
    (hstrict : g none = none) (hext : ∀ σ, g (some σ) = f σ) : g = liftBot f := by
  funext x
  cases x with
  | none => rw [hstrict]; rfl
  | some σ => rw [hext]; rfl
-- ANCHOR_END: prop24

/-- `f⊥⊥` 는 단조다. 순이므로 자동이다 — `⊥ ⊑ x` 는 `⊥ = g ⊥ ⊑ g x` 로 넘어간다. -/
theorem liftBot_monotone {V : Type u} (f : State V → SigmaBot V) : Monotone (liftBot f) := by
  intro x y hxy
  rcases hxy with h | h
  · rw [h]; simp [liftBot_none]
  · subst h; exact le_refl _

/-- `f⊥⊥` 는 연속이다. 평평한 정의역에서는 단조로 충분하다 (§3). -/
theorem liftBot_continuous {V : Type u} (f : State V → SigmaBot V) :
    Continuous (liftBot f) := Monotone.flat_continuous (liftBot_monotone f)

/-! ## 5. 여기서 어디로 가나

`Σ⊥` 가 도메인이 되었다. 남은 것은 `Σ → Σ⊥` — 명령의 뜻이 실제로 사는 곳 — 이
도메인이라는 사실이다. 점별 순서와 함수 공간을 `Domain/FunctionSpace.lean` 에서 만든다.

그것까지 있으면 §2.4 에서 `while` 의 함수자

```
F(w) = fun σ => if ⟦b⟧ σ then ⟦c⟧ σ >>= w else some σ
```

가 도메인 위의 연속 함수가 되고, 최소 고정점 정리가 `⟦while b do c⟧` 를 내놓는다. -/

end Reynolds.Answers.Ch02
