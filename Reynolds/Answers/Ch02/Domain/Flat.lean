/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Prelude

/-!
# `Option` 의 평평한 순서 — 두 트리가 공유하는 층

`Σ⊥ = Option (State V)` 에 얹는 순서다. 개념 설명은 `Domain/Lifting.lean` 에 있고,
여기는 인스턴스 선언만 있다.

## 왜 이 파일이 따로 있나

`Option` 은 Lean 의 루트 타입이라 Answers 와 Exercises 두 트리가 공유한다.
이 파일이 두 트리에 복제되면 **같은 타입에 순서 인스턴스가 두 벌** 등록된다 —
타입클래스 해소가 애매해지고, simp 보조정리는 서로의 중복이 되어 린터에 걸린다.

`Notation.lean` 의 구문 범주가 전역이라 공유했던 것과 같은 사정이다.
그래서 이 파일은 `scripts/gen-exercises.py` 의 `SHARED` 에 들어 있고,
연습 트리도 이쪽을 그대로 import 한다.

`Chain` 과 `Predomain` 을 쓰는 내용은 여기 없다. 그 둘은 트리마다 따로 정의되는
장 코드라서, 그쪽 층은 `Domain/Lifting.lean` 에 남아 트리별로 복제된다.
-/

@[expose] public section

namespace Reynolds

universe u

variable {α : Type u}

/-- 평평한 순서의 `≤`. `x ⊑ y ⟺ x = ⊥ 이거나 x = y`. -/
instance flatLE : LE (Option α) := ⟨fun x y => x = none ∨ x = y⟩

theorem Option.le_def {x y : Option α} : x ≤ y ↔ (x = none ∨ x = y) := Iff.rfl

@[simp] theorem Option.none_le (x : Option α) : (none : Option α) ≤ x := Or.inl rfl

@[simp] theorem Option.some_le_iff {a : α} {x : Option α} : some a ≤ x ↔ x = some a := by
  constructor
  · rintro (h | h)
    · exact absurd h (by simp)
    · exact h.symm
  · rintro rfl; exact Or.inr rfl

@[simp] theorem Option.le_none_iff {x : Option α} : x ≤ none ↔ x = none := by
  constructor
  · rintro (h | h) <;> exact h
  · rintro rfl; exact Or.inl rfl

/--
`Σ⊥` 의 평평한 순서. `⊥` 만 모든 것 아래에 있고 나머지는 서로 비교되지 않는다.

`x ⊑ y` 는 "`x` 가 말하는 것은 `y` 도 말한다" 다. `⊥` 는 아무것도 말하지 않으므로
모든 것 아래에 있고, 상태 둘은 서로 다른 것을 말하므로 나란히 설 수 없다.
-/
instance flatPartialOrder : PartialOrder (Option α) where
  le_refl _ := Or.inr rfl
  le_trans x y z hxy hyz := by
    rcases hxy with h | h
    · exact Or.inl h
    · rw [h]; exact hyz
  le_antisymm x y hxy hyx := by
    rcases hxy with h | h
    · rcases hyx with h' | h'
      · rw [h, h']
      · exact h'.symm
    · exact h

/-- `⊥ = none`. 비종료를 `none` 으로 읽은 §2.2 의 선택과 표기가 만난다. -/
instance flatOrderBot : OrderBot (Option α) where
  bot := none
  bot_le := Option.none_le

@[simp] theorem Option.bot_eq_none : (⊥ : Option α) = none := rfl

end Reynolds
