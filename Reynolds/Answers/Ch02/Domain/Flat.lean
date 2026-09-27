/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Prelude

/-!
# 평평한 결과 타입 — 두 트리가 공유하는 층

Reynolds §2.3의 평평한 리프팅을 `Flat α`로 표현한다.
`none`은 바닥이고 `some a`는 완성된 결과다. 서로 다른 결과는 비교되지 않는다.

## 내부 표현과 순서

`Flat`은 전용 귀납 타입이다. 일반 `Option`의 순서와 독립적으로 정보 순서를 준다.
`bind`는 앞 계산이 종료할 때만 다음 계산을 실행하며, 관찰은 `toOption`으로 꺼낸다.

## 두 트리가 공유하는 이유

Answers와 Exercises가 같은 결과 타입과 순서를 사용하도록 이 파일은
`scripts/gen-exercises.py`의 `SHARED`에 속한다. `Chain`과 `Predomain`은 장별
학습 코드이므로 그 위의 도메인 구성은 `Domain/Lifting.lean`에 둔다.

## 책과의 차이

임의의 순서를 보존하는 일반 리프팅 대신, 결과 집합에 바닥만 더한다.
`State V`의 점별 정수 순서는 계산 결과의 정보 순서에 반영하지 않는다.
-/

@[expose] public section

namespace Reynolds

universe u v w

-- ANCHOR: Flat
/-- 결과 집합에 바닥을 더한 평평한 타입. Reynolds §2.3의 이산 집합 리프팅이다. -/
inductive Flat (α : Type u) where
  /-- 유한한 결과를 얻지 못한 바닥. -/
  | none : Flat α
  /-- 종료하여 얻은 결과. -/
  | some : α → Flat α
  deriving DecidableEq, BEq, Repr
-- ANCHOR_END: Flat

namespace Flat

variable {α : Type u} {β : Type v} {γ : Type w}

/-- 앞 계산이 종료했을 때만 뒤 계산을 실행한다. Reynolds의 순 확장이다. -/
def bind (x : Flat α) (f : α → Flat β) : Flat β :=
  match x with
  | none => none
  | some a => f a

/-- 종료 결과에 함수를 적용한다. -/
def map (f : α → β) : Flat α → Flat β
  | none => none
  | some a => some (f a)

/-- 일반 관찰값으로 꺼낸다. 이 값의 순서는 일반 `Option`의 순서다. -/
def toOption : Flat α → Option α
  | none => Option.none
  | some a => Option.some a

/-- 유한한 결과가 없는지 확인한다. -/
def isNone : Flat α → Bool
  | none => true
  | some _ => false

/-- 종료 결과가 있는지 확인한다. -/
def isSome : Flat α → Bool
  | none => false
  | some _ => true

/-- 바닥은 종료 결과를 갖지 않는다. -/
@[simp] theorem isSome_none : (none : Flat α).isSome = false := rfl
/-- 값은 종료 결과를 갖는다. -/
@[simp] theorem isSome_some (a : α) : (some a).isSome = true := rfl
/-- 바닥 검사는 바닥에서 참이다. -/
@[simp] theorem isNone_none : (none : Flat α).isNone = true := rfl
/-- 바닥 검사는 종료 결과에서 거짓이다. -/
@[simp] theorem isNone_some (a : α) : (some a).isNone = false := rfl

/-- 바닥에 이어 붙인 계산도 바닥이다. -/
@[simp] theorem bind_none (f : α → Flat β) : bind none f = none := rfl
/-- 종료 결과는 다음 계산에 그대로 전달된다. -/
@[simp] theorem bind_some (a : α) (f : α → Flat β) : bind (some a) f = f a := rfl
/-- 바닥에 함수를 적용해도 바닥이다. -/
@[simp] theorem map_none (f : α → β) : map f none = none := rfl
/-- 종료 결과에 함수를 적용한다. -/
@[simp] theorem map_some (f : α → β) (a : α) : map f (some a) = some (f a) := rfl
/-- 바닥의 관찰값은 `Option.none`이다. -/
@[simp] theorem toOption_none : (none : Flat α).toOption = Option.none := rfl
/-- 종료 결과의 관찰값은 `Option.some`이다. -/
@[simp] theorem toOption_some (a : α) : (some a).toOption = Option.some a := rfl
/-- 종료 여부 검사는 종료 결과의 존재와 같다. -/
@[simp] theorem isSome_iff_exists {x : Flat α} : x.isSome ↔ ∃ a, x = some a := by
  cases x <;> simp [isSome]
/-- 순차 합성의 종료는 중간 결과와 뒷 계산의 종료로 분해된다. -/
theorem bind_eq_some_iff {x : Flat α} {f : α → Flat β} {b : β} :
    bind x f = some b ↔ ∃ a, x = some a ∧ f a = some b := by
  cases x <;> simp [bind]
/-- 결과 변환의 종료는 원래 결과와 그 변환값으로 분해된다. -/
theorem map_eq_some_iff {x : Flat α} {f : α → β} {b : β} :
    map f x = some b ↔ ∃ a, x = some a ∧ f a = b := by
  cases x <;> simp [map]
/-- 순차 합성의 괄호 위치는 결과를 바꾸지 않는다. -/
theorem bind_assoc (x : Flat α) (f : α → Flat β) (g : β → Flat γ) :
    bind (bind x f) g = bind x (fun a => bind (f a) g) := by
  cases x <;> rfl

/-- 평평한 순서의 `≤`. 바닥이거나 같은 결과일 때만 성립한다. -/
instance : LE (Flat α) := ⟨fun x y => x = none ∨ x = y⟩

/-- 평평한 순서를 등식으로 풀어 쓴다. -/
theorem le_def {x y : Flat α} : x ≤ y ↔ (x = none ∨ x = y) := Iff.rfl
/-- 바닥은 모든 결과 아래에 있다. -/
@[simp] theorem none_le (x : Flat α) : (none : Flat α) ≤ x := Or.inl rfl
/-- 완성된 결과 위에는 같은 결과만 있다. -/
@[simp] theorem some_le_iff {a : α} {x : Flat α} : some a ≤ x ↔ x = some a := by
  constructor
  · rintro (h | h)
    · exact absurd h (by simp)
    · exact h.symm
  · rintro rfl; exact Or.inr rfl
/-- 바닥 아래에는 바닥만 있다. -/
@[simp] theorem le_none_iff {x : Flat α} : x ≤ none ↔ x = none := by
  constructor
  · rintro (h | h) <;> exact h
  · rintro rfl; exact Or.inl rfl

/-- 바닥만 모든 결과 아래에 있고 서로 다른 결과는 비교되지 않는 부분 순서다. -/
instance : PartialOrder (Flat α) where
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

/-- `none`은 정보 순서의 바닥이다. -/
instance : OrderBot (Flat α) where
  bot := none
  bot_le := none_le

/-- 바닥 표기와 생성자는 같은 값이다. -/
@[simp] theorem bot_eq_none : (⊥ : Flat α) = none := rfl

end Flat
end Reynolds
