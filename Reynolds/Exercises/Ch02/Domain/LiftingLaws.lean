/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Exercises.Ch02.Domain.Lifting

/-!
# §2.3 명제 2.4 — 이산 집합에서의 리프팅 법칙

Reynolds 명제 2.4(p. 35)는 리프팅의 유일성과 합성을 다룬다.
`Flat.map f : Flat α → Flat β`는 결과도 리프팅하고,
`sourceLift g : Flat α → D`는 이미 바닥이 있는 도메인으로 값을 보낸다.
예를 들어 `g : State V → Flat (State V)`라면 두 번째 구성이 `liftBot g`다.

**책과의 차이**: 책의 `P`, `P'`, `P''`는 임의의 프리도메인이다.
여기서는 이산 순서의 집합 `α`, `β`, `γ`에 한정하여 `Flat`을 사용한다.
그 집합 사이의 함수는 모두 연속이다. 아래 등식에는 극한 자체가 쓰이지 않으므로
공역의 바닥만 요구한다. `sourceLift_continuous`가 순서와 연속성을 별도로 확인한다.
임의의 기존 순서를 보존하는 `P⊥` 구성과 리프팅 모나드는 후속 실습이다.

읽는 순서: `Lifting.lean` → 이 파일 → `FunctionSpace.lean`.
-/

@[expose] public section

namespace Reynolds.Exercises.Ch02

open Reynolds

universe u v w

namespace FlatLift

variable {α : Type u} {β : Type v} {γ : Type w}

/-- §2.3(p. 34)의 source-lifting. 입력에 바닥을 더하고 그 바닥을 공역의 바닥으로 보낸다. -/
def sourceLift [Bot β] (f : α → β) : Flat α → β
  | .none => ⊥
  | .some a => f a

/-- 입력 바닥은 공역의 바닥으로 간다. 이것이 순(strict)이라는 조건이다. -/
@[simp] theorem sourceLift_none [Bot β] (f : α → β) : sourceLift f .none = ⊥ := rfl

/-- 원래 입력에서는 원래 함수와 같다. -/
@[simp] theorem sourceLift_some [Bot β] (f : α → β) (a : α) :
    sourceLift f (.some a) = f a := rfl

/-- 상태 함수에 특수화하면 §2.2의 `liftBot`과 같다. -/
theorem sourceLift_eq_liftBot {V : Type u} (f : State V → SigmaBot V) :
    sourceLift f = liftBot f := by
  funext x
  cases x <;> rfl

/-- 명제 2.4(a), 이산 집합의 경우. 결과까지 리프팅하는 순 확장은 유일하다. -/
@[exercise "Prop 2.4a discrete" 1]
theorem map_unique (f : α → β) (g : Flat α → Flat β)
    (hbot : g .none = .none) (hval : ∀ a, g (.some a) = .some (f a)) :
    g = Flat.map f := by
  -- `funext x` 뒤 입력의 두 생성자를 나눈다. 두 가설을 각각 어디에 쓰는가?
  sorry

/-- 명제 2.4(b), 이산 집합의 경우. 공역은 바닥이 있는 임의의 타입이어도 된다. -/
@[exercise "Prop 2.4b discrete" 1]
theorem sourceLift_unique [Bot β] (f : α → β) (g : Flat α → β)
    (hbot : g .none = ⊥) (hval : ∀ a, g (.some a) = f a) :
    g = sourceLift f := by
  -- 바닥을 이미 가진 공역에서도 입력은 여전히 두 경우뿐이다.
  sorry

/-- 명제 2.4(c), 이산 집합의 경우. 합성한 뒤 리프팅해도 리프팅한 함수들을 합성해도 같다. -/
@[exercise "Prop 2.4c discrete" 1]
theorem map_comp (f : α → β) (g : β → γ) :
    Flat.map (g ∘ f) = Flat.map g ∘ Flat.map f := by
  -- 입력 바닥과 입력 값에서 두 합성을 직접 계산한다.
  sorry

/-- 명제 2.4(d), 이산 집합의 경우. 중간 결과의 리프팅을 source-lifting으로 이어 붙인다. -/
@[exercise "Prop 2.4d discrete" 1]
theorem sourceLift_comp_map [Bot γ] (f : α → β) (g : β → γ) :
    sourceLift (g ∘ f) = sourceLift g ∘ Flat.map f := by
  -- 중간 타입은 Flat β, 마지막 공역은 γ다. 두 입력 경우에서 타입을 따라간다.
  sorry

/-- 명제 2.4(e), 이산 입력의 경우. 뒤 함수가 바닥을 보존해야 합성이 source-lifting과 교환한다. -/
@[exercise "Prop 2.4e discrete" 2]
theorem sourceLift_comp_strict [Bot β] [Bot γ] (g : α → β) (h : β → γ)
    (hstrict : h ⊥ = ⊥) : sourceLift (h ∘ g) = h ∘ sourceLift g := by
  -- 바닥 입력에서만 hstrict가 필요하다. 오른쪽의 h ⊥와 왼쪽의 ⊥를 비교한다.
  sorry

/-- 순 확장은 평평한 정보 순서를 보존한다. 완성된 입력들끼리는 등식만 비교한다. -/
theorem sourceLift_monotone [PartialOrder β] [OrderBot β] (f : α → β) :
    Monotone (sourceLift f) := by
  intro x y hxy
  rcases hxy with h | h
  · subst x
    exact bot_le
  · subst y
    exact le_refl _

/-- 평평한 입력 사슬은 극한에 도달하므로, 순 확장은 연속이다. 공역은 평평할 필요가 없다. -/
theorem sourceLift_continuous [PartialOrder β] [OrderBot β] (f : α → β) :
    Continuous (sourceLift f) :=
  Monotone.flat_continuous (sourceLift_monotone f)

/-- 명제 2.4(e)에서 순 조건을 빼면 바닥 입력부터 등식이 깨진다. -/
theorem nonstrict_counterexample :
    sourceLift ((fun _ : Flat Nat ↦ Flat.some 1) ∘ (fun _ : Unit ↦ Flat.none)) ≠
      (fun _ : Flat Nat ↦ Flat.some 1) ∘ sourceLift (fun _ : Unit ↦ Flat.none) := by
  intro h
  have hbot := congrFun h Flat.none
  simp [sourceLift] at hbot

end FlatLift
end Reynolds.Exercises.Ch02
