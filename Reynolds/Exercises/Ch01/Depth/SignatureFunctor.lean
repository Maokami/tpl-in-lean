/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Exercises.Ch01.Depth.Algebra

/-!
# 심화 B · 시그니처 함자와 Lambek

선택 파일이다. `Depth/Algebra.lean` 을 먼저 읽어야 한다.

## 시작점

Reynolds 는 §2.4 끝에서 §1.1 의 추상 문법 정의를 다시 꺼낸다.

> *"By the least fixed-point theorem, `s` is the least solution of `s = f s`. …
> Of course, this depends on the function `f` being **continuous**. In fact, the continuity of `f`
> stems from the fact that each `fᵢ` is **finitely generated**, which in turn stems from the fact
> that **the constructors of the abstract syntax have a finite number of arguments**."*

인용문은 1장의 추상 구문 반송자를 부분집합 격자 위의 최소 고정점으로 다시 구성한다.
그 구성으로 가기 전에, 이 파일은 `Depth/Algebra.lean`의 초기 대수를 함자 하나의 대수로
다시 적는다. 생성자 한 겹을 나타내는 `Sig V`를 정의하면 항 대수의 구조 사상은
`roll : Sig V (IntExp V) → IntExp V`가 된다. 초기 대수의 구조 사상이 동형이라는 일반
명제가 Lambek 보조정리이며, 여기서는 그 동형을 `roll`과 `unroll`로 직접 계산한다.

## 사전 지식
`Depth/Algebra.lean`. 함자(functor)는 이 파일 §1 에서 설명한다.

## 읽는 순서
`Depth/Algebra.lean` → 이 파일 → (2장) `Depth/FixpointAlgebraically.lean`
-/

@[expose] public section

namespace Reynolds.Exercises.Ch01

universe u v w x

/-! ## 1. 시그니처를 함자로 보기

`IntExp` 의 정의를 다시 보자.

```
inductive IntExp (V) where
  | num : Int → IntExp V
  | var : V → IntExp V
  | neg : IntExp V → IntExp V
  | bin : IntOp → IntExp V → IntExp V → IntExp V
```

재귀를 **한 겹만 벗겨** 보자. 자식 자리에 `IntExp V` 대신 아무 타입 `X` 를 넣으면: -/

/--
**시그니처 함자(signature functor)** — 생성자를 한 겹만 적은 것.

`Sig V X` 는 정수 식 한 겹이고 자식 자리에 `X` 가 들어간다. 정의에 재귀가 없다.
`X := IntExp V` 를 넣으면 원래 `IntExp V` 의 생성자 목록이 그대로 나온다.

고정된 `V`에 대해 `X ↦ Sig V X`는 `Type` 위의 자기함자(endofunctor)다.
아래 `map`이 함수 `X → Y`를 `Sig V X → Sig V Y`로 보내고, `map_id`와 `map_comp`가
항등과 합성을 보존함을 확인한다. Mathlib의 `CategoryTheory.Functor` 구조체로 포장하지는
않지만 필요한 데이터와 법칙은 이 둘이다.
-/
inductive Sig (V : Type u) (X : Type v) where
  /-- 상수. 자식이 **0개**다. -/
  | num : Int → Sig V X
  /-- 변수. 자식이 0개다. -/
  | var : V → Sig V X
  /-- 단항 마이너스. 자식이 **1개**. -/
  | neg : X → Sig V X
  /-- 이항 연산. 자식이 **2개**. -/
  | bin : IntOp → X → X → Sig V X

/--
함자의 `map`. 자식 자리에만 `f` 를 적용한다.

생성자별 재귀 자리가 0, 0, 1, 2개라서 `Sig V`는 유한 항수의 다항 함자다.
Reynolds §2.4의 부분집합 격자 구성에서는 이 유한 항수가 각 생성자 연산의 유한 생성성과
그 결과로 얻는 사슬 연속성을 뒷받침한다. `map`이 있다는 사실만으로 임의의 함자가
연속인 것은 아니며, 여기서 필요한 것은 이 시그니처가 유한한 자릿수만 검사한다는 점이다.
-/
def Sig.map {V : Type u} {X : Type v} {Y : Type w} (f : X → Y) : Sig V X → Sig V Y
  | .num n        => .num n
  | .var v        => .var v
  | .neg x        => .neg (f x)
  | .bin op x₀ x₁ => .bin op (f x₀) (f x₁)

/-- 함자 법칙 (1) — 항등을 옮기면 항등이다. -/
theorem Sig.map_id {V : Type u} {X : Type v} (s : Sig V X) : Sig.map id s = s := by
  cases s <;> rfl

/-- 함자 법칙 (2) — 합성을 옮기면 합성이다. -/
theorem Sig.map_comp {V : Type u} {X : Type v} {Y : Type w} {Z : Type x}
    (f : X → Y) (g : Y → Z) (s : Sig V X) :
    Sig.map g (Sig.map f s) = Sig.map (g ∘ f) s := by
  cases s <;> rfl

/-! ## 2. Lambek 보조정리 -/

/-- 한 겹 감싸기: `Sig V (IntExp V) → IntExp V`. **대수의 구조 사상**이다. -/
def IntExp.roll {V : Type u} : Sig V (IntExp V) → IntExp V
  | .num n        => .num n
  | .var v        => .var v
  | .neg e        => .neg e
  | .bin op e₀ e₁ => .bin op e₀ e₁

/-- 한 겹 벗기기: `IntExp V → Sig V (IntExp V)`. -/
def IntExp.unroll {V : Type u} : IntExp V → Sig V (IntExp V)
  | .num n        => .num n
  | .var v        => .var v
  | .neg e        => .neg e
  | .bin op e₀ e₁ => .bin op e₀ e₁

/--
Lambek 보조정리의 이 구문 인스턴스. 초기 대수의 구조 사상은 동형(isomorphism)이다.

```
IntExp V  ≃  Sig V (IntExp V)
```

`roll : Sig V (IntExp V) → IntExp V`가 구조 사상이고, 이 정의는 그 역인 `unroll`을
함께 주어 동형을 표현한다. `IntExp V ≃ Sig V (IntExp V)`는 같은 동형을 역방향 함수부터
적은 것이다. 이런 동형 때문에 반송자 `IntExp V`를 `Sig V`의 고정점이라 부른다.

일반 Lambek 보조정리는 초기성으로부터 구조 사상의 가역성을 유도한다. 반대로 구조 사상이
가역이라는 사실만으로 그 대수가 초기라는 결론은 나오지 않는다. 이 파일의 `cases` 증명은
Lean의 `inductive`가 이미 만든 구체적인 고정점을 확인하고, 초기성 자체는
`Depth/Algebra.lean`의 `IntExp.initial`이 담당한다.

2장의 `Y f`는 순서가 있는 한 도메인의 원소에 대한 자기함수 `f : D → D`의 **최소**
고정점이다. 두 구성은 재귀 방정식의 해를 보편 성질로 고른다는 유사성이 있지만,
Lambek 동형 자체에는 근사 순서나 최소성 조건이 들어 있지 않다.

Lean 에서 `roll` 과 `unroll` 은 생성자를 그대로 옮기므로 증명이 `cases` 한 줄로 끝난다.
`inductive` 를 쓰는 시점에 고정점이 이미 만들어져 있기 때문이다.
-/
@[exercise "심화 B1.1" 2]
def IntExp.lambek (V : Type u) : IntExp V ≃ Sig V (IntExp V) where
  toFun := IntExp.unroll
  invFun := IntExp.roll
  left_inv e := by sorry
  right_inv s := by sorry

/-- `roll` 이 대수 연산임을 확인 — 항 대수의 구조 사상이 바로 이것이다. -/
theorem IntExp.roll_unroll {V : Type u} (e : IntExp V) : IntExp.roll (IntExp.unroll e) = e := by
  cases e <;> rfl

/-! ## 3. `fold` 를 함자로 다시 쓰기

`Depth/Algebra.lean` 의 `fold` 를 함자 어휘로 옮기면 이렇게 된다:

```
fold A = A.structureMap ∘ Sig.map (fold A) ∘ unroll
```

한 겹 벗기고, 자식들을 재귀적으로 접고, 대수의 연산으로 합친다.

이 꼴을 catamorphism 이라고 부른다. 함수형 프로그래밍의 `foldr` 이 리스트에 하는 일과 같고,
리스트는 시그니처가 `Sig X = nil | cons a X` 인 경우에 해당한다. -/

/-- 대수를 "구조 사상 하나"로 압축한 것. `Sig V C → C` 가 곧 대수다. -/
def IntExpAlg.structureMap {V : Type u} (A : IntExpAlg.{u, v} V) : Sig V A.Carrier → A.Carrier
  | .num n        => A.num n
  | .var v        => A.var v
  | .neg c        => A.neg c
  | .bin op c₀ c₁ => A.bin op c₀ c₁

/-- `fold` 가 정말 "벗기고 · 재귀하고 · 합치기" 임을 확인한다. -/
theorem IntExpAlg.fold_eq {V : Type u} (A : IntExpAlg.{u, v} V) (e : IntExp V) :
    A.fold e = A.structureMap (Sig.map A.fold (IntExp.unroll e)) := by
  cases e <;> rfl

/-! ## 4. CSlib 의 자유 모나드와의 관계

CSlib 에는 **다항 함자 위의 자유 모나드**가 이미 있다:
`Cslib/Foundations/Data/PFunctor/Free.lean` 의 `PFunctor.FreeM`.

```
inductive FreeM (P : PFunctor) : Type v → Type _
  | pure : α → FreeM P α
  | liftBind (a : P.A) (cont : P.B a → FreeM P α) : FreeM P α
```

적절한 다항 시그니처를 고르면 모든 변수 타입 `V`에 대해 `IntExp V`와 `FreeM P V`의
대응을 만들 수 있다. 아래 표는 생성자 수준의 대응이고, 아직 타입 동형이나 모나드 동형을
증명한 것은 아니다.

| CSlib | 우리 |
|---|---|
| `pure v` | `.var v` — **변수는 "잎"이다** |
| `liftBind op cont` | 생성자 `op` 와 그 자식들 |
| `P.A` | `num n` / `neg` / `bin op` (연산 이름) |
| `P.B a` | 그 연산의 **자식 자리 개수** (`Empty` / `Unit` / `Bool`) |
| `bind` | **치환** (`Depth/TermMonad.lean`) |

CSlib의 `FreeM.Interprets.iff`에는 이와 관련되지만 층이 다른 보편 성질이 있다.
그 정리는 효과 handler를 확장하는 모나드 interpreter가 유일하다고 말한다.

> *"The universal property of the free monad. That is, `liftM handler` is the unique
> interpreter that extends the effect handler `handler`."*

`Depth/Algebra.lean`의 `IntExp.initial`은 변수 타입 `V`를 고정한 뒤 임의의
`IntExpAlg V`로 가는 대수 준동형의 유일성을 말한다. 둘을 대응시키려면 모든 변수 타입에
자연적인 동형을 세우고 그 동형이 `pure`와 `bind`, 각 생성자를 보존함을 따로 증명해야 한다.
고정된 `V` 하나에서의 타입 동형만으로는 충분하지 않다. 이 파일은 그 동형과 호환성 증명을
연습으로 남긴다.

자식을 `P.B a → …` 꼴의 함수로 바꾸는 실제 동형과, 그 동형이 모든 `V`에서 자연하며
`pure`와 `bind`를 보존한다는 증명은 후속 연습의 범위다.

## 5. 고정점이라는 말이 가리키는 것들

2장에서 다루는 고정점과 여기의 함자 고정점은 방정식의 타입부터 다르다.
아래 표는 재귀 대상을 유한 근사에서 구성한다는 공통점을 보여 주되, 같은 정리로 합치지 않는다.

| | 1장 (여기) | 2장 |
|---|---|---|
| 무대 | 집합 | 도메인 `D` |
| 구성 | 초기 `Sig`-대수 | 최소 고정점 `⨆ₙ Fⁿ⊥` |
| 사슬 | `∅ → Sig ∅ → Sig² ∅ → ⋯` | `⊥ ⊑ F⊥ ⊑ F²⊥ ⊑ ⋯` |
| 극한 | 여극한(colimit) | 최소 상계(join) |
| 방정식의 모양 | `X ≃ Sig V X` (Lambek) | `f x = x` |
| Lean | `inductive` | 직접 만든 `lfp` |
| 고정점 방정식이 성립하는 이유 | Lambek 보조정리 | 자기함수의 연속성과 완비성 |

여기서는 세 대상을 구분해야 한다. Reynolds §2.4는 생성자를 반복해 구문 반송자를 만든다.
2장의 `Y`는 명령 의미가 사는 함수 도메인에서 최소 고정점을 고른다. Lambek 보조정리는
초기 대수의 구조 사상이 동형임을 말한다. 유한 생성에서 연속성으로 이어지는 연결은 있지만,
셋은 같은 구성이 아니다.
-/

end Reynolds.Exercises.Ch01
