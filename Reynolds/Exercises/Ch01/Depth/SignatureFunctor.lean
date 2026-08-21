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

1장의 구문과 2장의 최소 고정점을 같은 것으로 보는 관점이다.
여기서는 1장 쪽 절반, 즉 `Depth/Algebra.lean` 의 초기 대수가 왜 고정점이기도 한지를 다룬다.
`IntExp V ≃ Sig V (IntExp V)` 라는 동형이 그 내용이고, Lambek 보조정리라고 부른다.

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

함자(functor)라 부르는 이유는 `map` 이 있어서다.
`X → Y` 가 있으면 `Sig V X → Sig V Y` 를 얻는다. 자식 자리만 바뀌고 모양은 그대로다.
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

생성자별 자식 개수가 0, 0, 1, 2 로 전부 유한하다.
Reynolds 가 §2.4 에서 연속성의 근거로 드는 것이 이 유한성이다
(*"the constructors of the abstract syntax have a finite number of arguments"*).
2장에서 `f` 의 연속성으로 이어지고, 최소 고정점의 존재가 거기 걸려 있다.
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
Lambek 보조정리. 초기 대수의 구조 사상은 동형(isomorphism)이다.

```
IntExp V  ≃  Sig V (IntExp V)
```

구문에서 생성자 한 겹을 벗겨도 다시 구문이 나온다는 뜻이다.
`X = Sig V X` 라는 방정식의 해이므로 고정점이라고 부른다.
2장에서 `Y f` 가 `f (Y f) = Y f` 를 만족하는 것과 같은 종류의 사실이고,
무대가 집합이냐 도메인이냐만 다르다.

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

우리 `IntExp V` 가 정확히 이것이다:

| CSlib | 우리 |
|---|---|
| `pure v` | `.var v` — **변수는 "잎"이다** |
| `liftBind op cont` | 생성자 `op` 와 그 자식들 |
| `P.A` | `num n` / `neg` / `bin op` (연산 이름) |
| `P.B a` | 그 연산의 **자식 자리 개수** (`Empty` / `Unit` / `Bool`) |
| `bind` | **치환** (`Depth/TermMonad.lean`) |

`Depth/Algebra.lean` §5 에서 손으로 증명한 초기성이 CSlib 에는 이미 있다.
`FreeM.Interprets.iff` 의 docstring 이 그대로 이렇게 적고 있다.

> *"The universal property of the free monad. That is, `liftM handler` is the unique
> interpreter that extends the effect handler `handler`."*

동형을 실제로 세우는 일은 연습으로 남긴다.
자식을 `P.B a → …` 꼴의 함수로 바꿔야 해서 정지성 증명에 손이 조금 간다.

## 5. 이 다리의 반대쪽

2장에서 `Depth/FixpointAlgebraically.lean` 이 같은 이야기를 도메인 쪽에서 한다:

| | 1장 (여기) | 2장 |
|---|---|---|
| 무대 | 집합 | 도메인 `D` |
| 구성 | 초기 `Sig`-대수 | 최소 고정점 `⨆ₙ Fⁿ⊥` |
| 사슬 | `∅ → Sig ∅ → Sig² ∅ → ⋯` | `⊥ ⊑ F⊥ ⊑ F²⊥ ⊑ ⋯` |
| 극한 | 여극한(colimit) | 최소 상계(join) |
| "진짜 고정점" | **Lambek** (위 §2) | `f x = x` |
| Lean | `inductive` | 직접 만든 `lfp` |
| 왜 되나 | 자식이 유한 개 | `F` 가 연속 |

표의 마지막 줄이 두 열을 잇는 자리다. Reynolds 가 §2.4 에서 그 연결을 직접 적는다.
-/

end Reynolds.Exercises.Ch01
