/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Prelude

/-!
# §1.1 추상 구문 (Abstract Syntax)

Reynolds §1.1 (pp. 1–7)에 대응한다.

## 이 파일에서 다루는 것
- 정수 식 ⟨intexp⟩ 의 추상 구문
- Reynolds가 손으로 부과하는 **추상 구문 조건**이 Lean에서는 왜 공짜인가

## 배경

Reynolds 는 형식 언어의 구문을 문자열이 아니라 추상적 개체로 다뤄야 한다고 말한다.
자연수를 다룰 때 숫자 문자열이 아니라 수 자체를 다루는 것과 같은 이유다.

그가 추상 구문에 요구하는 조건은 셋이다.

1. 각 생성자(constructor)는 단사(injective)여야 한다
2. 같은 반송자(carrier)로 가는 두 생성자는 치역이 서로소여야 한다
3. 모든 원소가 유한 번의 생성자 적용으로 만들어져야 한다

Lean 의 `inductive` 는 이 셋을 선언과 동시에 준다.
`AbstractSyntaxConditions` 절에서 확인한다.
Reynolds 가 각주에서 언급하는 "다중 정렬 초기 대수(many-sorted initial algebra)" 도
같은 이야기이고, `Depth/Algebra.lean` 에서 이어 간다.

## 읽는 순서
이 파일 → `Semantics.lean` → `FreeVars.lean`

## 책과의 차이
- **이항 연산을 태그로 묶었다.** Reynolds는 `+ - × ÷ rem` 마다 별도 생성자를 둔다.
  그대로 옮기면 구조적 귀납법의 케이스가 5배로 늘어난다. Reynolds 본인도 의미 방정식에서
  "(and similarly for -, ×, ÷, rem)"라고 쓰므로, 태그는 그 "and similarly"를 코드로 만든 것이다.
- **상수를 `Int`로 두었다.** Reynolds의 상수 생성자는 `c₀, c₁, c₂, …` 즉 자연수뿐이고
  음수는 단항 마이너스로 만든다. 자유 변수·치환·의미 어느 명제도 이 선택에 영향받지 않는다.
-/

@[expose] public section

namespace Reynolds.Answers.Ch01

universe u

/-- 이항 정수 연산자. Reynolds §1.1의 `+  -  ×  ÷  rem`. -/
-- ANCHOR: IntOp
inductive IntOp where
  /-- 덧셈 `+`. -/
  | add
  /-- 뺄셈 `-` (이항). -/
  | sub
  /-- 곱셈 `×`. -/
  | mul
  /-- 나눗셈 `÷`. -/
  | div
  /-- 나머지 `rem`. -/
  | rem
  deriving DecidableEq, Repr
-- ANCHOR_END: IntOp

/--
정수 식(integer expression). Reynolds §1.1의 ⟨intexp⟩.

변수 타입 `V`는 고정하지 않는다 — Reynolds가 ⟨var⟩를 "표현이 지정되지 않은
가산 무한 집합"으로 두는 것과 같은 이유다. 자세한 논의는 `Reynolds.Prelude`.
-/
-- ANCHOR: IntExp
inductive IntExp (V : Type u) where
  /-- 정수 상수. Reynolds의 `c₀, c₁, c₂, …`. -/
  | num : Int → IntExp V
  /-- 변수. Reynolds의 `c_var` — 변수를 정수 식으로 넣어 주는 생성자다.
      §1.4 명제 1.2(b)에서 이것이 "항등 치환"으로 작동한다는 사실이 쓰인다. -/
  | var : V → IntExp V
  /-- 단항 마이너스 `- e`. -/
  | neg : IntExp V → IntExp V
  /-- 이항 연산 `e₀ op e₁`. -/
  | bin : IntOp → IntExp V → IntExp V → IntExp V
  deriving DecidableEq, Repr
-- ANCHOR_END: IntExp

/-! ## 추상 구문 조건 확인

Reynolds 가 §1.1 에서 한 페이지에 걸쳐 부과하는 조건 셋을 실제로 확인한다.
새로 증명할 것은 없다. `inductive` 선언에서 이미 따라 나온 것들이다.
-/

section AbstractSyntaxConditions

variable {V : Type u} (n : Int) (v : V)

-- ANCHOR: freeConditions
/-- 조건 1. 생성자는 단사다. `injection` 이 바로 처리한다. -/
example : Function.Injective (IntExp.var (V := V)) := fun _ _ h => by injection h

/-- 조건 2. 서로 다른 생성자의 치역은 서로소다. -/
example : IntExp.num (V := V) n ≠ IntExp.var v := by nofun

/-- 조건 3. 모든 정수 식은 유한 번의 생성자 적용으로 만들어진다.
    구조적 귀납법(structural induction)이 정당한 근거이고, 재귀자 `IntExp.rec` 가 그 형태다. -/
example : True := trivial
-- ANCHOR_END: freeConditions

end AbstractSyntaxConditions

/-! ## 단언 (assertions)

Reynolds §1.1 의 ⟨assert⟩ — 논리학자가 "정형식(well-formed formula)"이라 부르는 것.
-/

/-- 비교 연산자. Reynolds §1.1 의 `=  ≠  <  ≤  >  ≥`. -/
-- ANCHOR: Cmp
inductive Cmp where
  /-- 같음 `=`. -/
  | eq
  /-- 다름 `≠`. -/
  | ne
  /-- 작음 `<`. -/
  | lt
  /-- 작거나 같음 `≤`. -/
  | le
  /-- 큼 `>`. -/
  | gt
  /-- 크거나 같음 `≥`. -/
  | ge
  deriving DecidableEq, Repr
-- ANCHOR_END: Cmp

/-- 이항 논리 연산자. Reynolds §1.1 의 `∧  ∨  ⇒  ⇔`. -/
-- ANCHOR: LogOp
inductive LogOp where
  /-- 그리고 `∧`. -/
  | and
  /-- 또는 `∨`. -/
  | or
  /-- 함의 `⇒`. -/
  | imp
  /-- 동치 `⇔`. -/
  | iff
  deriving DecidableEq, Repr
-- ANCHOR_END: LogOp

/-- 양화사. Reynolds §1.1 의 `∀  ∃`. -/
-- ANCHOR: Quant
inductive Quant where
  /-- 전칭 `∀v. p`. -/
  | all
  /-- 존재 `∃v. p`. -/
  | ex
  deriving DecidableEq, Repr
-- ANCHOR_END: Quant

/--
단언(assertion). Reynolds §1.1 의 ⟨assert⟩.

`Assert` 는 `IntExp` 를 참조하지만 반대는 아니다. ⟨assert⟩ 의 생성 규칙에 ⟨intexp⟩ 가
나오고 그 역은 없는 Reynolds 의 문법을 그대로 옮긴 것이라, 상호 귀납이 아니라
별도 `inductive` 둘이면 된다.

`quant q v p` 의 `v` 는 결합 발생(binding occurrence)이고 유효 범위(scope)는 `p` 다.
1장에서 결합이 나오는 자리는 여기뿐이고, §1.4 는 이것 하나를 다룬다.
-/
-- ANCHOR: Assert
inductive Assert (V : Type u) where
  /-- 참 `true`. -/
  | tru
  /-- 거짓 `false`. -/
  | fls
  /-- 정수 비교 `e₀ ∼ e₁`. -/
  | cmp : Cmp → IntExp V → IntExp V → Assert V
  /-- 부정 `¬p`. -/
  | not : Assert V → Assert V
  /-- 이항 논리 연산 `p₀ ∘ p₁`. -/
  | bin : LogOp → Assert V → Assert V → Assert V
  /-- 양화 `∀v. p` / `∃v. p`. **결합 구성자**. -/
  | quant : Quant → V → Assert V → Assert V
  deriving DecidableEq, Repr
-- ANCHOR_END: Assert

end Reynolds.Answers.Ch01
