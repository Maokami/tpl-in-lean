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
- Reynolds가 추상 구문에 요구하는 세 조건과 Lean의 `inductive`

## 배경

Reynolds 는 형식 언어의 구문을 특정 문자열 표현과 분리한다. 의미 함수가 받는 것은
우선순위와 공백을 포함한 표기 문자열이 아니라, 어떤 생성자로 만들어졌는지가 드러나는
추상 구다. 이 파일에서는 그 추상 구를 귀납 타입으로 표현한다.

그가 추상 구문에 요구하는 조건은 셋이다.

1. 각 생성자(constructor)는 단사(injective)여야 한다
2. 같은 반송자(carrier)로 가는 두 생성자는 치역이 서로소여야 한다
3. 모든 원소가 유한 번의 생성자 적용으로 만들어져야 한다

Lean 의 `inductive` 는 생성자 단사성과 치역의 서로소성을 위한 no-confusion 원리,
유한한 생성 구조를 따라 정의하고 증명하는 재귀자와 귀납 원리를 함께 만든다.
`AbstractSyntaxConditions` 절에서는 이 셋이 코드에서 어떤 모습인지 확인한다.

Reynolds 는 이 조건들을 보편 대수의 말로 "다중 정렬 초기 대수(many-sorted initial
algebra)"라고도 부른다. 세 조건의 목록과 초기성의 보편 성질은 설명의 층이 다르다.
초기성은 임의의 목표 대수로 가는 준동형이 유일하다는 명제이며,
`Depth/Algebra.lean`에서 `fold`와 구조적 귀납법으로 별도 증명한다.

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

namespace Reynolds.Exercises.Ch01

universe u

/-- 이항 정수 연산자. Reynolds §1.1의 `+  -  ×  ÷  rem`. -/
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

/--
정수 식(integer expression). Reynolds §1.1의 ⟨intexp⟩.

변수 타입 `V`는 고정하지 않는다. Reynolds는 ⟨var⟩를 "표현이 지정되지 않은 가산 무한
집합"으로 두지만, 구문 자체에는 가산성이 필요 없어서 임의의 타입으로 일반화했다.
포획 회피 치환에서만 `HasFresh V`를 요구한다. 자세한 논의는 `Reynolds.Prelude`에 있다.
-/
inductive IntExp (V : Type u) where
  /-- 정수 상수. Reynolds의 `c₀, c₁, c₂, …`를 음의 정수까지 일반화했다. -/
  | num : Int → IntExp V
  /-- 변수. Reynolds의 `c_var` — 변수를 정수 식으로 넣어 주는 생성자다.
      §1.4 명제 1.2(b)에서 이것이 "항등 치환"으로 작동한다는 사실이 쓰인다. -/
  | var : V → IntExp V
  /-- 단항 마이너스 `- e`. -/
  | neg : IntExp V → IntExp V
  /-- 이항 연산 `e₀ op e₁`. -/
  | bin : IntOp → IntExp V → IntExp V → IntExp V
  deriving DecidableEq, Repr

/-! ## 추상 구문 조건 확인

Reynolds 가 §1.1 에서 한 페이지에 걸쳐 부과하는 조건 셋을 실제로 확인한다.
새로 증명할 것은 없다. `inductive` 선언에서 이미 따라 나온 것들이다.
-/

section AbstractSyntaxConditions

variable {V : Type u} (n : Int) (v : V)

/-- 조건 1. 생성자는 단사다. `injection`이 바로 처리한다. -/
example : Function.Injective (IntExp.var (V := V)) := fun _ _ h => by injection h

/-- 조건 2. 서로 다른 생성자의 치역은 서로소다. -/
example : IntExp.num (V := V) n ≠ IntExp.var v := by nofun

-- 조건 3. 모든 정수 식은 유한 번의 생성자 적용으로 만들어진다.
-- 별도의 `True` 증명이 아니라, Lean이 생성한 재귀자 자체가 유한 구성을 따라가는 원리다.
#check IntExp.rec

end AbstractSyntaxConditions

/-! Reynolds 는 이 구문을 다중 정렬 초기 대수로 읽을 수 있다고 각주에 적는다.
여기서 확인한 생성자 성질만으로 초기성의 내용을 다 보인 것은 아니다. 임의의 목표 대수로
가는 유일한 `fold`를 구성하는 단계가 남아 있으며, `Depth/Algebra.lean`에서 그 명제를
정확히 적고 증명한다. -/

/-! ## 단언 (assertions)

Reynolds §1.1 의 ⟨assert⟩ — 논리학자가 "정형식(well-formed formula)"이라 부르는 것.
-/

/-- 비교 연산자. Reynolds §1.1 의 `=  ≠  <  ≤  >  ≥`. -/
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

/-- 이항 논리 연산자. Reynolds §1.1 의 `∧  ∨  ⇒  ⇔`. -/
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

/-- 양화사. Reynolds §1.1 의 `∀  ∃`. -/
inductive Quant where
  /-- 전칭 `∀v. p`. -/
  | all
  /-- 존재 `∃v. p`. -/
  | ex
  deriving DecidableEq, Repr

/--
단언(assertion). Reynolds §1.1 의 ⟨assert⟩.

`Assert` 는 `IntExp` 를 참조하지만 반대는 아니다. ⟨assert⟩ 의 생성 규칙에 ⟨intexp⟩ 가
나오고 그 역은 없는 Reynolds 의 문법을 그대로 옮긴 것이라, 상호 귀납이 아니라
별도 `inductive` 둘이면 된다.

`quant q v p` 의 `v` 는 결합 발생(binding occurrence)이고 유효 범위(scope)는 `p` 다.
1장에서 결합이 나오는 자리는 여기뿐이고, §1.4 는 이것 하나를 다룬다.
-/
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

end Reynolds.Exercises.Ch01
