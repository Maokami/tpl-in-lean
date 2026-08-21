/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Exercises.Ch01.Syntax

/-!
# §2.1 단순 명령형 언어의 추상 구문

Reynolds §2.1 에 대응한다.

## 이 파일에서 다루는 것
- 불 식 ⟨boolexp⟩ 과 명령 ⟨comm⟩ 의 추상 구문
- 왜 불 식이 1장의 단언에서 양화사만 뺀 것인가
- 왜 `newvar` 를 §2.5 가 아니라 지금 넣는가

## 1장과 무엇이 다른가

1장의 언어에는 **비종료가 없었다.** 정수 식도 단언도 구조적 재귀로 뜻이 정해졌고,
의미 함수가 전함수(total function)였다.

2장에서 `while` 이 들어온다. `while b do c` 의 뜻을 정의하려면 자기 자신을 불러야 하는데,
그 재귀가 구문에 대한 재귀가 아니다. 이 파일에서는 아직 아무 문제가 없다 — 구문은
여전히 유한한 트리다. 문제는 `Semantics.lean` 에서 시작한다.

## 책과의 차이

- **`newvar` 를 처음부터 넣었다.** Reynolds 는 §2.5 에서 추가한다. 그대로 따르면
  `Comm` 을 두 번 정의하고 §2.2~2.4 의 모든 정의와 정리를 복제해야 한다.
  §2.5 이전 절에서는 `newvar` 를 쓰지 않는다. 각 정의에서 그 절이 어떻게 다뤄지는지는
  해당 파일의 docstring 에 적는다.
- **모든 변수가 정수형이다.** Reynolds 본인이 "somewhat simplistically" 라고 인정하는
  설계다. 불 값을 담는 변수가 없어서 `x := (y < 3)` 같은 것을 쓸 수 없다.
  타입 체계는 15장의 주제이고, 여기서 그것을 미리 끌어오면 2장의 논점이 흐려진다.

## 읽는 순서
이 파일 → `Notation.lean` → `Semantics.lean`
-/

@[expose] public section

namespace Reynolds.Exercises.Ch02

open Reynolds Reynolds.Exercises.Ch01

universe u

/-! ## 불 식

Reynolds 가 불 식을 도입하는 방식이 특이하다. 새로 정의하지 않고 1장의 단언을 가리킨다.

> *"boolean expressions are the same as assertions except for the omission of quantifiers
> (for the obvious reason that they are noncomputable)"*

이 한 문장이 이 장의 성격을 정한다. 정수 산술과 양화를 포함한 1장 단언 언어 전체에는
실행 가능한 공통 진리 판정기가 없다. 양화사를 뺀 불 식은 구문을 따라 계산할 수 있으므로,
뜻을 `Bool`로 줄 수 있다.

그 차이가 `Semantics.lean` 에서 드러난다. `Assert.eval` 은 `Prop` 을 돌려주고
`BoolExp.eval` 은 `Bool` 을 돌려준다. 후자는 `#eval` 로 실제로 돌아간다. -/

/--
불 식(boolean expression). Reynolds §2.1 의 ⟨boolexp⟩.

1장의 `Assert` 에서 **양화사 절만 뺀 것**이다. 나머지 다섯 절은 글자까지 같다.

비교와 이항 논리 연산은 1장의 `Cmp`, `LogOp` 를 그대로 쓴다. 같은 기호를 두 번 정의하면
`Semantics.lean` 에서 의미도 두 번 정의해야 하고, 그러면 "불 식은 양화사 없는 단언" 이라는
Reynolds 의 말이 코드에서 사라진다.
-/
inductive BoolExp (V : Type u) where
  /-- 참 `true`. -/
  | tru
  /-- 거짓 `false`. -/
  | fls
  /-- 정수 비교 `e₀ ∼ e₁`. -/
  | cmp : Cmp → IntExp V → IntExp V → BoolExp V
  /-- 부정 `¬b`. -/
  | not : BoolExp V → BoolExp V
  /-- 이항 논리 연산 `b₀ ∘ b₁`. -/
  | bin : LogOp → BoolExp V → BoolExp V → BoolExp V
  deriving DecidableEq, Repr

/-! ## 명령

Reynolds §2.1 의 생성 규칙은 다섯이다.

```
⟨comm⟩ ::= ⟨var⟩ := ⟨intexp⟩
         | skip
         | ⟨comm⟩ ; ⟨comm⟩
         | if ⟨boolexp⟩ then ⟨comm⟩ else ⟨comm⟩
         | while ⟨boolexp⟩ do ⟨comm⟩
```

여기에 §2.5 의 `newvar ⟨var⟩ := ⟨intexp⟩ in ⟨comm⟩` 을 미리 더한다. -/

/--
명령(command). Reynolds §2.1 의 ⟨comm⟩ 과 §2.5 의 `newvar`.

`newvar v e c` 가 `newvar v := e in c` 다. **`v` 는 결합 발생(binding occurrence)이고
그 유효 범위는 `c` 뿐이다 — `e` 는 범위 밖이다.** 초기값 `e` 는 새 변수를 만들기 전에
바깥 상태에서 재기 때문이다. 1장의 합 식(연습 1.5)에서 상계가 범위 밖이었던 것과 같다.

이 장에서 결합이 등장하는 자리는 여기 하나뿐이다. §2.5 까지는 쓰지 않는다.
-/
inductive Comm (V : Type u) where
  /-- 대입 `v := e`. -/
  | assign : V → IntExp V → Comm V
  /-- 아무것도 하지 않는다. -/
  | skip
  /-- 순차 합성 `c₀ ; c₁`. -/
  | seq : Comm V → Comm V → Comm V
  /-- 조건 `if b then c₀ else c₁`. -/
  | ite : BoolExp V → Comm V → Comm V → Comm V
  /-- 반복 `while b do c`. **이 장의 모든 어려움이 이 절 하나에서 나온다.** -/
  | wh : BoolExp V → Comm V → Comm V
  /-- 변수 선언 `newvar v := e in c`. `v` 의 유효 범위는 `c` 다. -/
  | newvar : V → IntExp V → Comm V → Comm V
  deriving DecidableEq, Repr

/-! ## 구문은 여전히 유한한 트리다

`while` 이 있다고 해서 구문이 무한해지지는 않는다. `Comm` 은 1장의 `IntExp`, `Assert` 와
똑같은 귀납 타입이고, 추상 구문의 세 조건(생성자 단사성 · 치역 서로소 · 유한 생성)도
`inductive` 선언에서 그대로 나온다. 확인은 `Ch01/Syntax.lean` 의 `AbstractSyntaxConditions`
절에서 이미 했으므로 되풀이하지 않는다.

무한한 것은 `while` 이 만드는 **계산**이다. `while tt do skip` 은 유한한 트리인데
그 뜻은 어떤 상태도 돌려주지 않는다. 구문의 유한함과 계산의 무한함이 갈리는 것,
그것이 `Semantics.lean` 의 주제다. -/

end Reynolds.Exercises.Ch02
