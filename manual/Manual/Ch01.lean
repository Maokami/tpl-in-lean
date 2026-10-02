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
set_option verso.exampleModule "Reynolds.Answers.Ch01.Syntax"

#doc (Manual) "1장 술어 논리" =>
%%%
tag := "ch01"
file := "ch01"
number := false
%%%

Reynolds 1장은 익숙한 술어 논리(predicate logic)를 작은 프로그래밍 언어처럼 다룬다.
구문을 데이터로 만들고, 각 생성자에 의미 방정식을 주고, 그 정의에서 성질을 증명한다.
2장 이후에도 대상 언어는 바뀌지만 이 작업 순서는 계속 남는다.

이 장 문서는 소스 파일의 순서를 따라가되, 코드만으로는 드러나지 않는 경계도 함께 적는다.
표준 정수 해석의 완전성과 일차 논리의 완전성은 무엇이 다른지, 결합 변수의 표현을 바꾸면
복잡성이 어디로 이동하는지, 동적 결합에서는 왜 이름 바꾸기가 안전하지 않은지가 그 예다.

# 이 장에서 배우는 것
%%%
tag := "ch01-goals"
file := "ch01-goals"
number := false
%%%

* *추상 구문(abstract syntax)* — 언어를 문자열이 아니라 트리로 정의하는 것, 그리고 그때 필요한 세 조건
* *표시적 의미론(denotational semantics)* — 구문의 각 절에 뜻을 주는 구문 지향 방정식
* *타당성과 추론* — 뜻으로 정의한 참과 규칙으로 유도한 참, 그리고 둘을 잇는 건전성(soundness)
* *결합과 치환* — 양화사(quantifier)가 들어오면서 생기는 자유 변수(free variable)와
  속박 변수(bound variable)의 구분, 그리고 변수 포획(capture)

특히 §1.4에서는 정의가 타입에 맞는 것만으로 충분하지 않다. 자유 변수를 빠뜨리거나
치환에서 포획을 허용하면 함수는 실행되지만 일치 정리와 치환 정리가 깨진다. 이 저장소는
정의의 타당성을 그 정리와 반례로 확인한다.

# 읽는 순서
%%%
tag := "ch01-order"
file := "ch01-order"
number := false
%%%

파일마다 docstring 첫머리에 "읽는 순서"가 적혀 있다. 처음 오는 사람을 위해 한자리에 모은다.

1. `Background.lean` — 메타언어와 객체언어. import 순서와 달리 학습 순서에서는 첫 파일이다
2. `Syntax.lean` — §1.1 추상 구문
3. `Notation.lean` — §1.1 구체 구문. 객체 언어를 Lean 표기로 쓰는 DSL
4. `Semantics.lean` — §1.2 표시적 의미론
5. `Validity.lean` — §1.3 타당성, 추론 규칙, 건전성
6. `FreeVars.lean` — §1.4 자유 변수와 일치 정리
7. `Substitution.lean` — §1.4 치환, 명제 1.2 ~ 1.5
8. `Realizations.lean`·`Realizations/`, `Ex.lean`, `Ex/Summation.lean` — 책 연습문제
9. `Design.lean` — 정의 선택과 정리의 성립. 틀린 정의가 무엇을 깨뜨리는지
10. `Depth/` — 심화 트랙. 건너뛰어도 1장은 완결된다

전부 `Reynolds/Answers/Ch01/` 아래에 있고, 같은 구조가 `Reynolds/Exercises/Ch01/`에도
있다. 그쪽은 연습 지점만 {lit}`sorry`로 비어 있다.

## 연습은 `Ex.lean`에만 있지 않다
%%%
tag := "ch01-exercises-are-everywhere"
file := "ch01-exercises-are-everywhere"
number := false
%%%

이름 때문에 오해하기 쉬운 자리가 있다.
*책의 명제 1.1 ~ 1.5 증명이 본문 파일 안에 연습으로 들어 있다.* `FreeVars.lean`의 일치 정리, `Substitution.lean`의 치환 정리,
`Validity.lean`의 건전성이 그렇다.

`Ex.lean`의 연습 1.4는 앞에서 정의한 포획 회피 치환을 실제 구문에 적용한다. 따라서 본문 파일을 건너뛰면
문제의 전제가 되는 정의와 보조정리를 아직 보지 않은 상태가 된다. 처음 읽을 때는 위 목록의
1 ~ 7을 따라가고, 이후에는 필요한 정리의 선언 위치로 돌아오면 된다.

무엇이 어디에 몇 개 있는지는 아래 [연습문제](--tag--ch01-exercise-list) 절에 있다.

# §1.1 추상 구문
%%%
tag := "ch01-syntax"
file := "ch01-syntax"
number := false
%%%

프로그램을 글자 열과 그 글자 열이 가리키는 대상으로 나눠 생각할 필요가 있다.
`1 + 2 * 3`은 전자이고, 연산자와 피연산자로 이루어진 트리는 후자다.

글자 열이라고 하면 곤란해진다. `1 + 2 * 3`과 `1 + (2 * 3)`은 다른 글자 열인데 같은 것을
말한다. 반대로 `1 + 2 * 3` 하나가 곱셈을 먼저 하는 트리와 덧셈을 먼저 하는 트리 둘 다로
읽힐 수도 있다. 우선순위 규칙이 그 애매함을 없애 주지만, 그건 *읽는 방법*에 관한 규칙이지
프로그램 자체에 관한 것이 아니다.

Reynolds는 그래서 둘을 나눈다.

: 구체 구문(concrete syntax)

  사람이 쓰고 읽는 글자 열. 우선순위, 괄호, 공백이 여기 산다.

: 추상 구문(abstract syntax)

  그 글자 열이 가리키는 *트리*. `1 + 2 * 3`의 추상 구문은 뿌리가 `+`이고 오른쪽
  가지가 `*` 인 트리 하나다. 우선순위는 이미 소진되어 사라졌다.

의미를 주고 성질을 증명하는 일은 전부 추상 구문 위에서 한다. 구체 구문은 §1.1의
`Notation.lean`에서 DSL 로 따로 다룬다.

## 트리를 트리답게 만드는 세 조건

"트리" 라고 말만 해서는 부족하다. 트리들의 집합이 어떤 집합이어야 하는지를 못박아야
구조적 귀납법 같은 도구를 쓸 수 있다. Reynolds가 손으로 부과하는 조건이 셋이다.

1. *생성자(constructor)가 단사(injective)다.* `e₀ + e₁`과 `e₀' + e₁'`이 같은 트리면
   `e₀ = e₀'`이고 `e₁ = e₁'`이다. 이것이 없으면 트리를 보고 부분식을 되찾을 수 없다.
2. *서로 다른 생성자의 치역(range)이 서로소(disjoint)다.* 어떤 트리도 "덧셈이면서 동시에
   변수" 일 수 없다. 이것이 없으면 경우를 나누는 정의가 서지 않는다.
3. *모든 원소가 유한 번의 생성자 적용으로 만들어진다.* 생성자로 도달할 수 없는 정체불명의
   원소가 없다는 뜻이다. 이것이 없으면 구조적 귀납법이 거짓말이 된다 — 모든 생성자 경우를
   증명해도 남는 원소가 있을 수 있으니까.

1과 2를 합쳐 *no confusion*, 3을 *no junk*라고 부르기도 한다. 이것은 구문 반송자의
생성 원리를 설명하는 말이다. 임의의 목표 대수로 가는 준동형이 유일하다는 초기성의 보편
성질은 여기서 한 단계 더 나아간 명제이며, `Depth/Algebra.lean`에서 따로 증명한다.

## Lean에서는 선언 한 번이 이 셋을 준다

`inductive`로 타입을 선언하면 위 셋이 자동으로 성립한다. 별도로 공리를 놓지 않는다.
확인해 보면 이렇다.

```anchor freeConditions (module := Reynolds.Answers.Ch01.Syntax)
/-- 조건 1. 생성자는 단사다. `injection`이 바로 처리한다. -/
example : Function.Injective (IntExp.var (V := V)) := fun _ _ h => by injection h

/-- 조건 2. 서로 다른 생성자의 치역은 서로소다. -/
example : IntExp.num (V := V) n ≠ IntExp.var v := by nofun

-- 조건 3. 모든 정수 식은 유한 번의 생성자 적용으로 만들어진다.
-- 별도의 `True` 증명이 아니라, Lean이 생성한 재귀자 자체가 유한 구성을 따라가는 원리다.
#check IntExp.rec
```

세 번째 조건이 구조적 귀납법(structural induction)을 정당하게 만든다. 1장의 증명은 거의
전부 구조적 귀납법이므로, 이 조건이 빠지면 손에 남는 것이 없다. 조건 3은 별도의 명제를
증명한 것이 아니라 `IntExp.rec`라는 *재귀자*의 타입으로 확인한다. `induction e with …`를
쓸 때마다 그 재귀자를 부르고 있다.

한 가지 더 짚을 것이 있다. 위 `IntExp` 선언에는 `(V : Type u)` 라는 매개변수가 붙어 있다.
변수 이름의 타입을 문자열로 고정하지 않고 열어 둔 것이다. Reynolds는 ⟨var⟩를
"표현이 지정되지 않은 가산 무한 집합"이라고 두지만, 구문·의미·일치 정리에는 가산성이
필요하지 않아 여기서는 임의의 `V`로 일반화했다. 따라서 유한 타입도 허용한다. 포획 회피
치환에서만 유한 집합 밖의 이름을 고르는 `HasFresh V`를 요구한다. 이 조건은 무한성은 주지만
가산성까지 요구하지 않는다. 예제에서는 `V = String`으로 읽으면 된다.

단언(assertion)의 구문은 이렇게 생겼다.

```anchor Assert (module := Reynolds.Answers.Ch01.Syntax)
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
```

마지막 절이 이 장에서 유일하게 새로운 것이다. `quant`는 *변수를 묶는다*.
정수 식(integer expression)에는 결합자(binder)가 없어서 자유·속박 구분이 생기지 않았는데,
여기서 생긴다.

종이에서는 "이런 조건을 만족하는 집합이 있다고 하자" 로 시작해서 그 집합을 끝까지 만들지
않는다. Lean에서는 선언 한 번이 그 집합을 실제로 만든다.

## 범주론 렌즈로 보면

Reynolds의 세 조건을 범주론의 말로 다시 쓰면, 구문 반송자는 _초기 대수_다 — 모든
목표 대수로 가는 준동형이 꼭 하나 있다는 뜻이다. `inductive` 선언 한 번이 그 대수를
즉시 만들어 준다. 책이 식 (1.2)에서 층별로 쌓아 올리는 구성은 그 초기 대수를 짓는
표준적인 방법 하나이고, 초기성 자체에서 구조적 귀납법과 유일한 "접기(fold)"가 둘 다
따라 나온다. 범주론 어휘를 몰라도 본문은 이 문단 없이 완결된다. 자세한 증명은
[선택 심화](--tag--ch01-depth-construction)에 있다.

# §1.2 표시적 의미론
%%%
tag := "ch01-semantics"
file := "ch01-semantics"
number := false
%%%

구문 트리는 아직 아무 뜻도 없다. `x + 1`에 해당하는 트리는 그냥 트리이지 숫자가 아니고,
숫자가 되려면 `x`가 얼마인지 알아야 한다.

그래서 뜻을 주는 함수가 트리 하나만 받지 않는다. *상태(state)* 를 함께 받는다.
상태는 변수에 값을 붙여 주는 함수 `σ : ⟨var⟩ → ℤ`이다. Reynolds의 `Σ`는 이런 상태들이
이루는 공간이고, `σ : Σ`가 상태 하나다.
논리학에서는 assignment, 프로그래머에게는 메모리에 해당한다.

```
⟦-⟧intexp : ⟨intexp⟩ → Σ → ℤ
```

트리를 받고 상태를 받으면 정수를 낸다. `⟨intexp⟩`와 `Σ → ℤ`를 분리해 적은 이 타입이
구문과 의미가 서로 다른 층에 있다는 사실을 보여 준다.

의미 함수(semantic function)는 구문의 절마다 방정식 하나씩이다. 구조적 재귀라서 정의가 곧
증명 도구가 된다 — 정의를 펼치는 것과 귀납법의 한 단계를 밟는 것이 같은 일이다.
단언 쪽은 이렇게 생겼다.

```anchor assertEval (module := Reynolds.Answers.Ch01.Semantics)
def Assert.eval {V : Type u} [DecidableEq V] : Assert V → State V → Prop
  | .tru,            _ => True
  | .fls,            _ => False
  | .cmp c e₀ e₁,    σ => c.denote (e₀.eval σ) (e₁.eval σ)
  | .not p,          σ => ¬ p.eval σ
  | .bin op p q,     σ => op.denote (p.eval σ) (q.eval σ)
  | .quant .all v p, σ => ∀ n : Int, p.eval (σ[v := n])
  | .quant .ex  v p, σ => ∃ n : Int, p.eval (σ[v := n])
```

양화사 절에서 `∀v. p`의 뜻은 "모든 정수 `n`에 대해, `v`를 `n`으로 덮은 상태에서 `p`가 참"
이다. 오른쪽에 쓴 `∀`는 Lean의 것이고, 왼쪽의 `∀v. p`는 객체 언어의 구다.
*메타 수준의 기호로 객체 수준의 기호를 설명하고 있다.*

이것이 Reynolds가 §1.2에서 계속 경계하는 자리다. 객체 언어의 기호와 메타 언어의 기호가
같은 모양이라 헷갈리기 쉽다. `Background.lean`이 그 구분만 따로 다루는 이유다.

*결과 타입이 `Prop`인 것도 여기서 정해진다.* 계산 가능한 `Bool` 평가기를 만들려면 모든
단언의 참·거짓을 판정하는 절차가 있어야 한다. 정수 양화가 있는 이 언어 전체에는 그런
절차가 없다. `Prop`은 판정 절차 없이 명제를 표현한다. 2장의 불 식은 양화사를 뺀 계산 가능한
조각이어서 `Bool` 평가기를 줄 수 있다.

정수 식 쪽은 양화사가 없으므로 지금도 계산된다. 돌려 보면 이렇다.

```anchor evalExample (module := Reynolds.Answers.Ch01.Semantics)
example : ⟦IntExp.bin .add (.var "x") (.num 1)⟧ₑ (State.const 41) = 42 := by decide
```

1장이 쉬운 이유가 여기 있다. 의미 함수가 *전함수(total function)* 다. 술어 논리에는
비종료(nontermination)가 없으므로 모든 구에 뜻이 있고, 뜻이 있는지부터 따질 일이 없다.
2장에서 `while`이 들어오면 이 사정이 무너진다.

## 곁가지 — "타입"이라는 말이 가리키는 층
%%%
tag := "ch01-type-levels"
file := "ch01-type-levels"
number := false
%%%

여기서 한 번 정리하고 가면 뒤가 편하다. 이 저장소를 읽다 보면 "타입"이라는 말이 서로 다른
것을 가리키며 여러 번 나오는데, 섞이면 §1.1과 §1.2의 구분 자체가 흐려진다.

지금까지 나온 것을 층으로 세워 보면 이렇다.

```
구문(syntax)          ⟨intexp⟩          구문 트리들의 집합
                          │
                          │  ⟦-⟧intexp    (트리를 받아 값을 계산하는 함수)
                          ▼
표시(denotation)      Σ → ℤ             상태를 받는 의미 함수
                          │  σ를 적용
                          ▼
값(value)             ℤ                 이 상태에서 얻은 값
```

`⟨intexp⟩`의 원소는 *트리*다. `1+1`에 해당하는 원소는 `c₊(c₁(), c₁())`이라는 트리이지
정수 2 가 아니다. 트리를 정수로 보내는 것이 `⟦-⟧intexp`이고, 그것이 §1.2에서 한 일이다.

Lean으로 옮기면 `IntExp String`이 위층이고 `Int`가 아래층이다. `IntExp.eval`이 화살표다.
`IntExp String`을 "정수 타입"이라고 부르면 안 되는 이유가 그것이다 — 그 타입의 원소는
정수가 아니라 트리다.

## 타입이 붙은 언어로 가면 층이 하나 더 생긴다

15장에서 타입 체계를 다루면 구문 쪽에 층이 하나 더 얹힌다. 타입 표현 `int`, `bool`,
`τ → σ` 자체가 하나의 구문이 되고, 그 구문에도 자기만의 의미 함수가 붙는다.

```
타입의 구문     ⟨type⟩        int, bool, →, × 로 만들어지는 트리
                    │  ⟦-⟧type
                    ▼
타입의 의미     ⟦τ⟧            값들이 사는 그릇 (⟦int⟧ = ℤ)
                    △  값이 그 그릇 안에 있다
항의 의미       ⟦e⟧σ ∈ ⟦τ⟧
                    △  ⟦-⟧term
항의 구문       ⟨term⟩
```

여기서 자주 어긋나는 대응 하나를 짚어 둔다.
*`⟨intexp⟩`와 같은 층에 있는 것은 `⟦τ⟧`가 아니라 `⟨type⟩`이다.* 둘 다 구문의 집합이고, 둘 다 생성자와 세 조건으로 만들어지는
같은 종류의 대상이다. `⟨intexp⟩`가 `⟦-⟧intexp`를 거쳐 도달하는 곳이 `ℤ = ⟦int⟧`이고,
그쪽이 `⟦τ⟧`에 해당한다.

Reynolds 1장을 억지로 타입이 붙은 언어로 다시 읽으면 이렇게 된다.

: `⟨intexp⟩`

  `int` 타입을 갖는 항들의 구문. 타입이 하나뿐이라 타입 표현을 따로 둘 이유가 없었다.

: `ℤ`

  `⟦int⟧`. 값들이 사는 그릇.

: `⟨assert⟩`와 `𝔹`

  같은 이야기의 진릿값 판이다. Reynolds의 `𝔹`는 실행 가능한 `Bool` 평가기를 뜻하지 않는다.
  이 형식화는 객체언어의 양화를 Lean의 양화로 바로 옮기기 위해 `Prop`을 쓴다.

## 집합, 도메인, 범주론의 역할

집합론, 도메인 이론, 범주론(category theory)은 같은 질문에 내놓은 세 가지 답이 아니다.
먼저 값이 어디에 사는지를 정한다.

: 집합론적(set-theoretic)

  `⟦τ⟧`가 그냥 집합이다. `⟦int⟧ = ℤ`, `⟦τ → σ⟧`는 함수들의 집합.
  1장이 이 관점이고, 비종료가 없으므로 이걸로 충분하다.

: 도메인 이론적(domain-theoretic)

  `⟦τ⟧`에 근사 순서를 주고, 모든 가산 증가 사슬의 최소 상계와 최소원 `⊥`을 갖추면 이 책이
  말하는 도메인이 된다. *2장에서 `while`이 들어오면 이쪽으로 넘어간다.* 보통 집합도
  `Option` 같은 타입으로 비종료를 부호화할 수는 있다. 도메인의 순서와 연속성은 재귀 의미
  방정식의 여러 고정점 가운데 최소 고정점을 골라 근사 사슬로 구성하게 해 준다.

도메인은 집합을 버리는 대안이 아니라 집합에 순서 구조를 더한 의미 공간이다.
범주론적 관점은 셋째 그릇이 아니다.
집합도 범주 `Set`의 대상이고, 도메인도 알맞은 범주의 대상이다. 범주론은 이런 대상과
그 사이의 함수를 한 언어로 설명한다. 예를 들어 `Depth/SignatureFunctor.lean`의 초기 대수는
여기서 구문을 재귀적으로 만드는 과정을 설명한다. 값이 사는 `⟦τ⟧`까지 대신 정해 주지는 않는다.

Curry–Howard 대응도 여기서 선택할 의미론 하나를 더 보태는 말이 아니다. 명제를 타입으로,
증명을 그 타입의 항으로 읽는 대응이다. `Assert.eval`의 결과를 `Prop`으로 둔 직접적인 이유는
객체언어의 양화를 Lean의 `∀`와 `∃`로 그대로 표현하기 위해서다. 이 책은 1장에서 값을 보통
집합으로 다루고, 2장에서는 비종료와 재귀를 다루려고 근사 순서가 있는 도메인을 도입한다.

## 범주론 렌즈 — 의미는 유일한 준동형이다
%%%
tag := "ch01-semantics-category-lens"
number := false
%%%

`IntExp.eval`과 `Assert.eval`은 구문 대수에서 이 절의 의미 대수로 가는 준동형 조건을
만족하는 유일한 함수 쌍이다(`Depth/Algebra.lean`의 초기성 정리). 그 조건 자체가 합성성
(compositionality)의 다른 이름이다 — 생성자 하나의 값이 그 조각들의 값으로만 정해지기
때문이다. 합성성의 귀결, 곧 뜻이 같은 부분구를 바꿔 끼워도 전체 뜻이 바뀌지 않는다는
성질은 [선택 심화: 합성성과 합동](--tag--ch01-congruence)에서 더 본다.
[선택 심화: 의미와 자유 변수는 어떤 접기인가](--tag--ch01-logic-fold)는 이 유일한 함수 쌍을
접기(catamorphism)로 직접 구성해 본다.

# §1.3 타당성과 추론
%%%
tag := "ch01-validity"
file := "ch01-validity"
number := false
%%%

`x > 0`의 참·거짓은 상태에 달려 있다. `x`가 3이면 참이고 -1이면 거짓이다.
단언 하나만으로는 진리값이 없고 상태가 있어야 정해진다는 것이 §1.2의 결론이었다.

그런데 상태를 *하나 고르지 않고 전부 훑으면* 단언 자체의 성질이 나온다.
`x > 0 ∨ x ≤ 0`은 어떤 상태에서도 참이고, `x > 0 ∧ x ≤ 0`은 어떤 상태에서도 거짓이다.
Reynolds는 §1.3에서 그런 성질 넷에 이름을 붙인다.

```anchor validity (module := Reynolds.Answers.Ch01.Validity)
/-- **타당(valid)** — 모든 상태에서 참. Reynolds §1.3. -/
def Valid (p : Assert V) : Prop := ∀ σ : State V, ⟦p⟧ₐ σ

/-- **충족 불가능(unsatisfiable)** — 어떤 상태에서도 거짓. -/
def Unsat (p : Assert V) : Prop := ∀ σ : State V, ¬ ⟦p⟧ₐ σ

/--
`p`가 `q`보다 **강하다(stronger)**. `q`는 `p`보다 **약하다(weaker)**.

Reynolds가 곧바로 붙이는 단서가 있다.

> *"'stronger' and 'weaker' are dual preorders, which does not quite jibe with normal
> English usage. For example, any assertion is both stronger and weaker than itself."*

`Stronger`는 반사적이고 추이적인 준순서(preorder)다. 어떤 단언이든 자기 자신보다 강하면서
동시에 약한 것은 반사성 때문이다. 의미가 같지만 구문이 다른 단언도 서로 강하므로, 구문
등식에 대한 반대칭성은 일반적으로 성립하지 않는다.
-/
def Stronger (p q : Assert V) : Prop := ∀ σ : State V, ⟦p⟧ₐ σ → ⟦q⟧ₐ σ

/-- **동치(equivalent)** — 같은 뜻. -/
def Equivalent (p q : Assert V) : Prop := ∀ σ : State V, (⟦p⟧ₐ σ ↔ ⟦q⟧ₐ σ)
```

여기까지는 전부 *뜻*으로 정의했다. 상태를 훑어 보고 판정한다.

증명은 그렇게 하지 않는다. 공리에서 출발해 규칙을 적용해 가며 문장을 얻고, 그 과정에서
상태를 한 번도 보지 않는다. 그것을 따로 정의한다.

```anchor proofSystem (module := Reynolds.Answers.Ch01.Validity)
/--
술어 논리의 작은 추론 체계. Reynolds §1.3 p.13이 공리·공리꼴·두 전제 규칙·한 전제
규칙의 예로 직접 드는 넷 그대로다: `x + 0 = x`, `e₁ = e₀ ⇒ e₀ = e₁`, 전건 긍정,
보편 일반화.

완전한 체계가 아니고 그럴 의도도 없다. 책도 이 넷을 "예시"라고만 하고 나머지는
논리학 교과서로 미룬다(모듈 docstring의 "책과의 차이" 참고).
-/
inductive Proof : Assert V → Prop where
  /--
  공리: `x + 0 = x`. 책은 메타변수가 없는 구체적인 객체 변수 x로 든다 — 바로 다음
  공리꼴과 대조하려는 것이다(p.13, "notice the special role of axiom schemas").

  **책과의 차이**: 여기서는 모든 객체 변수 x에 대해 한 번에 선언한다. Lean에서 변수마다
  따로 공리를 선언하면 쓸 수 없는 정의가 되기 때문이다. 책의 "메타변수 없음"은 이 x 하나를
  구체적으로 고정했을 때의 이야기이고, 다형화 자체는 책에 없는 저장소의 선택이다.
  -/
  | addZero (x : V) : Proof (.cmp .eq (.bin .add (.var x) (.num 0)) (.var x))
  /--
  공리꼴: `e₁ = e₀ ⇒ e₀ = e₁`. 전제 없이 바로 쓸 수 있지만 `e₀`, `e₁`이 메타변수라서
  임의의 정수 식 쌍에 대한 사례를 전부 대신한다 — 공리와 공리꼴의 차이가 바로 이
  메타변수 유무다(p.13, "their instances are assertions that can appear anywhere
  in a proof, regardless of what, if anything, precedes them").
  -/
  | eqSymmSchema (e₀ e₁ : IntExp V) :
      Proof (.bin .imp (.cmp .eq e₁ e₀) (.cmp .eq e₀ e₁))
  /-- 두 전제 규칙 — 전건 긍정(modus ponens). -/
  | mp {p q : Assert V} : Proof p → Proof (.bin .imp p q) → Proof q
  /--
  한 전제 규칙 — 보편 일반화(∀-도입).

  전제가 타당할 때만 결론이 타당해진다. 이 파일 §4에서 이 규칙과 함의 `p ⇒ ∀v. p`를
  나란히 놓고 비교한다.
  -/
  | genAll (v : V) {p : Assert V} : Proof p → Proof (.quant .all v p)
```

`Proof p`는 "`p`를 이 규칙들로 유도할 수 있다"는 뜻이다. `Valid p`와 달리 상태가
어디에도 나오지 않는 것을 확인해 보라. 두 정의는 서로를 모른다.

규칙으로 얻은 것이 실제로 참임을 보장하는 성질이 *건전성(soundness)*이다.
`Validity.lean`에서 `Proof p → Valid p`로 증명한다.
증명은 `Proof`에 대한 귀납법이다 — 규칙 하나하나가 타당성을 보존하는지 확인하면 된다.

반대 방향(`Valid p → Proof p`, 완전성)은 성립하지 않는다. 아래 곁가지에서 다룬다.

## 규칙과 함의는 다른 것이다
%%%
tag := "ch01-rule-vs-implication"
file := "ch01-rule-vs-implication"
number := false
%%%

보편 일반화 규칙은 건전한데, 같은 재료로 만든 함의는 타당하지 않다. 둘이 같은 말을 하는
것처럼 보여서 §1.3에서 가장 자주 걸리는 곳이다. 두 정리를 나란히 놓는다.

```anchor stmtGenSound (module := Reynolds.Answers.Ch01.Validity)
/-- 규칙 쪽. `p`가 타당하면 `∀v. p`도 타당하다. -/
@[exercise "§1.3 gen-sound" 1]
theorem valid_forall_of_valid (v : V) {p : Assert V} (h : Valid p) :
    Valid (.quant .all v p)
```

```anchor stmtGenNotImp (module := Reynolds.Answers.Ch01.Validity)
/--
함의 쪽. `x > 0 ⇒ ∀x. x > 0`은 타당하지 않다.

Reynolds의 반례를 그대로 쓴다. `x ↦ 3` 인 상태에서 왼쪽은 참이고,
오른쪽은 `x`에 0 을 넣으면 거짓이다.

같은 재료로 만든 규칙(위)과 함의(여기)의 판정이 갈린다.
-/
@[exercise "§1.3 gen-not-imp" 2]
theorem not_valid_imp_forall :
    ¬ Valid (.bin .imp (.cmp .gt (.var "x") (.num 0))
                       (.quant .all "x" (.cmp .gt (.var "x") (.num 0))) : Assert String)
```

규칙은 *전제가 타당할 때* 결론이 타당하다고 말한다. 함의는 *한 상태 안에서* 왼쪽이
참이면 오른쪽도 참이라고 말한다. `x ↦ 3` 인 상태 하나만 잡으면 뒤쪽이 무너진다.

## 곁가지 — 완전성과 괴델
%%%
tag := "ch01-completeness"
file := "ch01-completeness"
number := false
%%%

Reynolds는 §1.3을 닫으면서 이 책이 다루지 않을 것을 알려 준다. 코드로 옮기지 않기로
한 논의라 여기에 산문으로 남긴다.

건전성의 역이 *완전성(completeness)*이다. 타당한 것은 모두 유도되는가.

답은 "타당"을 어떻게 정의했느냐에 달렸다.

* 우리처럼 *정수에 대한 표준 해석*을 고정하면 참인 산술 문장까지 모두 다뤄야 한다.
  산술을 충분히 표현하면서 공리와 증명을 기계적으로 열거·검사할 수 있는 일관된 체계는
  그 참인 문장을 전부 증명할 수 없다. 괴델의 불완전성 정리는 이런 조건 아래에서 적용된다.
* *논리적 타당성(logical validity)* — 연산 기호의 뜻까지 임의로 바꿔도 성립하는 것 —
  으로 정의하면 일차 논리에는 건전하고 완전한 효과적 증명 체계가 있다. 괴델의 완전성
  정리가 그것이다.

같은 이름의 두 정리가 반대 방향을 말하는 것처럼 보이지만, 두 "타당"이 다른 것이다.

Reynolds는 여기에 실용적인 단서를 붙인다. 프로그램 검증에서 논리적 완전성은 별 쓸모가
없다는 것이다. 우리는 `+`가 정말 덧셈인 해석에만 관심이 있기 때문이다.
그 예외는 §3.8에서 다룬다.

*왜 코드로 만들지 않았나.* 이 주제를 형식화하려면 증명론 전체가 따라온다 — 산술의
인코딩, 증명 가능성 술어, 대각화. Reynolds 본인이 다루지 않고, 1장의 목표와도 멀다.
Lean으로 괴델을 보고 싶다면 `mathlib` 밖의 별도 프로젝트를 찾는 편이 낫다.

# §1.4 자유 변수와 일치 정리
%%%
tag := "ch01-freevars"
file := "ch01-freevars"
number := false
%%%

`∀x. x > y`에서 `x`와 `y`는 처지가 다르다. `y`의 값은 바깥 상태가 정하지만,
양화사는 모든 정수 `n`에 대해 상태를 `σ[x := n]`으로 갱신한 경우를 다룬다.
그래서 `x`의 바깥 값은 결과에 영향을 주지 않는다.
앞을 *자유(free)*, 뒤를 *속박(bound)* 이라고 부른다.

"자유" 라는 말은 결합자가 있어야 뜻이 생긴다. 정수 식에는 결합자가 없으니 나오는 변수가
전부 자유롭고, 단언 쪽에서 한 절만 다르다.

```anchor assertFv (module := Reynolds.Answers.Ch01.FreeVars)
def Assert.fv : Assert V → Finset V
  | .tru | .fls  => ∅
  | .cmp _ e₀ e₁ => e₀.fv ∪ e₁.fv
  | .not p       => p.fv
  | .bin _ p q   => p.fv ∪ q.fv
  | .quant _ v p => p.fv.erase v
```

`erase`가 붙은 절 하나가 결합의 전부다. `∀v. p`의 자유 변수는 `p`의 자유 변수에서 `v`를
뺀 것이다. `∀x. x > y`로 계산해 보면 `{x, y}`에서 `x`를 빼 `{y}`가 나온다.

이 정의가 옳다는 근거가 *일치 정리(coincidence theorem, 명제 1.1)* 다. 두 상태가
`FV(p)` 위에서 같으면 `p`의 뜻이 같다는 것이다. 다시 말해 `fv`는 뜻에 영향을 줄 수 있는
변수를 빠뜨리지 않는다. 그렇다고 적어 둔 변수가 전부 실제로 영향을 주는 것은 아니다.
`x - x`에는 `x`가 자유롭게 나타나지만 값은 어느 상태에서나 `0`이다.

증명에서 한 군데가 걸린다. Reynolds는 `∀v. p`를 다룰 때 귀납 가설을 원래 상태가 아니라
`σ[v := n]`, `σ'[v := n]`에 적용하라고 설명한다. Lean으로 옮기면
*진술을 `∀ (p) (σ σ')` 꼴로 써야 한다*는 요구가 된다.
`σ`, `σ'`를 정리의 인자로 빼면 귀납 가설이 그 특정 상태에만 붙어서 이 단계가 막힌다.

"진술을 더 일반화해야 귀납이 돈다" — 이 저장소에서 가장 자주 쓰는 요령이고,
1장에서만 여섯 번 나온다. 2장 명제 2.7 에서 더 어려운 모습으로 다시 만난다.

# §1.4 치환
%%%
tag := "ch01-substitution"
file := "ch01-substitution"
number := false
%%%

정의가 길어지는 곳은 여기 하나다. 앞의 의미 함수들은 절마다 한 줄이었는데, 치환은
양화사 절에서 새 이름을 골라야 한다.

````anchor assertSubst (module := Reynolds.Answers.Ch01.Substitution)
/--
`p /ₛ δ` — 단언에 대한 동시 치환.

양화사 절만 특별하다.

```
(∀v. p) /ₛ δ = ∀ vnew. (p /ₛ δ[v := var vnew])
```

`v`를 새 이름 `vnew`로 바꾸고, 치환 사상 쪽에서도 `v`를 `var vnew`로 보내도록 고친다.
`vnew`는 `newBinder`가 골라 주므로, 실제로 본문에 자유롭게 나타나 치환되는
`w ∈ p.fv.erase v`에 대해 `δ w`의 자유 변수와 겹치지 않는다.

이 정의가 내놓는 것은 신선한 이름 선택까지 기록한 원시 이름 구문이다. 따라서 서로 다른
신선 이름 선택은 구문 등식으로 같지 않을 수 있지만, 명제 1.5가 그 이름 차이가 의미를
바꾸지 않음을 보인다.

**정지성**: 재귀 호출이 `p` 라는 진부분항에 대해 일어나므로 구조적 재귀다.
"먼저 이름을 바꾸고 다시 치환한다"는 이름 있는 단일 치환의 직접 정의에는 별도의 정지성
증명이 필요하다. Reynolds의 동시 치환 정의는 그 추가 증명 없이 구조적 재귀로 받아들여진다.
-/
def Assert.subst [HasFresh V] : Assert V → Subst V → Assert V
  | .tru,          _ => .tru
  | .fls,          _ => .fls
  | .cmp c e₀ e₁,  δ => .cmp c (e₀ /ₑ δ) (e₁ /ₑ δ)
  | .not p,        δ => .not (p.subst δ)
  | .bin op p q,   δ => .bin op (p.subst δ) (q.subst δ)
  | .quant q v p,  δ =>
      .quant q (newBinder p v δ) (p.subst (Function.update δ v (.var (newBinder p v δ))))
````

양화사 절만 특별하다. `δ`가 데려오는 자유 변수가 `v`에 잡히면(*포획*, capture)
뜻이 달라지므로, 결합 변수를 안전한 이름으로 미리 바꾼다.

이 정의 위에서 명제 1.2부터 1.5까지가 이어진다. 치환 정리(명제 1.3)가 그중 중심이고,
치환한 구문을 평가한 결과와 치환 항들의 값을 상태에 넣은 뒤 원래 구문을 평가한 결과가
같다는 것을 말한다.

## 범주론 렌즈 — 치환은 모나드의 bind다
%%%
tag := "ch01-substitution-monad-lens"
number := false
%%%

`p /ₛ δ`를 변수 타입을 바꾸는 쪽으로 일반화하면(`Depth/TermMonad.lean`의 `IntExp.bind`)
모나드의 `bind`가 된다. 연습 1.7이 묻는 치환 두 번의 합성은 그 결합법칙이고, 결합자가
없는 정수 식에서는 등식으로 성립한다(`Subst.kleisli`). `∀v`가 있는 단언에서는 포획을
피하려고 고르는 새 이름이 매번 달라질 수 있어서, 등식 대신 α-동치(`=α`)까지만 성립한다.
[선택 심화: 치환 모나드와 α-동치](--tag--ch01-term-monad)에서 그 반례와 `=α`를 본다.

## 곁가지 — 이름을 어떻게 다룰 것인가
%%%
tag := "ch01-binding-representations"
file := "ch01-binding-representations"
number := false
%%%

Reynolds는 §1.4 끝에서 결합 변수 이름을 구체 표현의 일부로 보내고, α-동치인 표기들을
하나의 추상 구를 나타내는 표현으로 보는 방향을 *고차 추상 구문(higher-order abstract
syntax)*과 연결한다. 현대 용례에서 HOAS는 보통 메타언어의 함수로 객체언어의 결합을
표현하는 구체적인 기법을 가리킨다. 이름 차이를 추상 구문의 동일성에서 제외한다는 원칙과
그 원칙을 구현하는 특정 표현법을 구분해서 읽어야 한다.

대표적인 표현법은 다음과 같다. 어느 방법도 결합의 증명 부담을 없애지는 않고, 부담이
나타나는 정의와 보조정리를 바꾼다.

: 이름 있는(named) — 우리가 고른 방식

  결합 변수를 이름 그대로 둔다. 치환할 때 포획을 피해야 하며,
  `Substitution.lean`의 `captureSet`과 `newBinder`가 그 일을 맡는다.

: de Bruijn 색인

  결합 변수를 번호로 바꾼다. 항을 다른 자리로 옮길 때마다 번호를 미는 연산(shifting)이 필요하다.

: locally nameless

  묶인 변수는 번호로, 자유로운 변수는 이름으로 둔다. 두 표현 사이를 여닫는 연산이 필요하다.

: HOAS

  묶인 변수를 메타언어 함수의 인자로 표현한다. α-변환과 포획 회피 치환 일부를 메타언어에
  맡길 수 있지만, 임의의 메타언어 함수를 객체 구문으로 받아들이지 않도록 재귀·양성성
  원리를 설계해야 한다.

우리가 첫 번째를 고른 것은 Reynolds를 따라간 것이다. 다른 방식을 골랐다면
`newBinder`가 사라지는 대신 다른 코드가 생긴다.

CSlib 의존성 소스에는 locally nameless 구현이 포함돼 있다.

```
.lake/packages/cslib/Cslib/Languages/LambdaCalculus/LocallyNameless/Untyped/Basic.lean
```

우리의 `Assert.subst`와 나란히 열어 놓고 "포획 회피가 어디로 갔는지"를 찾아보는 것이
좋은 스터디 토론거리다. 묶인 변수에 이름이 없으므로 결합 변수의 이름을 바꾸다가 생기던
포획 문제는 사라진다. 대신 `open`과 `close`가 잘 맞물리는지, 그리고 항에 닫히지 않은
de Bruijn 색인이 없는지, 곧 국소적으로 닫혀 있는지(locally closed) 증명해야 한다.

## 곁가지 — 이름 바꾸기가 깨지는 언어
%%%
tag := "ch01-dynamic-binding"
file := "ch01-dynamic-binding"
number := false
%%%

명제 1.5 는 결합 변수의 이름이 뜻에 영향을 주지 않는다고 말한다. Reynolds는 바로 뒤에서
이 성질이 잘 작동하는 결합을 가진 모든 언어에 적용되지만, 일부 잘 알려진 언어는 예외라고
덧붙인다. §11.7의 *동적 결합(dynamic binding)* 예고다.

정적 결합(static binding)에서 자유 변수는 _그 변수가 쓰인 자리를 둘러싼 코드_에서 뜻을
얻는다. 그래서 결합 변수의 이름을 바꿔도 어느 결합자에 매이는지가 변하지 않는다.

동적 결합에서는 _호출한 쪽_에서 뜻을 얻는다. 그러면 이름이 실행 시점에 의미를 갖게 되고,
결합 변수를 다른 이름으로 바꾸는 순간 어떤 호출자와 만나는지가 달라진다. 명제 1.5 의
결론이 성립하지 않는다.

이 장에서 예고만 하고 넘어가는 이유는, 그것을 말하려면 프로시저와 호출 규약이 먼저
있어야 하기 때문이다. 1장에는 호출이 없다.

따라서 α-변환의 의미 보존은 모든 이름 붙은 구문에서 자동으로 성립하는 사실이 아니다.
1장의 정적 결합 의미와 포획 회피 치환이 그 정리의 가정을 충족한다.

# 정의 선택과 정리의 성립
%%%
tag := "ch01-design"
file := "ch01-design"
number := false
%%%

여기까지는 정의가 주어지고 그 정의에 대한 정리를 증명해 왔다. 그러면 "이 정의가 맞다"를
받아들이고 시작하게 된다. 그런데 Reynolds가 §1.4에서 공들이는 것은 정리 증명이 아니라
_정의를 고르는 일_ 이다. 포획 회피가 왜 필요한지, 자유 변수 함수가 뜻에 영향을 줄 가능성이
있는 변수를 빠뜨리지 않는지가 그 절의 내용이다. 그 집합이 항상 최소인 것은 아니다.
`x - x`에는 `x`가 자유롭게 나타나지만 값은 어느 상태에서나 0이다.

`Design.lean`은 방향을 뒤집어, *그럴듯하지만 틀린 정의* 셋을 주고 각각이 무엇을 깨뜨리는지
증명하게 한다.

* 자유 변수에서 이항 논리 연산의 오른쪽을 빠뜨리면 — _일치 정리_ 가 깨진다
* 의미에서 양화사가 상태를 갱신하지 않으면 — _일치 정리_ 가 깨진다
* 치환에서 결합 변수를 그대로 두면 — _치환 정리_ 가 깨진다

앞의 둘은 같은 정리를 깨뜨리지만 이유는 반대다. 하나는 `fv`가 너무 작고, 다른 하나는
의미가 묶인 변수에 여전히 의존한다. 두 반례를 나란히 보면 일치 정리가 무엇을 주장하는지가
분명해진다 — `fv`와 `eval`이 *서로 맞물려야* 하고, 어느 쪽을 건드려도 맞물림이 풀린다.

세 번째가 §1.4의 본론이다. `∃y. x < y`는 "x보다 큰 수가 있다"이므로 어떤 상태에서도
참인데, 포획을 막지 않은 치환으로 `x`를 `y`로 바꾸면 `∃y. y < y`가 되어 어떤 상태에서도
거짓이 된다. 들어온 `y`가 자유 변수여야 하는데 양화사에 잡힌 것이다.

한 가지는 이 방식으로 바로 보이기 어렵다. *동시 치환을 기본으로 두는 이유*다. 한 변수씩
치환하는 직접 방정식은 양화사 절에서 구조적 재귀가 아니므로 Lean이 그대로는 받아들이지
않는다. 구의 크기가 줄어든다는 보조정리와 정초 재귀(well-founded recursion)를 쓰면
정의할 수 있지만, 동시 치환은 그 추가 장치 없이 진부분항에 대한 구조적 재귀로 끝난다.
`Design.lean` 마지막 절에 산문으로 적어 두었다.

# 연습 1.5 · 1.6 — 정수 식의 결합자
%%%
tag := "ch01-summation"
file := "ch01-summation"
number := false
%%%

지금까지 결합자는 단언 층에만 있었다. 연습 1.5 는 합 식 `Σv : e₀ to e₁. e₂`를 더해서
*정수 식이면서 변수를 묶는* 경우를 만든다.

새로운 것은 묶는 범위가 부분식마다 다르다는 점이다. `v`는 `e₂` 안에서만 묶이고,
`e₀`와 `e₁`은 밖이다 — 상계(upper bound)와 하계는 합을 시작하기 전에 정해지므로
바깥의 `v`를 본다.

```anchor sExpFv (module := Reynolds.Answers.Ch01.Ex.Summation)
/-- `FV(e)` — 합 식이 있는 정수 식의 자유 변수. `sum` 절에서 `e₂`만 `erase` 한다. -/
def SExp.fv : SExp V → Finset V
  | .num _         => ∅
  | .var v         => {v}
  | .neg e         => e.fv
  | .bin _ e₀ e₁   => e₀.fv ∪ e₁.fv
  | .sum v e₀ e₁ e₂ => e₀.fv ∪ e₁.fv ∪ (e₂.fv.erase v)
```

`e₂`에서만 `erase` 한다. 같은 비대칭이 치환과 의미 방정식(semantic equation)에도
그대로 나타난다.

## 합 식에서도 치환 정리가 성립하는가

책 p. 23의 연습 1.5(c)는 정의를 제시하는 데서 끝나지 않는다. §1.4의 결합·치환 명제가
계속 성립해야 한다. `Ex/Summation/Substitution.lean`에서 명제 1.2의 치환 일치·항등·자유 변수
법칙을 확인하고, 아래 명제 1.3의 합 식 판을 새 연습으로 푼다.

```anchor stmtSubstitutionSExp (module := Reynolds.Answers.Ch01.Ex.Summation.Substitution)
/--
연습 1.5(c) (p. 23): 명제 1.3 (§1.4)의 합 식 판.
치환한 구문을 평가하는 것과 치환 사상을 평가한 상태에서 원래 구문을 평가하는 것이 같다.
`hcoin`은 별도 일치 정리 연습의 결론이다. 가설로 받아 두 연습의 채점을 분리한다.
-/
@[exercise "Ex 1.5c-substitution" 3]
theorem substitution_sExp
    (hcoin : ∀ (e : SExp V) (σ σ' : State V),
      (∀ w ∈ e.fv, σ w = σ' w) → ⟦e⟧ₛ σ = ⟦e⟧ₛ σ') :
    ∀ (e : SExp V) (δ : SSubst V) (σ σ' : State V),
      (∀ w ∈ e.fv, σ w = ⟦δ w⟧ₛ σ') → ⟦e /ₜ δ⟧ₛ σ' = ⟦e⟧ₛ σ
```

`hcoin`은 이미 주어진 가설이므로 앞의 `coincidence_sExp` 연습을 풀지 않고도 쓸 수 있다.
합의 두 경계는 원래 치환으로 처리하고, 본체는 새 결합 변수로 갱신한 치환으로 처리한다.
그 새 이름이 대입되는 식의 자유 변수를 포획하지 않는다는 사실이 증명의 핵심이다.

예를 들어 `Σi : 1 to 2. a`에 `a ↦ i`를 넣고 바깥 상태에서 `i = 7`이라면 값은 14다.
결합자를 그대로 두어 새 `i`를 포획하면 3이 되어 치환 정리에 어긋난다.
반면 `Σi : 1 to i. i`의 상계에 있는 `i`는 자유로우므로 치환해야 한다.
한 변수 치환과 결합 변수 이름 바꾸기는 새 정리의 따름정리로 제공한다.

이 실습은 합 식을 포함한 정수 식 `SExp`를 다룬다. 비교식·양화 단언 전체를 확장하거나,
연습 1.7의 구문적 α-동치까지 증명한 것은 아니다.

## 부정 합에서는 무엇이 달라지는가

연습 1.6은 여기서 한 걸음 더 간다. 부정 합(indefinite summation) `Σv. e`의 뜻이
`Σ_{v=0}^{v-1} e`라서,
`v`가 아래첨자로 묶이면서 동시에 상계로 자유롭다. 한 이름이 한 식 안에서 두 역할을
하고, §1.4의 결합 구조에는 그럴 곳이 없다. 결과로 *이름 바꾸기 정리(renaming theorem)가
깨진다* —
`Ex/Summation/Indefinite.lean`에서 반례를 증명한다.

앞 절의 동적 결합과 결과는 비슷하지만 원인은 다르다. 여기서는 `Σv. e`를 독립적인 원시
구문으로 두면서, 표면의 같은 `v` 중 어느 발생이 자유롭고 어느 발생이 묶이는지를 생성자
구조에 표현하지 못했다. 이를 `Σv : 0 to v-1. e`로 디슈거링하는 파생 구문으로 정의하면
상계의 자유 발생과 본체의 속박 발생이 다시 서로 다른 부분식에 놓이고, §1.4의 치환 정의를
그대로 적용할 수 있다.

# 직접 해 보기
%%%
tag := "ch01-try"
file := "ch01-try"
number := false
%%%

저장소를 받고 나서:

```
lake exe cache get        # Mathlib 캐시. 처음 한 번만
lake build
lake exe grade --chapter 1
```

`lake exe grade`가 아직 안 채운 연습을 표로 보여 준다. `Reynolds/Exercises/Ch01/`에서
{lit}`sorry`를 찾아 지우고 채운 뒤 다시 돌리면 된다.

막히면 `docs/solving-guide.md`를 먼저 봐라. 이 저장소가 반복하는 증명 패턴 넷과
자주 만나는 오류 메시지가 정리되어 있다.

# 연습 1.1–1.3 — 단언과 구문 세계 만들기
%%%
tag := "ch01-early-exercises"
file := "ch01-early-exercises"
number := false
%%%

책 p. 22의 연습 1.1·1.2는 주어진 단언을 계산하는 문제가 아니라, 설명에 맞는 단언을
직접 쓰는 문제다. `Exercises/Ch01/Ex.lean`의 `e11aAnswer`부터 `e12dAnswer`까지
여덟 빈칸에는 구문과 의미 증명을 함께 쓴다. 답의 첫 칸에는 객체 언어 `Assert String`의
값, 둘째 칸에는 그 단언이 의도한 뜻이라는 Lean 명제가 들어간다.

연습 1.1에서는 `refine ⟨fun lo hi => ⟪ … ⟫ₐ, ?_⟩`로 시작한다.
`lo`, `hi`는 Lean의 정수이고 `%(.num lo)`는 그 정수를 단언 안에 넣는 표기다.
책의 (a)·(b)는 열린 구간 `(0,2)`, (c)·(d)는 `(0,3)`이다.
적어도 둘이라는 말에는 서로 다른 두 수가 필요하다. 많아야 둘이라는 말은 세 수를
골랐을 때 적어도 한 쌍이 같다는 뜻으로 표현할 수 있다.

*책과의 차이*: 고정된 네 문장은 모두 참이라 참 단언만 써도 의미 검사를 통과한다.
이를 피하는 보조 실습으로 임의의 구간을 받으며, `intervalCount`의 원소 수와 비교한다.
`Finset.one_le_card`, `Finset.card_le_one`, `Finset.one_lt_card_iff`,
`Finset.two_lt_card_iff`는 개수를 양화 명제로 풀어 주는 도구다.
완성한 답에는 책의 끝점도 직접 대입하여 종이에 쓴 단언과 비교해 본다.

연습 1.2는 책의 지시대로 변수와 양화 범위가 자연수다. 이 문제만의 `evalNat`를 쓰며,
본문의 정수 의미 함수는 그대로 둔다. `NatAnswer`에는 단언, 허용 구문 검사,
모든 자연수 상태에 대한 뜻의 증명이 들어간다. `refine ⟨⟪ … ⟫ₐ, rfl, ?_⟩`로
단언을 쓴 뒤 `evalNat`와 의미 명세를 펼쳐 비교한다.

*책과의 차이*: 산술 구문은 네 답에 충분한 자연수 상수·변수·덧셈·곱셈으로 제한한다.
책이 금하는 나눗셈·나머지뿐 아니라 음수 리터럴과 뺄셈도 이 보조 실습에서는 받지 않는다.
이 제한으로 식의 값이 항상 자연수 범위에 머문다. 구문 검사와 이 사실의 증명은
`Ex/Specifications.lean`에 있다.

최대공약수 문항은 공약수 집합의 *최대 원소*를 표현한다. 두 입력이 모두 0이면
모든 자연수가 공약수이고, 어떤 후보보다 1 큰 공약수가 있으므로 최대가 없다.
따라서 이 문항은 그 상태에서 거짓이다. `Nat.gcd 0 0 = 0`은 별도 함수의 규약이므로
그 등식으로 이 경계를 대신하지 않는다. 소수 문항에서는 0과 1도 직접 검사해 본다.

연습 1.3은 `Realizations.lean` → `Realizations/Assertions.lean` →
`Realizations/Constructors.lean` 순서로 읽는다. 마지막 파일의 한 연습에서 식 (1.1)
(p. 4)의 모든 정수 식·단언 생성자가 인자를 보존함을 증명한다. 이항 생성자의 결과는
두 토큰 열을 이어 붙이므로, 앞 구의 끝을 유일하게 복원하는 접두사 자유성이 필요하다.
양화 생성자는 변수 이름도 보존한다. 이 단계에서는 α-동치인 단언도 서로 다른 구문이다.

*책과의 차이*: 책은 구의 세계와 생성자도 설계하라고 한다. 여기서는 문자열 대신
구별되는 토큰과 올바른 토큰 열의 부분타입을 완성 자료로 주고, 생성자의 단사성을 푼다.
빈 목록이나 인자가 모자란 목록은 구가 아니다. 아홉 연습은 서로 독립적으로 채점된다.

# 연습 1.4 — 치환 결과를 직접 쓰기
%%%
tag := "ch01-substitution-calculation"
file := "ch01-substitution-calculation"
number := false
%%%

책 p. 23의 세 문항은 `Exercises/Ch01/Ex.lean`의 `e14aResult`, `e14bResult`,
`e14cResult`에 있다. 입력 단언과 치환 사상은 주어지고, 결과 단언과 그 결과를 확인하는
증명을 함께 채운다. 앞의 치환 정리를 아직 풀지 않았어도 이 세 문항은 각각 풀 수 있다.

결과 타입 `{q : Assert String // e14a /ₛ e14aSubst = q}`는 두 칸짜리 묶음이다.
첫 칸은 결과 단언 `q`, 둘째 칸은 실제 치환 결과가 그 단언이라는 증명이다.
`refine ⟨⟪ … ⟫ₐ, ?_⟩`로 먼저 계산한 단언을 쓰고, 남은 등식을 힌트의 정의와
이름 선택 보조정리로 확인한다. `/ₛ`를 그대로 첫 칸에 넣으면 계산할 구문을 다시 적은
것이므로, 이 실습에서는 양화사와 비교식으로 결과를 끝까지 써 본다.

각 양화사에서는 본문에 자유롭게 나타나는 변수만 살핀다. 그 발생에 들어올 식의 자유 변수가
결합자와 겹칠 때만 이름을 바꾼다. 치환 사상에 변수 이름이 있다고 해서 속박 발생까지
바꾸지는 않는다. 또한 동시 치환은 들어온 식에 같은 치환을 다시 적용하지 않는다.

책은 불필요한 이름 바꾸기를 금하지만 새 이름의 철자는 지정하지 않는다.
이 저장소는 안전하면 원래 이름을 유지하고, 바꿔야 할 때는 `x`, `xx`, `xxx`, … 중
피해야 할 집합에 없는 첫 이름을 고른다. 따라서 책에서 가능한 다른 철자의 답은
이 실습의 구문 등식과 다를 수 있다. 의미 보존은 완성 자료 `e14b_meaning`으로 따로 볼 수 있다.

# 연습문제
%%%
tag := "ch01-exercise-list"
file := "ch01-exercise-list"
number := false
%%%

1장에는 채점되는 연습이 37개 있다. 책 연습문제와 본문 명제가 섞여 있고,
아래는 [읽는 순서](--tag--ch01-order)와 같은 차례로 늘어놓은 것이다.

* `Validity.lean` — §1.3 건전성과 규칙. *3개*
* `FreeVars.lean`, `Substitution.lean` — 본문 명제 1.1 ~ 1.3. *5개*
* `Realizations/Constructors.lean`, `Ex.lean` — 책 연습 1.1 ~ 1.4. *12개*
* `Ex/Summation.lean`·`Ex/Summation/` — 책 연습 1.5 · 1.6. *7개*
* `Design.lean` — 정의 선택과 정리의 성립. *3개*
* `Depth/` — 심화 트랙. *7개*

본문 명제를 건너뛰면 책 연습에서 쓸 재료가 없다.

명제 1.1(정수 식 판, `coincidence_intExp`)과 명제 1.5는 파일에 있지만
채점 대상이 아니다. 방향이 서로 반대다 — 정수 식 판은 명제 1.1(단언 판)과 명제 1.3
(치환 정리)이 그 결과를 직접 쓰므로 완성된 채로 주고, 명제 1.5는
거꾸로 치환 정리 자체를 쓴다. 채점기는 "이 증명이 `sorry`에 기대는가"만 보고
그것이 자기 `sorry` 인지 앞 연습에서 물려받은 것인지 구별하지 못한다. 그래서 비우는 연습들은
서로 의존하지 않도록 골라 두었다.

심화 트랙은 책을 따라가는 데 필요하지 않다. 건너뛰어도 1장은 완결된다.

# 선택 심화: 책 식 (1.2) — 깊이별 구성
%%%
tag := "ch01-depth-construction"
%%%

Reynolds §1.1 p.4–5는 추상 구문의 반송자가 만족해야 할 조건 중 셋째("유한 번의 생성자
적용으로 만들어진다")를 집합으로 직접 구성하는 방법으로도 보여 준다. 식 (1.2)다.

```
⟨intexp⟩⁽⁰⁾   = ∅
⟨intexp⟩⁽ʲ⁺¹⁾ = {c₀(), c₁(), …} ∪ {c_var(x) | x ∈ ⟨var⟩}
                 ∪ {c₋(e) | e ∈ ⟨intexp⟩⁽ʲ⁾} ∪ …
⟨intexp⟩      = ⋃ⱼ ⟨intexp⟩⁽ʲ⁾
```

`inductive`는 이 구성을 전부 생략하고 결과만 공짜로 준다. `Depth/Construction.lean`은
그 생략된 구성을 `IntExp V` 위의 부분집합 층으로 되살린다.

```anchor IntExp.layer (module := Reynolds.Answers.Ch01.Depth.Construction)
def IntExp.layer (V : Type u) : ℕ → Set (IntExp V)
  | 0     => ∅
  | j + 1 =>
      Set.range IntExp.num ∪ Set.range IntExp.var
        ∪ IntExp.neg '' IntExp.layer V j
        ∪ ⋃ op : IntOp, Set.image2 (IntExp.bin op) (IntExp.layer V j) (IntExp.layer V j)
```

`num`과 `var`는 자식이 없으므로 첫 층(`j = 0 → 1`)부터 나타나고, 그 뒤로는 매 층에서
같은 집합으로 다시 나온다. `neg`와 `bin`은 한 단계 아래 층의 원소를 재료로 쓴다. 다음은
그 "다시 나온다"는 단조성(완성된 `layer_mono`)을 재료로 쓰는 연습이다.

```anchor IntExp.mem_layer_succ_depth (module := Reynolds.Answers.Ch01.Depth.Construction)
@[exercise "심화 A1.7" 2]
theorem IntExp.mem_layer_succ_depth {V : Type u} (e : IntExp V) :
    e ∈ IntExp.layer V (e.depth + 1) := by
```

모든 구는 자기 깊이(depth)보다 한 층 위에 있다. `neg` 케이스는 귀납 가설의 층이 그대로
맞고, `bin` 케이스에서는 두 자식을 `layer_mono`로 같은 층까지 끌어올린 뒤 합친다.

식 (1.2)의 결론 — 반송자는 깊이별 층들의 합집합이다 — 은 이 연습의 바로 쓸 수 있는
귀결이라 완성된 채로 둔다. 책의 셋째 조건 자체도 집합으로 다시 적을 수 있다.

```anchor IntExp.eq_univ_of_closed (module := Reynolds.Answers.Ch01.Depth.Construction)
@[exercise "심화 A1.6" 1]
theorem IntExp.eq_univ_of_closed {V : Type u} (S : Set (IntExp V))
    (hnum : ∀ n, IntExp.num n ∈ S) (hvar : ∀ v, IntExp.var v ∈ S)
    (hneg : ∀ e ∈ S, IntExp.neg e ∈ S)
    (hbin : ∀ op, ∀ e₀ ∈ S, ∀ e₁ ∈ S, IntExp.bin op e₀ e₁ ∈ S) :
    S = Set.univ := by
```

생성자를 적용해도 빠져나가지 못하는 부분집합은 애초에 전체였어야 한다("no junk").
`IntExp.rec`가 그대로 증명을 준다 — `layer`를 전혀 쓰지 않으므로 앞 연습과는 독립이다.

_책과의 차이_: 책은 이 구성을 ⟨intexp⟩와 ⟨assert⟩ 둘 다에 대해 말한다. 여기서는 정수
식만 다룬다. `Assert`는 반송자가 둘이고 `cmp`가 정렬을 건너가므로, 층을 두 반송자에
동시에 매기는 구성이 한 단계 더 필요하다.

이 깊이별 구성은 2장 §2.4 끝에서 나오는, 명령 의미의 최소 고정점 구성과 같은 모양이다 —
둘 다 "∅(또는 ⊥)에서 시작해 한 단계 연산자를 반복 적용한 사슬의 합"이다.

# 선택 심화: 초기성이 구조적 귀납을 돌려준다
%%%
tag := "ch01-depth-induction"
%%%

`Depth/Algebra.lean`의 초기성(`IntExp.initial`)은 "항 대수가 모든 대수로 유일한
준동형을 갖는다"는 명제였고, 그 유일성은 구조적 귀납법으로 증명했다. 반대 방향도
성립한다 — 초기성 하나만 있으면 구조적 귀납 원리를 되찾을 수 있다.

다음 연습은 그 반대 방향을 일반 정리로 적은 것이다. 특정 대수가 실제로 초기라는 사실은
쓰지 않는다. 대신 "어떤 `IntExp V`가 초기 대수라면"이라는 가설 `hinit`에서 결론을
끌어낸다.

```anchor IntExp.induction_of_initial (module := Reynolds.Answers.Ch01.Depth.Algebra)
@[exercise "심화 A1.5" 3]
theorem IntExp.induction_of_initial {V : Type u}
    (hinit : ∀ A : IntExpAlg.{u, u} V, ∃! h : IntExp V → A.Carrier, IsHom A h)
    (P : IntExp V → Prop)
    (hnum : ∀ n, P (.num n)) (hvar : ∀ v, P (.var v))
    (hneg : ∀ e, P e → P (.neg e))
    (hbin : ∀ op e₀ e₁, P e₀ → P e₁ → P (.bin op e₀ e₁)) :
    ∀ e, P e := by
```

증명의 뼈대는 부분 대수 논법(sub-algebra argument)이다. `P`에 닫힌 부분집합
`{x // P x}`를 대수로 만들면, 포함 사상 `Subtype.val`은 그 부분 대수에서 항 대수로
가는 준동형이다. `hinit`으로 얻은 유일한 사상을 그 포함 사상과 합성하면 항 대수의
자기 자신으로 가는 준동형이 되는데, `id`도 그런 준동형이고 `hinit`을 항 대수 자신에
적용하면 그런 준동형이 하나뿐이라고 말해 준다. 그래서 둘이 같고, 그 등식이 바로
"모든 `e`에서 `P e`"가 된다.

이 정리는 `IntExp.initial`(심화 A1.1)을 전혀 몰라도 성립한다. 반대로 `IntExp.initial`을
`hinit`에 넣으면 §5의 유일성 증명 없이도 구조적 귀납 원리를 얻는다 — 다만 그 결합을
따로 적지는 않는다. 독자가 "이 연습이 A1.1에 기대는 건가?"라고 헷갈리기 쉬워서다.
`induction e with …` 태틱이 이미 공짜로 주는 것과 같은 결론이지만, 증명 방법이 다르다는
것이 요점이다 — 케이스 분석 없이 보편 성질 하나로 모든 생성자 조건을 동시에 처리한다.

# 선택 심화: 초기성이 Lambek 보조정리를 돌려준다
%%%
tag := "ch01-depth-lambek-general"
%%%

`Depth/SignatureFunctor.lean`의 `IntExp.lambek`은 `cases`로 끝난다. `inductive`가
이미 만들어 둔 `roll`/`unroll`을 확인할 뿐이지, 초기 대수의 구조 사상이 _왜_ 항상
동형인지는 아직 보이지 않는다. 다음 정리가 그 이유다 — 특정 구문을 전혀 쓰지 않고
"초기 `Sig V`-대수의 구조 사상은 동형이다"를 추상적으로 보인다.

```anchor IsSigHom (module := Reynolds.Answers.Ch01.Depth.SignatureFunctor)
def IsSigHom {V : Type u} {C D : Type v} (s : Sig V C → C) (t : Sig V D → D) (h : C → D) :
    Prop :=
  ∀ x, h (s x) = t (Sig.map h x)
```

`h`가 "자식에 `h`를 입힌 뒤 구조 사상을 적용한 것"과 "`h`를 적용한 뒤 구조 사상을
적용한 것"을 같게 만든다는 한 줄이다. `Depth/Algebra.lean`의 `IsHom`은 이 조건을
`IntExpAlg`의 생성자별 필드로 풀어 쓴 것과 같다.

```anchor isIso_of_initial (module := Reynolds.Answers.Ch01.Depth.SignatureFunctor)
theorem isIso_of_initial {V : Type u} {C : Type u} (s : Sig V C → C)
    (hinit : ∀ {D : Type u} (t : Sig V D → D), ∃! h : C → D, IsSigHom s t h) :
    Function.Bijective s := by
  obtain ⟨φ, hφ, _⟩ := hinit (Sig.map s)
  have hψ : IsSigHom s s (s ∘ φ) := by
    intro x
    change s (φ (s x)) = s (Sig.map (s ∘ φ) x)
    rw [hφ x, Sig.map_comp]
  obtain ⟨_, _, huniq⟩ := hinit s
  have hidHom : IsSigHom s s (id : C → C) := fun x => by rw [Sig.map_id]; rfl
  have hcomp : s ∘ φ = id := (huniq _ hψ).trans (huniq id hidHom).symm
  have hleft : φ ∘ s = id := by
    funext x
    change φ (s x) = x
    calc φ (s x) = Sig.map s (Sig.map φ x) := hφ x
      _ = Sig.map (s ∘ φ) x := Sig.map_comp φ s x
      _ = Sig.map id x := by rw [hcomp]
      _ = x := Sig.map_id x
  exact Function.bijective_iff_has_inverse.mpr ⟨φ, congrFun hleft, congrFun hcomp⟩
```

초기성을 가설 `hinit`으로 받는다 — 다른 모든 `Sig V`-대수로 가는 준동형이 `(C, s)`에서
정확히 하나 있다는 뜻이다. 증명은 범주론의 표준 논증이다. 자식 자리에 `s`를 한 번 더
입힌 대수 `(Sig V C, Sig.map s)`로 가는 유일한 준동형 `φ`를 얻고, `s ∘ φ`와 `id`가 둘 다
`(C, s)`의 자기 준동형임을 보여 `s ∘ φ = id`를 얻는다. 그 등식을 `φ`의 준동형 조건에
다시 넣고 함자 법칙(`map_id`)을 쓰면 `φ ∘ s = id`도 나온다.

이 정리는 비채점 _심화 B1.2_로 분류하되 완성본으로 둔다. `IntExp.lambek`(심화 B1.1)이
`C := IntExp V`, `s := IntExp.roll`로 놓은 한 사례이지만, 그 사례를 따로 선언하지는
않는다 — 같은 결론을 복제하면 B1.1을 자명하게 만든다.

# 선택 심화: 정수 식과 단언을 함께 접기
%%%
tag := "ch01-logic-initiality"
%%%

`x < 3`을 해석하려면 먼저 `x`와 `3`이라는 정수 식의 결과가 필요하다.
반대로 정수 식을 해석할 때는 단언의 결과가 필요하지 않다. `Depth/Algebra.lean`의
`LogicAlg`는 이 연결을 정수 식 반송자 `E`와 단언 반송자 `A`로 표현한다.
반송자는 해석 결과가 사는 타입이다. 변수 타입 `V`는 대수마다 바꾸지 않고 고정한다.

준동형은 생성자를 만드는 순서와 해석하는 순서를 바꾸어도 결과가 같은 함수다.
여기서는 구문의 종류가 둘이므로 함수도 쌍으로 둔다. `h.1`은 정수 식을 옮기고
`h.2`는 단언을 옮긴다. `cmp`의 등식에서 입력과 출력에 어느 함수를 쓰는지 확인하면
두 정렬이 어떻게 연결되는지 읽을 수 있다.

```anchor LogicAlg.IsHom (module := Reynolds.Answers.Ch01.Depth.Algebra)
/--
고정된 변수 타입 `V`의 원시 구문에서 `L`로 가는 준동형 조건이다.

함수 쌍의 첫 성분은 정수 식, 둘째 성분은 단언을 옮긴다. `cmp`는 두 성분을 함께 쓰며,
`quant`는 결합 변수의 이름까지 보존한다. 두 목표 반송자는 기존 `LogicAlg`처럼 같은
우주 `Type v`에 놓고, 변수 타입의 우주 `Type u`와는 독립적으로 둔다.
-/
structure LogicAlg.IsHom {V : Type u} (L : LogicAlg.{u, v} V)
    (h : (IntExp V → L.E) × (Assert V → L.A)) : Prop where
  /-- 정수 상수 보존. -/
  num : ∀ n, h.1 (.num n) = L.num n
  /-- 변수 보존. -/
  var : ∀ x, h.1 (.var x) = L.var x
  /-- 정수 부호 반전 보존. -/
  eneg : ∀ e, h.1 (.neg e) = L.eneg (h.1 e)
  /-- 정수 이항 연산 보존. -/
  ebin : ∀ op e₀ e₁, h.1 (.bin op e₀ e₁) = L.ebin op (h.1 e₀) (h.1 e₁)
  /-- 참 보존. -/
  tru : h.2 .tru = L.tru
  /-- 거짓 보존. -/
  fls : h.2 .fls = L.fls
  /-- 비교의 입력에는 정수 식 함수를, 출력에는 단언 함수를 쓴다. -/
  cmp : ∀ c e₀ e₁, h.2 (.cmp c e₀ e₁) = L.cmp c (h.1 e₀) (h.1 e₁)
  /-- 논리 부정 보존. -/
  anot : ∀ p, h.2 (.not p) = L.anot (h.2 p)
  /-- 논리 이항 연산 보존. -/
  abin : ∀ op p q, h.2 (.bin op p q) = L.abin op (h.2 p) (h.2 q)
  /-- 양화사 종류와 결합 변수 이름을 고정한 채 본문을 옮긴다. -/
  quant : ∀ q x p, h.2 (.quant q x p) = L.quant q x (h.2 p)
```

`foldE`와 `foldA`는 각 생성자를 목표 대수의 연산으로 바꾸는 함수다.
이 둘은 위의 열 조건을 만족한다. 초기성은 그런 함수 쌍이 존재하고 유일하다는 뜻이며,
Lean에서는 `∃!`로 적는다. 다음은 심화 연습 A1.3의 진술이다.

```anchor LogicAlg.initial (module := Reynolds.Answers.Ch01.Depth.Algebra)
@[exercise "심화 A1.3" 3]
theorem LogicAlg.initial {V : Type u} (L : LogicAlg.{u, v} V) :
    ∃! h : (IntExp V → L.E) × (Assert V → L.A), L.IsHom h := by
```

유일성을 증명할 때는 정수 식의 결과가 정해짐을 먼저 보인다. 단언의 구조를 따라갈 때
비교식에서는 그 결과를 쓰고, 부정과 논리 연산에서는 단언에 대한 귀납 가설을 쓴다.
양화사의 경우 `quant` 조건은 변수 이름까지 그대로 유지한다. 따라서 이 정리는
`∀x. p`와 이름을 바꾼 구문을 동일시하는 α-동치나 치환 법칙을 말하지 않는다.
범주론 용어를 배우지 않아도 열 조건과 `∃!`만으로 이 연습을 읽을 수 있다.

# 선택 심화: 의미와 자유 변수는 어떤 접기인가
%%%
tag := "ch01-logic-fold"
%%%

Reynolds §1.2 pp.10–11은 생성자마다 주어진 의미 방정식이 정수 식과 단언의 의미를
함께 유일하게 정한다고 설명한다. 앞 절의 추상적인 목표 대수에 실제 해석을 넣어 보자.
정수 식은 상태에서 정수를 얻는 함수로, 단언은 상태에서 명제를 얻는 함수로 옮긴다.
비교 연산은 정수 함수 둘을 받아 명제 함수를 만든다.

```anchor logicEvalAlg (module := Reynolds.Answers.Ch01.Depth.LogicFold)
def logicEvalAlg (V : Type u) [DecidableEq V] : LogicAlg V where
  E := State V → Int
  A := State V → Prop
  num n := fun _ => n
  var x := fun σ => σ x
  eneg f := fun σ => -f σ
  ebin op f g := fun σ => op.denote (f σ) (g σ)
  tru := fun _ => True
  fls := fun _ => False
  cmp c f g := fun σ => c.denote (f σ) (g σ)
  anot p := fun σ => ¬ p σ
  abin op p q := fun σ => op.denote (p σ) (q σ)
  quant
    | .all, x, p => fun σ => ∀ n : Int, p (σ[x := n])
    | .ex, x, p => fun σ => ∃ n : Int, p (σ[x := n])
```

양화사의 본문은 여러 갱신 상태에서 해석된다. 따라서 본문을 접은 결과에는 상태 하나의
진릿값 대신 상태 전체를 입력받는 함수가 들어간다. Lean에서는 책의 진릿값을 `Prop`으로
표현한다. 예를 들어 `∃x. x = 7`은 바깥 상태가 `x`에 어떤 값을 주더라도 참이다.

다음 한 문제는 단언의 구조적 귀납법으로 푼다. 비교 분기에서는 완성된
`IntExp.eval_eq_foldE`를 사용하고, 양화 분기에서는 본문에 대한 함수 등식을 쓴다.
초기성 문제 A1.3을 먼저 풀 필요는 없다.

```anchor Assert.eval_eq_foldA (module := Reynolds.Answers.Ch01.Depth.LogicFold)
@[exercise "심화 A1.4" 2]
theorem Assert.eval_eq_foldA {V : Type u} [DecidableEq V] (p : Assert V) :
    p.eval = (logicEvalAlg V).foldA p := by
```

초기성 정리에 이 목표 대수를 넣으면 의미 방정식을 만족하는 함수 쌍이 기존 해석과
같다는 귀결을 얻는다. 이 유일한 접기를 catamorphism이라고도 부른다.
아래 정리는 초기성을 이용한 제공 자료이며 별도의 채점 문제가 아니다.

```anchor logicEval_unique (module := Reynolds.Answers.Ch01.Depth.LogicFold)
theorem logicEval_unique {V : Type u} [DecidableEq V]
    (h : (IntExp V → State V → Int) × (Assert V → State V → Prop))
    (hh : (logicEvalAlg V).IsHom h) : h = (IntExp.eval, Assert.eval) := by
```

§1.4 pp.15–16의 자유 변수 방정식도 같은 방식으로 읽는다. `logicFvAlg`는 두 반송자를
모두 `Finset V`로 두고, 비교와 이항 연산에서 합집합을 취하며, 양화사에서는 결합 이름을
지운다. 이 방정식의 유일한 해석 쌍은 `IntExp.fv`와 `Assert.fv`다.

```anchor logicFv_unique (module := Reynolds.Answers.Ch01.Depth.LogicFold)
theorem logicFv_unique {V : Type u} [DecidableEq V]
    (h : (IntExp V → Finset V) × (Assert V → Finset V))
    (hh : (logicFvAlg V).IsHom h) : h = (IntExp.fv, Assert.fv) := by
```

자유 변수 집합은 구문을 따라 계산한다. `x - x`의 값은 늘 0이지만 자유 변수 집합에는
`x`가 남는다. 이 선택 보충은 책의 구문 지향 정의를 대수로 연결하며, 의미의 최소 의존
집합이나 α-동치까지 다루지는 않는다.

# 선택 심화: 같은 초기성을 Mathlib으로 읽기
%%%
tag := "ch01-category-bridge"
%%%

두 정렬 초기성의 `∃!`를 이해했다면, 범주론에서 말하는 초기 대상도 읽을 수 있다.
범주(category)는 대상과 대상 사이의 사상, 그리고 사상을 이어 붙이는 합성을 갖춘다.
여기서 대상은 `LogicAlg`, 사상은 연산을 보존하는 함수 쌍이다.
초기성 정리에서는 사상의 출발점이 늘 구문이었지만, 이제 출발점도 임의의 대수로 둔다.

예를 들어 `f : L ⟶ M`은 정수 식 반송자의 함수 `f.e`와 단언 반송자의 함수 `f.a`를
갖는다. 비교 연산의 보존 조건은 `f.a (L.cmp c x y) = M.cmp c (f.e x) (f.e y)`다.
입력 둘은 정수 식 성분으로, 결과는 단언 성분으로 옮긴다. 양화사에서는 종류와 변수
이름을 그대로 두고 본문에만 `f.a`를 적용한다.

항등 사상은 두 반송자의 항등 함수 쌍이다. `f ≫ g`는 먼저 `f`, 다음에 `g`를
적용하므로 정수 식 성분은 `g.e ∘ f.e`, 단언 성분은 `g.a ∘ f.a`가 된다.
함수 합성의 항등 법칙과 결합 법칙으로 아래 범주 법칙을 증명한다.

```anchor LogicAlg.category (module := Reynolds.Answers.Ch01.Depth.CategoryBridge)
/-- 고정된 우주의 대수와 준동형으로 이루어진 범주. 법칙은 함수 합성의 법칙이다. -/
instance category : Category (LogicAlg.{u, u} V) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp _ := Hom.ext rfl rfl
  comp_id _ := Hom.ext rfl rfl
  assoc _ _ _ := Hom.ext rfl rfl
```

여기서는 변수 타입과 두 반송자를 모두 같은 `Type u`에 둔다. 따라서
서로 다른 우주의 목표 대수도 허용했던 `LogicAlg.initial`을 이 범주의 대상들에
한정해서 사용한다. `syntaxAlg V`는 정수 식과 단언 자체를 반송자로 갖는 대수다.

```anchor LogicAlg.syntaxIsInitial (module := Reynolds.Answers.Ch01.Depth.CategoryBridge)
/-- 기존 `LogicAlg.initial`을 적용하면 구문 대수가 이 범주의 초기 대상이 된다. -/
noncomputable def syntaxIsInitial (V : Type u) : IsInitial (syntaxAlg V) :=
  isInitialOfUniqueHom (fun L ↦ L.initial)
```

`IsInitial (syntaxAlg V)`는 각 목표로 가는 사상을 고르는 자료와 그 유일성 증명을
포함한다. 그 자료가 주어지면 `h.to L`로 사상을 얻고, `h.hom_ext`로 두 사상의
등식을 얻는다. 다음 연습은 이 두 API를 `LogicAlg.IsHom`의 함수 쌍 언어로 옮기는 문제다.
초기성을 가설로 주므로 A1.3을 아직 풀지 않았어도 시작할 수 있다.

```anchor LogicAlg.uniqueHom_of_isInitial (module := Reynolds.Answers.Ch01.Depth.CategoryBridge)
@[exercise "심화 C1.1" 2]
theorem uniqueHom_of_isInitial (h : IsInitial (syntaxAlg V)) (L : LogicAlg.{u, u} V) :
    ∃! f : (IntExp V → L.E) × (Assert V → L.A), L.IsHom f := by
```

힌트: `Hom.pair`와 `Hom.isHom`으로 함수 쌍과 보존 조건을 꺼낸다. 유일성을 보일 때는
다른 함수 쌍을 `Hom.ofIsHom`으로 사상에 묶은 다음 비교한다.
`isInitial_iff_uniqueHom`은 두 방향을 한 명제로 모은다. 왼쪽의 `Nonempty`는
`IsInitial` 자료가 있다는 것을 명제로 표현한다.

이 선택 심화는 이름을 그대로 보존하는 원시 구문의 범주에 머문다. α-동치로 나눈
구문의 초기성, 치환의 법칙, 일반 함자의 대수에 대한 Lambek 정리는 선택 후속 주제다.
본문의 1장 학습은 이 파일 없이도 이어갈 수 있다.

# 선택 심화: 합성성과 합동
%%%
tag := "ch01-congruence"
%%%

[범주론 렌즈](--tag--ch01-semantics-category-lens)에서 본 것처럼, 구문 지향적으로 정의한
의미 함수는 자동으로 합성적(compositional)이다. Reynolds §1.2 p.11은 이 귀결을 이렇게
적는다.

> *"A semantics is said to be compositional when the meaning of each phrase does not depend on any property of its immediate subphrases except the meanings of these subphrases. … It implies that, in any phrase, one can replace an occurrence of a subphrase by another phrase with the same meaning, without changing the meaning of the enclosing phrase."*

"바꿔 끼워도 전체 뜻이 바뀌지 않는다"를 문맥마다 따로 보이는 대신, `Validity.lean`은
단언의 생성자 각각이 `Equivalent`를 보존한다는 합동(congruence) 보조정리로 한 번에 준다.
부정의 합동이 심화 A1.8 연습이다.

```anchor stmtNotCongr (module := Reynolds.Answers.Ch01.Validity)
@[exercise "심화 A1.8" 1]
theorem Equivalent.not_congr {p p' : Assert V} (h : Equivalent p p') :
    Equivalent (.not p) (.not p')
```

이항 논리 연산의 합동(`bin_congr`)도 같은 패턴(`Assert.eval`을 펼치고 가정을 꽂는다)의
완성본이다. 비교식의 두 자리는 단언이 아니라 정수 식이므로, 합동의 가정도 다른 모양을
받는다 — 합성성이 단언 생성자에만 있는 특별한 성질이 아니라 정수 식과 단언을 넘나드는
경계에서도 같은 모양으로 성립한다는 뜻이다.

```anchor Equivalent.cmp_congr (module := Reynolds.Answers.Ch01.Validity)
theorem Equivalent.cmp_congr {c : Cmp} {e₀ e₀' e₁ e₁' : IntExp V}
    (h₀ : ∀ σ, e₀.eval σ = e₀'.eval σ) (h₁ : ∀ σ, e₁.eval σ = e₁'.eval σ) :
    Equivalent (.cmp c e₀ e₁) (.cmp c e₀' e₁') := by
  intro σ; simp [Assert.eval, h₀ σ, h₁ σ]
```

양화의 합동은 결합 변수 `v`를 그대로 두고 본문만 바꾼다.

```anchor Equivalent.quant_congr (module := Reynolds.Answers.Ch01.Validity)
theorem Equivalent.quant_congr {qt : Quant} (v : V) {p p' : Assert V}
    (h : Equivalent p p') : Equivalent (.quant qt v p) (.quant qt v p') := by
  intro σ
  have key : ∀ n : Int, (p.eval (σ[v := n]) ↔ p'.eval (σ[v := n])) := fun n => h _
  cases qt
  · simpa [Assert.eval] using forall_congr' key
  · simpa [Assert.eval] using exists_congr key
```

Reynolds가 §1.4 p.21에서 이름 바꾸기 정리(명제 1.5) 바로 뒤에 다시 꺼내는 문장은 결합
변수 자체를 바꾸는 경우까지 포함한다.

> *"From this proposition and the compositional nature of our semantics, it is clear that, in any context, one can replace an occurrence of a subphrase of the form ∀v. q by ∀vnew. (q/v → vnew), without changing the meaning of the context."*

[이름 바꾸기 정리](--tag--ch01-substitution)의 `renaming_assert`는 "그 양화 구 하나"의
뜻이 같다는 것만 준다. "어느 문맥에 넣어도" 쪽은 생성자별 합동(`not_congr`, `bin_congr`,
`quant_congr`)을 문맥의 모양에 대한 귀납으로 이어서 얻는다. α-변환이 임의의 문맥에서
적용된다는 것은 이름 바꾸기 정리와 합동을 조합한 결과다.

# 선택 심화: 치환 모나드와 α-동치
%%%
tag := "ch01-term-monad"
%%%

[범주론 렌즈](--tag--ch01-substitution-monad-lens)에서 짚었듯, §1.4의 치환 `p /ₛ δ`는
변수 타입을 바꾸지 않는 특수한 경우다. `Depth/TermMonad.lean`은 변수 잎을 다른 변수
타입의 식으로 바꿔 끼우는 일반형 `bind`를 둔다.

```anchor IntExp.bind (module := Reynolds.Answers.Ch01.Depth.TermMonad)
def IntExp.bind {V W : Type u} (e : IntExp V) (f : V → IntExp W) : IntExp W :=
  match e with
  | .num n        => .num n
  | .var v        => f v
  | .neg e        => .neg (e.bind f)
  | .bin op e₀ e₁ => .bin op (e₀.bind f) (e₁.bind f)
```

좌단위·우단위 법칙 둘이 등식으로 성립한다. 좌단위는 정의를 펼치면 바로 나온다.

```anchor IntExp.bind_pure_left (module := Reynolds.Answers.Ch01.Depth.TermMonad)
/-- 좌단위. `pure v >>= f = f v`. `IntExp.bind`의 `var` 절이 곧 이 등식이다. -/
theorem IntExp.bind_pure_left {V W : Type u} (v : V) (f : V → IntExp W) :
    (IntExp.var v).bind f = f v := rfl
```

우단위(`IntExp.bind_pure_right : e.bind IntExp.var = e`)는 Reynolds가 명제 1.2(b)에서
"`c_var`가 항등 치환으로 작동한다"고 쓴 §1의 결과(`subst_pure_right`)를 변수 타입을
바꾸는 쪽으로 일반화한 것이다. 증명은 `e`에 대한 구조적 귀납법으로, `bind_pure_left`와
같은 모양의 케이스 분석이다.

연습 1.7(a)가 묻는 치환 두 번의 합성은 모나드의 결합법칙이다. `δ`로 옮기고 다시 `δ'`로
옮기는 것을 한 번에 하는 합친 치환이 Kleisli 합성(`Subst.kleisli`, `>=>ₑ`)이다.

```anchor Subst.kleisli (module := Reynolds.Answers.Ch01.Depth.TermMonad)
def Subst.kleisli {V W X : Type u} (δ : V → IntExp W) (δ' : W → IntExp X) : V → IntExp X :=
  fun v => (δ v).bind δ'

@[inherit_doc Subst.kleisli] scoped infixr:90 " >=>ₑ " => Subst.kleisli
```

결합자가 없는 정수 식에서는 이 결합법칙이 등식으로 성립한다. "심화 A2.1"(§1, 변수
타입을 고정한 판)을 먼저 풀어 본 사람은 `var` 케이스가 `rfl`인 이유가 여기서도
그대로임을 알아챈다 — 심화 A2.2는 그 결과를 쓰지 않고 독립적으로 다시 증명한다.

```anchor stmtBindAssoc (module := Reynolds.Answers.Ch01.Depth.TermMonad)
@[exercise "심화 A2.2" 2]
theorem IntExp.bind_assoc {V W X : Type u} (e : IntExp V) (δ : V → IntExp W) (δ' : W → IntExp X) :
    (e.bind δ).bind δ' = e.bind (δ >=>ₑ δ')
```

`∀v`가 있는 단언에서는 사정이 다르다. 포획을 피하려고 고르는 새 결합 변수가 치환을
어떻게 나누느냐에 따라 달라질 수 있어서, 결합법칙이 *구문의 등식으로는* 깨진다.
심화 A2.3은 그 구체적인 반례를 만드는 연습이다.

```anchor stmtSubstAssocAssertNotEq (module := Reynolds.Answers.Ch01.Depth.TermMonad)
@[exercise "심화 A2.3" 2]
theorem subst_assoc_assert_not_eq :
    ∃ (p : Assert String) (δ δ' : Subst String),
      (p /ₛ δ) /ₛ δ' ≠ p /ₛ (fun w => (δ w) /ₑ δ')
```

구문으로는 달라도 *뜻은 같다* — 결합 변수 이름의 차이만 있을 뿐이다. 그 이름 차이를
무시하는 관계가 α-동치(`=α`)다. `cmp` 절은 정수 식 쪽에 결합자가 없으므로 두 비교식이
그대로 같아야 한다고 요구하고, `quant` 절만 결합 변수 이름 차이를 허용한다.

```anchor Assert.AlphaEq (module := Reynolds.Answers.Ch01.Depth.TermMonad)
inductive Assert.AlphaEq [DecidableEq V] [HasFresh V] : Assert V → Assert V → Prop
  | tru : Assert.AlphaEq .tru .tru
  | fls : Assert.AlphaEq .fls .fls
  | cmp (c : Cmp) (e₀ e₁ : IntExp V) : Assert.AlphaEq (.cmp c e₀ e₁) (.cmp c e₀ e₁)
  | not {p p' : Assert V} : Assert.AlphaEq p p' → Assert.AlphaEq (.not p) (.not p')
  | bin (op : LogOp) {p p' q q' : Assert V} :
      Assert.AlphaEq p p' → Assert.AlphaEq q q' → Assert.AlphaEq (.bin op p q) (.bin op p' q')
  | quant (qt : Quant) (v v' : V) (p p' : Assert V) (w : V)
      (hw : w ∉ p.fv.erase v ∪ p'.fv.erase v') :
      Assert.AlphaEq (p /[v := .var w]) (p' /[v' := .var w]) →
      Assert.AlphaEq (.quant qt v p) (.quant qt v' p')
```

심화 A2.4는 α-동치가 뜻을 보존한다는 것 — 명제 1.5(이름 바꾸기 정리)의 구문적 일반화다.
명제 1.5는 결합 변수 하나를 그 자리에서 새 이름으로 바꾼 결과의 뜻이 같다고 말하고,
`=α`는 그 바꿔치기를 구문의 어느 깊이에서든 몇 번이든 허용한다. 명제 1.5 자체
(`renaming_assert`)는 그 증명이 치환 정리(`Prop 1.3-assert`, 채점)를 직접 쓰므로,
연습 독립성을 지키려고 가설 `hrename`으로 받는다 — 실제로 쓸 때는 `renaming_assert`를
그 자리에 넘긴다.

```anchor stmtAlphaEqSound (module := Reynolds.Answers.Ch01.Depth.TermMonad)
@[exercise "심화 A2.4" 3]
theorem Assert.AlphaEq.sound [HasFresh V]
    (hrename : ∀ (qt : Quant) (v₀ vnew : V) (body : Assert V), vnew ∉ body.fv.erase v₀ →
      ∀ σ : State V,
        ⟦Assert.quant qt vnew (body /[v₀ := IntExp.var vnew] )⟧ₐ σ ↔ ⟦Assert.quant qt v₀ body⟧ₐ σ)
    {p p' : Assert V} (h : p =α p') :
    Equivalent p p'
```

2장의 리프팅 모나드 `Σ⊥ = Flat (State V)`(`Ch02/Semantics.lean`의 `SigmaBot`)도 같은
모양의 구조를 갖는다. `pure`에 해당하는 것이 `Flat.some`, Kleisli 확장에 해당하는 것이
`liftBot`이고, `liftBot_eq_bind`가 그 `liftBot`이 정확히 `Flat.bind`와 같음을 보여 준다.
`IntExp`의 `bind`/`Subst.kleisli`와 `Σ⊥`의 `Flat.bind`/`liftBot`은 "항 모나드"와
"리프팅 모나드"라는 서로 다른 계산 효과가 공유하는 같은 뼈대다.

# 더 읽을거리
%%%
tag := "ch01-further"
file := "ch01-further"
number := false
%%%

* *일치 정리와 치환 정리* — 이름을 다루는 모든 언어에서 같은 짝으로 나온다.
  CSlib의 `Cslib/Languages/LambdaCalculus/`가 λ-계산법에서 같은 일을 한다.
* *초기 대수 의미론(initial algebra semantics)* — Reynolds가 §1.1 본문 괄호 속(p.5,
  각주가 아니다)에서 "다중 정렬 초기 대수"라고 부르는 관점이다. `Depth/Algebra.lean`은
  고정된 변수 타입의 정수 식 정렬부터 시작해, 목표 대수마다 유일한 준동형이 생긴다는
  명제를 증명한다.
* *치환은 모나드의 bind 다* — `Depth/TermMonad.lean`. 연습 1.7 이 실은
  모나드 결합법칙이라는 것을 보인다.
* *2장으로* — 1장의 의미 함수가 전함수였던 것은 술어 논리에 비종료가 없었기 때문이다.
  `while`이 들어오면 의미 방정식이 뜻을 유일하게 정하지 못한다. 그 지점이 도메인 이론이
  태어난 자리다.
