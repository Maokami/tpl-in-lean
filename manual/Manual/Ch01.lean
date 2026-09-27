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
술어 논리의 작은 추론 체계. Reynolds §1.3이 예시로 드는 규칙들이다.

완전한 체계가 아니고 그럴 의도도 없다. 추론 규칙과 건전성이 무엇인지 보이는 데 필요한
최소한만 담았다.
-/
inductive Proof : Assert V → Prop where
  /-- 공리꼴: `e = e`. -/
  | eqRefl (e : IntExp V) : Proof (.cmp .eq e e)
  /-- 한 전제 규칙: `e₀ = e₁`로부터 `e₁ = e₀`. -/
  | eqSymm {e₀ e₁ : IntExp V} : Proof (.cmp .eq e₀ e₁) → Proof (.cmp .eq e₁ e₀)
  /-- 두 전제 규칙 — 전건 긍정(modus ponens). -/
  | mp {p q : Assert V} : Proof p → Proof (.bin .imp p q) → Proof q
  /-- 두 전제 규칙 — 연언 도입. -/
  | andIntro {p q : Assert V} : Proof p → Proof q → Proof (.bin .and p q)
  /--
  보편 일반화(∀-도입).

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

```anchor genVsImp (module := Reynolds.Answers.Ch01.Validity)
/-- 규칙 쪽. `p`가 타당하면 `∀v. p`도 타당하다. -/
@[exercise "§1.3 gen-sound" 1]
theorem valid_forall_of_valid (v : V) {p : Assert V} (h : Valid p) :
    Valid (.quant .all v p) := fun _ _ => h _

/--
함의 쪽. `x > 0 ⇒ ∀x. x > 0`은 타당하지 않다.

Reynolds의 반례를 그대로 쓴다. `x ↦ 3` 인 상태에서 왼쪽은 참이고,
오른쪽은 `x`에 0 을 넣으면 거짓이다.

같은 재료로 만든 규칙(위)과 함의(여기)의 판정이 갈린다.
-/
@[exercise "§1.3 gen-not-imp" 2]
theorem not_valid_imp_forall :
    ¬ Valid (.bin .imp (.cmp .gt (.var "x") (.num 0))
                       (.quant .all "x" (.cmp .gt (.var "x") (.num 0))) : Assert String) := by
  intro h
  -- x ↦ 3 인 상태를 잡으면 왼쪽은 참이다.
  have h3 := h (State.const 3)
  simp only [Assert.eval, LogOp.denote, Cmp.denote, IntExp.eval, State.const] at h3
  -- 따라서 오른쪽이 성립해야 하는데, n = 0 을 넣으면 거짓이다.
  have := h3 (by decide) 0
  simp at this
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

1장에는 채점되는 연습이 36개 있다. 책 연습문제와 본문 명제가 섞여 있고,
아래는 [읽는 순서](--tag--ch01-order)와 같은 차례로 늘어놓은 것이다.

* `Validity.lean` — §1.3 건전성과 규칙. *3개*
* `FreeVars.lean`, `Substitution.lean` — 본문 명제 1.1 ~ 1.3. *5개*
* `Realizations/Constructors.lean`, `Ex.lean` — 책 연습 1.1 ~ 1.4. *12개*
* `Ex/Summation.lean`·`Ex/Summation/` — 책 연습 1.5 · 1.6. *7개*
* `Design.lean` — 정의 선택과 정리의 성립. *3개*
* `Depth/` — 심화 트랙. *6개*

본문 명제를 건너뛰면 책 연습에서 쓸 재료가 없다.

명제 1.1(정수 식 판, `coincidence_intExp`)과 명제 1.5는 파일에 있지만
채점 대상이 아니다. 방향이 서로 반대다 — 정수 식 판은 명제 1.1(단언 판)과 명제 1.3
(치환 정리)이 그 결과를 직접 쓰므로 완성된 채로 주고, 명제 1.5는
거꾸로 치환 정리 자체를 쓴다. 채점기는 "이 증명이 `sorry`에 기대는가"만 보고
그것이 자기 `sorry` 인지 앞 연습에서 물려받은 것인지 구별하지 못한다. 그래서 비우는 연습들은
서로 의존하지 않도록 골라 두었다.

심화 트랙은 책을 따라가는 데 필요하지 않다. 건너뛰어도 1장은 완결된다.

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

# 선택 심화: 같은 초기성을 Mathlib으로 읽기
%%%
tag := "ch01-category-bridge"
%%%

앞 절의 `∃!`를 이해했다면, 범주론에서 말하는 초기 대상도 읽을 수 있다.
범주(category)는 대상과 대상 사이의 사상, 그리고 사상을 이어 붙이는 합성을 갖춘다.
여기서 대상은 `LogicAlg`, 사상은 연산을 보존하는 함수 쌍이다.
앞 절에서는 사상의 출발점이 늘 구문이었지만, 이제 출발점도 임의의 대수로 둔다.

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

여기서는 변수 타입과 두 반송자를 모두 같은 `Type u`에 둔다. 따라서 앞 절에서
서로 다른 우주의 목표 대수도 허용했던 `LogicAlg.initial`을 이 범주의 대상들에
한정해서 사용한다. `syntaxAlg V`는 정수 식과 단언 자체를 반송자로 갖는 대수다.

```anchor LogicAlg.syntaxIsInitial (module := Reynolds.Answers.Ch01.Depth.CategoryBridge)
/-- 기존 `LogicAlg.initial`을 적용하면 구문 대수가 이 범주의 초기 대상이 된다. -/
noncomputable def syntaxIsInitial (V : Type u) : IsInitial (syntaxAlg V) :=
  isInitialOfUniqueHom (fun L ↦ L.initial)
```

`IsInitial (syntaxAlg V)`는 각 목표로 가는 사상을 고르는 자료와 그 유일성 증명을
포함한다. 그 자료가 주어지면 `h.to L`로 사상을 얻고, `h.hom_ext`로 두 사상의
등식을 얻는다. 다음 연습은 이 두 API를 앞 절의 함수 쌍 언어로 옮기는 문제다.
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
구문의 초기성, 치환의 법칙, 일반 함자의 대수에 대한 Lambek 정리는 별도로 다룬다.
본문의 1장 학습은 이 파일 없이도 이어갈 수 있다.

# 더 읽을거리
%%%
tag := "ch01-further"
file := "ch01-further"
number := false
%%%

* *일치 정리와 치환 정리* — 이름을 다루는 모든 언어에서 같은 짝으로 나온다.
  CSlib의 `Cslib/Languages/LambdaCalculus/`가 λ-계산법에서 같은 일을 한다.
* *초기 대수 의미론(initial algebra semantics)* — Reynolds가 §1.1 각주에서
  "다중 정렬 초기 대수"라고 부르는 관점이다. `Depth/Algebra.lean`은 고정된 변수 타입의
  정수 식 정렬부터 시작해, 목표 대수마다 유일한 준동형이 생긴다는 명제를 증명한다.
* *치환은 모나드의 bind 다* — `Depth/TermMonad.lean`. 연습 1.7 이 실은
  모나드 결합법칙이라는 것을 보인다.
* *2장으로* — 1장의 의미 함수가 전함수였던 것은 술어 논리에 비종료가 없었기 때문이다.
  `while`이 들어오면 의미 방정식이 뜻을 유일하게 정하지 못한다. 그 지점이 도메인 이론이
  태어난 자리다.
