/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Answers.Ch01.FreeVars
-- `#eval` 과 `#guard` 는 컴파일 시점에 계산하므로 meta 문맥이다.
public meta import Reynolds.Answers.Ch01.Syntax
public meta import Reynolds.Answers.Ch01.FreeVars
public meta import Mathlib.Data.Finset.Defs

/-!
# 1장을 읽기 전에 — 술어 논리와 메타/객체 구분

> **이 파일을 가장 먼저 읽어라.** 선택 사항이 아니다.
> (예제로 `Assert` 를 쓰기 때문에 import 순서는 뒤지만, **읽는 순서로는 첫 번째**다.)

Reynolds 는 §1 을 이렇게 연다:

> *"predicate logic is close enough to conventional mathematical notation that the reader's
> intuitive understanding is likely to be accurate"*

즉 **술어 논리를 안다고 가정하고 넘어간다.** 대부분 맞는 가정이다 — `∀`, `∃`, `∧`, `¬` 를
못 읽는 개발자는 없다. 그런데 그가 넘어간 것 중에 **이 책 전체를 좌우하는 구분** 이 하나 있다:

**메타언어(metalanguage)와 객체언어(object language)의 구분.**

이 파일은 그 구분을 다룬다. 그리고 우리에게는 운이 좋은 일이 하나 있다 —
**Lean 에서는 그 구분이 규율이 아니라 타입이다.** 종이에서는 헷갈릴 수 있는 것이
여기서는 타입 오류로 막힌다.

## 다루는 것
1. 술어 논리가 무엇인가 (아주 짧게)
2. ★ 메타언어와 객체언어
3. Lean 에 이미 `∀` 가 있는데 왜 `Assert` 를 또 만드나
4. 상태와 만족 — 진리값이 왜 상태에 의존하는가
5. 자유 변수와 속박 변수
6. 타당 · 충족 가능 · 불충족

## 더 읽을 것
Lean 자체가 처음이라면 [Functional Programming in Lean] 과
[Theorem Proving in Lean] 이 표준 입문서다. 이 파일은 그것들을 대신하지 않는다.
-/

-- 이 파일은 `#eval` / `#guard` 로 **직접 돌려 보는 것**이 목적이다.
-- Mathlib 린터는 라이브러리 코드에서 `#`-커맨드를 막지만 여기서는 그게 요점이다.
set_option linter.hashCommand false

@[expose] public section

namespace Reynolds.Answers.Ch01.Background

open Reynolds Reynolds.Answers.Ch01

/-! ## 1. 술어 논리란

**명제 논리**는 `∧ ∨ ¬ ⇒` 로 명제를 조합한다. 여기에 두 가지를 더한 것이 **술어 논리**다:

* **변수와 술어** — `x > 0` 처럼 값에 대해 무언가를 말하는 것
* **양화사** — `∀v. …`("모든 v 에 대해"), `∃v. …`("어떤 v 가 있어서")

Reynolds 가 다루는 것은 **정수 위의** 술어 논리다. 변수는 정수 값을 갖고,
술어는 `=  ≠  <  ≤  >  ≥` 여섯 개뿐이다. 함수 기호는 `+  -  ×  ÷  rem`.

일반 논리 교과서와 용어가 다르다는 점에 주의할 것 — Reynolds 는 프로그래밍 언어의
용어를 쓴다:

| 논리학자 | Reynolds | 우리 코드 |
|---|---|---|
| 항(term) | 정수 식(integer expression) | `IntExp` |
| 정형식(well-formed formula) | 단언(assertion) | `Assert` |
| 배정(assignment) | 상태(state) | `State` |
| 모델(model) | 의미 함수 | `Assert.eval` |

## 2. ★ 메타언어와 객체언어

같은 문장을 **두 가지 방식으로** 쓸 수 있다. 이 둘은 완전히 다른 것이다.

**(가) 메타언어로 — 우리가 *주장*한다**

```lean
∀ n : Int, n > 0 → n ≥ 1
```
이건 Lean 의 명제(`Prop`)다. 우리가 참이라고 **주장**하고 증명할 수 있는 것이다.

**(나) 객체언어로 — 우리가 *다루는 데이터*다**

```lean
Assert.bin .imp (.cmp .gt (.var "n") (.num 0)) (.cmp .ge (.var "n") (.num 1))
```
이건 `Assert String` 타입의 **값**이다. 문자열이나 리스트처럼 만들고, 뜯어보고,
함수에 넘길 수 있는 데이터다.

Reynolds 는 이 구분을 **글꼴**로 표시한다 — 메타변수는 이탤릭과 그리스 문자,
객체 변수는 산세리프. 종이에서는 그게 최선이다.

**Lean 에서는 타입이 강제한다.** `Prop` 과 `Assert V` 는 다른 타입이고,
섞어 쓰면 컴파일이 안 된다. 헷갈릴 수가 없다. -/

/-- 예제용 객체 변수 `x`. -/
def x : IntExp String := .var "x"

/-- 예제용 객체 변수 `y`. -/
def y : IntExp String := .var "y"

/-- 예제용 상태 — `x ↦ 3`, `y ↦ 5`, 나머지는 전부 0. -/
def σ₀ : State String := fun v => if v = "x" then 3 else if v = "y" then 5 else 0

/-- 객체언어의 `x > 0`. 이건 **데이터**다. -/
def xPos : Assert String := .cmp .gt x (.num 0)

-- 데이터이므로 출력할 수 있다.
#eval xPos

-- 데이터이므로 자유 변수를 **계산**할 수 있다.
#guard xPos.fv == ({"x"} : Finset String)

/--
`⟦-⟧ₐ` 가 두 세계를 잇는 다리다: 객체언어의 값 + 상태 → 메타언어의 명제.

**증명이 `decide` 가 아니라 `simp` 인 것에 주목하라.** `⟦p⟧ₐ σ` 는 `Prop` 이고
`Prop` 은 일반적으로 결정 가능하지 않다 (양화사가 있으면 ℤ 전체를 훑어야 한다).
`Decidable` 인스턴스가 없으니 `decide` 가 실패한다.

반면 정수 식은 `⟦e⟧ₑ σ : Int` 라서 계산된다 — `#eval` 도 `decide` 도 된다.
**쓸 수 있는 태틱이 다르다는 것 자체가 `Prop` / 계산 가능성의 경계다.**
-/
example : ⟦xPos⟧ₐ σ₀ := by
  simp [xPos, Assert.eval, Cmp.denote, IntExp.eval, x, σ₀]

/-- 정수 식은 계산된다. 이쪽은 `decide` 가 통한다. -/
example : ⟦x⟧ₑ σ₀ = 3 := by simp [x, σ₀, IntExp.eval]

/-- 같은 내용을 메타언어로 직접 쓰면 이렇다. 상태가 없으므로 값을 박아 넣어야 한다. -/
example : (3 : Int) > 0 := by decide

/-! ## 3. Lean 에 `∀` 가 있는데 왜 `Assert` 를 또 만드나

스터디에서 반드시 나오는 질문이다. 답은 한 문장이다:

> **우리는 논리를 *쓰는* 것이 아니라, 논리에 *대해* 이야기한다.**

컴파일러를 만들어 본 사람에게는 익숙한 구분이다.
파이썬 프로그램을 *실행하는* 것과, 파이썬 프로그램을 *파싱해서 변수를 세는* 것은 다른 일이다.
후자를 하려면 프로그램이 **데이터**여야 한다.

우리가 1장에서 하려는 일이 전부 후자다:

* `FV(p)` — 자유 변수를 **센다**
* `p / v ↦ e` — 구를 **바꿔치기한다**
* "이 추론 규칙이 건전한가" — 규칙을 **검사한다**

Lean 의 `Prop` 으로는 이 중 아무것도 할 수 없다. -/

-- 객체언어: 자유 변수를 계산할 수 있다.
#guard (Assert.quant .all "x" (.cmp .gt x y)).fv == ({"y"} : Finset String)

/-
메타언어: 불가능하다. 아래 같은 함수는 **쓸 방법이 없다.**

    def fvOfProp : Prop → Finset String := ???

`Prop` 의 값은 들여다볼 수 없다. `∀ n : Int, n > 0` 이라는 명제로부터
"여기 변수가 몇 개인가"를 물을 방법이 Lean 에는 없다 —
그리고 그게 정상이다. `Prop` 은 **말하기 위한 것**이지 **다루기 위한 것**이 아니다.

그래서 다루고 싶으면 직접 만들어야 한다. 그것이 `Assert` 다.
-/

/-! ## 4. 상태와 만족 — 진리값은 왜 상태에 의존하는가

`x > 0` 은 **참도 거짓도 아니다.** `x` 가 무엇인지 모르기 때문이다.

이것이 `⟦-⟧ₐ` 의 타입이 `Assert V → State V → Prop` 인 이유다.
단언 하나만으로는 진리값이 안 나오고, **상태가 있어야** 정해진다.

Reynolds 의 용어(§1.3): `⟦p⟧ₐ σ` 가 성립할 때
"`p` 가 `σ` 에서 참이다", "`σ` 가 `p` 를 만족한다", "`p` 가 `σ` 를 기술한다"고 말한다.

3장에서 프로그램 명세를 쓸 때 이 구조가 그대로 쓰인다 —
`{P} c {Q}` 의 `P` 와 `Q` 가 바로 "상태에 대한 단언"이다. -/

/-- `x ↦ 3` 인 상태에서는 `x > 0` 이 참이다. -/
example : ⟦xPos⟧ₐ σ₀ := by
  simp [xPos, Assert.eval, Cmp.denote, IntExp.eval, x, σ₀]

/-- 모든 변수가 `-1` 인 상태에서는 거짓이다. **같은 단언, 다른 상태, 다른 진리값.** -/
example : ¬ ⟦xPos⟧ₐ (State.const (-1)) := by
  simp [xPos, Assert.eval, Cmp.denote, IntExp.eval, x, State.const]

/-! ## 5. 자유 변수와 속박 변수

`∀x. x > y` 에서 `x` 와 `y` 의 지위는 완전히 다르다.

* `x` 는 **속박(bound)** 되어 있다 — `∀x` 가 잡아먹었다.
  바깥에서 `x` 가 무엇인지 알려 줄 필요가 없고, **알려 줘도 영향이 없다.**
* `y` 는 **자유(free)** 다 — 바깥에서 정해 줘야 뜻이 정해진다.

그래서 `FV(∀v. p) = FV(p) \ {v}` 다.

**이름은 중요하지 않다.** `∀x. x > y` 와 `∀z. z > y` 는 같은 뜻이다.
속박 변수의 이름을 바꾸는 것을 α-변환(alpha conversion)이라 하고,
그것이 뜻을 보존한다는 것이 §1.4 의 명제 1.5 다. -/

/-- `∀x. x > y` — `x` 는 속박, `y` 는 자유. -/
def allXGtY : Assert String := .quant .all "x" (.cmp .gt x y)

#guard allXGtY.fv == ({"y"} : Finset String)

/--
속박 변수의 값을 바꿔도 뜻이 안 변한다 — 일치 정리(명제 1.1)의 직접적 결과다.
`x` 는 `FV` 에 없으므로 `x` 자리를 아무 값으로 덮어도 상관없다.
-/
example (k : Int) : ⟦allXGtY⟧ₐ σ₀ ↔ ⟦allXGtY⟧ₐ (σ₀["x" := k]) := by
  refine coincidence_assert _ σ₀ _ ?_
  intro w hw
  simp [allXGtY, Assert.fv, IntExp.fv, x, y] at hw
  simp [hw]

/-! ## 6. 타당 · 충족 가능 · 불충족

상태마다 진리값이 다르므로, "참이다"에도 세 단계가 있다.

| | 뜻 | 예 |
|---|---|---|
| **타당(valid)** | **모든** 상태에서 참 | `x = x` |
| **충족 가능(satisfiable)** | **어떤** 상태에서 참 | `x > 0` |
| **불충족(unsatisfiable)** | 어떤 상태에서도 거짓 | `x ≠ x` |

§1.3 에서 `Valid` 라는 이름으로 다시 만난다. 그리고 거기서 중요한 함정이 나온다:

**증명의 각 단계는 타당해야 한다.** `x > 0` 은 증명 단계가 될 수 없다 —
`x ↦ 0` 인 상태에서 거짓이기 때문이다. Reynolds 가 직접 경고하는 대목이다. -/

/-- `x = x` 는 타당하다 — 어떤 상태에서도 참. -/
example : ∀ σ : State String, ⟦Assert.cmp .eq x x⟧ₐ σ := by
  intro σ; simp [Assert.eval, Cmp.denote]

/-- `x > 0` 은 타당하지 않다. 반례는 모든 변수가 0인 상태. -/
example : ¬ (∀ σ : State String, ⟦xPos⟧ₐ σ) := by
  intro h
  have := h (State.const 0)
  simp [xPos, Assert.eval, Cmp.denote, IntExp.eval, x, State.const] at this

/-- 그래도 충족 가능하다 — `σ₀` 에서 참이다. -/
example : ∃ σ : State String, ⟦xPos⟧ₐ σ :=
  ⟨σ₀, by simp [xPos, Assert.eval, Cmp.denote, IntExp.eval, x, σ₀]⟩

/-- `x ≠ x` 는 불충족이다. -/
example : ∀ σ : State String, ¬ ⟦Assert.cmp .ne x x⟧ₐ σ := by
  intro σ; simp [Assert.eval, Cmp.denote]

/-! ## 정리

기억할 것은 하나다.

> **`Assert V` 는 데이터이고, `Prop` 은 주장이다. `⟦-⟧ₐ` 가 둘을 잇는다.**

이 구분이 흐려지면 1장의 나머지가 전부 흐려진다. 반대로 이것만 붙잡으면
자유 변수·치환·건전성이 전부 자연스럽게 읽힌다.

Reynolds 가 §1.2 끝에서 남기는 경고를 그대로 옮긴다:

> *"It is important to distinguish between the language in which semantic equations or other
> parts of a definition are written, called the **metalanguage**, and the language being defined,
> called the **object language**."*
-/

end Reynolds.Answers.Ch01.Background
