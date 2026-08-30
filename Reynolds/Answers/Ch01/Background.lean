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

이 파일은 뒤에서 정의한 `Assert` 를 예제로 쓰기 때문에 import 순서에서는 늦지만,
학습 순서에서는 1장의 첫 파일이다.

Reynolds 는 §1 을 이렇게 연다.

> *"predicate logic is close enough to conventional mathematical notation that the reader's
> intuitive understanding is likely to be accurate"*

이 기호들의 일상적인 뜻은 익숙해도, 같은 `∀`가 지금 정의하는 언어의 기호인지 그 언어를
설명하는 수학의 기호인지는 따로 구분해야 한다. 뒤의 장들이 계속 기대는
메타언어(metalanguage)와 객체언어(object language)의 구분이 여기서 생긴다.

Reynolds 는 두 층을 글꼴과 문맥으로 구분한다. Lean 에서는 객체 구문을 `Assert V`라는
데이터 타입으로 만들기 때문에, 메타언어의 `Prop`과 잘못 섞으면 타입 검사에서 드러난다.

## 다루는 것
1. 술어 논리 한 문단 요약
2. 메타언어와 객체언어
3. Lean 에 이미 `∀` 가 있는데 왜 `Assert` 를 또 만드나
4. 상태와 만족
5. 자유 변수와 속박 변수
6. 타당 · 충족 가능 · 불충족

## 더 읽을 것
Lean 자체가 처음이라면 [Functional Programming in Lean] 과
[Theorem Proving in Lean] 이 표준 입문서다. 이 파일은 그것들을 대신하지 않는다.
-/

-- 이 파일은 `#eval` / `#guard` 로 **직접 돌려 보는 것**이 목적이다.
-- Mathlib 린터는 라이브러리 코드에서 `#`-커맨드를 막는데, 이 파일에서는 그것이 내용이다.
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
| 구조(structure) | 정수 영역과 연산·관계 기호의 해석 | `Int`, `IntOp.denote`, `Cmp.denote` |
| 만족(satisfaction) | 상태에서 단언이 참임 | `Assert.eval p σ` |

구조가 주어진 문장이나 이론을 만족할 때 그 구조를 모델(model)이라고 부른다. 이 저장소는
정수 구조를 처음부터 고정하므로, 코드에서는 별도의 `Model` 타입을 만들지 않는다.

## 2. 메타언어와 객체언어

같은 문장을 두 가지 방식으로 적을 수 있다.

**(가) 메타언어로 — 우리가 주장한다**

```lean
∀ n : Int, n > 0 → n ≥ 1
```
Lean 의 명제(`Prop`)다. 참이라고 주장하고 증명할 수 있다.

**(나) 객체언어로 — 우리가 다루는 데이터다**

```lean
Assert.bin .imp (.cmp .gt (.var "n") (.num 0)) (.cmp .ge (.var "n") (.num 1))
```
`Assert String` 타입의 값이다. 문자열이나 리스트처럼 만들고, 뜯어보고, 함수에 넘길 수 있다.

Reynolds 는 이 구분을 글꼴로 표시한다. 메타변수는 이탤릭과 그리스 문자, 객체 변수는 산세리프.
우리는 타입으로 구분한다. `Prop` 과 `Assert V` 를 섞으면 컴파일이 실패한다. -/

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

`Prop`이라고 해서 항상 계산할 수 없는 것은 아니다. 이 파일 아래쪽의 `3 > 0`처럼
결정 절차가 주어진 명제에는 `decide`를 쓸 수 있다. 여기서는 의미 정의를 풀어 주는 `simp`를
쓴다. 구분해야 할 것은 개별 명제의 결정 가능성과 언어 전체를 받는 판정기다. 곱셈과 정수
양화를 포함한 모든 `Assert`의 표준 해석을 판정하는 공통 프로그램은 존재하지 않는다.

정수 식은 사정이 다르다. 평가는 실제 `Int`를 돌려주므로, 상태까지 계산 가능한 값으로
주어지면 `#eval`로 실행할 수 있다.
-/
example : ⟦xPos⟧ₐ σ₀ := by
  simp [xPos, Assert.eval, Cmp.denote, IntExp.eval, x, σ₀]

/-- 정수 식은 계산된다. 이쪽은 `decide` 가 통한다. -/
example : ⟦x⟧ₑ σ₀ = 3 := by simp [x, σ₀, IntExp.eval]

/-- 같은 내용을 메타언어로 직접 쓰면 이렇다. 상태가 없으므로 값을 박아 넣어야 한다. -/
example : (3 : Int) > 0 := by decide

/-! ## 3. Lean 에 `∀` 가 있는데 왜 `Assert` 를 또 만드나

여기서는 논리를 사용해 다른 정리를 증명하기보다, 술어 논리의 구문 자체를 입력 데이터로
받아 분석하고 변환한다.

프로그램을 실행하는 일과 프로그램의 구문 트리를 받아 변수 개수를 세는 일은 다르다.
뒤의 작업에는 프로그램을 나타내는 데이터가 필요하다. 1장의 `FV`와 치환은 이 구문 데이터
위에서 동작하고, 의미 함수는 그 데이터를 다시 Lean의 값과 명제로 해석한다.

* `FV(p)` — 자유 변수를 센다
* `p / v ↦ e` — 구의 일부를 바꿔치기한다
* "이 추론 규칙이 건전한가" — 규칙을 검사한다

`Prop` 으로는 셋 다 할 수 없다. -/

-- 객체언어: 자유 변수를 계산할 수 있다.
#guard (Assert.quant .all "x" (.cmp .gt x y)).fv == ({"y"} : Finset String)

/-
메타언어 쪽에는 대응하는 것이 없다. 아래 함수는 채울 방법이 없다.

    def fvOfProp : Prop → Finset String := ???

`∀ n : Int, n > 0` 이라는 명제를 받아 "변수가 몇 개인가" 를 묻는 길이 Lean 에 없다.
`Prop` 은 주장을 담는 타입이지 구문을 담는 타입이 아니기 때문이다.
구문을 다루려면 구문 타입을 직접 만들어야 하고, 그게 `Assert` 다.
-/

/-! ## 4. 상태와 만족

열린 단언 `x > 0`은 정수 구조를 고정해도 상태를 주기 전에는 참·거짓이 정해지지 않는다.

`⟦-⟧ₐ` 의 타입이 `Assert V → State V → Prop` 인 것이 그래서다.
단언만으로는 부족하고 상태가 하나 더 필요하다.

Reynolds 의 용어(§1.3): `⟦p⟧ₐ σ` 가 성립할 때
"`p` 가 `σ` 에서 참이다", "`σ` 가 `p` 를 만족한다", "`p` 가 `σ` 를 기술한다"고 말한다.

3장의 `{P} c {Q}` 에서 `P` 와 `Q` 가 바로 이 "상태에 대한 단언" 이다. -/

/-- `x ↦ 3` 인 상태에서는 `x > 0` 이 참이다. -/
example : ⟦xPos⟧ₐ σ₀ := by
  simp [xPos, Assert.eval, Cmp.denote, IntExp.eval, x, σ₀]

/-- 모든 변수가 `-1` 인 상태에서는 거짓이다. **같은 단언, 다른 상태, 다른 진리값.** -/
example : ¬ ⟦xPos⟧ₐ (State.const (-1)) := by
  simp [xPos, Assert.eval, Cmp.denote, IntExp.eval, x, State.const]

/-! ## 5. 자유 변수와 속박 변수

`∀x. x > y` 에서 `x` 와 `y` 의 지위가 다르다.

`x` 는 `∀x` 에 속박(bound)되어 있다. 바깥에서 `x` 값을 알려 줄 필요가 없고,
알려 줘도 결과가 달라지지 않는다.
`y` 는 자유(free)다. 바깥에서 정해 줘야 뜻이 정해진다.
그래서 `FV(∀v. p) = FV(p) \ {v}` 다.

속박 변수의 이름은 뜻에 영향을 주지 않는다. `∀x. x > y` 와 `∀z. z > y` 는 같은 뜻이다.
이름을 바꾸는 것을 α-변환(alpha conversion)이라 하고, 뜻이 보존된다는 것이 §1.4 의 명제 1.5 다. -/

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

§1.3 에서 `Valid` 라는 이름으로 다시 나온다.
거기서 함께 나오는 규칙 하나를 미리 적어 두면, 증명의 각 단계는 타당해야 한다.
`x > 0` 은 `x ↦ 0` 인 상태에서 거짓이므로 증명 단계가 될 수 없다. -/

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

/-! ## 참고

Reynolds 가 §1.2 끝에 남기는 경고를 그대로 옮겨 둔다.

> *"It is important to distinguish between the language in which semantic equations or other
> parts of a definition are written, called the metalanguage, and the language being defined,
> called the object language."*

이 파일에서 `Assert V` 와 `Prop` 이 그 두 언어이고, `⟦-⟧ₐ` 가 사이를 잇는 함수다.
-/

end Reynolds.Answers.Ch01.Background
