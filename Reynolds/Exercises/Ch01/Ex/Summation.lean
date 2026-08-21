/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Exercises.Ch01.Semantics
public import Reynolds.Meta.Exercise
public import Cslib.Foundations.Data.HasFresh
public import Mathlib.Data.Int.Interval
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
-- `#guard` 는 컴파일 시점에 계산한다 (AGENTS.md §10).
public meta import Reynolds.Prelude
public meta import Reynolds.Exercises.Ch01.Semantics
public meta import Mathlib.Data.Int.Interval
public meta import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# 연습 1.5 · 1.6 — 합 식 (summation expression)

## 1.5 가 요구하는 것

> *"Suppose that, when `v` is a variable and `e₀`, `e₁`, and `e₂` are integer expressions,
> `Σv : e₀ to e₁. e₂` is an integer expression (called a summation expression) with the same
> meaning as the conventional mathematical expression `Σ_{v=e₀}^{e₁} e₂`.
> Describe this extension of predicate logic by giving:
> (a) an abstract-grammar production;
> (b) a semantic equation;
> (c) a definition of the set of free variables and the effect of substitution on a summation
> expression, in such a way that the propositions we have given about binding and substitution
> remain true;
> (d) sound and nontrivial inference rules for the summation expression."*

## 왜 축소판 언어를 따로 만드나

`IntExp` 에 생성자를 하나 더하면 `Semantics.lean` 부터 `Substitution.lean` 까지 모든 정의와
증명이 케이스 하나씩 늘어난다. 본문 연습이 전부 깨진다. 그래서 여기서는 `SExp` 라는 자족적인
축소판을 세우고, 그 안에서 (a)~(d) 를 처음부터 다시 밟는다.

축소판이라 잃는 것은 없다. 1.5 가 묻는 것은 **결합자가 정수 식 층에 들어올 때 무엇이 달라지는가**
하나이고, 그건 `SExp` 에서 그대로 드러난다.

## 무엇이 새로운가

지금까지 결합자는 단언 층에만 있었다. `∀v. p` 의 `v` 는 단언을 묶었고, 정수 식에는 결합이 없어서
`IntExp.fv` 에 `erase` 가 한 번도 나오지 않았다.

`Σv : e₀ to e₁. e₂` 는 **정수 식이면서 변수를 묶는다.** 그리고 묶는 범위가 부분식마다 다르다.

- `e₂` 는 `v` 의 유효 범위(scope) 안이다
- `e₀`, `e₁` 은 밖이다 — 상계와 하계는 합을 시작하기 전에 정해지므로 바깥의 `v` 를 본다

이 비대칭이 (b)(c)(d) 전부에 그대로 나타난다. `fv` 에서 `e₀.fv ∪ e₁.fv` 는 지우지 않고
`e₂.fv` 만 `erase` 하는 것, `subst` 에서 `e₀ e₁` 은 원래 `δ` 로 치환하고 `e₂` 만 갱신된 `δ` 로
치환하는 것 모두 `v`의 유효 범위가 `e₂`에만 미친다는 데서 나온다.

## 채점되는 것과 안 되는 것

(a)~(c) 의 정의는 완성해 두었다. 정의를 비우면 그 아래 정리들이 전부 컴파일되지 않아서
연습 파일이 빌드되지 않는다. 대신 **정의가 옳다는 증거**를 연습으로 냈다.

- (c) 일치 정리가 합 식으로 확장해도 성립하는가 → `coincidence_sExp`
- (d) 건전한 추론 규칙 넷 → `sum_empty`, `sum_single`, `sum_split`, `sum_add`
- 1.6 이름 바꾸기가 깨진다는 것 → `isum_renaming_fails`

정의 자체는 `#guard` 로 확인한다. 값이 예상과 다르면 빌드가 실패하므로 자동 검사이기도 하다.

## 읽는 순서
`Substitution.lean` 을 끝낸 뒤. `Ex.lean` 의 나머지 연습과는 독립이다.

## DSL 을 쓰지 않는 이유
`Notation.lean` 의 `⟪ … ⟫ₑ` 는 `IntExp` 전용이다. `SExp` 용 구문 범주를 새로 열면
두 트리에서 충돌한다 (`Notation.lean` 첫머리 참고). 예제가 몇 개뿐이라 생성자를 그대로 쓴다.
-/

-- 이 파일은 `#guard` 로 정의를 확인한다.
set_option linter.hashCommand false

-- `Finset.Icc` 가 계산되게 하려면 이 한 줄이 필요하다.
--
-- `Finset.Icc a b` 는 `Preorder ℤ` 인스턴스를 찾는데, Mathlib 과 CSlib 을 함께 열어 두면
-- 조건부 완비 순서(`Int.instConditionallyCompleteLinearOrder`)를 거치는 경로가 먼저 잡힌다.
-- 그 인스턴스는 계산 불가능해서 `SExp.eval` 까지 계산 불가능해지고 `#guard` 가 막힌다.
-- 이 파일에서만 그 인스턴스를 후보에서 빼면 격자 경로가 잡히고 전부 계산된다.
-- 어느 경로든 순서 자체는 같으므로 `Finset.Icc_eq_empty` 같은 보조정리는 그대로 쓰인다.
attribute [-instance] Int.instConditionallyCompleteLinearOrder

@[expose] public section

namespace Reynolds.Exercises.Ch01.Summation

open Reynolds Reynolds.Exercises.Ch01 Cslib

universe u

variable {V : Type u} [DecidableEq V]

/-! ## (a) 추상 구문

Reynolds 의 생성 규칙 하나를 더하는 것에 해당한다.

```
⟨intexp⟩ ::= … | Σ⟨var⟩ : ⟨intexp⟩ to ⟨intexp⟩. ⟨intexp⟩
```

`Syntax.lean` 과 같은 이유로 이항 연산자는 `IntOp` 태그로 묶고, 그 타입을 그대로 재사용한다.
-/

/--
합 식이 있는 정수 식. `IntExp` 에 `sum` 절 하나를 더한 것이다.

`sum v e₀ e₁ e₂` 가 `Σv : e₀ to e₁. e₂` 다. 인자 순서는 책의 표기 순서를 따랐다.
-/
inductive SExp (V : Type u) where
  /-- 정수 상수. -/
  | num : Int → SExp V
  /-- 변수. -/
  | var : V → SExp V
  /-- 단항 마이너스. -/
  | neg : SExp V → SExp V
  /-- 이항 연산. -/
  | bin : IntOp → SExp V → SExp V → SExp V
  /-- `Σv : e₀ to e₁. e₂`. `v` 는 `e₂` 안에서만 묶인다. -/
  | sum : V → SExp V → SExp V → SExp V → SExp V
  deriving DecidableEq, Repr

/-! ## (b) 의미 방정식

`Semantics.lean` 의 `⟦e⟧ₑ σ` 를 그대로 잇는다. 새 절 하나만 쓰면 된다.

```
⟦Σv : e₀ to e₁. e₂⟧ σ  =  Σ_{k = ⟦e₀⟧σ}^{⟦e₁⟧σ} ⟦e₂⟧ (σ[v := k])
```

메타 수준의 유한합으로 옮기면 `∑ k ∈ Finset.Icc (⟦e₀⟧σ) (⟦e₁⟧σ), ⟦e₂⟧ (σ[v := k])` 이다.

**`Finset.Icc` 를 고른 이유.** `⟦e₁⟧σ < ⟦e₀⟧σ` 일 때 `Icc` 는 빈 집합이고 합은 0 이 된다.
관례적인 수학 표기에서 위끝이 아래끝보다 작은 합을 0 으로 두는 것과 같다.
경계 조건을 따로 쓸 필요가 없어서 정의가 한 줄로 끝난다.

**상태를 갱신하는 자리.** `⟦e₂⟧` 는 `σ` 가 아니라 `σ[v := k]` 에서 잰다.
§1.2 의 `⟦∀v. p⟧ σ = ∀n. ⟦p⟧ (σ[v := n])` 과 같은 모양이다. 결합자의 의미는 언제나
"묶인 변수에 값을 넣어 가며 본체를 잰다" 이고, 양화사는 그 결과를 `∀` 로, 합은 `Σ` 로 모은다.
-/

/--
합 식이 있는 정수 식의 뜻. Reynolds §1.2 의 의미 함수를 연장한 것이다.

`sum` 절만 새롭다. 나머지 네 절은 `IntExp.eval` 과 글자 그대로 같다.
-/
def SExp.eval : SExp V → State V → Int
  | .num n,        _ => n
  | .var v,        σ => σ v
  | .neg e,        σ => -(e.eval σ)
  | .bin op e₀ e₁, σ => op.denote (e₀.eval σ) (e₁.eval σ)
  | .sum v e₀ e₁ e₂, σ =>
      ∑ k ∈ Finset.Icc (e₀.eval σ) (e₁.eval σ), e₂.eval (σ[v := k])

@[inherit_doc SExp.eval]
scoped notation:max "⟦" e "⟧ₛ" => SExp.eval e

-- `Σi : 1 to 4. i` = 1+2+3+4 = 10.
#guard ⟦(.sum "i" (.num 1) (.num 4) (.var "i") : SExp String)⟧ₛ (State.const 0) == 10

-- 위끝이 아래끝보다 작으면 빈 합, 즉 0.
#guard ⟦(.sum "i" (.num 3) (.num 1) (.var "i") : SExp String)⟧ₛ (State.const 0) == 0

-- 바깥의 `i` 는 본체에서 가려진다. `σ i = 99` 여도 결과가 같다.
#guard ⟦(.sum "i" (.num 1) (.num 4) (.var "i") : SExp String)⟧ₛ (State.const 99) == 10

-- 상계는 바깥에서 잰다. `Σi : 1 to n. i` 에서 `n` 은 자유롭다.
#guard ⟦(.sum "i" (.num 1) (.var "n") (.var "i") : SExp String)⟧ₛ (State.const 3) == 6

/-! ## (c-1) 자유 변수

```
FV(Σv : e₀ to e₁. e₂)  =  FV(e₀) ∪ FV(e₁) ∪ (FV(e₂) \ {v})
```

`e₂` 에서만 `v` 를 지운다. `e₀`, `e₁` 에 나타나는 `v` 는 바깥의 `v` 라서 자유롭다.

`Σi : 1 to i. i` 를 보면 분명해진다. 상계의 `i` 는 합을 시작하기 전에 한 번 읽는 값이고,
본체의 `i` 는 0, 1, … 로 훑는 값이다. 같은 글자지만 다른 변수다.
-/

/-- `FV(e)` — 합 식이 있는 정수 식의 자유 변수. `sum` 절에서 `e₂`만 `erase` 한다. -/
def SExp.fv : SExp V → Finset V
  | .num _         => ∅
  | .var v         => {v}
  | .neg e         => e.fv
  | .bin _ e₀ e₁   => e₀.fv ∪ e₁.fv
  | .sum v e₀ e₁ e₂ => e₀.fv ∪ e₁.fv ∪ (e₂.fv.erase v)

-- `Σi : 1 to i. i` 의 자유 변수는 상계의 `i` 하나다.
#guard (SExp.sum "i" (.num 1) (.var "i") (.var "i") : SExp String).fv == {"i"}

-- 본체에만 나오는 `i` 는 묶인다. `n` 만 남는다.
#guard (SExp.sum "i" (.num 1) (.var "n") (.var "i") : SExp String).fv == {"n"}

-- 본체의 다른 변수는 자유롭다.
#guard (SExp.sum "i" (.num 1) (.num 4) (.bin .mul (.var "a") (.var "i")) : SExp String).fv
        == {"a"}

/-! ## (c-2) 치환

`Substitution.lean` 의 구조를 그대로 옮긴다. 새 결합 변수를 고르는 방식도 같다.

```
(Σv : e₀ to e₁. e₂) /ₛ δ  =  Σ vnew : (e₀ /ₛ δ) to (e₁ /ₛ δ). (e₂ /ₛ δ[v := var vnew])
```

`e₀`, `e₁` 은 원래 `δ` 로 치환한다. `v` 의 유효 범위 밖이기 때문이다.
`e₂` 만 `δ[v := var vnew]` 로 치환한다.

포획(capture)이 일어날 수 있는 곳도 `e₂` 뿐이므로, `newBinder` 가 피해야 할 집합은
`e₂` 의 자유 변수만 보고 정한다. `Assert.subst` 의 `captureSet` 과 같은 정의다.
-/

/-- 치환 사상. `Subst` 와 같은 역할이고 대상 타입만 `SExp` 다. -/
abbrev SSubst (V : Type u) := V → SExp V

/-- `Σv : … . e₂` 를 `δ` 로 치환할 때 새 결합 변수가 피해야 할 변수들. -/
def SExp.captureSet (e₂ : SExp V) (v : V) (δ : SSubst V) : Finset V :=
  (e₂.fv.erase v).biUnion fun w => (δ w).fv

/-- 새 결합 변수. `v` 가 안전하면 그대로 쓰고, 아니면 `HasFresh` 로 새로 뽑는다. -/
def SExp.newBinder [HasFresh V] (e₂ : SExp V) (v : V) (δ : SSubst V) : V :=
  if v ∈ e₂.captureSet v δ then HasFresh.fresh (e₂.captureSet v δ) else v

/--
`e /ₛ δ` — 합 식이 있는 정수 식의 동시 치환.

`sum` 절에서 세 부분식이 서로 다르게 다뤄지는 것이 요점이다.
`e₀`, `e₁` 은 `δ` 로, `e₂` 는 결합 변수를 새로 잡은 `δ` 로 치환한다.
-/
def SExp.subst [HasFresh V] : SExp V → SSubst V → SExp V
  | .num n,        _ => .num n
  | .var v,        δ => δ v
  | .neg e,        δ => .neg (e.subst δ)
  | .bin op e₀ e₁, δ => .bin op (e₀.subst δ) (e₁.subst δ)
  | .sum v e₀ e₁ e₂, δ =>
      .sum (e₂.newBinder v δ) (e₀.subst δ) (e₁.subst δ)
           (e₂.subst (Function.update δ v (.var (e₂.newBinder v δ))))

@[inherit_doc SExp.subst]
scoped infixl:80 " /ₜ " => SExp.subst

/-- `e / v ↦ e'` — 한 변수만 바꾸는 치환. -/
scoped notation:80 e:80 " /[" v ":=" e' "] " => SExp.subst e (Function.update SExp.var v e')

/-! ### 치환이 상계와 본체를 다르게 다루는지 확인

`Σi : 1 to i. i` 에 `i ↦ n` 을 넣는다. 상계의 `i` 는 자유롭게 나타나므로 `n` 이 되고,
본체의 `i` 는 묶여 있으므로 그대로 남아야 한다. -/

#guard ((SExp.sum "i" (.num 1) (.var "i") (.var "i") : SExp String) /["i" := .var "n"])
        == SExp.sum "i" (.num 1) (.var "n") (.var "i")

/-! ### 포획 회피

`Σi : 1 to 4. (a × i)` 에 `a ↦ i` 를 넣는다. 결합 변수를 그대로 두면 새로 들어온 `i` 가
합에 잡혀 뜻이 달라진다. `newBinder` 가 결합 변수를 `x` 로 바꾼다
(`Prelude` 의 `hasFreshString` 이 `'x'` 를 반복해 이름을 만든다). -/

#guard ((SExp.sum "i" (.num 1) (.num 4) (.bin .mul (.var "a") (.var "i")) : SExp String)
          /["a" := .var "i"])
        == SExp.sum "x" (.num 1) (.num 4) (.bin .mul (.var "i") (.var "x"))

/-! ## (c-3) 명제들이 그대로 성립하는가

1.5(c) 는 정의를 아무렇게나 쓰지 말고 **§1.4 의 명제들이 살아남도록** 쓰라고 요구한다.
그중 대표가 일치 정리다. 이것이 성립하면 `fv`가 뜻에 영향을 줄 수 있는 변수를 빠뜨리지
않았다는 것을 알 수 있다. `fv`에 들어간 변수가 모두 실제로 영향을 준다는 뜻은 아니다.
-/

/--
**명제 1.1 (일치 정리)** — 합 식 판.

`FreeVars.lean` 의 `coincidence_intExp` 와 진술이 같고 `sum` 케이스만 늘어난다.
그 케이스에서 `e₀`, `e₁` 과 `e₂` 를 다르게 다뤄야 한다는 점이 이 연습의 핵심이다.

- `e₀`, `e₁` 은 `σ`, `σ'` 에서 그대로 잰다. 자유 변수가 통째로 `FV(Σ…)` 에 들어 있다.
- `e₂` 는 `σ[v := k]`, `σ'[v := k]` 에서 잰다. `v` 자리를 같은 값으로 덮으면 두 상태가
  `FV(e₂)` 전체에서 일치하게 된다.

두 번째가 `coincidence_assert` 의 양화사 케이스와 같은 논법이다. 그래서 진술을
`∀ (e) (σ σ')` 꼴로 써야 귀납 가설이 갱신된 상태에도 붙는다.
-/
@[exercise "Ex 1.5c" 3]
theorem coincidence_sExp :
    ∀ (e : SExp V) (σ σ' : State V), (∀ w ∈ e.fv, σ w = σ' w) → ⟦e⟧ₛ σ = ⟦e⟧ₛ σ' := by
  -- 먼저 볼 것: `FreeVars.lean` 의 `coincidence_intExp`. 앞 네 케이스는 글자까지 같다.
  -- 힌트 1: `sum` 케이스에서 `e₀`, `e₁` 은 `σ`, `σ'` 에서 그대로 잰다.
  --         자유 변수가 통째로 `FV(Σ…)` 안에 있으므로 가설을 바로 쓴다.
  -- 힌트 2: 본체는 `Finset.sum_congr rfl` 로 항마다 나눈 뒤 `ih₂` 를 쓴다.
  -- 힌트 3: `w = v` 인지로 나눈다. 같으면 `State.subst_self`, 다르면 `State.subst_of_ne`.
  sorry


/-! ## (d) 건전한 추론 규칙

Reynolds 는 "sound and nontrivial inference rules" 를 요구한다. §1.3 의 추론 규칙은
단언 사이의 관계인데, 합 식은 정수 식이라 규칙도 **정수 식 사이의 등식**으로 나온다.
객체 언어로 쓰면 이런 모양이다.

```
                                    e₁ < e₀
(Σv : e₀ to e₁. e₂) = 0
```

건전성(soundness)은 §1.3 에서 정의한 대로 "모든 상태에서 뜻이 같다" 이므로,
Lean 으로 옮기면 `∀ σ, ⟦…⟧ₛ σ = ⟦…⟧ₛ σ` 꼴의 정리가 된다. 아래 넷이 그것이다.

넷을 고른 기준은 Reynolds 의 "nontrivial" 이다. 빈 범위와 한 항짜리는 경계를 정하고,
분리 규칙은 합을 귀납적으로 계산하게 해 주며, 선형성은 합을 대수적으로 다루게 해 준다.
이 넷이 있으면 합 식에 대한 웬만한 등식을 유도할 수 있다.
-/

variable (v : V) (e₀ e₁ e₂ : SExp V) (σ : State V)

/--
**빈 범위 규칙.** 위끝이 아래끝보다 작으면 합은 0 이다.

`Finset.Icc` 를 고른 대가를 여기서 받는다. 정의만 펼치면 `Icc` 가 비어 있음을 보이는
문제로 바뀐다.
-/
@[exercise "Ex 1.5d-1" 2]
theorem sum_empty (h : ⟦e₁⟧ₛ σ < ⟦e₀⟧ₛ σ) :
    ⟦SExp.sum v e₀ e₁ e₂⟧ₛ σ = 0 := by
  -- 힌트: `Finset.Icc_eq_empty` 가 `¬ a ≤ b → Finset.Icc a b = ∅` 다.
  sorry

/--
**한 항 규칙.** 아래끝과 위끝이 같으면 합은 항 하나다.

오른쪽을 `⟦e₂⟧ₛ (σ[v := ⟦e₀⟧ₛ σ])` 로 썼다. 치환으로 `e₂ /[v := e₀]` 라고 써도 같은 뜻이지만,
그러려면 치환 정리(명제 1.3)의 합 식 판이 먼저 있어야 한다. 상태 갱신으로 쓰면 그 의존이 없다.
-/
@[exercise "Ex 1.5d-2" 2]
theorem sum_single (h : ⟦e₀⟧ₛ σ = ⟦e₁⟧ₛ σ) :
    ⟦SExp.sum v e₀ e₁ e₂⟧ₛ σ = ⟦e₂⟧ₛ (σ[v := ⟦e₀⟧ₛ σ]) := by
  -- 힌트: `h` 로 위끝을 아래끝으로 바꾸면 `Finset.Icc_self` 가 붙는다.
  sorry

/--
**분리 규칙.** 위끝을 하나 늘리면 항이 하나 붙는다.

`Σv : e₀ to e₁+1. e₂ = (Σv : e₀ to e₁. e₂) + e₂[v := e₁+1]`.

`e₀ ≤ e₁ + 1`이라는 단서가 필요하다. 아래끝이 `5`, 위끝이 `0`, 본체가 `1`인 경우를
넣어 보면 바로 드러난다. 왼쪽의 `5..1`과 오른쪽의 `5..0`은 둘 다 빈 범위지만,
오른쪽에는 마지막 항 `1`이 따로 남는다.

이 규칙이 있으면 합을 위끝에 대한 귀납으로 계산할 수 있다. Reynolds 가 말하는
"nontrivial" 에 해당하는 것이 이것이다.
-/
@[exercise "Ex 1.5d-3" 3]
theorem sum_split (h : ⟦e₀⟧ₛ σ ≤ ⟦e₁⟧ₛ σ + 1) :
    ⟦SExp.sum v e₀ (.bin .add e₁ (.num 1)) e₂⟧ₛ σ
      = ⟦SExp.sum v e₀ e₁ e₂⟧ₛ σ + ⟦e₂⟧ₛ (σ[v := ⟦e₁⟧ₛ σ + 1]) := by
  -- 힌트 1: `Finset.Icc a (b+1) = insert (b+1) (Finset.Icc a b)` 을 먼저 `have` 로 세운다.
  --         `ext k` 뒤 `Finset.mem_Icc`, `Finset.mem_insert` 로 풀면 `omega` 가 닫는다.
  -- 힌트 2: 그다음은 `Finset.sum_insert`. 그 가설도 `omega` 로 닫힌다.
  sorry

/--
**선형성.** 본체의 덧셈은 합 밖으로 나온다.

`Finset.sum_add_distrib` 를 객체 언어로 옮긴 것이다. 결합 변수가 양쪽에서 같은 값을 훑으므로
상태 갱신이 그대로 통과한다.
-/
@[exercise "Ex 1.5d-4" 2]
theorem sum_add (e e' : SExp V) :
    ⟦SExp.sum v e₀ e₁ (.bin .add e e')⟧ₛ σ
      = ⟦SExp.sum v e₀ e₁ e⟧ₛ σ + ⟦SExp.sum v e₀ e₁ e'⟧ₛ σ := by
  -- 힌트: 정의를 편 뒤 `Finset.sum_add_distrib` 하나면 된다.
  sorry


-- 분리 규칙으로 `Σi : 1 to 4. i` 를 손으로 접어 볼 수 있다. 값이 맞는지만 확인한다.
#guard ⟦(.sum "i" (.num 1) (.num 4) (.var "i") : SExp String)⟧ₛ (State.const 0)
        == ⟦(.sum "i" (.num 1) (.num 3) (.var "i") : SExp String)⟧ₛ (State.const 0) + 4

/-! ## 남겨 둔 것 — 치환 정리

명제 1.3(치환 정리)의 합 식 판은 여기에 없다. 진술은 이렇게 된다.

```
⟦e /ₜ δ⟧ₛ σ = ⟦e⟧ₛ (fun w => ⟦δ w⟧ₛ σ)
```

증명은 `Substitution.lean` 의 `substitution_assert` 와 같은 길을 간다. `sum` 케이스에서
`newBinder` 가 고른 새 이름이 `δ w` 의 자유 변수에 없다는 사실과 일치 정리를 함께 쓴다.
분량이 본문 절 하나만큼 되어서 이 파일에는 넣지 않았다.

직접 해 보려면 `Substitution.lean` 의 `newBinder_notMem_fv` 부터 옮기면 된다.
-/

/-! # 연습 1.6 — 부정 합(indefinite summation)

> *"Suppose the language in the previous exercise is further extended by introducing an integer
> expression for 'indefinite' summation, `Σv. e`, with the same meaning as `Σ_{v=0}^{v-1} e`.
> (Notice the similarity to the usual notation `∫ dv e` for an indefinite integral.)
> Discuss the difficulties raised by the binding and substitution properties of this expression."*

## 무엇이 이상한가

`Σv. e` 의 뜻은 `Σ_{v=0}^{v-1} e` 다. 오른쪽에서 `v` 가 **두 가지 역할**을 한다.

- 아래첨자의 `v` 는 0, 1, …, 로 훑는 묶인 변수다
- 위끝의 `v` 는 바깥에서 값을 읽는 자유 변수다

한 이름이 같은 식 안에서 묶이면서 동시에 자유롭다. §1.4 의 결합 구조는 이런 경우를 허용하지
않는다. `∀v. p` 에서 `v` 는 `p` 전체에서 묶이고, `Σv : e₀ to e₁. e₂` 에서도 `v` 가 묶이는
범위와 자유로운 범위가 부분식으로 갈렸다. 여기서는 갈 곳이 없다.

아래에서 그 결과를 실제로 확인한다.
-/

namespace Indefinite

/-- 부정 합만 있는 최소 언어. 문제를 드러내는 데 필요한 것만 남겼다. -/
inductive ISExp (V : Type u) where
  /-- 정수 상수. -/
  | num : Int → ISExp V
  /-- 변수. -/
  | var : V → ISExp V
  /-- 이항 연산. -/
  | bin : IntOp → ISExp V → ISExp V → ISExp V
  /-- `Σv. e` — 위끝을 `v` 자신이 정하는 합. -/
  | isum : V → ISExp V → ISExp V
  deriving DecidableEq, Repr

/--
부정 합의 뜻. `Σv. e = Σ_{k=0}^{σv - 1} ⟦e⟧ (σ[v := k])`.

위끝 `σ v` 를 **갱신 전** 상태에서 읽는다는 것이 정의의 전부다.
`Finset.Ico 0 (σ v)` 가 `0 ≤ k < σ v` 를 준다.
-/
def ISExp.eval : ISExp V → State V → Int
  | .num n,       _ => n
  | .var v,       σ => σ v
  | .bin op a b,  σ => op.denote (a.eval σ) (b.eval σ)
  | .isum v e,    σ => ∑ k ∈ Finset.Ico 0 (σ v), e.eval (σ[v := k])

@[inherit_doc ISExp.eval]
scoped notation:max "⟦" e "⟧ᵢ" => ISExp.eval e

/--
부정 합의 자유 변수.

`isum` 절에 `insert v` 가 붙는다. 본체에서는 `v` 를 지우지만 위끝으로 다시 들어온다.
`FV(Σv. e) = {v} ∪ (FV(e) \ {v})` 이므로 결과적으로 `v` 는 언제나 자유롭다.
-/
def ISExp.fv : ISExp V → Finset V
  | .num _       => ∅
  | .var v       => {v}
  | .bin _ a b   => a.fv ∪ b.fv
  | .isum v e    => insert v (e.fv.erase v)

-- 결합 변수가 자유 변수 목록에 남는다. `Σi. 1` 조차 `i` 에 의존한다.
#guard (ISExp.isum "i" (.num 1) : ISExp String).fv == {"i"}

/-! ## 어려움 1 — 이름 바꾸기가 뜻을 바꾼다

명제 1.5(이름 바꾸기 정리)는 `vnew ∉ FV(q) \ {v}`이면 결합 변수를 `vnew`로 바꿔도 뜻이
같다고 말한다. 부정 합에서는 그 단서를 만족시켜도 뜻이 달라진다.

`Σi. 1` 을 보자. 본체에 `i` 가 없으므로 `FV(1) \ {i} = ∅` 이고, 어떤 `vnew` 든 단서를
통과한다. `i` 를 `j` 로 바꾸면 `Σj. 1` 이 되는데, 앞의 뜻은 `σi` 이고 뒤의 뜻은 `σj` 다.
`σi ≠ σj` 인 상태를 하나 잡으면 끝난다.

무슨 일이 일어났나. 이름 바꾸기는 **묶인** 자리만 건드린다는 전제 위에 서 있는데,
여기서는 같은 이름이 자유로운 자리에도 있어서 그것까지 함께 바뀐다.
-/

/--
**이름 바꾸기 정리가 깨진다.** 명제 1.5 의 단서를 만족하는데도 뜻이 달라지는 예가 있다.

`Σi. 1` 과 `Σj. 1` 을 쓴다. 본체 `1` 에 자유 변수가 없으므로 `j ∉ FV(1) \ {i} = ∅` 이고,
따라서 `Σj. 1` 은 `Σi. 1` 의 적법한 이름 바꾸기다. 그런데 앞은 `σ i` 를, 뒤는 `σ j` 를 센다.

증명은 `σ i = 1`, `σ j = 0` 인 상태를 제시하면 된다.
-/
@[exercise "Ex 1.6" 3]
theorem isum_renaming_fails :
    ∃ σ : State String,
      ⟦(ISExp.isum "i" (.num 1) : ISExp String)⟧ᵢ σ
        ≠ ⟦(ISExp.isum "j" (.num 1) : ISExp String)⟧ᵢ σ := by
  -- 힌트: `σ i = 1`, `σ j = 0` 인 상태를 `refine ⟨fun w => …, ?_⟩` 로 제시한다.
  --       그다음은 `simp [ISExp.eval]` 이 계산해 준다.
  sorry

/-! ## 어려움 2 — 치환이 결합 변수를 건너뛸 수 없다

`Assert.subst` 는 `(∀v. p) /ₛ δ` 에서 `δ` 의 `v` 자리를 `var vnew` 로 덮어썼다.
`v` 는 묶여 있으니 `δ v` 를 볼 일이 없다는 판단이었다.

부정 합에서는 그 판단이 틀린다. 위끝의 `v`는 자유롭고, 치환은 그 자리를 `δ v`로 바꿔야 한다.
그런데 위끝은 부분식이 아니라 결합 변수 자체다. `Σv. e` 에 `v ↦ e'` 를 넣으면
"위끝은 `e'` 로, 본체의 `v` 는 그대로" 를 표현해야 하는데, 구문에 그런 자리가 없다.

바꿔 말하면 `Σv. e` 는 `Σv : 0 to (v-1). e` 의 줄임말인데, 줄이면서 위끝 자리를 잃어버렸다.
줄이지 않은 쪽에서는 §1.4 의 정의가 그대로 통한다 — `SExp` 에서 확인한 그대로다.

## 그래서 어떻게 하나

세 가지 길이 있고, Reynolds 가 이후 장들에서 모두 지나간다.

- **위끝을 부분식으로 되돌린다.** `Σv : e₀ to e₁. e₂` 로 돌아가는 것이다.
  `Σv. e` 를 그 위의 파생 형태(derived form)로 정의하면 결합 문제가 사라진다.
- **결합 변수와 자유 변수를 표기로 구분한다.** de Bruijn 색인이 그것이다.
  묶인 자리는 번호로, 자유로운 자리는 이름으로 두면 두 역할이 섞이지 않는다.
  CSlib 의 `Cslib/Languages/LambdaCalculus/LocallyNameless/` 가 이 방식이다.
- **애초에 이런 구문을 금지한다.** 실제 언어 설계에서 흔히 택하는 답이다.

1.6 이 "discuss" 로 끝나는 이유가 이것이다. 정답 하나가 아니라, 결합 구조를 어떻게
설계하느냐에 따라 값을 치르는 자리가 달라진다.
-/

end Indefinite

end Reynolds.Exercises.Ch01.Summation
