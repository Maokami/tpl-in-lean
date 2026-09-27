/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Answers.Ch01.Semantics
public import Reynolds.Answers.Ch01.Ex.Summation.Indefinite
public import Reynolds.Meta.Exercise
public import Cslib.Foundations.Data.HasFresh
public import Mathlib.Data.Int.Interval
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
-- `#guard` 는 컴파일 시점에 계산한다 (AGENTS.md §10).
public meta import Reynolds.Prelude
public meta import Reynolds.Answers.Ch01.Semantics
public meta import Mathlib.Data.Int.Interval
public meta import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# 연습 1.5 · 1.6 — 합 식 (summation expression)

## 1.5가 요구하는 것 (p. 23)

유한 합 식을 더하고 (a) 문법, (b) 의미, (c) 자유 변수와 치환, (d) 건전한 추론 규칙을
제시한다. (c)는 §1.4의 결합·치환 명제가 계속 성립하도록 정의할 것을 요구한다.

## 왜 축소판 언어를 따로 만드나

`IntExp` 에 생성자를 하나 더하면 `Semantics.lean` 부터 `Substitution.lean` 까지 모든 정의와
증명이 케이스 하나씩 늘어난다. 본문 연습이 전부 깨진다. 그래서 여기서는 `SExp` 라는 자족적인
축소판을 세우고, 그 안에서 (a)~(d) 를 처음부터 다시 밟는다.

**책과의 차이**: 합 식을 더한 정수 식의 성질을 다룬다. 이를 비교식과 양화 단언에도
연결한 전체 술어 논리 언어는 여기서 새로 정의하지 않는다.

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
- (c) 치환 정리의 합 식 판 → `Summation/Substitution.lean`의 `substitution_sExp`
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

namespace Reynolds.Answers.Ch01.Summation

open Reynolds Reynolds.Answers.Ch01 Cslib

universe u

variable {V : Type u} [DecidableEq V]

/-! ## (a) 추상 구문

Reynolds 의 생성 규칙 하나를 더하는 것에 해당한다.

```
⟨intexp⟩ ::= … | Σ⟨var⟩ : ⟨intexp⟩ to ⟨intexp⟩. ⟨intexp⟩
```

`Syntax.lean` 과 같은 이유로 이항 연산자는 `IntOp` 태그로 묶고, 그 타입을 그대로 재사용한다.
-/

-- ANCHOR: sExp
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
-- ANCHOR_END: sExp

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

-- ANCHOR: sExpEval
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
-- ANCHOR_END: sExpEval

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

-- ANCHOR: sExpFv
/-- `FV(e)` — 합 식이 있는 정수 식의 자유 변수. `sum` 절에서 `e₂`만 `erase` 한다. -/
def SExp.fv : SExp V → Finset V
  | .num _         => ∅
  | .var v         => {v}
  | .neg e         => e.fv
  | .bin _ e₀ e₁   => e₀.fv ∪ e₁.fv
  | .sum v e₀ e₁ e₂ => e₀.fv ∪ e₁.fv ∪ (e₂.fv.erase v)
-- ANCHOR_END: sExpFv

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

-- ANCHOR: sExpSubst
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
-- ANCHOR_END: sExpSubst

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

-- ANCHOR: coincidenceSExp
/--
**명제 1.1 (일치 정리)** — 합 식 판.

`FreeVars.lean` 의 `coincidence_intExp` 와 진술이 같고 `sum` 케이스만 늘어난다.
그 케이스에서는 합의 경계 `e₀`, `e₁` 과 본문 `e₂` 에 서로 다른 상태를 사용한다.

- `e₀`, `e₁` 은 `σ`, `σ'` 에서 그대로 잰다. 자유 변수가 통째로 `FV(Σ…)` 에 들어 있다.
- `e₂` 는 `σ[v := k]`, `σ'[v := k]` 에서 잰다. `v` 자리를 같은 값으로 덮으면 두 상태가
  `FV(e₂)` 전체에서 일치하게 된다.

두 번째가 `coincidence_assert` 의 양화사 케이스와 같은 논법이다. 그래서 진술을
`∀ (e) (σ σ')` 꼴로 써야 귀납 가설이 갱신된 상태에도 붙는다.
-/
@[exercise "Ex 1.5c" 3]
theorem coincidence_sExp :
    ∀ (e : SExp V) (σ σ' : State V), (∀ w ∈ e.fv, σ w = σ' w) → ⟦e⟧ₛ σ = ⟦e⟧ₛ σ' := by
  intro e
  induction e with
  | num n => intro _ _ _; rfl
  | var v => intro _ _ h; exact h v (by simp [SExp.fv])
  | neg e ih => intro σ σ' h; simp [SExp.eval, ih σ σ' h]
  | bin op e₀ e₁ ih₀ ih₁ =>
      intro σ σ' h
      have h₀ := ih₀ σ σ' fun w hw => h w (by simp [SExp.fv, hw])
      have h₁ := ih₁ σ σ' fun w hw => h w (by simp [SExp.fv, hw])
      simp [SExp.eval, h₀, h₁]
  | sum v e₀ e₁ e₂ ih₀ ih₁ ih₂ =>
      intro σ σ' h
      -- 경계는 바깥에서 잰다. 자유 변수가 그대로 `FV(Σ…)` 에 있으므로 가설을 바로 쓴다.
      have h₀ := ih₀ σ σ' fun w hw => h w (by simp [SExp.fv, hw])
      have h₁ := ih₁ σ σ' fun w hw => h w (by simp [SExp.fv, hw])
      simp only [SExp.eval, h₀, h₁]
      -- 본체는 갱신된 상태에서 잰다. `v` 를 같은 값으로 덮으면 `FV(e₂)` 에서 일치한다.
      refine Finset.sum_congr rfl fun k _ => ih₂ _ _ fun w hw => ?_
      by_cases hwv : w = v
      · subst hwv; simp
      · simp only [State.subst_of_ne _ _ _ _ hwv]
        exact h w (by simp [SExp.fv, hw, hwv])
-- ANCHOR_END: coincidenceSExp

/-! ## (d) 건전한 추론 규칙

Reynolds 는 "sound and nontrivial inference rules" 를 요구한다. §1.3 의 추론 규칙은
단언 사이의 관계인데, 합 식은 정수 식이라 규칙도 **정수 식 사이의 등식**으로 나온다.
객체 언어로 쓰면 이런 모양이다.

```
                                    e₁ < e₀
(Σv : e₀ to e₁. e₂) = 0
```

§1.3의 건전성(soundness)은 전제의 타당성이 결론의 타당성을 보존한다는 뜻이다.
여기서는 더 구체적으로, 임의의 상태에서 경계 조건이 성립하면 두 합 식의 값이 같음을
보인다. 이를 모든 상태에 적용하면 등식 단언에 대한 건전한 추론 규칙을 얻는다.

넷을 고른 기준은 Reynolds 의 "nontrivial" 이다. 빈 범위와 한 항짜리는 경계를 정하고,
분리 규칙은 합을 귀납적으로 계산하게 해 주며, 선형성은 합을 대수적으로 다루게 해 준다.
이 넷이 있으면 합 식에 대한 웬만한 등식을 유도할 수 있다.
-/

variable (v : V) (e₀ e₁ e₂ : SExp V) (σ : State V)

-- ANCHOR: sumRules
/--
**빈 범위 규칙.** 위끝이 아래끝보다 작으면 합은 0 이다.

`Finset.Icc` 를 고른 대가를 여기서 받는다. 정의만 펼치면 `Icc` 가 비어 있음을 보이는
문제로 바뀐다.
-/
@[exercise "Ex 1.5d-1" 2]
theorem sum_empty (h : ⟦e₁⟧ₛ σ < ⟦e₀⟧ₛ σ) :
    ⟦SExp.sum v e₀ e₁ e₂⟧ₛ σ = 0 := by
  simp [SExp.eval, Finset.Icc_eq_empty (not_le.mpr h)]

/--
**한 항 규칙.** 아래끝과 위끝이 같으면 합은 항 하나다.

오른쪽을 `⟦e₂⟧ₛ (σ[v := ⟦e₀⟧ₛ σ])` 로 썼다. 치환으로 `e₂ /[v := e₀]` 라고 써도 같은 뜻이지만,
그러려면 치환 정리(명제 1.3)의 합 식 판이 먼저 있어야 한다. 상태 갱신으로 쓰면 그 의존이 없다.
-/
@[exercise "Ex 1.5d-2" 2]
theorem sum_single (h : ⟦e₀⟧ₛ σ = ⟦e₁⟧ₛ σ) :
    ⟦SExp.sum v e₀ e₁ e₂⟧ₛ σ = ⟦e₂⟧ₛ (σ[v := ⟦e₀⟧ₛ σ]) := by
  simp [SExp.eval, ← h, Finset.Icc_self]

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
  simp only [SExp.eval, IntOp.denote]
  have key : Finset.Icc (⟦e₀⟧ₛ σ) (⟦e₁⟧ₛ σ + 1)
      = insert (⟦e₁⟧ₛ σ + 1) (Finset.Icc (⟦e₀⟧ₛ σ) (⟦e₁⟧ₛ σ)) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [key, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega)]
  ring

/--
**선형성.** 본체의 덧셈은 합 밖으로 나온다.

`Finset.sum_add_distrib` 를 객체 언어로 옮긴 것이다. 결합 변수가 양쪽에서 같은 값을 훑으므로
상태 갱신이 그대로 통과한다.
-/
@[exercise "Ex 1.5d-4" 2]
theorem sum_add (e e' : SExp V) :
    ⟦SExp.sum v e₀ e₁ (.bin .add e e')⟧ₛ σ
      = ⟦SExp.sum v e₀ e₁ e⟧ₛ σ + ⟦SExp.sum v e₀ e₁ e'⟧ₛ σ := by
  simp [SExp.eval, IntOp.denote, Finset.sum_add_distrib]
-- ANCHOR_END: sumRules

-- 분리 규칙으로 `Σi : 1 to 4. i` 를 손으로 접어 볼 수 있다. 값이 맞는지만 확인한다.
#guard ⟦(.sum "i" (.num 1) (.num 4) (.var "i") : SExp String)⟧ₛ (State.const 0)
        == ⟦(.sum "i" (.num 1) (.num 3) (.var "i") : SExp String)⟧ₛ (State.const 0) + 4

/-! ## 이어서 확인할 것 — 치환 정리

`Summation/Substitution.lean`은 명제 1.2의 구문적 성질, 명제 1.3의 치환 정리,
한 변수 치환과 합의 결합 변수 이름 바꾸기를 증명한다. 치환 정리 연습은 일치 정리의
결론을 가설로 받으므로, 이 파일의 연습을 아직 풀지 않아도 독립적으로 풀 수 있다.
-/

end Reynolds.Answers.Ch01.Summation
