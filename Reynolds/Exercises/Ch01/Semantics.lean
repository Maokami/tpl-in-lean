/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Exercises.Ch01.Syntax

/-!
# §1.2 표시적 의미론 (Denotational Semantics) — 정수 식

Reynolds §1.2 (pp. 8–11)의 앞부분에 대응한다.

## 이 파일에서 다루는 것
- 의미 함수 `⟦-⟧intexp ∈ ⟨intexp⟩ → Σ → ℤ`

## 배경

구의 값은 정수지만 뜻은 정수가 아니다. 값이 변수에 따라 달라지기 때문이다.
그래서 뜻을 `상태 → 정수` 라는 함수로 잡는다. 표시적 의미론의 출발점이고,
2장에서 명령의 뜻이 `Σ → Σ⊥` 가 되는 것도 같은 자리에서 나온다.

의미 함수는 합성적(compositional)이다. 구의 뜻이 부분구의 뜻만으로 정해진다는 뜻이다.
Lean 에서는 구조적 재귀로 쓰면 합성성이 정의에서 따라온다.

## 읽는 순서
`Syntax.lean` → 이 파일 → `FreeVars.lean`
-/

@[expose] public section

namespace Reynolds.Exercises.Ch01

open Reynolds

universe u

/--
연산자 기호가 실제로 무슨 함수인가.

0 으로 나누기에 대해 Reynolds §1.2 는 이렇게 못박는다.

> *"expressions always terminate without an error stop. In particular, division by zero
> must produce some integer result."*

Reynolds가 요구하는 것은 0으로 나누는 경우에도 어떤 정수를 돌려주는 전함수라는 점까지다.
이 형식화는 그 미지정 값을 Lean `Int`의 규약인 `x / 0 = 0`, `x % 0 = x`로 정했다.
따라서 0인 제수의 구체적인 결과에 의존하는 명제는 이 선택에 의존하고, 그 경우를 쓰지 않는
명제만 이 선택과 무관하다. 이는 하드웨어 동작에 대한 주장이 아니다.
-/
def IntOp.denote : IntOp → Int → Int → Int
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b
  | .div, a, b => a / b
  | .rem, a, b => a % b

/--
`⟦e⟧ σ` — 정수 식의 뜻. Reynolds §1.2의 `⟦-⟧intexp ∈ ⟨intexp⟩ → Σ → ℤ`.

각 절이 Reynolds의 의미 방정식 (1.3)~(1.6) 하나씩에 대응한다.
전함수(total function)다. 술어 논리에는 비종료가 없기 때문이고,
2장에서 `while` 이 들어오면 이 사정이 달라진다.

이 방정식들이 함수를 유일하게 정한다는 사실의 증명은 `Depth/Algebra.lean` §7 에 있다. (선택)
-/
def IntExp.eval {V : Type u} : IntExp V → State V → Int
  | .num n,        _ => n
  | .var v,        σ => σ v
  | .neg e,        σ => -(e.eval σ)
  | .bin op e₀ e₁, σ => op.denote (e₀.eval σ) (e₁.eval σ)

/--
Reynolds 의 `⟦e⟧intexp` 를 흉내낸 표기. `open Reynolds.Exercises.Ch01` 안에서만 보인다.

아래 첨자를 붙인 것은 Mathlib 이 `⟦a⟧` 를 몫(quotient) 대표원소 표기로 이미 쓰기 때문이다.
그대로 두면 중복 정의로 애매해진다. Reynolds 도 구의 종류마다 `⟦-⟧intexp`, `⟦-⟧assert`
처럼 아래 첨자를 붙이므로 표기가 오히려 책에 가까워졌다.
2장에서는 불 식이 `⟦b⟧ᵇ`, 명령이 `⟦c⟧ᶜ` 다. 유니코드에 아래 첨자 `b`, `c` 가 없어서 위 첨자를 쓴다.
-/
scoped notation:max "⟦" e "⟧ₑ" => IntExp.eval e

/-- 정의를 그대로 계산해 본다. `x + 1` 을 모든 변수가 41 인 상태에서. -/
example : ⟦IntExp.bin .add (.var "x") (.num 1)⟧ₑ (State.const 41) = 42 := by decide

/-! ## 단언의 의미 -/

/-- 비교 기호의 뜻. -/
def Cmp.denote : Cmp → Int → Int → Prop
  | .eq, a, b => a = b
  | .ne, a, b => a ≠ b
  | .lt, a, b => a < b
  | .le, a, b => a ≤ b
  | .gt, a, b => a > b
  | .ge, a, b => a ≥ b

/-- 논리 기호의 뜻. -/
def LogOp.denote : LogOp → Prop → Prop → Prop
  | .and, a, b => a ∧ b
  | .or,  a, b => a ∨ b
  | .imp, a, b => a → b
  | .iff, a, b => a ↔ b

/--
`⟦p⟧ₐ σ` — 단언의 뜻. Reynolds §1.2 의 `⟦-⟧assert`.

**책과의 차이**: Reynolds 는 `⟦-⟧assert ∈ ⟨assert⟩ → Σ → 𝔹` 라고 쓰지만 여기서는 `Prop` 이다.

양화사 때문이다. 계산 가능한 `Bool` 평가기를 만들려면 모든 단언의 참·거짓을 판정하는
절차가 필요하다.
`⟦∀v. p⟧ σ = ∀ n : ℤ, ⟦p⟧ σ[v := n]` 같은 정수 양화가 있는 이 언어에는 그런 절차가
일반적으로 없다. `Prop`은 결정 절차 없이도 명제를 표현할 수 있다.

Reynolds 도 §2.1 에서 명령형 언어의 ⟨boolexp⟩ 를 만들 때 같은 이유를 든다.
*"the same as assertions except for the omission of quantifiers
(for the obvious reason that they are noncomputable)"*
`Prop` 과 `Bool` 의 갈림이 ⟨assert⟩ 와 ⟨boolexp⟩ 의 갈림과 같은 자리에 있다.

2장의 `BoolExp.eval : BoolExp V → State V → Bool` 은 `#eval` 로 돌아간다.
양화사 없는 조각에서 두 의미가 일치한다는 것도 그때 증명한다.
-/
def Assert.eval {V : Type u} [DecidableEq V] : Assert V → State V → Prop
  | .tru,            _ => True
  | .fls,            _ => False
  | .cmp c e₀ e₁,    σ => c.denote (e₀.eval σ) (e₁.eval σ)
  | .not p,          σ => ¬ p.eval σ
  | .bin op p q,     σ => op.denote (p.eval σ) (q.eval σ)
  | .quant .all v p, σ => ∀ n : Int, p.eval (σ[v := n])
  | .quant .ex  v p, σ => ∃ n : Int, p.eval (σ[v := n])

/-- Reynolds 의 `⟦p⟧assert` 를 흉내낸 표기. 아래 첨자 규약은 `⟦e⟧ₑ` 와 같다. -/
scoped notation:max "⟦" p "⟧ₐ" => Assert.eval p

end Reynolds.Exercises.Ch01
