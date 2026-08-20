/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Answers.Ch01.Syntax

/-!
# §1.2 표시적 의미론 (Denotational Semantics) — 정수 식

Reynolds §1.2 (pp. 8–11)의 앞부분에 대응한다.

## 이 파일에서 다루는 것
- 의미 함수 `⟦-⟧intexp ∈ ⟨intexp⟩ → Σ → ℤ`

## 핵심 아이디어

구의 **값**은 정수지만 구의 **뜻**은 정수가 아니다. 값이 변수에 따라 달라지기 때문이다.
그래서 뜻은 `상태 → 정수` 라는 함수가 된다. 이것이 표시적 의미론의 출발점이고,
2장에서 명령의 뜻이 `Σ → Σ⊥` 가 되는 것도 같은 사고 방식이다.

의미 함수는 **합성적(compositional)** 이다 — 구의 뜻이 부분구의 뜻만으로 정해진다.
Lean에서는 이것이 그냥 **구조적 재귀**다. 그래서 정의를 쓰는 것만으로 합성성이 보장된다.

## 읽는 순서
`Syntax.lean` → 이 파일 → `FreeVars.lean`
-/

@[expose] public section

namespace Reynolds.Answers.Ch01

open Reynolds

universe u

/--
연산자 기호가 실제로 무슨 함수인가.

**0으로 나누기**: Reynolds §1.2는 *"expressions always terminate without an error stop.
In particular, division by zero must produce some integer result."* 라고 못박는다.
즉 언어 설계자가 오류를 검사하지 않기로 했다면, 그 연산은 하드웨어가 실제로 계산하는
(수학적으로 틀린) 함수여야 하고 **어쨌든 함수이기만 하면 된다.**

Lean의 `Int` 나눗셈은 `x / 0 = 0`, `x % 0 = x` 다. 우리는 이 규약을 쓴다.
§2.7에서 "어떤 규약을 쓰든 성립하는 등식들"을 증명하며 이 선택이 정말 무관함을 확인한다.
-/
-- ANCHOR: denote
def IntOp.denote : IntOp → Int → Int → Int
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b
  | .div, a, b => a / b
  | .rem, a, b => a % b

/--
`⟦e⟧ σ` — 정수 식의 뜻. Reynolds §1.2의 `⟦-⟧intexp ∈ ⟨intexp⟩ → Σ → ℤ`.

각 절이 Reynolds의 의미 방정식 (1.3)~(1.6) 하나씩에 대응한다.
전함수(total function)라는 점에 주목할 것 — 술어 논리에는 비종료가 없다.
2장에서 `while`이 들어오는 순간 이 사정이 완전히 달라진다.
-/
def IntExp.eval {V : Type u} : IntExp V → State V → Int
  | .num n,        _ => n
  | .var v,        σ => σ v
  | .neg e,        σ => -(e.eval σ)
  | .bin op e₀ e₁, σ => op.denote (e₀.eval σ) (e₁.eval σ)
-- ANCHOR_END: denote

/--
Reynolds 의 `⟦e⟧intexp` 를 흉내낸 표기. `open Reynolds.Answers.Ch01` 안에서만 보인다.

**아래 첨자를 왜 붙이나**: Mathlib 이 `⟦a⟧` 를 몫(quotient) 대표원소 표기로 이미 쓴다.
그대로 쓰면 중복 정의(overload)로 애매해진다. 마침 Reynolds 도 구의 종류마다
`⟦-⟧intexp`, `⟦-⟧assert`, `⟦-⟧comm` 처럼 아래 첨자를 붙이므로,
`ₑ`(expression)를 붙이는 것이 책에 더 충실하기까지 하다.
2장의 명령은 `⟦c⟧꜀` 가 된다.
-/
scoped notation:max "⟦" e "⟧ₑ" => IntExp.eval e

-- ANCHOR: evalExample
/-- 계산해 볼 수 있다는 것이 이 프로젝트의 핵심이다. `x + 1` 을 모든 변수가 41인 상태에서. -/
example : ⟦IntExp.bin .add (.var "x") (.num 1)⟧ₑ (State.const 41) = 42 := by decide
-- ANCHOR_END: evalExample

end Reynolds.Answers.Ch01
