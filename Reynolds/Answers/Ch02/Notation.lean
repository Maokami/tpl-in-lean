/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Answers.Ch02.Syntax
public import Reynolds.Answers.Ch01.Notation
-- `#guard` 는 컴파일 시점에 계산한다 (AGENTS.md §10).
public meta import Reynolds.Answers.Ch02.Syntax

/-!
# §2.1 구체 구문 — 명령을 Lean 안에서 쓰기

1장의 DSL 을 명령까지 늘린다. 정수 식 문법 `reyE` 는 그대로 재사용한다.

## 표기 규약

| 문법 | 뜻 |
|---|---|
| `⟪ … ⟫ₑ` | 정수 식 `IntExp String` (1장) |
| `⟪ … ⟫ₐ` | 단언 `Assert String` (1장) |
| `⟪ … ⟫ᵇ` | 불 식 `BoolExp String` |
| `⟪ … ⟫ᶜ` | 명령 `Comm String` |
| `%t` | Lean 항 `t` 를 그대로 끼워 넣는다 |

닫는 기호로 갈래를 구분하는 방식은 1장과 같다. 유니코드에 아래 첨자 `b`, `c` 가 없어서
불 식과 명령만 위 첨자를 쓴다.

## 무엇이 달라지는가

없으면 예제가 이렇게 생긴다.

```lean
Comm.seq (.assign "x" (.num 1))
  (Comm.wh (.cmp .le (.var "x") (.num 10))
    (Comm.seq (.assign "y" (.bin .add (.var "y") (.var "x")))
              (.assign "x" (.bin .add (.var "x") (.num 1)))))
```

있으면 이렇게 쓴다.

```lean
⟪ x := 1; while x ≤ 10 do (y := y + x; x := x + 1) ⟫ᶜ
```

## 우선순위

순차 합성 `;` 이 가장 낮고 오른쪽 결합이다. `if`, `while`, `newvar` 의 본체는
닫는 괄호까지 뻗으므로, 본체가 `;` 를 포함하면 괄호를 쳐야 한다.

```lean
⟪ while b do (c₀; c₁) ⟫ᶜ   -- 반복 안에 둘 다
⟪ while b do c₀; c₁ ⟫ᶜ     -- 반복은 c₀ 만, 그다음 c₁
```

Reynolds 도 §2.1 에서 같은 모호함을 지적하고 괄호로 푼다.
`;` 가 결합적(associative)이라는 사실은 §2.2 에서 의미로 증명한다 — 구문에서는 다른 트리다.

## 왜 `mkIdent` 인가

1장과 같은 이유다. Lean 매크로는 위생적이라 생성자 이름을 매크로 **정의 자리**에서
해석하는데, 그러면 이 DSL 이 `Reynolds.Answers.Ch02` 로 못 박혀 연습 트리에서 안 맞는다.
`Lean.mkIdent` 로 만든 이름은 **쓰는 자리**에서 해석된다. 자세한 사정은
`Ch01/Notation.lean` 의 같은 절에 적어 두었다.
-/

-- 이 파일 끝의 `#guard` 가 번역 규칙을 확인한다.
set_option linter.hashCommand false

@[expose] public section

namespace Reynolds.Answers.Ch02

open Reynolds Reynolds.Answers.Ch01

/-! ## 구문 범주 -/

/-- 객체 언어의 불 식. Reynolds 의 ⟨boolexp⟩. -/
declare_syntax_cat reyB

/-- 객체 언어의 명령. Reynolds 의 ⟨comm⟩. -/
declare_syntax_cat reyC

/-! ### 불 식

1장의 단언 문법에서 양화사 두 줄만 뺀 것이다. 우선순위도 그대로다. -/

/-- 참. -/
syntax:max "tt" : reyB
/-- 거짓. -/
syntax:max "ff" : reyB
/-- 괄호. -/
syntax:max "(" reyB ")" : reyB
/-- Lean 항을 불 식으로 끼워 넣는다. -/
syntax:max "%" term:max : reyB
/-- 같음. -/
syntax:50 reyE " = " reyE : reyB
/-- 다름. -/
syntax:50 reyE " ≠ " reyE : reyB
/-- 작음. -/
syntax:50 reyE " < " reyE : reyB
/-- 작거나 같음. -/
syntax:50 reyE " ≤ " reyE : reyB
/-- 큼. -/
syntax:50 reyE " > " reyE : reyB
/-- 크거나 같음. -/
syntax:50 reyE " ≥ " reyE : reyB
/-- 부정. -/
syntax:40 "¬" reyB:40 : reyB
/-- 연언. -/
syntax:35 reyB:36 " ∧ " reyB:35 : reyB
/-- 선언. -/
syntax:30 reyB:31 " ∨ " reyB:30 : reyB
/-- 함의. -/
syntax:25 reyB:26 " ⇒ " reyB:25 : reyB
/-- 동치. -/
syntax:20 reyB:21 " ⇔ " reyB:20 : reyB

/-! ### 명령 -/

/-- 아무것도 하지 않는다. -/
syntax:max "skip" : reyC
/-- 괄호. -/
syntax:max "(" reyC ")" : reyC
/-- Lean 항을 명령으로 끼워 넣는다. -/
syntax:max "%" term:max : reyC
/-- 대입. -/
syntax:30 ident " := " reyE : reyC
/-- 조건. 두 가지가 다 닫는 괄호까지 뻗는다. -/
syntax:20 "if " reyB " then " reyC:20 " else " reyC:20 : reyC
/-- 반복. 본체가 닫는 괄호까지 뻗는다. -/
syntax:20 "while " reyB " do " reyC:20 : reyC
/-- 변수 선언. 본체가 닫는 괄호까지 뻗는다. -/
syntax:20 "newvar " ident " := " reyE " in " reyC:20 : reyC
/-- 순차 합성. 가장 낮고 오른쪽 결합이다. -/
syntax:10 reyC:11 "; " reyC:10 : reyC

/-! ## 진입점 -/

/-- 객체 언어의 불 식을 쓴다. `⟪ x < 3 ⟫ᵇ : BoolExp String`. -/
syntax:max "⟪" reyB "⟫ᵇ" : term

/-- 객체 언어의 명령을 쓴다. `⟪ x := x + 1 ⟫ᶜ : Comm String`. -/
syntax:max "⟪" reyC "⟫ᶜ" : term

/-! ## 번역 규칙 -/

open Lean in
macro_rules
  | `(⟪ tt ⟫ᵇ)          => `($(mkIdent `BoolExp.tru))
  | `(⟪ ff ⟫ᵇ)          => `($(mkIdent `BoolExp.fls))
  | `(⟪ ( $b:reyB ) ⟫ᵇ) => `(⟪ $b ⟫ᵇ)
  | `(⟪ % $t:term ⟫ᵇ)   => `(($t : $(mkIdent `BoolExp) String))
  | `(⟪ $a:reyE = $b:reyE ⟫ᵇ) => `($(mkIdent `BoolExp.cmp) $(mkIdent `Cmp.eq) ⟪ $a ⟫ₑ ⟪ $b ⟫ₑ)
  | `(⟪ $a:reyE ≠ $b:reyE ⟫ᵇ) => `($(mkIdent `BoolExp.cmp) $(mkIdent `Cmp.ne) ⟪ $a ⟫ₑ ⟪ $b ⟫ₑ)
  | `(⟪ $a:reyE < $b:reyE ⟫ᵇ) => `($(mkIdent `BoolExp.cmp) $(mkIdent `Cmp.lt) ⟪ $a ⟫ₑ ⟪ $b ⟫ₑ)
  | `(⟪ $a:reyE ≤ $b:reyE ⟫ᵇ) => `($(mkIdent `BoolExp.cmp) $(mkIdent `Cmp.le) ⟪ $a ⟫ₑ ⟪ $b ⟫ₑ)
  | `(⟪ $a:reyE > $b:reyE ⟫ᵇ) => `($(mkIdent `BoolExp.cmp) $(mkIdent `Cmp.gt) ⟪ $a ⟫ₑ ⟪ $b ⟫ₑ)
  | `(⟪ $a:reyE ≥ $b:reyE ⟫ᵇ) => `($(mkIdent `BoolExp.cmp) $(mkIdent `Cmp.ge) ⟪ $a ⟫ₑ ⟪ $b ⟫ₑ)
  | `(⟪ ¬ $b:reyB ⟫ᵇ)         => `($(mkIdent `BoolExp.not) ⟪ $b ⟫ᵇ)
  | `(⟪ $a:reyB ∧ $b:reyB ⟫ᵇ) => `($(mkIdent `BoolExp.bin) $(mkIdent `LogOp.and) ⟪ $a ⟫ᵇ ⟪ $b ⟫ᵇ)
  | `(⟪ $a:reyB ∨ $b:reyB ⟫ᵇ) => `($(mkIdent `BoolExp.bin) $(mkIdent `LogOp.or) ⟪ $a ⟫ᵇ ⟪ $b ⟫ᵇ)
  | `(⟪ $a:reyB ⇒ $b:reyB ⟫ᵇ) => `($(mkIdent `BoolExp.bin) $(mkIdent `LogOp.imp) ⟪ $a ⟫ᵇ ⟪ $b ⟫ᵇ)
  | `(⟪ $a:reyB ⇔ $b:reyB ⟫ᵇ) => `($(mkIdent `BoolExp.bin) $(mkIdent `LogOp.iff) ⟪ $a ⟫ᵇ ⟪ $b ⟫ᵇ)

open Lean in
macro_rules
  | `(⟪ skip ⟫ᶜ)        => `($(mkIdent `Comm.skip))
  | `(⟪ ( $c:reyC ) ⟫ᶜ) => `(⟪ $c ⟫ᶜ)
  | `(⟪ % $t:term ⟫ᶜ)   => `(($t : $(mkIdent `Comm) String))
  | `(⟪ $x:ident := $e:reyE ⟫ᶜ) =>
      `($(mkIdent `Comm.assign) $(Lean.quote x.getId.toString) ⟪ $e ⟫ₑ)
  | `(⟪ if $b:reyB then $c₀:reyC else $c₁:reyC ⟫ᶜ) =>
      `($(mkIdent `Comm.ite) ⟪ $b ⟫ᵇ ⟪ $c₀ ⟫ᶜ ⟪ $c₁ ⟫ᶜ)
  | `(⟪ while $b:reyB do $c:reyC ⟫ᶜ) =>
      `($(mkIdent `Comm.wh) ⟪ $b ⟫ᵇ ⟪ $c ⟫ᶜ)
  | `(⟪ newvar $x:ident := $e:reyE in $c:reyC ⟫ᶜ) =>
      `($(mkIdent `Comm.newvar) $(Lean.quote x.getId.toString) ⟪ $e ⟫ₑ ⟪ $c ⟫ᶜ)
  | `(⟪ $c₀:reyC ; $c₁:reyC ⟫ᶜ) =>
      `($(mkIdent `Comm.seq) ⟪ $c₀ ⟫ᶜ ⟪ $c₁ ⟫ᶜ)

/-! ## 번역이 맞는지 확인

DSL 은 구문을 옮기기만 한다. 옮긴 결과가 손으로 쓴 생성자와 같은지 확인해 둔다.
아래가 어긋나면 빌드가 실패한다. -/

-- 대입 하나.
#guard ⟪ x := x + 1 ⟫ᶜ == Comm.assign "x" (.bin .add (.var "x") (.num 1))

-- `;` 은 오른쪽 결합이다.
#guard ⟪ x := 1; y := 2; z := 3 ⟫ᶜ
        == Comm.seq (.assign "x" (.num 1))
             (Comm.seq (.assign "y" (.num 2)) (.assign "z" (.num 3)))

-- 반복의 본체는 닫는 괄호까지 뻗는다. 괄호가 없으면 `;` 의 앞쪽만 본체다.
#guard ⟪ while x ≤ 10 do (y := y + x; x := x + 1) ⟫ᶜ
        == Comm.wh (.cmp .le (.var "x") (.num 10))
             (Comm.seq (.assign "y" (.bin .add (.var "y") (.var "x")))
                       (.assign "x" (.bin .add (.var "x") (.num 1))))

#guard ⟪ while x ≤ 10 do y := y + x; x := x + 1 ⟫ᶜ
        == Comm.seq
             (Comm.wh (.cmp .le (.var "x") (.num 10))
                      (.assign "y" (.bin .add (.var "y") (.var "x"))))
             (.assign "x" (.bin .add (.var "x") (.num 1)))

-- 불 식은 양화사 없는 단언이다.
#guard ⟪ 0 < x ∧ x < 10 ⟫ᵇ
        == BoolExp.bin .and (.cmp .lt (.num 0) (.var "x")) (.cmp .lt (.var "x") (.num 10))

-- `newvar` 의 초기값은 결합 범위 밖이다. 바깥의 `x` 를 읽는다.
#guard ⟪ newvar x := x + 1 in y := x ⟫ᶜ
        == Comm.newvar "x" (.bin .add (.var "x") (.num 1)) (.assign "y" (.var "x"))

-- Reynolds §2.1 의 예 — 계승.
#guard ⟪ y := 1; while x > 0 do (y := y × x; x := x - 1) ⟫ᶜ
        == Comm.seq (.assign "y" (.num 1))
             (Comm.wh (.cmp .gt (.var "x") (.num 0))
               (Comm.seq (.assign "y" (.bin .mul (.var "y") (.var "x")))
                         (.assign "x" (.bin .sub (.var "x") (.num 1)))))

end Reynolds.Answers.Ch02
