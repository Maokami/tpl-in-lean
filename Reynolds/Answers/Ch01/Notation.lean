/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Answers.Ch01.Semantics

/-!
# §1.1 구체 구문 — 객체 언어를 Lean 안에서 쓰기

Reynolds §1.1 의 추상 문법(abstract grammar)에 대응한다.

## 배경

Reynolds 는 추상 구문과 구체 표현을 나눈 뒤, 그래도 표현은 필요하다고 말한다.

> *"although phrases may be conceptually abstract, one still needs a notation for them.
> Thus the study of semantics has traditionally used a compromise formalism called an
> abstract grammar, which defines sets of abstract phrases that are independent of any
> particular representation, but which also provides a simple representation for these
> phrases without such complications as precedence levels."*

책에서는 이것이 타협이다. 문법을 적어 두고 사람이 읽는다.
Lean 에서는 매크로로 구현할 수 있어서, 구체 구문이 실제로 추상 구문으로 번역된다.

## 무엇이 달라지는가

이 파일이 없으면 예제가 이렇게 생긴다.

```lean
Assert.quant .ex "y" (.cmp .gt (.var "y") (.bin .add (.var "x") (.num 1)))
```

있으면 이렇게 쓴다.

```lean
⟪ ∃ y, y > x + 1 ⟫ₐ
```

## 표기 규약

| 문법 | 뜻 |
|---|---|
| `⟪ … ⟫ₑ` | 정수 식 `IntExp String` |
| `⟪ … ⟫ₐ` | 단언 `Assert String` |
| `%t` | Lean 항 `t` 를 그대로 끼워 넣는다 (메타 수준 삽입) |

식별자는 객체 변수가 된다. `x` 는 `IntExp.var "x"` 다.
`%` 로 시작하는 것만 메타 수준으로 넘어간다. `Background.lean` §2 의 구분이
여기서 문법으로 드러난다.

## 우선순위

Reynolds §1.1 의 우선순위 목록을 그대로 옮겼다. 전부 좌결합이다.

```
(× ÷ rem)  (-단항 + -이항)  (= ≠ < ≤ > ≥)  ¬  ∧  ∨  ⇒  ⇔
```

양화사의 본문은 "첫 정지 기호나 둘러싼 구의 끝까지" 뻗는다.
여기서는 괄호 `⟫ₐ` 나 `)` 가 그 역할을 한다.

## 변수 타입을 `String` 으로 고정한 이유

본문 정의는 변수 타입 `V` 에 대해 다형이지만(`Prelude.lean` 참고),
구체 구문에서 식별자를 쓰려면 어딘가로 보내야 한다. 문자열이 가장 읽힌다.
다른 변수 타입이 필요하면 생성자를 직접 쓰면 된다.
-/

@[expose] public section

namespace Reynolds.Answers.Ch01

open Reynolds

/-! ## 구문 범주 -/

/-- 객체 언어의 정수 식. Reynolds 의 ⟨intexp⟩. -/
declare_syntax_cat reyE

/-- 객체 언어의 단언. Reynolds 의 ⟨assert⟩. -/
declare_syntax_cat reyA

/-! ### 정수 식 -/

/-- 객체 변수. 식별자가 변수 이름이 된다. -/
syntax:max ident : reyE
/-- 정수 상수. -/
syntax:max num : reyE
/-- 괄호. -/
syntax:max "(" reyE ")" : reyE
/-- Lean 항을 정수 식으로 끼워 넣는다. -/
syntax:max "%" term:max : reyE
/-- 단항 마이너스. -/
syntax:75 "-" reyE:75 : reyE
/-- 곱셈. -/
syntax:70 reyE:70 " × " reyE:71 : reyE
/-- 나눗셈. -/
syntax:70 reyE:70 " ÷ " reyE:71 : reyE
/-- 나머지. -/
syntax:70 reyE:70 " rem " reyE:71 : reyE
/-- 덧셈. -/
syntax:65 reyE:65 " + " reyE:66 : reyE
/-- 뺄셈. -/
syntax:65 reyE:65 " - " reyE:66 : reyE

/-! ### 단언 -/

/-- 참. 객체 언어의 `true` (Lean 의 것과 겹치지 않게 `tt` 로 쓴다). -/
syntax:max "tt" : reyA
/-- 거짓. -/
syntax:max "ff" : reyA
/-- 괄호. -/
syntax:max "(" reyA ")" : reyA
/-- Lean 항을 단언으로 끼워 넣는다. -/
syntax:max "%" term:max : reyA
/-- 같음. -/
syntax:50 reyE " = " reyE : reyA
/-- 다름. -/
syntax:50 reyE " ≠ " reyE : reyA
/-- 작음. -/
syntax:50 reyE " < " reyE : reyA
/-- 작거나 같음. -/
syntax:50 reyE " ≤ " reyE : reyA
/-- 큼. -/
syntax:50 reyE " > " reyE : reyA
/-- 크거나 같음. -/
syntax:50 reyE " ≥ " reyE : reyA
/-- 부정. -/
syntax:40 "¬" reyA:40 : reyA
/-- 연언. -/
syntax:35 reyA:35 " ∧ " reyA:36 : reyA
/-- 선언. -/
syntax:30 reyA:30 " ∨ " reyA:31 : reyA
/-- 함의. -/
syntax:25 reyA:25 " ⇒ " reyA:26 : reyA
/-- 동치. -/
syntax:20 reyA:20 " ⇔ " reyA:21 : reyA
/-- 전칭 양화. 본문은 둘러싼 구의 끝까지 뻗는다. -/
syntax:10 "∀" ident ", " reyA:10 : reyA
/-- 존재 양화. -/
syntax:10 "∃" ident ", " reyA:10 : reyA

/-! ## 진입점

두 표기가 여는 괄호를 공유하지만 닫는 기호가 달라서 파서가 갈래를 고를 수 있다. -/

/-- 객체 언어의 정수 식을 쓴다. `⟪ x + 1 ⟫ₑ : IntExp String`. -/
syntax:max "⟪" reyE "⟫ₑ" : term

/-- 객체 언어의 단언을 쓴다. `⟪ ∀ y, y ≤ x ⟫ₐ : Assert String`. -/
syntax:max "⟪" reyA "⟫ₐ" : term

/-! ## 번역 규칙

각 규칙이 Reynolds 의 생성 규칙 하나에 대응한다.

생성자 이름을 `Lean.mkIdent` 로 만드는 이유가 있다. Lean 매크로는 위생적(hygienic)이라
`` `(IntExp.var …) `` 이라고 쓰면 **매크로를 정의한 자리**에서 이름이 해석된다.
그러면 이 DSL 은 `Reynolds.Answers.Ch01.IntExp` 로 못 박히고,
같은 정의를 다른 이름공간에 둔 `Reynolds.Exercises.Ch01` 에서는 타입이 안 맞는다.

`mkIdent` 로 만든 이름은 **쓰는 자리**에서 해석된다. 그래서 두 트리 어디서 써도
그 트리의 정의로 풀린다. 대신 `open` 이 안 되어 있으면 이름을 못 찾는다. -/

open Lean in
macro_rules
  | `(⟪ $x:ident ⟫ₑ)   => `($(mkIdent `IntExp.var) $(Lean.quote x.getId.toString))
  | `(⟪ $n:num ⟫ₑ)     => `($(mkIdent `IntExp.num) $n)
  | `(⟪ ( $e:reyE ) ⟫ₑ) => `(⟪ $e ⟫ₑ)
  | `(⟪ % $t:term ⟫ₑ)  => `(($t : $(mkIdent `IntExp) String))
  | `(⟪ - $e:reyE ⟫ₑ)  => `($(mkIdent `IntExp.neg) ⟪ $e ⟫ₑ)
  | `(⟪ $a:reyE × $b:reyE ⟫ₑ)   => `($(mkIdent `IntExp.bin) $(mkIdent `IntOp.mul) ⟪ $a ⟫ₑ ⟪ $b ⟫ₑ)
  | `(⟪ $a:reyE ÷ $b:reyE ⟫ₑ)   => `($(mkIdent `IntExp.bin) $(mkIdent `IntOp.div) ⟪ $a ⟫ₑ ⟪ $b ⟫ₑ)
  | `(⟪ $a:reyE rem $b:reyE ⟫ₑ) => `($(mkIdent `IntExp.bin) $(mkIdent `IntOp.rem) ⟪ $a ⟫ₑ ⟪ $b ⟫ₑ)
  | `(⟪ $a:reyE + $b:reyE ⟫ₑ)   => `($(mkIdent `IntExp.bin) $(mkIdent `IntOp.add) ⟪ $a ⟫ₑ ⟪ $b ⟫ₑ)
  | `(⟪ $a:reyE - $b:reyE ⟫ₑ)   => `($(mkIdent `IntExp.bin) $(mkIdent `IntOp.sub) ⟪ $a ⟫ₑ ⟪ $b ⟫ₑ)

open Lean in
macro_rules
  | `(⟪ tt ⟫ₐ)          => `($(mkIdent `Assert.tru))
  | `(⟪ ff ⟫ₐ)          => `($(mkIdent `Assert.fls))
  | `(⟪ ( $p:reyA ) ⟫ₐ) => `(⟪ $p ⟫ₐ)
  | `(⟪ % $t:term ⟫ₐ)   => `(($t : $(mkIdent `Assert) String))
  | `(⟪ $a:reyE = $b:reyE ⟫ₐ) => `($(mkIdent `Assert.cmp) $(mkIdent `Cmp.eq) ⟪ $a ⟫ₑ ⟪ $b ⟫ₑ)
  | `(⟪ $a:reyE ≠ $b:reyE ⟫ₐ) => `($(mkIdent `Assert.cmp) $(mkIdent `Cmp.ne) ⟪ $a ⟫ₑ ⟪ $b ⟫ₑ)
  | `(⟪ $a:reyE < $b:reyE ⟫ₐ) => `($(mkIdent `Assert.cmp) $(mkIdent `Cmp.lt) ⟪ $a ⟫ₑ ⟪ $b ⟫ₑ)
  | `(⟪ $a:reyE ≤ $b:reyE ⟫ₐ) => `($(mkIdent `Assert.cmp) $(mkIdent `Cmp.le) ⟪ $a ⟫ₑ ⟪ $b ⟫ₑ)
  | `(⟪ $a:reyE > $b:reyE ⟫ₐ) => `($(mkIdent `Assert.cmp) $(mkIdent `Cmp.gt) ⟪ $a ⟫ₑ ⟪ $b ⟫ₑ)
  | `(⟪ $a:reyE ≥ $b:reyE ⟫ₐ) => `($(mkIdent `Assert.cmp) $(mkIdent `Cmp.ge) ⟪ $a ⟫ₑ ⟪ $b ⟫ₑ)
  | `(⟪ ¬ $p:reyA ⟫ₐ)          => `($(mkIdent `Assert.not) ⟪ $p ⟫ₐ)
  | `(⟪ $p:reyA ∧ $q:reyA ⟫ₐ) => `($(mkIdent `Assert.bin) $(mkIdent `LogOp.and) ⟪ $p ⟫ₐ ⟪ $q ⟫ₐ)
  | `(⟪ $p:reyA ∨ $q:reyA ⟫ₐ) => `($(mkIdent `Assert.bin) $(mkIdent `LogOp.or) ⟪ $p ⟫ₐ ⟪ $q ⟫ₐ)
  | `(⟪ $p:reyA ⇒ $q:reyA ⟫ₐ) => `($(mkIdent `Assert.bin) $(mkIdent `LogOp.imp) ⟪ $p ⟫ₐ ⟪ $q ⟫ₐ)
  | `(⟪ $p:reyA ⇔ $q:reyA ⟫ₐ) => `($(mkIdent `Assert.bin) $(mkIdent `LogOp.iff) ⟪ $p ⟫ₐ ⟪ $q ⟫ₐ)
  | `(⟪ ∀ $x:ident , $p:reyA ⟫ₐ) =>
      `($(mkIdent `Assert.quant) $(mkIdent `Quant.all) $(Lean.quote x.getId.toString) ⟪ $p ⟫ₐ)
  | `(⟪ ∃ $x:ident , $p:reyA ⟫ₐ) =>
      `($(mkIdent `Assert.quant) $(mkIdent `Quant.ex) $(Lean.quote x.getId.toString) ⟪ $p ⟫ₐ)

end Reynolds.Answers.Ch01
