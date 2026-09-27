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
set_option verso.exampleModule "Reynolds.Answers.Ch02.ArithErrors"

#doc (Manual) "§2.7 산술 오류" =>
%%%
tag := "ch02-arith-errors"
file := "ch02-arith-errors"
number := false
%%%

Reynolds는 0으로 나누기와 정수 범위 넘침(overflow)을 함께 다룬다(§2.7, pp. 47–48).
언어 설계의 선택은 오류를 검사해 알릴지, 검사하지 않고 하드웨어의 결과를 사용할지다.
대부분의 응용에서는 잘못된 결과보다 오류 보고가 낫다는 이유로 검사를 권한다.

오류를 검사하지 않는 경우에는 실제 연산을 정확한 전함수로 기술하면 이 장의 의미론을
쓸 수 있다. 같은 입력에는 같은 결과를 내야 한다. 이 조건은 `x ÷ 0`뿐 아니라 범위를
넘는 덧셈에도 적용된다(p. 48).

오류 검출을 표현하려면 식의 결과에 오류 값을 추가하는 등의 확장이 필요하다. 책은 이를
§11.6으로 미루고, 여기서는 다음 장의 술어 논리와의 연결을 유지하기 위해 식의 오류
결과를 다루지 않는다. 언어 설계상의 권고와 이번 장에서 다루는 의미론의 범위를 구별해야 한다.

# 선택을 매개변수로 뺀다
%%%
tag := "ch02-zero-division"
file := "ch02-zero-division"
number := false
%%%

검사하지 않는 연산에 관한 주장을 확인하려고 선택을 인자로 만든다.

```anchor ZeroDivision (module := Reynolds.Answers.Ch02.ArithErrors)
/--
오류를 검사하지 않을 때 0인 제수에서 `÷`와 `rem`이 내놓을 값(§2.7, p. 48).

두 필드는 `Int → Int`이므로 각 입력에 결과 하나를 정한다. 어떤 전함수를 선택하든
성립하는 등식과 그 선택을 관찰하는 식을 이 매개변수로 구분한다.
-/
structure ZeroDivision where
  /-- `a ÷ 0` 의 값. -/
  divZero : Int → Int
  /-- `a rem 0` 의 값. -/
  remZero : Int → Int
```

이 파일은 책의 논의 중 0인 제수만 매개변수화한다. 덧셈 등에는 범위 제한 없는 `Int`를
쓰므로 하드웨어의 범위 넘침까지 모형화하지는 않는다.

# 왜 축소판인가
%%%
tag := "ch02-arith-mini"
file := "ch02-arith-mini"
number := false
%%%

매개변수화를 이 절 안에서만 한다. 본 의미론 전체를 `ZeroDivision`으로 매개변수화하면
앞 절들의 모든 정리에 쓸데없는 인자가 붙는다. 여기서 확인하려는 것은 나눗셈의 선택이
무엇을 바꾸고 무엇을 안 바꾸는가 하나뿐이므로, 그 질문에 필요한 만큼만 언어를 다시
만든다.

```anchor AExp (module := Reynolds.Answers.Ch02.ArithErrors)
/-- 축소판 정수 식. `div` 와 `rem` 만 선택을 본다. -/
inductive AExp (V : Type u) where
  /-- 정수 상수. -/
  | num : Int → AExp V
  /-- 변수. -/
  | var : V → AExp V
  /-- 전연산 `+`, `-`, `×`. 0 에서 문제가 없다. -/
  | bin : IntOp → AExp V → AExp V → AExp V
  /-- 나눗셈. 제수가 0 이면 선택을 본다. -/
  | div : AExp V → AExp V → AExp V
  /-- 나머지. 제수가 0 이면 선택을 본다. -/
  | rem : AExp V → AExp V → AExp V

/-- 선택 `A` 아래에서의 식의 값. 제수가 0 인 자리에서만 `A` 가 쓰인다. -/
def AExp.eval (A : ZeroDivision) : AExp V → State V → Int
  | .num n,        _ => n
  | .var v,        σ => σ v
  | .bin op e₀ e₁, σ => op.denote (e₀.eval A σ) (e₁.eval A σ)
  | .div e₀ e₁,    σ =>
      if e₁.eval A σ = 0 then A.divZero (e₀.eval A σ)
      else e₀.eval A σ / e₁.eval A σ
  | .rem e₀ e₁,    σ =>
      if e₁.eval A σ = 0 then A.remZero (e₀.eval A σ)
      else e₀.eval A σ % e₁.eval A σ
```

전연산(`+`, `-`, `×`)은 1장의 `IntOp`를 그대로 쓰고, 0에서 문제가 생기는 두 연산만
따로 생성자를 준다. 문법에서부터 갈라 두면 어느 절이 선택을 보는지가 눈에 띈다.

`while`도 뺐다. 산술 오류는 비종료와 무관한 주제이고, 빼면 명령의 뜻이
`State V → State V`인 _전함수_가 되어 `Σ⊥`도 고정점도 없이 등식이 깔끔해진다.

# "선택을 관찰하는가"
%%%
tag := "ch02-indep"
file := "ch02-indep"
number := false
%%%

이 절의 물음을 술어 하나로 적는다.

```anchor Indep (module := Reynolds.Answers.Ch02.ArithErrors)
/-- 식이 선택과 무관하다 — 어떤 두 선택에서도 같은 값을 낸다. -/
def AExp.Indep (e : AExp V) : Prop :=
  ∀ (A A' : ZeroDivision) (σ : State V), e.eval A σ = e.eval A' σ

/-- 불 식이 선택과 무관하다. -/
def ABExp.Indep (b : ABExp V) : Prop :=
  ∀ (A A' : ZeroDivision) (σ : State V), b.eval A σ = b.eval A' σ

/-- 명령이 선택과 무관하다. -/
def AComm.Indep (c : AComm V) : Prop :=
  ∀ (A A' : ZeroDivision) (σ : State V), c.eval A σ = c.eval A' σ
```

어떤 두 선택에서도 같은 것을 내놓으면 그 구는 선택을 관찰하지 않는다.

# 관찰하지 않는 등식들
%%%
tag := "ch02-indep-eqs"
file := "ch02-indep-eqs"
number := false
%%%

Reynolds가 드는 예들이다. 어느 것도 `÷ 0`의 _구체적인 값_을 쓰지 않는다.

* `e × 0`은 언제나 0이다. 곱해지는 쪽이 `÷ 0`을 품고 있어도 상관없다.
* `e = e`는 언제나 참이다. 값을 _모르고도_ 등식을 말할 수 있다는 것이 요점이다.
* `if b then c else c`는 `c`와 같다. 어느 쪽으로 가든 같은 곳에 닿는다.
* 덮어써지는 대입은 사라진다.

마지막 것만 조건이 붙는다.

```anchor deadAssign (module := Reynolds.Answers.Ch02.ArithErrors)
/--
**덮어써지는 대입은 사라진다.** `y ∉ FV(e)` 이면 `y := d; y := e ≡ y := e`.

`d` 가 `x ÷ 0` 이어도 좋다 — 그 값은 곧바로 덮어써지고 아무 데도 쓰이지 않는다.
`y ∉ FV(e)` 가 필요한 이유는 `e` 가 `y` 를 읽으면 덮어쓰기 전의 값을 보기 때문이다.

증명은 두 조각이다. 일치 정리로 `e` 의 값이 `y` 를 덮어쓴 상태에서도 같음을 보이고,
같은 자리에 두 번 대입한 것이 한 번 대입한 것과 같음(`Function.update_idem`)을 쓴다.
-/
@[exercise "§2.7 dead-assign" 2]
theorem AComm.eval_assign_overwrite (A : ZeroDivision) (v : V) (d e : AExp V)
    (h : v ∉ e.fv) (σ : State V) :
    (AComm.seq (.assign v d) (.assign v e)).eval A σ = (AComm.assign v e).eval A σ := by
  change (σ[v := d.eval A σ])[v := e.eval A (σ[v := d.eval A σ])] = σ[v := e.eval A σ]
  have he : e.eval A (σ[v := d.eval A σ]) = e.eval A σ := by
    refine AExp.coincidence A e _ σ ?_
    intro u hu
    have hune : u ≠ v := fun hEq => h (hEq ▸ hu)
    exact State.subst_of_ne _ _ _ _ hune
  rw [he]
  simp [State.subst_def, Function.update_idem]
```

`y ∉ FV(e)`가 필요한 이유는 `e`가 `y`를 읽으면 덮어쓰기 전의 값을 보기 때문이다.
이것으로 `y := x ÷ 0; y := 3`이 선택과 무관함을 얻는다. `÷ 0`이 구문에 버젓이 있는데도
뜻이 선택에 의존하지 않는 프로그램이다. 계산된 값이 쓰이지 않으면 그 값이 무엇인지는
아무도 모른다.

# 관찰하는 식
%%%
tag := "ch02-not-indep"
file := "ch02-not-indep"
number := false
%%%

앞 절의 등식들이 "선택과 무관하다"고 말할 수 있으려면, 무관하지 _않은_ 것이 실제로
있어야 한다. 없다면 매개변수화가 헛일이다.

```anchor notIndep (module := Reynolds.Answers.Ch02.ArithErrors)
omit [DecidableEq V] in
/--
**`x ÷ 0` 은 선택을 관찰한다.**

두 선택을 들이댄다. 하나는 0 을 돌려주고 하나는 1 을 돌려준다. 같은 상태에서 값이
달라지므로 이 식의 뜻은 선택 없이는 정해지지 않는다.

이것이 있어야 앞 절의 `Indep` 들이 내용 있는 주장이 된다 — 모든 식이 무관하다면
매개변수화할 이유가 없다. Reynolds 의 요구("함수이기만 하면 된다")가 **무언가를 정말로
요구한다**는 확인이다.
-/
@[exercise "§2.7 not-indep" 2]
theorem AExp.not_indep_div_zero (v : V) : ¬ (AExp.div (.var v) (.num 0) : AExp V).Indep := by
  intro hindep
  have h := hindep ⟨fun _ => 0, fun _ => 0⟩ ⟨fun _ => 1, fun _ => 0⟩ (State.const 0)
  simp [AExp.eval] at h
```

이것이 있어야 Reynolds의 요구가 _무언가를 정말로 요구한다_는 확인이 된다.

# Lean의 `Int` 나눗셈은 이미 전함수다
%%%
tag := "ch02-lean-int-div"
file := "ch02-lean-int-div"
number := false
%%%

스터디에서 반드시 나오는 질문이다. Lean의 `/`와 `%`는 Euclid 나눗셈(`Int.ediv`,
`Int.emod`)이고, 나머지가 _언제나 0 이상_이다.

```
(-7) / 2 = -4,   (-7) % 2 = 1
7 / (-2) = -3,   7 % (-2) = 1
(-7) / (-2) = 4, (-7) % (-2) = 1
```

C·Java의 `tdiv`/`tmod`는 0 쪽으로 자르므로 나머지 부호가 피제수를 따르고
(`(-7).tdiv 2 = -3`, `tmod = -1`), Python의 `fdiv`/`fmod`는 바닥이라 나머지 부호가
제수를 따른다(`(7).fdiv (-2) = -4`, `fmod = -1`).

그리고 결정적으로 `5 / 0 = 0`이고 `5 % 0 = 5`다. *Reynolds가 하라는 선택을 표준
라이브러리가 벌써 해 두었다.*

```anchor leanChoice (module := Reynolds.Answers.Ch02.ArithErrors)
omit [DecidableEq V] in
/--
**축소판의 `÷` 는 Lean 의 선택 아래에서 Lean 의 `/` 와 같다.**

`ZeroDivision.leanChoice` 를 넣으면 `if d = 0` 갈래가 사라진다. Lean 의 `/` 가 이미
`a / 0 = 0` 이고 `%` 가 `a % 0 = a` 이기 때문이다 — 표준 라이브러리가 Reynolds 의
요구대로 전함수를 만들어 두었고, 그 선택이 무엇인지 이 등식이 드러낸다.
-/
@[exercise "§2.7 lean-choice" 1]
theorem AExp.eval_leanChoice (e₀ e₁ : AExp V) (σ : State V) :
    (AExp.div e₀ e₁).eval .leanChoice σ
        = e₀.eval .leanChoice σ / e₁.eval .leanChoice σ
      ∧ (AExp.rem e₀ e₁).eval .leanChoice σ
        = e₀.eval .leanChoice σ % e₁.eval .leanChoice σ := by
  by_cases h : e₁.eval (V := V) .leanChoice σ = 0
  · -- 제수가 0 인 갈래. Lean 의 `/` 와 `%` 가 0 에서 무엇을 내는지가 그대로 드러난다.
    refine ⟨?_, ?_⟩
    · simp only [AExp.eval, h]
      simp [ZeroDivision.leanChoice, Int.ediv_zero]
    · simp only [AExp.eval, h]
      simp [ZeroDivision.leanChoice, Int.emod_zero]
  · -- 제수가 0 이 아니면 선택이 아예 쓰이지 않는다.
    exact ⟨by simp only [AExp.eval, if_neg h], by simp only [AExp.eval, if_neg h]⟩
```

`ZeroDivision.leanChoice`를 넣으면 `if d = 0` 갈래가 사라진다. 표준 라이브러리가
Reynolds의 요구대로 전함수를 만들어 두었고, 그 선택이 무엇인지 이 등식이 드러낸다.
