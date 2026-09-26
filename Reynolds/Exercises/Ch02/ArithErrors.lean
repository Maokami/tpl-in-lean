/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Exercises.Ch02.Sugar2
-- `#guard`는 컴파일 시점에 계산한다 (AGENTS.md §10).
public meta import Reynolds.Prelude

/-!
# §2.7 산술 오류 — 0 으로 나누기

Reynolds §2.7 에 대응한다. 이 절은 대부분 산문이지만 한 가지는 반드시 형식화한다.

## 논점

`x ÷ 0` 을 어떻게 할 것인가? 셋 중 하나다.

1. 오류를 검사해서 프로그램을 멈춘다 (의미론에 새 결과 `error` 를 들인다).
2. 결과를 정하지 않는다 (의미 함수가 부분 함수가 된다).
3. **아무 값이나 정해 둔다.**

Reynolds 는 3 을 택하고, 거기 붙는 제약이 하나뿐임을 강조한다.

> *"The only restriction is that these operations must actually be functional.
> For example, `x ÷ 0` must be some integer function of `x`."*

즉 **무엇을 고르든 상관없지만 고르기는 해야 한다.** 함수여야 한다는 것, 그것이 전부다.

## 이 파일이 하는 일

그 주장을 확인하는 방법은 선택을 **매개변수로 빼는** 것이다. `ZeroDivision` 이 0 인
제수에서 `÷` 와 `rem` 이 내놓을 값을 담고, 축소판 의미론이 그것을 인자로 받는다.
그러면 "이 등식이 선택을 실제로 관찰하는가" 를 물을 수 있다.

- 관찰하지 않는 등식 — `(x+y) × 0 = 0`, `e = e`, `if b then c else c ≡ c`,
  `y := x ÷ 0; y := 3 ≡ y := 3`. 어떤 선택에서도 성립한다.
- 관찰하는 식 — `x ÷ 0` 자체. 두 선택이 다른 값을 내므로 `¬ Indep` 이다.

## 왜 축소판인가

매개변수화를 **이 파일 안에서만** 한다. 본 의미론 전체를 `ZeroDivision` 으로 매개변수화
하면 앞 절들의 모든 정리에 쓸데없는 인자가 붙는다. 여기서 확인하려는 것은 나눗셈의
선택이 무엇을 바꾸고 무엇을 안 바꾸는가 하나뿐이므로, 그 질문에 필요한 만큼만 언어를
다시 만든다. `while` 도 뺐다 — 산술 오류는 비종료와 무관한 주제이고, `while` 이 없으면
의미 함수가 `State V → State V` 로 전함수가 되어 등식이 깔끔해진다.

연산자 타입(`IntOp`, `Cmp`, `LogOp`)은 1·2 장 것을 그대로 쓴다. 바뀐 것은 식의 문법과
의미뿐이다.

## 읽는 순서
`Sugar2.lean` → 이 파일. 이후는 §2.8 (건전성과 완전 추상성).
-/

-- 이 파일의 `#guard` 가 Lean 의 `Int` 나눗셈 규약을 눈으로 보여 준다.
set_option linter.hashCommand false

@[expose] public section

namespace Reynolds.Exercises.Ch02

open Reynolds Reynolds.Answers.Ch01

universe u

variable {V : Type u} [DecidableEq V]

/-! ## 1. 선택을 매개변수로 빼기 -/

/--
0 인 제수에서 `÷` 와 `rem` 이 내놓을 값. Reynolds 가 "골라 두기만 하면 된다" 고 한 그것.

두 필드가 **임의의** `Int → Int` 라는 점이 핵심이다. 어떤 함수든 좋다는 것이 Reynolds 의
주장이고, 타입이 요구하는 것은 함수라는 사실 하나뿐이다 — 전함수여야 한다는 제약이
`Int → Int` 라는 타입에 이미 들어 있다.
-/
structure ZeroDivision where
  /-- `a ÷ 0` 의 값. -/
  divZero : Int → Int
  /-- `a rem 0` 의 값. -/
  remZero : Int → Int

/--
Lean 표준 라이브러리가 이미 하고 있는 선택. `a / 0 = 0`, `a % 0 = a`.

**Lean 의 `Int` 나눗셈은 이미 전함수다.** Reynolds 가 "골라야 한다" 고 말한 그 선택을
표준 라이브러리가 벌써 해 두었고, 그 선택이 이것이다. 아래 `eval_leanChoice` 가
이 축소판의 `÷` 가 Lean 의 `/` 와 같아짐을 확인한다.
-/
def ZeroDivision.leanChoice : ZeroDivision where
  divZero := fun _ => 0
  remZero := fun a => a

/-! ## 2. 축소판 식

1장의 `IntExp` 에 나눗셈과 나머지를 더했다. 전연산(`+`, `-`, `×`)은 `IntOp` 를 그대로
쓰고, 0 에서 문제가 생기는 두 연산만 따로 생성자를 준다 — 문법에서부터 갈라 두면
어느 절이 선택을 보는지가 눈에 띈다. -/

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

/-- 축소판 식의 자유 변수. 1장과 같은 모양이다. -/
def AExp.fv : AExp V → Finset V
  | .num _        => ∅
  | .var v        => {v}
  | .bin _ e₀ e₁  => e₀.fv ∪ e₁.fv
  | .div e₀ e₁    => e₀.fv ∪ e₁.fv
  | .rem e₀ e₁    => e₀.fv ∪ e₁.fv

/-- 축소판 판 일치 정리. 선택을 고정해 두면 1장 명제 1.1 과 같은 증명이다. -/
theorem AExp.coincidence (A : ZeroDivision) :
    ∀ (e : AExp V) (σ σ' : State V), (∀ w ∈ e.fv, σ w = σ' w) → e.eval A σ = e.eval A σ' := by
  intro e
  induction e with
  | num n => intro _ _ _; rfl
  | var v => intro _ _ h; exact h v (by simp [AExp.fv])
  | bin op e₀ e₁ ih₀ ih₁ =>
      intro σ σ' h
      simp [AExp.eval, ih₀ σ σ' fun w hw => h w (by simp [AExp.fv, hw]),
        ih₁ σ σ' fun w hw => h w (by simp [AExp.fv, hw])]
  | div e₀ e₁ ih₀ ih₁ =>
      intro σ σ' h
      simp [AExp.eval, ih₀ σ σ' fun w hw => h w (by simp [AExp.fv, hw]),
        ih₁ σ σ' fun w hw => h w (by simp [AExp.fv, hw])]
  | «rem» e₀ e₁ ih₀ ih₁ =>
      intro σ σ' h
      simp [AExp.eval, ih₀ σ σ' fun w hw => h w (by simp [AExp.fv, hw]),
        ih₁ σ σ' fun w hw => h w (by simp [AExp.fv, hw])]

/-! ## 3. 축소판 불 식과 명령

`while` 을 뺐으므로 명령의 뜻이 `State V → State V` 인 **전함수**다. `Σ⊥` 도 고정점도
필요 없다 — 이 절의 주제가 비종료와 무관하기 때문이다. -/

/-- 축소판 불 식. 비교와 논리 결합자뿐이다. -/
inductive ABExp (V : Type u) where
  /-- 참. -/
  | tru
  /-- 거짓. -/
  | fls
  /-- 비교. -/
  | cmp : Cmp → AExp V → AExp V → ABExp V
  /-- 부정. -/
  | not : ABExp V → ABExp V
  /-- 논리 결합. -/
  | bin : LogOp → ABExp V → ABExp V → ABExp V

/-- 선택 `A` 아래에서의 불 식의 값. -/
def ABExp.eval (A : ZeroDivision) : ABExp V → State V → Bool
  | .tru,          _ => true
  | .fls,          _ => false
  | .cmp c e₀ e₁,  σ => c.denoteBool (e₀.eval A σ) (e₁.eval A σ)
  | .not b,        σ => !b.eval A σ
  | .bin op b₀ b₁, σ => op.denoteBool (b₀.eval A σ) (b₁.eval A σ)

/-- 축소판 명령. `while` 이 없어서 뜻이 전함수다. -/
inductive AComm (V : Type u) where
  /-- 대입. -/
  | assign : V → AExp V → AComm V
  /-- 아무것도 하지 않는다. -/
  | skip
  /-- 순차 합성. -/
  | seq : AComm V → AComm V → AComm V
  /-- 조건. -/
  | ite : ABExp V → AComm V → AComm V → AComm V

/-- 선택 `A` 아래에서의 명령의 뜻. `Σ⊥` 가 아니라 `Σ` 로 간다 — `while` 이 없어서다. -/
def AComm.eval (A : ZeroDivision) : AComm V → State V → State V
  | .assign v e,  σ => σ[v := e.eval A σ]
  | .skip,        σ => σ
  | .seq c₀ c₁,   σ => c₁.eval A (c₀.eval A σ)
  | .ite b c₀ c₁, σ => if b.eval A σ then c₀.eval A σ else c₁.eval A σ

/-! ## 4. "선택을 관찰하는가"

이 절의 물음을 술어 하나로 적는다. 어떤 두 선택에서도 같은 것을 내놓으면 그 구는
선택을 관찰하지 않는다. -/

/-- 식이 선택과 무관하다 — 어떤 두 선택에서도 같은 값을 낸다. -/
def AExp.Indep (e : AExp V) : Prop :=
  ∀ (A A' : ZeroDivision) (σ : State V), e.eval A σ = e.eval A' σ

/-- 불 식이 선택과 무관하다. -/
def ABExp.Indep (b : ABExp V) : Prop :=
  ∀ (A A' : ZeroDivision) (σ : State V), b.eval A σ = b.eval A' σ

/-- 명령이 선택과 무관하다. -/
def AComm.Indep (c : AComm V) : Prop :=
  ∀ (A A' : ZeroDivision) (σ : State V), c.eval A σ = c.eval A' σ

/-! ## 5. 선택을 관찰하지 않는 등식들

Reynolds 가 드는 예들이다. 어느 것도 `÷ 0` 의 **구체적인 값**을 쓰지 않는다 — 값이
0 과 곱해져 사라지거나, 자기 자신과 비교되거나, 덮어써지거나, 양쪽 가지가 같거나. -/

omit [DecidableEq V] in
/--
**0 을 곱하면 무엇이었든 0 이다.** 곱해지는 쪽이 `÷ 0` 을 품고 있어도 상관없다.

`(x + y) × 0 = 0` 이 Reynolds 의 예인데, 왼쪽 인자는 아무 식이나 되어도 된다.
-/
theorem AExp.indep_mul_zero (e : AExp V) : (AExp.bin .mul e (.num 0)).Indep := by
  intro A A' σ
  simp [AExp.eval, IntOp.denote]

omit [DecidableEq V] in
/--
**자기 자신과의 비교는 언제나 참이다.** `x ÷ 0 = x ÷ 0` 이 Reynolds 의 예다.

선택이 무엇이든 양변이 같은 값이므로 비교 결과가 `true` 로 고정된다. 값을 **모르고도**
등식을 말할 수 있다는 것이 요점이다.
-/
theorem ABExp.indep_cmp_self (e : AExp V) : (ABExp.cmp .eq e e).Indep := by
  intro A A' σ
  simp [ABExp.eval, Cmp.denoteBool]

/--
**같은 가지를 둘 다 두면 조건은 아무래도 좋다.** `if b then c else c ≡ c`.

조건 `b` 가 `÷ 0` 을 품어도 결과가 안 바뀐다 — 어느 쪽으로 가든 같은 곳에 닿기 때문이다.
-/
theorem AComm.eval_ite_self (A : ZeroDivision) (b : ABExp V) (c : AComm V) (σ : State V) :
    (AComm.ite b c c).eval A σ = c.eval A σ := by
  simp [AComm.eval]

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
  -- 먼저 볼 것: 바로 위 `AExp.coincidence` (완성되어 있다).
  -- 힌트 1: `change` 로 양변을 상태 갱신까지 펼친다. `while` 이 없어 전함수라 `Option` 이 없다.
  -- 힌트 2: `e` 의 값이 `v` 를 덮어쓴 상태에서도 같음을 일치 정리로 보인다.
  --         `u ∈ e.fv` 이면 `u ≠ v` (가정 `h` 때문) 이므로 `State.subst_of_ne`.
  -- 힌트 3: 같은 자리에 두 번 대입한 것은 한 번 대입한 것과 같다.
  --         `simp [State.subst_def, Function.update_idem]`.
  sorry


/--
**0 으로 나누기를 품고도 선택과 무관한 프로그램.** `y := x ÷ 0; y := 3`.

`÷ 0` 이 구문에 버젓이 있는데도 뜻이 선택에 의존하지 않는다. 계산된 값이 쓰이지
않으면 그 값이 무엇인지는 아무도 모른다 — 이것이 Reynolds 가 3번 길을 택해도 되는
이유다.
-/
theorem AComm.indep_dead_div (v u : V) :
    (AComm.seq (.assign v (.div (.var u) (.num 0))) (.assign v (.num 3))).Indep := by
  intro A A' σ
  rw [AComm.eval_assign_overwrite A v _ _ (by simp [AExp.fv]) σ,
    AComm.eval_assign_overwrite A' v _ _ (by simp [AExp.fv]) σ]
  rfl

/-! ## 6. 선택을 관찰하는 식

앞 절의 등식들이 "선택과 무관하다" 고 말할 수 있으려면, 무관하지 **않은** 것이 실제로
있어야 한다. 없다면 매개변수화가 헛일이다. -/

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
  -- 힌트: `Indep` 은 "어떤 두 선택에서도 같다" 이므로, 다른 값을 내는 선택 둘을 들이대면 된다.
  --       `⟨fun _ => 0, fun _ => 0⟩` 과 `⟨fun _ => 1, fun _ => 0⟩`, 상태는 `State.const 0`.
  --       `simp [AExp.eval] at` 으로 `0 = 1` 을 끌어내면 끝난다.
  sorry


/-! ## 7. Lean 의 `Int` 나눗셈 규약

스터디에서 반드시 나오는 질문이다. Lean 의 `/` 와 `%` 는 **Euclid 나눗셈**(`Int.ediv`,
`Int.emod`)이고, 나머지가 **언제나 0 이상**이다. C·Java 의 `tdiv`/`tmod`(0 쪽으로 자름),
Python 의 `fdiv`/`fmod`(바닥)와 음수에서 갈린다. -/

-- Lean 의 `/`, `%` — 나머지가 늘 0 이상이다.
#guard ((-7 : Int) / 2, (-7 : Int) % 2) == (-4, 1)
#guard ((7 : Int) / (-2), (7 : Int) % (-2)) == (-3, 1)
#guard ((-7 : Int) / (-2), (-7 : Int) % (-2)) == (4, 1)

-- C·Java 식(0 쪽으로 자름): 나머지 부호가 피제수를 따른다.
#guard ((-7 : Int).tdiv 2, (-7 : Int).tmod 2) == (-3, -1)

-- Python 식(바닥): 나머지 부호가 제수를 따른다.
#guard ((7 : Int).fdiv (-2), (7 : Int).fmod (-2)) == (-4, -1)

-- 그리고 Lean 의 나눗셈은 **이미 전함수**다. Reynolds 의 선택이 이미 되어 있다.
#guard ((5 : Int) / 0, (5 : Int) % 0) == (0, 5)

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
  -- 힌트 1: 제수가 0 인지로 나눈다 (`by_cases h : e₁.eval (V := V) .leanChoice σ = 0`).
  -- 힌트 2: 0 이 아니면 선택이 아예 안 쓰인다 — `simp only [AExp.eval, if_neg h]`.
  -- 힌트 3: 0 이면 Lean 의 규약이 드러난다. `Int.ediv_zero` (`a / 0 = 0`) 와
  --         `Int.emod_zero` (`a % 0 = a`) 가 `ZeroDivision.leanChoice` 의 선택과 맞물린다.
  sorry


/-! ## 8. 여기서 어디로 가나

Reynolds 의 주장을 확인했다. 0 으로 나눈 값을 **무엇으로 정하든** 그것을 관찰하지 않는
등식은 그대로 성립하고, 관찰하는 식은 선택 없이는 뜻이 없다. 제약은 "함수일 것" 하나뿐
이며, 그것은 `Int → Int` 라는 타입이 이미 강제한다.

다음은 §2.8 이다. 지금까지 만든 의미론이 **충분히 추상적인가** 를 묻는다 — 뜻이 같으면
어느 문맥에 넣어도 같게 행동하는가(건전성), 그리고 어느 문맥에서도 같게 행동하면 뜻이
같은가(완전 추상성). 그 답이 *무엇을 관찰하기로 했는가* 에 달렸다는 것이 이 장의
마지막 교훈이고, 이 절에서 "관찰한다" 를 술어로 적어 본 것이 그 준비가 된다. -/

end Reynolds.Exercises.Ch02
