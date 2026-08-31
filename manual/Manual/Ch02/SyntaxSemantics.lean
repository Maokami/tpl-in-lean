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
set_option verso.exampleModule "Reynolds.Answers.Ch02.Syntax"

#doc (Manual) "§2.1~§2.2 구문과 의미 방정식" =>
%%%
tag := "ch02-syntax-semantics"
file := "ch02-syntax-semantics"
number := false
%%%

# §2.1 불 식과 명령
%%%
tag := "ch02-syntax"
file := "ch02-syntax"
number := false
%%%

2장의 언어에는 정수 식, 불 식, 명령이 있다. 정수 식은 1장의 `IntExp`를 그대로 쓴다.
불 식은 1장의 단언에서 양화사를 뺀 조각이고, 명령은 상태를 바꾸는 구문이다.

불 식(boolean expression)의 모양은 다음과 같다.

```anchor BoolExp (module := Reynolds.Answers.Ch02.Syntax)
/--
불 식(boolean expression). Reynolds §2.1 의 ⟨boolexp⟩.

1장의 `Assert` 에서 **양화사 절만 뺀 것**이다. 나머지 다섯 절은 글자까지 같다.

비교와 이항 논리 연산은 1장의 `Cmp`, `LogOp` 를 그대로 쓴다. 같은 기호를 두 번 정의하면
`Semantics.lean` 에서 의미도 두 번 정의해야 하고, 그러면 "불 식은 양화사 없는 단언" 이라는
Reynolds 의 말이 코드에서 사라진다.
-/
inductive BoolExp (V : Type u) where
  /-- 참 `true`. -/
  | tru
  /-- 거짓 `false`. -/
  | fls
  /-- 정수 비교 `e₀ ∼ e₁`. -/
  | cmp : Cmp → IntExp V → IntExp V → BoolExp V
  /-- 부정 `¬b`. -/
  | not : BoolExp V → BoolExp V
  /-- 이항 논리 연산 `b₀ ∘ b₁`. -/
  | bin : LogOp → BoolExp V → BoolExp V → BoolExp V
  deriving DecidableEq, Repr
```

여기서 양화사를 뺀 이유는 구문을 작게 만들기 위해서가 아니다. 정수 전체에 대한 양화가
있는 1장의 단언에는 모든 식의 참과 거짓을 계산하는 공통 절차를 줄 수 없다. 양화사가 없는
`BoolExp`는 유한한 구문 트리를 따라 각 절을 계산할 수 있다. 이 차이가 §2.2에서 결과 타입
`Prop`과 `Bool`의 차이로 나타난다.

명령(command)은 여섯 생성자로 정의한다.

```anchor Comm (module := Reynolds.Answers.Ch02.Syntax)
/--
명령(command). Reynolds §2.1 의 ⟨comm⟩ 과 §2.5 의 `newvar`.

`newvar v e c` 가 `newvar v := e in c` 다. **`v` 는 결합 발생(binding occurrence)이고
그 유효 범위는 `c` 뿐이다 — `e` 는 범위 밖이다.** 초기값 `e` 는 새 변수를 만들기 전에
바깥 상태에서 재기 때문이다. 1장의 합 식(연습 1.5)에서 상계가 범위 밖이었던 것과 같다.

이 장에서 결합이 등장하는 자리는 여기 하나뿐이다. §2.5 까지는 쓰지 않는다.
-/
inductive Comm (V : Type u) where
  /-- 대입 `v := e`. -/
  | assign : V → IntExp V → Comm V
  /-- 아무것도 하지 않는다. -/
  | skip
  /-- 순차 합성 `c₀ ; c₁`. -/
  | seq : Comm V → Comm V → Comm V
  /-- 조건 `if b then c₀ else c₁`. -/
  | ite : BoolExp V → Comm V → Comm V → Comm V
  /-- 반복 `while b do c`. 의미는 구문에 대한 구조적 재귀만으로 정의되지 않는다. -/
  | wh : BoolExp V → Comm V → Comm V
  /-- 변수 선언 `newvar v := e in c`. `v` 의 유효 범위는 `c` 다. -/
  | newvar : V → IntExp V → Comm V → Comm V
  deriving DecidableEq, Repr
```

`newvar`는 책에서 §2.5에 추가된다. Lean 타입을 중간에 다시 정의하면 §2.2~§2.4의 의미와
정리도 새 타입에 맞춰 복제해야 하므로, 이 저장소는 생성자를 처음부터 넣고 §2.5 전에는
사용하지 않는다. 현재 문서 범위에서 `newvar`는 이후 절을 위한 자리다.

`while`이 들어가도 `Comm` 값 자체는 유한한 트리다. 예를 들어
`while tt do skip`은 생성자 두 개를 자식으로 가진 작은 트리다. 끝나지 않는 것은 그 트리를
실행하는 과정이지 트리의 크기가 아니다.

# 구체 구문은 트리를 만드는 입구다
%%%
tag := "ch02-notation"
file := "ch02-notation"
number := false
%%%

`Notation.lean`의 DSL을 열면 다음처럼 쓸 수 있다.

```
⟪ y := 1; while x > 0 do (y := y × x; x := x - 1) ⟫ᶜ
```

세미콜론은 오른쪽으로 결합하고, 괄호가 반복문의 본체 범위를 정한다. 이 표기는 새 의미를
추가하지 않는다. 위 문장을 `Comm.seq`, `Comm.assign`, `Comm.wh`로 이루어진 트리로
번역한다. 이후의 의미 함수와 정리는 번역된 `Comm` 값만 본다.

# §2.2 불 식은 계산된다
%%%
tag := "ch02-bool-eval"
file := "ch02-bool-eval"
number := false
%%%

불 식의 의미는 상태를 받아 `Bool`을 내는 함수다.

```anchor BoolExp.eval (module := Reynolds.Answers.Ch02.Semantics)
/--
`⟦b⟧ᵇ σ` — 불 식의 뜻. Reynolds §2.2 의 `⟦-⟧boolexp ∈ ⟨boolexp⟩ → Σ → 𝔹`.

1장의 `Assert.eval` 과 절이 하나씩 대응하고, 결과 타입만 `Prop` 에서 `Bool` 로 바뀌었다.
그 차이가 `#eval` 로 돌릴 수 있느냐를 가른다.
-/
def BoolExp.eval {V : Type u} : BoolExp V → State V → Bool
  | .tru,         _ => true
  | .fls,         _ => false
  | .cmp c e₀ e₁, σ => c.denoteBool (⟦e₀⟧ₑ σ) (⟦e₁⟧ₑ σ)
  | .not b,       σ => !b.eval σ
  | .bin op b₀ b₁, σ => op.denoteBool (b₀.eval σ) (b₁.eval σ)
```

`State.const 3`에서 `x < 10`을 재면 `true`이고, `State.const 42`에서는 `false`다.
`boolExp_eval_iff` 정리는 같은 불 식을 1장의 단언으로 읽었을 때에도 참·거짓이 일치함을
증명한다. “양화사 없는 단언”이라는 설명을 구문 모양의 유사성에 그치지 않고 의미 수준에서
확인한 것이다.

# 명령의 결과에는 비종료가 들어간다
%%%
tag := "ch02-sigmabot"
file := "ch02-sigmabot"
number := false
%%%

상태 `σ`에서 명령을 실행한 결과는 새 상태일 수도 있고, 결과 상태가 없을 수도 있다.
이 두 경우를 `Option`으로 표현한다.

````anchor SigmaBot (module := Reynolds.Answers.Ch02.Semantics)
/--
`Σ⊥` — 상태 하나 또는 비종료. `none` 이 `⊥` 다.

이 타입은 결정적 언어의 정상 종료와 비종료만 구분한다. `none`을 실행 오류나 비결정적
결과로도 함께 읽지 않는다. Reynolds가 §2.7에서 산술 오류를 추가하면 의미 공간을 다시
매개변수화해야 하고, 비결정성은 7장에서 멱집합이나 멱영역과 같은 다른 구조를 요구한다.

`Option` 을 쓰는 것이 편의만은 아니다. Reynolds 가 §2.2 에서 손으로 도입하는 확장

```
f⊥⊥ x = if x = ⊥ then ⊥ else f x
```

이 정확히 `Option.bind` 다. 아래 `liftBot_eq_bind` 가 그것을 확인한다.
-/
abbrev SigmaBot (V : Type u) := Option (State V)
````

`none`의 뜻은 이 장의 범위에서 좁게 잡혀 있다.

: `some σ'`

  실행이 끝났고 결과 상태가 `σ'`이라는 정보다.

: `none`

  유한한 결과 상태를 얻지 못했다는 정보다. 연료 해석기에서는 실제 비종료와 연료 부족이
  모두 이 값으로 보인다.

이 구분은 §2.7에서 오류를 넣거나 7장에서 비결정성을 넣을 때 다시 확장해야 한다.
`Option` 하나가 모든 효과를 표현한다고 일반화하면 안 된다.

# 순차 합성은 `Option.bind`다
%%%
tag := "ch02-bind"
file := "ch02-bind"
number := false
%%%

`c₀ ; c₁`을 실행하려면 먼저 `c₀`이 끝나야 한다. `c₀`의 결과가 `some σ'`이면
`σ'`에서 `c₁`을 실행하고, `none`이면 `c₁`로 넘어갈 상태가 없다.

```
Option.bind none      k = none
Option.bind (some σ') k = k σ'
```

Reynolds의 순 확장 `f⊥⊥`가 이 두 식이고, Lean에서는 이미 `Option.bind`로 주어진다.
따라서 순차 합성의 의미 방정식은 다음처럼 읽힌다.

```
⟦c₀ ; c₁⟧ σ = Option.bind (⟦c₀⟧ σ) ⟦c₁⟧
```

이 식은 먼저 실행한 명령의 비종료가 뒤 명령으로 넘어가지 않는다는 점까지 표현한다.

# 의미 방정식은 아직 정의가 아니다
%%%
tag := "ch02-semantics-spec"
file := "ch02-semantics-spec"
number := false
%%%

§2.2에서는 의미 함수 `m`이 만족해야 할 여섯 방정식을 먼저 모은다.

```anchor IsSemantics (module := Reynolds.Answers.Ch02.Semantics)
/--
명령의 의미 함수가 만족해야 할 조건. Reynolds §2.2 의 의미 방정식 여섯 개를 그대로 적었다.

**정의가 아니라 명세(specification)다.** 이런 `m` 이 있는지, 있다면 하나뿐인지는
이 술어가 답하지 않는다. 앞의 다섯 방정식은 `m` 을 구문에 대한 재귀로 결정하지만,
`wh` 방정식은 양변에 같은 구가 나와서 그렇게 하지 못한다.

§2.4 에서 이 조건을 만족하는 `Comm.eval` 을 만들고 `Comm.eval_isSemantics` 를 증명한다.
-/
def IsSemantics {V : Type u} [DecidableEq V] (m : Comm V → State V → SigmaBot V) : Prop :=
  (∀ v e σ, m (.assign v e) σ = some (σ[v := ⟦e⟧ₑ σ]))
  ∧ (∀ σ, m .skip σ = some σ)
  ∧ (∀ c₀ c₁ σ, m (.seq c₀ c₁) σ = Option.bind (m c₀ σ) (m c₁))
  ∧ (∀ b c₀ c₁ σ, m (.ite b c₀ c₁) σ = if ⟦b⟧ᵇ σ then m c₀ σ else m c₁ σ)
  ∧ (∀ b c σ, m (.wh b c) σ = if ⟦b⟧ᵇ σ then Option.bind (m c σ) (m (.wh b c)) else some σ)
  ∧ (∀ v e c σ, m (.newvar v e c) σ = restore v σ (m c (σ[v := ⟦e⟧ₑ σ])))
```

대입, `skip`, 순차 합성, 조건문, `newvar`의 우변은 더 작은 명령의 뜻만 참조한다.
`while` 절만 같은 `while` 명령을 다시 참조한다. 그래서 `IsSemantics`는 의미 함수를
만드는 재귀 정의가 아니라, 후보 함수가 지켜야 할 명세다.

# 풀기 방정식의 해가 둘 이상 생긴다
%%%
tag := "ch02-unwinding"
file := "ch02-unwinding"
number := false
%%%

비유일성은 `while x ≠ 0 do x := x - 2`에서 드러난다. `x`가 0 이상의 짝수면 언젠가
0에 도달한다. 양의 홀수는 1에서 -1로 지나가고, 음수는 계속 작아지므로 0에 도달하지 않는다.

`decrTrue`는 끝나는 입력에서 `x = 0`인 상태를 내고 나머지에서는 `none`을 낸다.
`decrFake`는 끝나는 입력에서 같은 답을 내지만, 끝나지 않는 입력에서 `x = 999`인 상태를
낸다. 999라는 수에는 뜻이 없다. 방정식이 그 입력의 결과를 제한하지 않는다는 것을 보이기
위해 고른 임의의 값이다.

두 함수가 같은 풀기 방정식을 만족하고도 서로 다르다는 사실을 Lean에서 증명한다.

```anchor unwinding_not_unique (module := Reynolds.Answers.Ch02.Semantics)
/-- 한 걸음 간 상태. 네 갈래 계산에서 계속 쓴다. -/
theorem decr_step (f : State String → SigmaBot String) (σ : State String) :
    Option.bind (decrBody σ) f = f (σ["x" := σ "x" - 2]) := rfl

/-- 끝나는 상태에서 한 걸음 가도 여전히 끝나는 상태다. -/
theorem decrHalts_step {σ : State String} (hh : decrHalts σ) (h0 : σ "x" ≠ 0) :
    decrHalts (σ["x" := σ "x" - 2]) := by
  unfold decrHalts at hh ⊢
  simp only [State.subst_self]
  omega

/-- 끝나지 않는 상태에서 한 걸음 가도 여전히 끝나지 않는다. 홀수는 홀수로, 음수는 음수로. -/
theorem decrHalts_step_not {σ : State String} (hh : ¬ decrHalts σ) :
    ¬ decrHalts (σ["x" := σ "x" - 2]) := by
  unfold decrHalts at hh ⊢
  simp only [State.subst_self]
  omega

/-- 의도한 의미 후보 `decrTrue`는 풀기 방정식을 만족한다. -/
theorem unwindsDecr_true : UnwindsDecr decrTrue := by
  intro σ
  by_cases h0 : σ "x" = 0
  · -- 조건이 거짓이라 한 걸음도 가지 않는다.
    rw [if_neg (by simp [h0])]
    have hh : decrHalts σ := by unfold decrHalts; omega
    simp only [decrTrue, if_pos hh, State.subst_eq_self σ "x" h0]
  · rw [if_pos h0, decr_step]
    by_cases hh : decrHalts σ
    · simp only [decrTrue, if_pos hh, if_pos (decrHalts_step hh h0), State.subst_subst]
    · simp only [decrTrue, if_neg hh, if_neg (decrHalts_step_not hh)]

/--
대안으로 만든 `decrFake`도 풀기 방정식을 만족한다.

`decrTrue` 와 `decrFake` 는 끝나지 않는 상태에서 다른 답을 내지만 둘 다 같은 방정식을
만족한다. 종료하지 않는 입력에서는 우변이 다시 미지 함수에 돌아가므로, 방정식만으로는
그 입력의 결과를 제한하지 못한다.
-/
theorem unwindsDecr_fake : UnwindsDecr decrFake := by
  intro σ
  by_cases h0 : σ "x" = 0
  · rw [if_neg (by simp [h0])]
    have hh : decrHalts σ := by unfold decrHalts; omega
    simp only [decrFake, if_pos hh, State.subst_eq_self σ "x" h0]
  · rw [if_pos h0, decr_step]
    by_cases hh : decrHalts σ
    · simp only [decrFake, if_pos hh, if_pos (decrHalts_step hh h0), State.subst_subst]
    · simp only [decrFake, if_neg hh, if_neg (decrHalts_step_not hh), State.subst_subst]

/--
풀기 방정식은 해를 유일하게 결정하지 않는다.

`decrTrue`와 `decrFake`가 모두 해라는 두 보조정리와 둘이 다르다는 증거를 묶은 정리다.
§2.3~2.4에서는 이 해들을 근사 순서로 비교하고 최소인 해를 선택한다.

증명은 두 해를 제시하고 다른 값을 내는 상태를 하나 짚으면 된다.
`x` 가 1 인 상태에서 하나는 `⊥` 를, 다른 하나는 상태를 낸다.
-/
@[exercise "§2.2 unwinding-not-unique" 3]
theorem unwinding_not_unique :
    ∃ f g : State String → SigmaBot String, UnwindsDecr f ∧ UnwindsDecr g ∧ f ≠ g := by
  refine ⟨decrTrue, decrFake, unwindsDecr_true, unwindsDecr_fake, ?_⟩
  intro h
  have hne : ¬ decrHalts (State.const 1 : State String) := by
    unfold decrHalts State.const; omega
  have := congrFun h (State.const 1)
  simp only [decrTrue, decrFake, if_neg hne] at this
  -- `⊥ = some …` 은 성립할 수 없다.
  simp at this
```

풀기 방정식은 반복문의 한 단계 행동을 올바르게 적지만, 끝나지 않는 입력에서 무엇을
내야 하는지는 고르지 못한다. §2.3은 후보 함수들을 “얼마나 많은 종료 정보를 주는가”로
비교할 순서를 만든다.
