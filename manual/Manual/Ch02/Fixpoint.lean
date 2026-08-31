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
set_option verso.exampleModule "Reynolds.Answers.Ch02.Fixpoint"

#doc (Manual) "§2.4 최소 고정점과 연료 해석기" =>
%%%
tag := "ch02-fixpoint"
file := "ch02-fixpoint"
number := false
%%%

# `while` 한 바퀴를 함수로 떼어 낸다
%%%
tag := "ch02-while-operator"
file := "ch02-while-operator"
number := false
%%%

반복문의 전체 뜻을 바로 재귀 정의하지 않고, 반복을 한 번 펼치는 연산자 `F`를 먼저 만든다.
`w`를 “남은 반복의 뜻”이라고 놓으면 한 바퀴는 다음처럼 쓸 수 있다.

```anchor whileF (module := Reynolds.Answers.Ch02.Eval)
/--
`while` 한 바퀴. `w`가 "반복의 나머지"다.

조건이 거짓이면 그 자리에서 끝나고, 참이면 본체를 한 번 돈 뒤 나머지 `w`에 넘긴다.
`s`는 본체의 뜻 — `Comm.eval`에서 `⟦c⟧`가 들어올 자리다.
-/
def whileF (b : BoolExp V) (s : State V → SigmaBot V)
    (w : State V → SigmaBot V) : State V → SigmaBot V :=
  fun σ => if ⟦b⟧ᵇ σ then Option.bind (s σ) w else some σ
```

조건 `b`와 본체의 뜻 `s`를 고정하면 `whileF b s`는 함수에서 함수로 가는 연산자다.

```
F : (State V → SigmaBot V) → (State V → SigmaBot V)
```

전체 반복 의미 `w`가 풀기 방정식을 만족한다는 말은 `F w = w`, 곧 `w`가 `F`의
고정점이라는 말과 같다. §2.2에서 확인했듯 고정점은 여러 개일 수 있다.

# 아래에서 시작해 유한 근사를 늘린다
%%%
tag := "ch02-kleene-chain"
file := "ch02-kleene-chain"
number := false
%%%

후보 의미 공간의 최소원 `⊥`은 모든 입력에서 `none`을 내는 함수다. 이 값에는 종료 정보가
하나도 없다. 여기에 `F`를 반복 적용한다.

```
⊥ ⊑ F(⊥) ⊑ F²(⊥) ⊑ F³(⊥) ⊑ ⋯
```

0번째 근사는 어떤 반복도 끝났다고 말하지 않는다. 다음 근사는 한 번 펼쳐 확인할 수 있는
종료를, 그다음 근사는 두 번 펼쳐 확인할 수 있는 종료를 추가한다. `F`가 단조이면 앞 근사의
종료 결과가 뒤에서 사라지지 않는다.

```anchor iterChain (module := Reynolds.Answers.Ch02.Fixpoint)
/-- 반복의 사슬. `⊥ ⊑ F(⊥) ⊑ F(F(⊥)) ⊑ ⋯`. Reynolds 세 단계의 첫째다. -/
def iterChain {F : α → α} (hF : Monotone F) : Chain α :=
  ⟨fun n => F^[n] ⊥, monotone_nat_of_le_succ (iterate_le_succ hF)⟩
```

`fix F hF`는 이 사슬의 최소 상한으로 정의된다. 어느 유한 단계에서 확인한 종료 정보도
포함하되, 사슬에 없던 종료 정보를 따로 보태지 않는 값이다.

# 연속성이 극한을 고정점으로 만든다
%%%
tag := "ch02-fix-eq"
file := "ch02-fix-eq"
number := false
%%%

사슬의 극한에 `F`를 적용한 값을 계산하려면 `F`를 극한 안으로 옮겨야 한다.

```
F (⨆ₙ Fⁿ(⊥)) = ⨆ₙ Fⁿ⁺¹(⊥)
```

왼쪽에서 첫 등식을 허용하는 가정이 연속성이다. 오른쪽 사슬은 원래 사슬에서 맨 앞의 `⊥`만
뺀 사슬이고, `⊥`은 모든 항 아래에 있으므로 극한이 바뀌지 않는다.

```anchor fix_eq (module := Reynolds.Answers.Ch02.Fixpoint)
/--
**최소 고정점 정리, 둘째 단계 — 극한은 고정점이다.**

`F`의 연속성을 반복의 사슬에 적용하면 `F(fix)`가 "F를 입힌 사슬"의 극한이 된다.
그 사슬은 원래 사슬을 한 칸 민 것이고, 밀어도 극한은 그대로다. 극한의 유일성으로 끝난다.
-/
@[exercise "§2.4 fix-eq" 3]
theorem fix_eq {F : α → α} (hF : Continuous F) :
    F (fix F hF.monotone) = fix F hF.monotone := by
  -- 연속성: `F(fix)`는 `F '' (사슬의 값들)`의 극한이다.
  have h₁ := hF (iterChain hF.monotone)
  -- 그 상은 밀린 사슬의 값들과 같다.
  have himg : F '' Set.range (iterChain hF.monotone).seq
      = Set.range fun n => F^[n + 1] ⊥ := by
    ext y
    constructor
    · rintro ⟨_, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, Function.iterate_succ_apply' F n ⊥⟩
    · rintro ⟨n, rfl⟩
      exact ⟨F^[n] ⊥, ⟨n, rfl⟩, (Function.iterate_succ_apply' F n ⊥).symm⟩
  rw [himg] at h₁
  -- 밀린 사슬의 극한은 `fix`이기도 하다. 극한은 유일하다.
  exact h₁.unique (isLUB_shifted hF.monotone)
```

여기서 단조성만 가정하면 반복 사슬은 만들 수 있지만 `F`를 극한 안으로 옮길 수 없다.
§2.3의 단조지만 연속이 아닌 반례가 이 단계에서 연속성이 필요한 이유를 보여 준다.

# 그 고정점이 모든 다른 해보다 아래에 있다
%%%
tag := "ch02-fix-least"
file := "ch02-fix-least"
number := false
%%%

`F x ⊑ x`인 값을 전고정점(pre-fixed point)이라 부른다. `x`가 고정점이면 당연히
전고정점이다. 반복 사슬의 모든 항이 `x` 아래에 있음을 자연수 귀납으로 보이면, 그 극한도
`x` 아래에 있다.

```anchor fix_least (module := Reynolds.Answers.Ch02.Fixpoint)
/--
**최소 고정점 정리, 셋째 단계 — 전고정점 아래에 있다.**

`F(x) ⊑ x`이면 `fix ⊑ x`다. 특히 `F(x) = x`이면 `F(x) ⊑ x`이므로, `fix`는 모든
고정점 아래에 있다.

§2.2의 두 해로 돌아가면 `decrFake`도 풀기 방정식의 해이므로 `fix ⊑ decrFake`다.
구체적인 감소 반복문의 뜻이 `decrTrue`와 같다는 계산은 책의 연습 2.3에 해당한다.
-/
@[exercise "§2.4 fix-least" 2]
theorem fix_least {F : α → α} (hF : Monotone F) {x : α} (hx : F x ≤ x) :
    fix F hF ≤ x := by
  refine (iterChain hF).lub_le fun n => ?_
  induction n with
  | zero => exact bot_le
  | succ n ih =>
      calc F^[n + 1] ⊥ = F (F^[n] ⊥) := Function.iterate_succ_apply' F n ⊥
        _ ≤ F x := hF ih
        _ ≤ x := hx
```

최소라는 말은 “실행 시간이 가장 짧다”거나 “결과 상태의 정수가 가장 작다”는 뜻이 아니다.
정보 순서에서 아래라는 뜻이다. 최소 고정점은 유한 근사로 확인할 수 없는 입력에 임의의
종료 결과를 붙이지 않는다. §2.2의 `decrFake`가 탈락하는 이유가 여기에 있다.

# Scott 귀납법은 유한 근사의 성질을 극한으로 넘긴다
%%%
tag := "ch02-scott-induction"
file := "ch02-scott-induction"
number := false
%%%

최소 고정점에 관한 성질 `P`를 증명할 때는 세 조건을 확인한다.

1. `P ⊥` — 아무 정보도 없는 근사에서 성립한다.
2. `P x → P (F x)` — 한 단계를 더 펼쳐도 보존된다.
3. 사슬의 모든 항에서 `P`가 성립하면 극한에서도 성립한다.

세 번째 조건을 허용 가능성(admissibility)이라 부른다.

```anchor scott_induction (module := Reynolds.Answers.Ch02.Fixpoint)
/--
**Scott 귀납법.** 허용 가능한 성질이 `⊥`에서 성립하고 `F`가 보존하면, `fix F`에서
성립한다.

증명은 두 단계다. 반복의 각 단계에서 성질이 성립함을 자연수 귀납으로 확인하고,
허용 가능성이 그것을 극한으로 넘긴다. 어려움은 "허용 가능한가"를 확인하는 쪽에
있다는 것이 이 원리의 특징이고, §2.5부터 그 확인이 실제 일이 된다.
-/
@[exercise "§2.4 scott" 2]
theorem scott_induction {F : α → α} (hF : Monotone F) {P : α → Prop}
    (hadm : ∀ c : Chain α, (∀ n, P (c.seq n)) → P c.lub)
    (hbot : P ⊥) (hstep : ∀ x, P x → P (F x)) : P (fix F hF) := by
  refine hadm (iterChain hF) fun n => ?_
  induction n with
  | zero => exact hbot
  | succ n ih =>
      rw [iterChain_seq, Function.iterate_succ_apply']
      exact hstep _ ih
```

일반적인 구조적 귀납법은 구문 트리의 생성자를 따라간다. Scott 귀납법은 의미의 유한
근사를 따라간다. `while`의 의미는 구문 재귀만으로 만들어지지 않으므로 두 귀납법의
역할도 다르다.

# 최소 고정점으로 `Comm.eval`을 완성한다
%%%
tag := "ch02-comm-eval"
file := "ch02-comm-eval"
number := false
%%%

`whileF`가 연속이라는 정리를 증명한 뒤, `wh` 절에서 그 최소 고정점을 택한다.

```anchor Comm.eval (module := Reynolds.Answers.Ch02.Eval)
/--
`⟦c⟧ᶜ` — 명령의 뜻. Reynolds §2.2의 `⟦-⟧comm ∈ ⟨comm⟩ → Σ → Σ⊥`, §2.4에서 완성된 판.

여섯 절 가운데 `wh` 절에서만 최소 고정점이 필요하다. 반복의 뜻은 `whileF`의 최소
고정점이고, "최소"가 §2.2에서 확인한 여러 해 중 하나를 고르는 원리다.

`Classical.choice`를 거치므로 계산되지 않는다. 실행은 연료 해석기가 맡는다.
-/
noncomputable def Comm.eval : Comm V → State V → SigmaBot V
  | .assign v e   => fun σ => some (σ[v := ⟦e⟧ₑ σ])
  | .skip         => fun σ => some σ
  | .seq c₀ c₁    => fun σ => Option.bind (c₀.eval σ) c₁.eval
  | .ite b c₀ c₁  => fun σ => if ⟦b⟧ᵇ σ then c₀.eval σ else c₁.eval σ
  | .wh b c       => fix (whileF b c.eval) (whileF_monotone b c.eval)
  | .newvar v e c => fun σ => restore v σ (c.eval (σ[v := ⟦e⟧ₑ σ]))
```

`Comm.eval_isSemantics`는 이 정의가 §2.2의 여섯 방정식을 모두 만족한다고 증명한다.
`Comm.eval_while_least`는 같은 본체와 조건에 대한 다른 풀기 방정식의 해보다 이 의미가
아래에 있음을 증명한다. 존재, 방정식 만족, 최소성이 서로 다른 정리로 나뉘어 있다.

`Comm.eval`은 `noncomputable`이다. 평평한 사슬에서 언젠가 종료 결과가 나타나는지를
일반적으로 계산할 수 없기 때문이다. 증명에 쓸 뜻과 실제로 돌릴 해석기를 분리해야 한다.

# 연료 해석기는 유한 근사를 실행한다
%%%
tag := "ch02-interpreter"
file := "ch02-interpreter"
number := false
%%%

`Comm.run c n σ`는 반복을 펼칠 수 있는 연료 `n`을 받는다. 반복이 아닌 절은 연료를
소비하지 않고, `while`을 한 번 펼칠 때 남은 반복에 넘길 연료를 하나 줄인다.

```anchor Comm.run (module := Reynolds.Answers.Ch02.Interpreter)
/--
연료 해석기. Reynolds §2.4의 유한 근사와 같은 역할을 하는 실행 가능한 정의다.

`wh` 절만 연료를 쓴다. 연료가 남았으면 조건을 검사하고, 참이면 본체와 나머지 반복을
실행한다. 바깥 반복을 한 번 풀 때 나머지 반복의 연료는 하나 줄지만, 본체에는 현재 연료를
그대로 준다. 본체에 중첩된 반복이 있으면 그 반복도 유한하게 실행하기 위해서다.

연료가 바닥나면 `none`을 돌려준다. 이 값은 발산과 연료 부족을 구분하지 않는다.
`Comm.eval`과 달리 정의 전체를 계산할 수 있어 `#eval`과 `#guard`에서 사용할 수 있다.
-/
def Comm.run : Comm V → ℕ → State V → SigmaBot V
  | .assign v e,   _, σ => some (σ[v := ⟦e⟧ₑ σ])
  | .skip,         _, σ => some σ
  | .seq c₀ c₁,    n, σ => Option.bind (c₀.run n σ) (c₁.run n)
  | .ite b c₀ c₁,  n, σ => if ⟦b⟧ᵇ σ then c₀.run n σ else c₁.run n σ
  | .newvar v e c, n, σ => restore v σ (c.run n (σ[v := ⟦e⟧ₑ σ]))
  | .wh _ _,       0, _ => none
  | .wh b c,   n + 1, σ =>
      if ⟦b⟧ᵇ σ then Option.bind (c.run (n + 1) σ) ((Comm.wh b c).run n) else some σ
```

연료가 부족해 `none`이 나왔다고 해서 프로그램이 발산한다고 결론 내릴 수는 없다.
`while x > 0 do x := x - 1`을 `x = 5`에서 실행하면 연료 5로는 마지막 조건 검사를
마치지 못하지만, 연료 6에서는 `x = 0`인 상태를 얻는다. 반대로
`while tt do skip`은 어떤 유한 연료에서도 `none`이다.

`Comm.run_le_succ`는 연료를 늘릴 때 정보를 잃지 않는다는 정리다. 한 번
`some σ'`이 나오면 더 큰 연료에서도 같은 `some σ'`이 나온다. 평평한 순서에서는
종료 결과를 다른 값으로 바꾸는 것이 허용되지 않기 때문이다.

# 적합성은 증명용 의미와 실행용 의미를 잇는다
%%%
tag := "ch02-adequacy"
file := "ch02-adequacy"
number := false
%%%

표시적 의미에서 종료 결과를 증명해도 해석기가 재현하지 못한다면 실행과 동떨어진 뜻이다.
반대로 해석기가 낸 결과가 표시적 의미와 다르면 테스트를 정리의 근거로 옮길 수 없다.

```anchor Comm.eval_eq_run (module := Reynolds.Answers.Ch02.Interpreter)
/--
**적합성(adequacy)** — 표시적 의미와 해석기가 일치한다.

왼쪽은 증명용이고 오른쪽은 실행용이다. `#guard`로 확인한 종료 결과는 건전성 방향을 통해
`⟦-⟧ᶜ`의 결과가 된다. 반대로 표시적 의미에서 증명한 종료 결과는 충분한 연료의 `run`에서
재현된다. 이 정리는 `none`에 관한 임의의 성질까지 옮긴다고 주장하지 않는다.

채점 연습이 아니다 — 증명이 Scott 귀납법과 `fix_eq` 위에 서 있어서, 비우면 비운 것끼리
의존한다 (연습 독립성 원칙). 완전성 방향의 Scott 귀납법 적용을 완성본으로 읽는 것이
이 파일의 목적이다.
-/
theorem Comm.eval_eq_run {c : Comm V} {σ σ' : State V} :
    c.eval σ = some σ' ↔ ∃ n, c.run n σ = some σ' := by
  constructor
  · exact Comm.run_complete
  · rintro ⟨n, hn⟩
    exact Comm.run_sound hn
```

정리의 오른쪽은 “어떤 유한 연료에서 같은 종료 결과가 나온다”다. 따라서 `run`으로 확인한
종료 결과는 `eval`의 결과이고, `eval`에서 얻은 종료 결과도 충분한 연료로 실행된다.
이 진술은 `eval σ = none`과 “모든 연료에서 `run`이 `none`” 사이의 동치를 직접 적은
정리는 아니다. 현재 적합성 정리가 옮기는 범위는 `some`인 종료 결과다.

# 직접 해 보기와 연습 범위
%%%
tag := "ch02-practice"
file := "ch02-practice"
number := false
%%%

현재 2장에는 §2.2~§2.4의 채점 대상이 16개 있다.

* `Semantics.lean` — 불 식과 단언의 일치, 리프팅과 `bind`, 풀기 방정식의 비유일성
* `Domain.lean` — 연속이면 단조, 명제 2.1, 단조지만 연속이 아닌 반례
* `Domain/Lifting.lean` — 평평한 도메인의 연속성, 명제 2.4
* `Domain/FunctionSpace.lean` — 명제 2.2와 2.3
* `Fixpoint.lean` — 고정점, 최소성, Scott 귀납법
* `Eval.lean` — 연속성 계산 연습 2.4
* `Interpreter.lean` — 연료 단조성

`Reynolds/Exercises/Ch02/`에서 `sorry`를 채운 뒤 다음 명령으로 상태를 확인한다.

```
lake exe grade --chapter 2
```

§2.5~§2.8과 책 연습 2.1~2.10 전체는 아직 구현 범위가 아니다. 현재 연습 목록의
“§2.2” 같은 식별자는 해당 절의 형식화를 익히기 위해 저장소가 둔 연습이고,
“Prop 2.1”과 “Ex 2.4”는 책의 번호에 직접 대응한다.
