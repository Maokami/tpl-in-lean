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
set_option verso.exampleModule "Reynolds.Answers.Ch03.Examples.Fib"

#doc (Manual) "§3.8~3.9 예제" =>
%%%
tag := "ch03-examples"
file := "ch03-examples"
number := false
%%%

두 예제를 끝까지 유도한다. 둘 다 불변식에 단언 언어로 적을 수 없는 것이 들어간다.
피보나치에는 `fib`가, 빠른 거듭제곱에는 거듭제곱이 든다. 그래서 _의미 단언_ 위에서 간다.

이것이 §3.10의 요점을 미리 보여 준다. _명세를 적는 언어가 프로그램을 적는 언어보다
풍부해야 한다._ Reynolds가 단언에 수학 기호를 자유롭게 쓰는 그 자유가, 형식화에서는
"단언은 Lean의 술어"라는 선택에서 나온다.

# 의미 판 규칙
%%%
tag := "ch03-sem-rules"
file := "ch03-sem-rules"
number := false
%%%

`Hoare`의 규칙들을 의미 단언 위에서 다시 적는다. 대입의 의미 판은 치환이 아니라 _상태
갱신_이다. 명제 1.4가 둘이 같다고 말해 주므로, 구문 판에서 치환이 하던 일을 여기서는 갱신이
그대로 한다.

```anchor stmtAsSound (module := Reynolds.Answers.Ch03.Semantic)
/-- AS (§3.3). 갱신된 상태에서 사후조건을 묻는 대입은 부분·전체 정확성을 함께 만족한다. -/
@[exercise "§3.3 as-sound" 1]
theorem as_sound (Q : State V → Prop) (v : V) (e : IntExp V) :
    PartialCorrectS (fun σ => Q (σ[v := ⟦e⟧ₑ σ])) (.assign v e) Q ∧
    TotalCorrectS (fun σ => Q (σ[v := ⟦e⟧ₑ σ])) (.assign v e) Q
```

```anchor stmtSqSound (module := Reynolds.Answers.Ch03.Semantic)
/-- SQ (§3.3). 가운데 조건을 공유하는 두 명령을 순서대로 실행한다. -/
@[exercise "§3.3 sq-sound" 1]
theorem sq_sound {P R Q : State V → Prop} {c₀ c₁ : Comm V} :
    (PartialCorrectS P c₀ R → PartialCorrectS R c₁ Q → PartialCorrectS P (.seq c₀ c₁) Q) ∧
    (TotalCorrectS P c₀ R → TotalCorrectS R c₁ Q → TotalCorrectS P (.seq c₀ c₁) Q)
```

```anchor stmtCdSound (module := Reynolds.Answers.Ch03.Semantic)
/-- CD (§3.5). 참인 가지와 거짓인 가지의 정확성을 각각 확인한다. -/
@[exercise "§3.5 cd-sound" 1]
theorem cd_sound {P Q : State V → Prop} {b : BoolExp V} {c₀ c₁ : Comm V} :
    (PartialCorrectS (fun σ => P σ ∧ ⟦b⟧ᵇ σ = true) c₀ Q →
      PartialCorrectS (fun σ => P σ ∧ ⟦b⟧ᵇ σ = false) c₁ Q →
      PartialCorrectS P (.ite b c₀ c₁) Q) ∧
    (TotalCorrectS (fun σ => P σ ∧ ⟦b⟧ᵇ σ = true) c₀ Q →
      TotalCorrectS (fun σ => P σ ∧ ⟦b⟧ᵇ σ = false) c₁ Q →
      TotalCorrectS P (.ite b c₀ c₁) Q)
```

```anchor stmtWhpSound (module := Reynolds.Answers.Ch03.Semantic)
/-- WHP (§3.4). 불변식을 보존하는 본체에서 Scott 귀납법으로 반복의 부분 정확성을 얻는다. -/
@[exercise "§3.4 whp-sound" 3]
theorem PartialCorrectS.wh {I : State V → Prop} {b : BoolExp V} {c : Comm V}
    (hbody : PartialCorrectS (fun σ => I σ ∧ ⟦b⟧ᵇ σ = true) c I) :
    PartialCorrectS I (.wh b c) (fun σ => I σ ∧ ⟦b⟧ᵇ σ = false)
```

AS·SQ·CD는 각각 부분 정확성과 전체 정확성을 한 연습에서 함께 증명한다. WHP는
부분 정확성의 반복 규칙이다. 구문 단언의 AS·SQ·CD·WHP 정리는 이 의미 규칙에서 얻는
완성 자료로 제공한다.

이번 이관에서는 `sat_admissible`과 `wlp_wh_greatest`도 완성 자료로 제공하므로,
이 이관으로 채점 항목은 두 개 줄었다. 전자는 `Sat.admissible`에서 재사용하고,
후자는 WHP의 귀결로 얻는다. WHT도 의미 단언 위의 독립 연습이며 구문 유령 변수 판은 그 따름정리다.
전체 정확성의 사슬 극한 보존과 바닥에서의 실패는 `§3.1 total-admissible`에서 함께 확인한다.

변수 선언도 `Ex 3.9 dc-sound`에서 부분·전체 정확성을 함께 증명한다.
기존 `§3.6 newvar-sound`를 이 문제로 옮기고, 독립적인 `§3.5 rn-sound`를 추가했다.
두 진술과 초기값·그림자 이름의 예는 앞의 규칙 절에 있다. 현재 3장 채점 항목은 20개다.

# §3.6 피보나치
%%%
tag := "ch03-fib"
file := "ch03-fib"
number := false
%%%

책 pp.69–71의 프로그램은 입력 `n`이 0인 경우를 먼저 처리한다. 그 밖에는
`k = 1`, `f = 1`, `g = 0`에서 시작한다. 반복문에 들어갈 때 `f`는
`fib k`이고 `g`는 그 앞 수 `fib (k−1)`다. 임시 변수 `t`가 옛 `g`를
기억하므로, `g := f; f := f+t`가 두 수를 한 칸 앞으로 옮긴다.

```anchor fibProg (module := Reynolds.Answers.Ch03.Examples.Fib)
/-- `t`에 옛 `g`를 보관한 뒤 두 피보나치 수와 인덱스를 갱신한다. -/
def fibBody : Comm String :=
  .newvar "t" (.var "g") ⟪ g := f; f := f + t; k := k + 1 ⟫ᶜ

/-- 책 §3.6의 프로그램. `k`, `g`, `t`의 선언 범위가 프로그램에 드러난다. -/
def fibProg : Comm String :=
  .ite ⟪ n = 0 ⟫ᵇ ⟪ f := 0 ⟫ᶜ
    (.newvar "k" (.num 1) (.newvar "g" (.num 0)
      (.seq ⟪ f := 1 ⟫ᶜ (.wh ⟪ k ≠ n ⟫ᵇ fibBody))))

/-- 책의 `f = fib k ∧ g = fib (k−1) ∧ k ≤ n`에 도달 가능 조건 `1 ≤ k`를 더한다. -/
def fibInv (σ : State String) : Prop :=
  ∃ m : ℕ, σ "k" = (m + 1 : ℕ) ∧ m + 1 ≤ (σ "n").toNat ∧ 0 ≤ σ "n" ∧
    σ "f" = Nat.fib (m + 1) ∧ σ "g" = Nat.fib m
```

`k`, `g`, `t`는 각각 선언 범위가 끝나면 원래 값으로 돌아간다. 따라서
프로그램의 결과로 관찰할 값은 `f`이며, 입력 `n`과 호출 전의 지역 변수 값은 보존된다.

책은 정수 전체에 정의한 피보나치 함수를 쓴다. 여기서는 Mathlib의 `Nat.fib`를
쓰므로, 반복 상태에 항상 성립하는 `1 ≤ k`를 불변식에 추가했다.
`fibInv`의 증인 `m`은 `k−1`이다. 예를 들어 `m = 2`라면
`k = 3`, `f = 2`, `g = 1`이고 다음 상태는 `k = 4`, `f = 3`, `g = 2`다.

## 한 단계의 산술

`fibStep σ`는 지역 선언을 도입하기 전 네 대입
`t := g; g := f; f := f+t; k := k+1`의 결과다. 선택 연습 하나에서
불변식 보존과 변항 감소를 함께 확인한다. `fibInv`와 `fibStep`의 정의,
`Nat.fib_add_two`만으로 풀 수 있어 다른 규칙 연습을 먼저 끝낼 필요가 없다.

```anchor stmtFibStep (module := Reynolds.Answers.Ch03.Examples.Fib)
/-- §3.6의 산술 의무. 한 단계가 불변식을 보존하면서 변항 `n−k`를 줄인다. -/
@[exercise "§3.6 fib-step" 2]
theorem fib_step (σ : State String)
    (h : fibInv σ ∧ ⟦⟪k ≠ n⟫ᵇ⟧ᵇ σ = true) :
    fibInv (fibStep σ) ∧ (fibStep σ) "n" - (fibStep σ) "k" < σ "n" - σ "k"
```

조건 `k ≠ n`과 불변식의 `k ≤ n`이 함께 있어야 다음 인덱스도 `n` 이하가 된다.
`n−k`는 한 바퀴마다 1만큼 줄어든다. 피보나치 등식에는 `Nat.fib_add_two`를,
인덱스와 변항의 부등식에는 정수 산술을 적용한다.

## 부분 정확성에서 전체 정확성으로

부분 정확성의 조립은 다음과 같다. 직선 대입 계산 뒤 DC로 `t`를 지역화한다.
WHP가 불변식이 보존되는 반복문을 만들고, 종료 조건 `k = n`이 결과를 준다.
초기화를 앞에 붙인 뒤에는 `k := 1`을 접두 명령으로 남겨 둔 채 DC로 `g`를
지역화한다. 다음 DC가 `k`를 지역화하고, CD가 `n = 0`인 가지와 합친다.
이 순서가 책 p70에서 DC를 두 번 적용하는 이유를 보여 준다.

```anchor stmtFibCorrect (module := Reynolds.Answers.Ch03.Examples.Fib)
/-- §3.6의 부분 정확성. WHP·DC·CD를 조립하면 종료한 결과는 `fib n`이다. -/
theorem fib_correct :
    PartialCorrectS (fun σ => 0 ≤ σ "n") fibProg
      (fun τ => τ "f" = Nat.fib (τ "n").toNat)
```

전체 정확성에서는 같은 본체가 종료하며 `n−k`를 줄인다는 사실을 사용한다.
불변식은 활성 반복 상태에서 `n−k ≥ 0`을 보장하므로 WHT를 적용할 수 있다.
이후 초기화·DC·CD의 조립 순서는 같다. 다음 정리에는 종료를 별도로 가정하지 않는다.

```anchor stmtFibTotalCorrect (module := Reynolds.Answers.Ch03.Examples.Fib)
/-- §3.6의 전체 정확성. 변항 `n−k`에 WHT를 적용하므로 종료 가정이 필요 없다. -/
theorem fib_total_correct :
    TotalCorrectS (fun σ => 0 ≤ σ "n") fibProg
      (fun τ => τ "f" = Nat.fib (τ "n").toNat)
```

정답의 전체 증명은 Answers 폴더의 `Ch03/Examples/Fib.lean`에서,
직접 풀 한 지점은 Exercises 폴더의 같은 파일에 있는
`§3.6 fib-step`에서 확인한다. 실행 회귀 검사는 `n = 0, 1, 2, 10`의 결과와
`k`, `g`, `t`의 복원을 함께 확인한다.

# 빠른 거듭제곱
%%%
tag := "ch03-fastexp"
file := "ch03-fastexp"
number := false
%%%

```anchor expProg (module := Reynolds.Answers.Ch03.Examples.FastExp)
/-- 초기화 — `y := 1`, `x := a`, `k := n`. -/
def expInit : Comm String := ⟪ y := 1; x := a; k := n ⟫ᶜ

/-- 홀수 갈래 — `y` 에 `x` 를 한 번 곱해 넣고 지수를 하나 줄인다. -/
def expOdd : Comm String := ⟪ y := y × x; k := k - 1 ⟫ᶜ

/-- 짝수 갈래 — 밑을 제곱하고 지수를 반으로. -/
def expEven : Comm String := ⟪ x := x × x; k := k ÷ 2 ⟫ᶜ

/-- 빠른 거듭제곱. -/
def expProg : Comm String :=
  .seq expInit (.wh ⟪ k > 0 ⟫ᵇ (.ite ⟪ k rem 2 = 1 ⟫ᵇ expOdd expEven))

/-- 불변식 `n ≥ 0 ∧ k ≥ 0 ∧ y · x^k = a^n`. `k` 를 자연수 `m` 으로 붙든다. -/
def expInv (σ : State String) : Prop :=
  0 ≤ σ "n" ∧ ∃ m : ℕ, σ "k" = m ∧ σ "y" * σ "x" ^ m = σ "a" ^ (σ "n").toNat
```

§1.1의 `IntOp`에 `÷`와 `rem`이 있다(§2.7의 유클리드 나눗셈). `k ≥ 0`이고 나누는 수가 2이니
수학의 몫, 나머지와 같다. 한 바퀴는 두 갈래다.

: 홀수

  `y · x · x^(m-1) = y · x^m`. `m = j + 1`로 쓰고 `pow_succ`를 쓴다.

: 짝수

  `(x · x)^(m/2) = x^(2 · (m/2)) = x^m`. `pow_mul`을 쓰고 `2 · (m/2) = m`을 보인다.

```anchor expCorrect (module := Reynolds.Answers.Ch03.Examples.FastExp)
/-- **빠른 거듭제곱은 옳다.** 끝나면 `y = a^n`. 루프가 끝난 자리에서 `k = 0` 이다. -/
theorem exp_correct :
    PartialCorrectS (fun σ => 0 ≤ σ "n") expProg fun τ => τ "y" = τ "a" ^ (τ "n").toNat := by
  refine PartialCorrectS.seq expInit_ok
    (PartialCorrectS.conseq (fun _ h => h) (PartialCorrectS.wh expBody_ok) ?_)
  rintro τ ⟨⟨hn, m, hk, hinv⟩, hb⟩
  have hm : m = 0 := by
    simp [BoolExp.eval, IntExp.eval, Cmp.denoteBool, hk] at hb
    omega
  subst hm
  simpa using hinv
```
