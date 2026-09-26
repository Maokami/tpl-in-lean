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

```anchor semRules (module := Reynolds.Answers.Ch03.Semantic)
/-- 대입 — 의미 판. 사후조건을 갱신된 상태에서 묻는다. -/
theorem assign (Q : State V → Prop) (v : V) (e : IntExp V) :
    PartialCorrectS (fun σ => Q (σ[v := ⟦e⟧ₑ σ])) (.assign v e) Q := by
  intro σ hq τ hτ
  obtain rfl := Option.some.inj hτ
  exact hq

/-- 순차 합성 — 의미 판. -/
theorem seq {P R Q : State V → Prop} {c₀ c₁ : Comm V}
    (h₀ : PartialCorrectS P c₀ R) (h₁ : PartialCorrectS R c₁ Q) :
    PartialCorrectS P (.seq c₀ c₁) Q := by
  intro σ hp τ hτ
  change Option.bind (⟦c₀⟧ᶜ σ) ⟦c₁⟧ᶜ = some τ at hτ
  rcases h : ⟦c₀⟧ᶜ σ with _ | ρ
  · rw [h] at hτ; simp at hτ
  · rw [h] at hτ
    exact h₁ ρ (h₀ σ hp ρ h) τ hτ

/-- 조건 — 의미 판. 조건을 단언으로 옮길 필요 없이 불 값 그대로 쓴다. -/
theorem ite {P Q : State V → Prop} {b : BoolExp V} {c₀ c₁ : Comm V}
    (h₀ : PartialCorrectS (fun σ => P σ ∧ ⟦b⟧ᵇ σ = true) c₀ Q)
    (h₁ : PartialCorrectS (fun σ => P σ ∧ ⟦b⟧ᵇ σ = false) c₁ Q) :
    PartialCorrectS P (.ite b c₀ c₁) Q := by
  intro σ hp τ hτ
  change (if ⟦b⟧ᵇ σ then ⟦c₀⟧ᶜ σ else ⟦c₁⟧ᶜ σ) = some τ at hτ
  cases hb : ⟦b⟧ᵇ σ
  · rw [hb] at hτ
    exact h₁ σ ⟨hp, hb⟩ τ hτ
  · rw [hb, if_pos rfl] at hτ
    exact h₀ σ ⟨hp, hb⟩ τ hτ

/-- 반복 — 의미 판. `I` 가 불변식. Scott 귀납법. -/
theorem wh {I : State V → Prop} {b : BoolExp V} {c : Comm V}
    (hbody : PartialCorrectS (fun σ => I σ ∧ ⟦b⟧ᵇ σ = true) c I) :
    PartialCorrectS I (.wh b c) (fun σ => I σ ∧ ⟦b⟧ᵇ σ = false) := by
  change Sat I (fix (whileF b ⟦c⟧ᶜ) (whileF_monotone b ⟦c⟧ᶜ)) _
  refine scott_induction (whileF_monotone b ⟦c⟧ᶜ)
    (P := fun w => Sat I w fun σ => I σ ∧ ⟦b⟧ᵇ σ = false)
    (fun d hd => Sat.admissible _ _ d hd) (Sat.bot _ _) ?_
  intro w hw σ hi τ hτ
  change (if ⟦b⟧ᵇ σ then Option.bind (⟦c⟧ᶜ σ) w else some σ) = some τ at hτ
  cases hb : ⟦b⟧ᵇ σ
  · rw [hb] at hτ
    obtain rfl := Option.some.inj hτ
    exact ⟨hi, hb⟩
  · rw [hb, if_pos rfl] at hτ
    rcases hc : ⟦c⟧ᶜ σ with _ | ρ
    · rw [hc] at hτ; simp at hτ
    · rw [hc] at hτ
      exact hw ρ (hbody σ ⟨hi, hb⟩ ρ hc) τ hτ

/-- 결과 규칙 — 의미 판. 전제가 술어 사이의 함의다. -/
theorem conseq {P P' Q Q' : State V → Prop} {c : Comm V}
    (hp : ∀ σ, P' σ → P σ) (h : PartialCorrectS P c Q) (hq : ∀ σ, Q σ → Q' σ) :
    PartialCorrectS P' c Q' :=
  fun σ h' τ hτ => hq τ (h σ (hp σ h') τ hτ)
```

# 피보나치
%%%
tag := "ch03-fib"
file := "ch03-fib"
number := false
%%%

```anchor fibProg (module := Reynolds.Answers.Ch03.Examples.Fib)
/-- 초기화 — 불변식을 세운다. -/
def fibInit : Comm String := ⟪ k := 0; f := 0; g := 1 ⟫ᶜ

/-- 한 바퀴 — `f, g := g, f + g` 를 임시 변수 `t` 로 하고 `k` 를 하나 늘린다. -/
def fibBody : Comm String := ⟪ t := f + g; f := g; g := t; k := k + 1 ⟫ᶜ

/-- 피보나치 프로그램. 주석 명세의 두 조각을 그대로 잇는다. -/
def fibProg : Comm String := .seq fibInit (.wh ⟪ k ≠ n ⟫ᵇ fibBody)

/-- 불변식 `0 ≤ k ≤ n ∧ f = fib k ∧ g = fib (k+1)`. `k` 를 자연수 `m` 으로 붙든다. -/
def fibInv (σ : State String) : Prop :=
  ∃ m : ℕ, σ "k" = m ∧ m ≤ (σ "n").toNat ∧ 0 ≤ σ "n" ∧
    σ "f" = Nat.fib m ∧ σ "g" = Nat.fib (m + 1)
```

불변식은 `k`를 자연수 `m`으로 붙들어 둔다. 그러면 `fib`의 인자에 `Int.toNat`이 끼지 않고,
한 바퀴 뒤에는 `m + 1`이 된다. 한 바퀴의 핵심은 `Nat.fib_add_two` 한 줄이다.

```anchor fibBodyOk (module := Reynolds.Answers.Ch03.Examples.Fib)
/--
**한 바퀴가 불변식을 지킨다.**

조건 `k ≠ n` 과 `k ≤ n` 에서 `k + 1 ≤ n`. 새 `f` 는 옛 `g = fib (m+1)`, 새 `g` 는 옛
`f + g = fib m + fib (m+1) = fib (m+2)` (`Nat.fib_add_two`).
-/
@[exercise "§3.8 fib-body" 2]
theorem fibBody_ok :
    PartialCorrectS (fun σ => fibInv σ ∧ ⟦⟪ k ≠ n ⟫ᵇ⟧ᵇ σ = true) fibBody fibInv := by
  intro σ ⟨⟨m, hk, hle, hn, hf, hg⟩, hb⟩ τ hτ
  obtain rfl := Option.some.inj hτ
  have hne : σ "k" ≠ σ "n" := by
    simpa [BoolExp.eval, IntExp.eval, Cmp.denoteBool] using hb
  refine ⟨m + 1, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [State.subst_def, Function.update, IntExp.eval, IntOp.denote, hk, hf, hg,
      Nat.fib_add_two] <;> omega
```

루프가 끝난 자리에서는 조건이 거짓이므로 `k = n`이고, 불변식이 곧 사후조건이 된다.

```anchor fibCorrect (module := Reynolds.Answers.Ch03.Examples.Fib)
/-- **피보나치 프로그램은 옳다.** 끝나면 `f = fib n`. 루프가 끝난 자리에서 `k = n` 이다. -/
theorem fib_correct :
    PartialCorrectS (fun σ => 0 ≤ σ "n") fibProg fun τ => τ "f" = Nat.fib (τ "n").toNat := by
  refine PartialCorrectS.seq fibInit_ok
    (PartialCorrectS.conseq (fun _ h => h) (PartialCorrectS.wh fibBody_ok) ?_)
  rintro τ ⟨⟨m, hk, hle, hn, hf, hg⟩, hb⟩
  have heq : τ "k" = τ "n" := by
    simpa [BoolExp.eval, IntExp.eval, Cmp.denoteBool] using hb
  rw [hf]
  congr
  omega
```

증명과 별도로, 파일의 `#guard`가 프로그램을 2장의 연료 해석기로 실제로 돌려 `fib 10 = 55`를
확인한다.

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
