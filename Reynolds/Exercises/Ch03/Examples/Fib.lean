/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Exercises.Ch03.Semantic
public import Mathlib.Data.Nat.Fib.Basic
-- `#guard`는 컴파일 시점에 계산한다 (AGENTS.md §10).
public meta import Reynolds.Exercises.Ch02.Interpreter
public meta import Reynolds.Answers.Ch02.Notation
public meta import Reynolds.Exercises.Ch02.Semantics
public meta import Reynolds.Prelude

/-!
# §3.8 예제 — 피보나치

```
{ n ≥ 0 }
k := 0 ; f := 0 ; g := 1 ;
{ 0 ≤ k ≤ n ∧ f = fib k ∧ g = fib (k+1) }        -- 불변식
while k ≠ n do
  t := f + g ; f := g ; g := t ; k := k + 1
{ f = fib n }
```

## 왜 의미 단언인가

`fib` 는 단언 언어에 없다. "`f`·`g` 가 연속한 두 피보나치 수다" 를 `∃` 와 산술로 풀어 쓸 수는
있지만 — 유한 수열을 정수 하나로 부호화하는 괴델의 β-함수가 필요하다 — 길고 읽을 수 없다.
그래서 불변식을 **의미 단언**으로 쓴다. Mathlib 의 `Nat.fib` 를 그대로 부른다.

이것이 §3.10 의 요점을 미리 보여 준다. **명세를 적는 언어가 프로그램을 적는 언어보다
풍부해야 한다.** Reynolds 가 단언에 수학 기호를 자유롭게 쓰는 그 자유가, 형식화에서는
"단언 = Lean 의 술어" 라는 선택에서 나온다.

## 불변식의 모양

`k` 를 자연수 `m` 으로 붙들어 둔다 (`σ k = m`). 그러면 `fib` 의 인자가 `Int.toNat` 없이
`m` 이고, 한 바퀴 뒤에는 `m + 1` 이다. 한 바퀴의 핵심은 `Nat.fib_add_two` 한 줄이다.

## 읽는 순서
`Semantic.lean` → 이 파일 → `FastExp.lean`.
-/

@[expose] public section

namespace Reynolds.Exercises.Ch03.Examples

open Reynolds Reynolds.Exercises.Ch01 Reynolds.Exercises.Ch02 Reynolds.Exercises.Ch03

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

-- 실행해 본다. `fib 10 = 55`.
set_option linter.hashCommand false
#guard (fibProg.run 100 ((State.const 0)["n" := (10 : Int)])).map (fun σ => σ "f") == some 55

/-- 초기화가 불변식을 세운다. 대입 셋을 정의대로 계산한다. -/
theorem fibInit_ok : PartialCorrectS (fun σ => 0 ≤ σ "n") fibInit fibInv := by
  intro σ hn τ hτ
  obtain rfl := Option.some.inj hτ
  refine ⟨0, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [State.subst_def, Function.update, IntExp.eval, hn]

/--
**한 바퀴가 불변식을 지킨다.**

조건 `k ≠ n` 과 `k ≤ n` 에서 `k + 1 ≤ n`. 새 `f` 는 옛 `g = fib (m+1)`, 새 `g` 는 옛
`f + g = fib m + fib (m+1) = fib (m+2)` (`Nat.fib_add_two`).
-/
@[exercise "§3.8 fib-body" 2]
theorem fibBody_ok :
    PartialCorrectS (fun σ => fibInv σ ∧ ⟦⟪ k ≠ n ⟫ᵇ⟧ᵇ σ = true) fibBody fibInv := by
  -- 먼저 볼 것: Mathlib 의 `Nat.fib_add_two`, 이 파일 위의 `fibInit_ok`.
  -- 힌트 1: `intro σ ⟨⟨m, hk, hle, hn, hf, hg⟩, hb⟩ τ hτ` 뒤 `obtain rfl := Option.some.inj hτ`.
  --         본체에 반복이 없어 `⟦fibBody⟧ᶜ σ` 가 정의대로 `some (…)` 로 계산된다.
  -- 힌트 2: 조건 `hb` 를 `simpa [BoolExp.eval, IntExp.eval, Cmp.denoteBool]` 로 `σ "k" ≠ σ "n"` 로.
  -- 힌트 3: 새 증인은 `m + 1`. 다섯 조각을 `simp [State.subst_def, Function.update, IntExp.eval,
  --         IntOp.denote, hk, hf, hg, Nat.fib_add_two]` 와 `omega` 로.
  sorry


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

end Reynolds.Exercises.Ch03.Examples
