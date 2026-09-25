/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Answers.Ch03.Examples.Fib
-- `#guard`는 컴파일 시점에 계산한다 (AGENTS.md §10).
public meta import Reynolds.Answers.Ch02.Interpreter
public meta import Reynolds.Answers.Ch02.Notation
public meta import Reynolds.Answers.Ch02.Semantics
public meta import Reynolds.Prelude

/-!
# §3.9 예제 — 빠른 거듭제곱

```
{ n ≥ 0 }
y := 1 ; x := a ; k := n ;
{ k ≥ 0 ∧ y · x^k = a^n }                          -- 불변식
while k > 0 do
  if k rem 2 = 1 then (y := y · x ; k := k - 1)
  else (x := x · x ; k := k ÷ 2)
{ y = a^n }
```

## `÷` 와 `rem` 은 있다

설계 문서(`docs/chapter-03.md` §3.9)는 이 예제에 나눗셈과 나머지가 없어 우회가 필요하다고
적었는데, 틀렸다. §1.1 의 `IntOp` 에 `div`·`rem` 이 이미 있고 DSL 도 `÷`·`rem` 을 받는다.
§2.7 에서 정했듯 Lean 의 유클리드 나눗셈(`Int.ediv`·`Int.emod`)이고 `0` 으로 나누면 `0` 이다.
이 예제에서는 `k ≥ 0` 이고 나누는 수가 `2` 라 수학의 몫·나머지와 같다.

## 거듭제곱은 단언 언어에 없다

`fib` 와 같은 사정이다. 불변식 `y · x^k = a^n` 을 **의미 단언**으로 적는다. 피보나치처럼 `k` 를
자연수 `m` 으로 붙들어 두면 지수가 `Int.toNat` 없이 `m` 이다.

한 바퀴는 두 갈래다.

- 홀수 — `y · x · x^(m-1) = y · x^m`. `m = j + 1` 로 쓰고 `pow_succ`.
- 짝수 — `(x · x)^(m/2) = x^(2 · (m/2)) = x^m`. `pow_mul` 과 `2 · (m/2) = m`.

## 읽는 순서
`Fib.lean` → 이 파일.
-/

@[expose] public section

namespace Reynolds.Answers.Ch03.Examples

open Reynolds Reynolds.Answers.Ch01 Reynolds.Answers.Ch02 Reynolds.Answers.Ch03

-- ANCHOR: expProg
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
-- ANCHOR_END: expProg

-- 실행해 본다. `3 ^ 13 = 1594323`.
set_option linter.hashCommand false
#guard (expProg.run 100 ((State.const 0)["a" := (3 : Int)]["n" := (13 : Int)])).map
  (fun σ => σ "y") == some 1594323

/-- 초기화가 불변식을 세운다. -/
theorem expInit_ok : PartialCorrectS (fun σ => 0 ≤ σ "n") expInit expInv := by
  intro σ hn τ hτ
  obtain rfl := Option.some.inj hτ
  refine ⟨by simp [State.subst_def, Function.update, IntExp.eval, hn], (σ "n").toNat, ?_, ?_⟩ <;>
    simp [State.subst_def, Function.update, IntExp.eval, hn]

-- ANCHOR: expBodyOk
/--
**한 바퀴가 불변식을 지킨다.** 조건 규칙의 의미 판으로 두 갈래를 따로 본다.
-/
@[exercise "§3.9 fastexp-body" 3]
theorem expBody_ok :
    PartialCorrectS (fun σ => expInv σ ∧ ⟦⟪ k > 0 ⟫ᵇ⟧ᵇ σ = true)
      (.ite ⟪ k rem 2 = 1 ⟫ᵇ expOdd expEven) expInv := by
  refine PartialCorrectS.ite ?_ ?_
  · -- 홀수 갈래.
    rintro σ ⟨⟨⟨hn, m, hk, hinv⟩, hpos⟩, hodd⟩ τ hτ
    obtain rfl := Option.some.inj hτ
    have hm : m % 2 = 1 ∧ 0 < m := by
      simp [BoolExp.eval, IntExp.eval, IntOp.denote, Cmp.denoteBool, hk] at hpos hodd
      omega
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    refine ⟨by simpa [State.subst_def, Function.update] using hn, j, ?_, ?_⟩
    · simp [State.subst_def, IntExp.eval, IntOp.denote, hk]
    · have key : σ "y" * σ "x" * σ "x" ^ j = σ "a" ^ (σ "n").toNat := by
        rw [← hinv, pow_succ]; ring
      simpa [State.subst_def, Function.update, IntExp.eval, IntOp.denote] using key
  · -- 짝수 갈래.
    rintro σ ⟨⟨⟨hn, m, hk, hinv⟩, hpos⟩, heven⟩ τ hτ
    obtain rfl := Option.some.inj hτ
    have hm : m % 2 = 0 := by
      simp [BoolExp.eval, IntExp.eval, IntOp.denote, Cmp.denoteBool, hk] at heven
      omega
    refine ⟨by simpa [State.subst_def, Function.update] using hn, m / 2, ?_, ?_⟩
    · simp [State.subst_def, IntExp.eval, IntOp.denote, hk]
    · have key : σ "y" * (σ "x" * σ "x") ^ (m / 2) = σ "a" ^ (σ "n").toNat := by
        rw [← hinv, ← pow_two, ← pow_mul, Nat.two_mul_div_two_of_even (Nat.even_iff.mpr hm)]
      simpa [State.subst_def, Function.update, IntExp.eval, IntOp.denote] using key
-- ANCHOR_END: expBodyOk

-- ANCHOR: expCorrect
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
-- ANCHOR_END: expCorrect

end Reynolds.Answers.Ch03.Examples
