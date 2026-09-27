/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Answers.Ch03.Semantic
public meta import Reynolds.Answers.Ch02.Interpreter
public meta import Reynolds.Answers.Ch02.Notation
public meta import Reynolds.Answers.Ch02.Semantics
public meta import Reynolds.Prelude

/-!
# §3.7 예제 — 빠른 거듭제곱

Reynolds §3.7 (pp.71–73)의 프로그램 유도를 따른다.

## 이 파일에서 다루는 것
입력 `x`, `n`에서 `y = x^n`을 계산한다. 지역 변수 `k`, `z`는 반복이 끝나면 복원된다.
불변식 `y*z^k = x^n ∧ k ≥ 0`과 변항 `k`로 전체 정확성을 증명한다.

## 핵심 아이디어
먼저 본체 `B`가 불변식을 보존하고 `k`를 줄인다고 가정하여 프로그램 전체를 조립한다.
그 뒤 홀수 감소와 짝수 반감으로 그 계약을 채운다. `z`를 새로 두어 입력 `x`를
보존하면서도 반복 중 밑을 제곱할 수 있다.

## 읽는 순서
`Semantic.lean` → `exp_schema_total` → 두 본체 가지 → `exp_total_correct`.

## 책과의 차이
책의 `even k`는 기존 언어의 `k rem 2 = 0`으로 표현한다. 지수는 자연수이므로
불변식에서 `k = m`인 자연수 `m`을 함께 둔다. `k ≥ 0`인 실행에서 뜻은 같다.
정수는 무한 정밀도다. 종료는 증명하지만 실행 비용이나 기계 정수 오버플로는 다루지 않는다.
-/

@[expose] public section

namespace Reynolds.Answers.Ch03.Examples

open Reynolds Reynolds.Answers.Ch01 Reynolds.Answers.Ch02 Reynolds.Answers.Ch03

-- ANCHOR: expProg
/-- 책 p73의 짝수 가지. 지수를 반으로 줄인 뒤 밑을 제곱한다. -/
def expEven : Comm String := ⟪ k := k ÷ 2; z := z × z ⟫ᶜ

/-- 책 p73의 홀수 가지. 지수를 하나 줄인 뒤 결과에 밑을 곱한다. -/
def expOdd : Comm String := ⟪ k := k - 1; y := y × z ⟫ᶜ

/-- 짝수이면 반감하고, 아니면 하나 줄이는 본체. -/
def expBody : Comm String := .ite ⟪ k rem 2 = 0 ⟫ᵇ expEven expOdd

/-- 책 p72의 프로그램 틀. 지역 `k`, `z`의 바깥 값은 종료 뒤 복원된다. -/
def expSchema (B : Comm String) : Comm String :=
  .newvar "k" (.var "n") (.newvar "z" (.var "x")
    (.seq ⟪ y := 1 ⟫ᶜ (.wh ⟪ k ≠ 0 ⟫ᵇ B)))

/-- §3.7의 빠른 거듭제곱 프로그램. 입력은 `x`, `n`이고 출력은 `y`다. -/
def expProg : Comm String := expSchema expBody

/-- 책의 불변식. 자연수 증인 `m`이 지수 `k`의 비음수성을 함께 표현한다. -/
def expInv (σ : State String) : Prop :=
  ∃ m : Nat, σ "k" = m ∧ σ "y" * σ "z" ^ m = σ "x" ^ (σ "n").toNat
-- ANCHOR_END: expProg

private theorem expConseq {P P' Q Q' : State String → Prop} {c : Comm String}
    (hp : ∀ σ, P σ → P' σ) (h : TotalCorrectS P' c Q')
    (hq : ∀ σ, Q' σ → Q σ) : TotalCorrectS P c Q := by
  intro σ hσ
  obtain ⟨τ, ht, hτ⟩ := h σ (hp σ hσ)
  exact ⟨τ, ht, hq τ hτ⟩

private def expPost (σ : State String) : Prop := σ "y" = σ "x" ^ (σ "n").toNat

-- ANCHOR: expSchemaTotal
-- ANCHOR: stmtExpSchemaTotal
/-- 책 p72의 증명 틀. 본체의 종료·불변식 보존·변항 감소만 알면 전체 프로그램이 옳다. -/
theorem exp_schema_total (B : Comm String)
    (hB : ∀ old : Int, TotalCorrectS
      (fun σ => expInv σ ∧ ⟦⟪ k ≠ 0 ⟫ᵇ⟧ᵇ σ = true ∧ σ "k" = old)
      B (fun σ => expInv σ ∧ σ "k" < old)) :
    TotalCorrectS (fun σ => 0 ≤ σ "n") (expSchema B)
      (fun τ => τ "y" = τ "x" ^ (τ "n").toNat)
-- ANCHOR_END: stmtExpSchemaTotal
    := by
  have loop : TotalCorrectS expInv (.wh ⟪ k ≠ 0 ⟫ᵇ B) expPost := by
    apply expConseq (fun _ h => h) (TotalCorrectS.wh hB ?_) ?_
    · rintro σ ⟨m, hk, _⟩ _
      omega
    · rintro σ ⟨⟨m, hk, hi⟩, hb⟩
      have hz : σ "k" = 0 := by
        simpa [BoolExp.eval, IntExp.eval, Cmp.denoteBool] using hb
      have hm : m = 0 := by omega
      simpa [expPost, hm] using hi
  have init : TotalCorrectS (fun σ => 0 ≤ σ "n")
      ⟪ k := n; z := x; y := 1 ⟫ᶜ expInv := by
    intro σ hn
    refine ⟨σ["k" := σ "n"]["z" := σ "x"]["y" := (1 : Int)], rfl,
      (σ "n").toNat, ?_, ?_⟩ <;> simp [hn]
  have straight := sq_sound.2 init loop
  -- DC를 z에 먼저 적용할 때 k 대입은 접두 명령으로 남는다.
  have hz := (dc_sound [⟪ k := n ⟫ᶜ] (fun σ => 0 ≤ σ "n") expPost
    "z" (.var "x") (.seq ⟪ y := 1 ⟫ᶜ (.wh ⟪ k ≠ 0 ⟫ᵇ B))
    (by intro σ v; simp [expPost])).2 straight
  exact (dc_sound [] (fun σ => 0 ≤ σ "n") expPost "k" (.var "n")
    (.newvar "z" (.var "x") (.seq ⟪ y := 1 ⟫ᶜ (.wh ⟪ k ≠ 0 ⟫ᵇ B)))
    (by intro σ v; simp [expPost])).2 hz
-- ANCHOR_END: expSchemaTotal

-- ANCHOR: expBodyOk
-- ANCHOR: stmtExpEvenArithmetic
/-- 짝수 반감의 두 의무: 누적 곱을 보존하고 양의 지수를 엄격히 줄인다. -/
@[exercise "§3.7 fastexp-even" 2]
theorem exp_even_arithmetic (y z : Int) (m : Nat) (heven : m % 2 = 0) (hpos : 0 < m) :
    y * (z * z) ^ (m / 2) = y * z ^ m ∧ m / 2 < m
-- ANCHOR_END: stmtExpEvenArithmetic
    := by
  constructor
  · rw [← pow_two, ← pow_mul, Nat.two_mul_div_two_of_even (Nat.even_iff.mpr heven)]
  · omega
-- ANCHOR_END: expBodyOk

private theorem expTwoAssign (Q : State String → Prop)
    (v w : String) (e f : IntExp String) :
    TotalCorrectS (fun σ => Q ((σ[v := e.eval σ])[w := f.eval (σ[v := e.eval σ])]))
      (.seq (.assign v e) (.assign w f)) Q :=
  sq_sound.2 (as_sound (fun σ => Q (σ[w := f.eval σ])) v e).2 (as_sound Q w f).2

private theorem expEven_total (old : Int) : TotalCorrectS
    (fun σ => (expInv σ ∧ ⟦⟪ k ≠ 0 ⟫ᵇ⟧ᵇ σ = true ∧ σ "k" = old) ∧
      ⟦⟪ k rem 2 = 0 ⟫ᵇ⟧ᵇ σ = true)
    expEven (fun σ => expInv σ ∧ σ "k" < old) := by
  apply expConseq ?_ (expTwoAssign _ "k" "z" ⟪ k ÷ 2 ⟫ₑ ⟪ z × z ⟫ₑ) (fun _ h => h)
  rintro σ ⟨⟨⟨m, hk, hi⟩, hb, hold⟩, he⟩
  have hm : m % 2 = 0 ∧ 0 < m := by
    simp [BoolExp.eval, IntExp.eval, IntOp.denote, Cmp.denoteBool, hk] at hb he
    omega
  obtain ⟨hpow, hlt⟩ := exp_even_arithmetic (σ "y") (σ "z") m hm.1 hm.2
  refine ⟨⟨m / 2, ?_, ?_⟩, ?_⟩
  · simp [IntExp.eval, IntOp.denote, hk]
  · simpa [IntExp.eval, IntOp.denote] using hpow.trans hi
  · simp [IntExp.eval, IntOp.denote, hk]
    omega

private theorem expOdd_total (old : Int) : TotalCorrectS
    (fun σ => (expInv σ ∧ ⟦⟪ k ≠ 0 ⟫ᵇ⟧ᵇ σ = true ∧ σ "k" = old) ∧
      ⟦⟪ k rem 2 = 0 ⟫ᵇ⟧ᵇ σ = false)
    expOdd (fun σ => expInv σ ∧ σ "k" < old) := by
  apply expConseq ?_ (expTwoAssign _ "k" "y" ⟪ k - 1 ⟫ₑ ⟪ y × z ⟫ₑ) (fun _ h => h)
  rintro σ ⟨⟨⟨m, hk, hi⟩, hb, hold⟩, _⟩
  have hm : 0 < m := by
    simp [BoolExp.eval, IntExp.eval, Cmp.denoteBool, hk] at hb
    omega
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  have hp : σ "y" * σ "z" * σ "z" ^ j = σ "x" ^ (σ "n").toNat := by
    rw [← hi, pow_succ]
    ring
  refine ⟨⟨j, ?_, ?_⟩, ?_⟩
  · simp [IntExp.eval, IntOp.denote, hk]
  · simpa [IntExp.eval, IntOp.denote] using hp
  · simp [IntExp.eval, IntOp.denote]
    omega

/-- CD로 두 대입열을 합치면 프로그램 틀이 요구하는 본체 계약을 만족한다. -/
theorem expBody_total (old : Int) : TotalCorrectS
    (fun σ => expInv σ ∧ ⟦⟪ k ≠ 0 ⟫ᵇ⟧ᵇ σ = true ∧ σ "k" = old)
    expBody (fun σ => expInv σ ∧ σ "k" < old) :=
  cd_sound.2 (expEven_total old) (expOdd_total old)

-- ANCHOR: stmtExpTotalCorrect
/-- §3.7 전체 정확성. 본체 계약을 채웠으므로 종료를 따로 가정하지 않는다. -/
theorem exp_total_correct :
    TotalCorrectS (fun σ => 0 ≤ σ "n") expProg
      (fun τ => τ "y" = τ "x" ^ (τ "n").toNat)
-- ANCHOR_END: stmtExpTotalCorrect
    := exp_schema_total expBody expBody_total

-- ANCHOR: expCorrect
-- ANCHOR: stmtExpCorrect
/-- 전체 정확성에서 얻는 부분 정확성. 종료한 결과는 `x^n`이다. -/
theorem exp_correct :
    PartialCorrectS (fun σ => 0 ≤ σ "n") expProg
      (fun τ => τ "y" = τ "x" ^ (τ "n").toNat)
-- ANCHOR_END: stmtExpCorrect
    := by
  intro σ hn τ ht
  obtain ⟨ρ, hr, hq⟩ := exp_total_correct σ hn
  have heq : ρ = τ := Flat.some.inj (hr.symm.trans ht)
  simpa [heq] using hq
-- ANCHOR_END: expCorrect

end Reynolds.Answers.Ch03.Examples
