/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Exercises.Ch03.Semantic
public import Reynolds.Exercises.Ch03.Derived
public import Mathlib.Data.Nat.Fib.Basic
public meta import Reynolds.Answers.Ch02.Interpreter
public meta import Reynolds.Answers.Ch02.Notation
public meta import Reynolds.Answers.Ch02.Semantics
public meta import Reynolds.Prelude

/-!
# §3.6 피보나치: 지역 변수와 종료

Reynolds pp.69–71의 프로그램을 부분 정확성과 전체 정확성으로 검증한다.
`n = 0`을 먼저 처리하고, 나머지 경우에는 연속한 두 피보나치 수를 유지한다.
`k`, `g`, `t`는 지역 변수다. 실행이 끝나면 각 선언 전의 값으로 돌아간다.

## 읽는 순서

`Semantic.lean`의 DC·WHP·WHT → `fib_step`의 산술 의무 → `fib_correct`와
`fib_total_correct`의 조립 순서로 읽는다. `FastExp.lean`은 다음 예제다.

## 책과의 차이

책은 정수 전체에서 정의한 `fib`를 쓴다. 여기서는 `Nat.fib`를 쓰고,
도달 가능한 반복 상태에 맞춰 `1 ≤ k`를 불변식에 추가한다. 증인 `m`으로
`k = m+1`, `g = fib m`을 나타내므로 음수 인덱스가 생기지 않는다.
`fib`를 담기 위해 단언은 Lean 술어로 쓴다. AS·SQ·DC·CD·WHP·WHT의 의미 판을
조립하며, 책의 RAS·MSQ에 해당하는 직선 계산은 별도 보조정리로 묶는다.
-/

@[expose] public section

namespace Reynolds.Exercises.Ch03.Examples

open Reynolds Reynolds.Answers.Ch01 Reynolds.Answers.Ch02 Reynolds.Exercises.Ch03

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

/-- 지역 선언을 도입하기 전, 책 RAS 단계의 네 대입이 만드는 상태. -/
def fibStep (σ : State String) : State String :=
  σ["t" := σ "g"]["g" := σ "f"]["f" := σ "f" + σ "g"]["k" := σ "k" + 1]

/-- §3.6의 산술 의무. 한 단계가 불변식을 보존하면서 변항 `n−k`를 줄인다. -/
@[exercise "§3.6 fib-step" 2]
theorem fib_step (σ : State String)
    (h : fibInv σ ∧ ⟦⟪k ≠ n⟫ᵇ⟧ᵇ σ = true) :
    fibInv (fibStep σ) ∧ (fibStep σ) "n" - (fibStep σ) "k" < σ "n" - σ "k" := by
  -- `fibInv`의 증인 m은 k−1이다. 다음 상태의 증인을 정한다.
  -- `Nat.fib_add_two`로 연속한 피보나치 수를 연결한다.
  -- `State.subst_def`로 갱신을 펼치면 변항의 감소는 정수 산술이다.
  -- 이 연습은 미완성 DC·WHP·WHT 정리를 사용하지 않는다.
  sorry


private theorem totalPartial {P Q : State String → Prop} {c : Comm String}
    (h : TotalCorrectS P c Q) : PartialCorrectS P c Q := by
  intro σ hp τ ht
  obtain ⟨ρ, hr, hq⟩ := h σ hp
  have : ρ = τ := Flat.some.inj (hr.symm.trans ht)
  simpa [this] using hq

private theorem totalConseq {P P' Q Q' : State String → Prop} {c : Comm String}
    (hp : ∀ σ, P σ → P' σ) (h : TotalCorrectS P' c Q')
    (hq : ∀ σ, Q' σ → Q σ) : TotalCorrectS P c Q := by
  intro σ hσ
  obtain ⟨τ, ht, hτ⟩ := h σ (hp σ hσ)
  exact ⟨τ, ht, hq τ hτ⟩

/-- RAS의 계산 결과에 DC를 적용한다. 사후조건은 임시 변수 `t`를 보지 않는다. -/
theorem fibBody_total (old : Int) : TotalCorrectS
    (fun σ => fibInv σ ∧ ⟦⟪ k ≠ n ⟫ᵇ⟧ᵇ σ = true ∧ σ "n" - σ "k" = old)
    fibBody (fun σ => fibInv σ ∧ σ "n" - σ "k" < old) := by
  apply (dc_sound [] _ _ "t" (.var "g") ⟪ g := f; f := f + t; k := k + 1 ⟫ᶜ
    (by intro σ z; simp [fibInv])).2
  intro σ ⟨hi, hb, he⟩
  refine ⟨fibStep σ, ?_, ?_⟩
  · rfl
  · simpa [he] using fib_step σ ⟨hi, hb⟩

/-- WHP가 요구하는 본체 부분 정확성. 감소 정보와 종료 정보는 이 경로에서 쓰지 않는다. -/
theorem fibBody_ok :
    PartialCorrectS (fun σ => fibInv σ ∧ ⟦⟪ k ≠ n ⟫ᵇ⟧ᵇ σ = true) fibBody fibInv := by
  intro σ h τ ht
  exact (totalPartial (fibBody_total (σ "n" - σ "k")) σ ⟨h.1, h.2, rfl⟩ τ ht).1

private def fibPost (σ : State String) : Prop := σ "f" = Nat.fib (σ "n").toNat

private theorem fibExit (σ : State String)
    (h : fibInv σ ∧ ⟦⟪k ≠ n⟫ᵇ⟧ᵇ σ = false) : fibPost σ := by
  obtain ⟨⟨m, hk, hle, hn, hf, hg⟩, hb⟩ := h
  have he : σ "k" = σ "n" := by
    simpa [BoolExp.eval, IntExp.eval, Cmp.denoteBool] using hb
  have hm : m + 1 = (σ "n").toNat := by omega
  simpa [fibPost, hm] using hf

private theorem fibInit_total : TotalCorrectS (fun σ => 0 < σ "n")
    ⟪ k := 1; g := 0; f := 1 ⟫ᶜ fibInv := by
  intro σ hn
  refine ⟨σ["k" := (1 : Int)]["g" := (0 : Int)]["f" := (1 : Int)], rfl, 0, ?_⟩
  simp [State.subst_def, Function.update]
  omega

private theorem fibZero_total : TotalCorrectS
    (fun σ => 0 ≤ σ "n" ∧ ⟦⟪ n = 0 ⟫ᵇ⟧ᵇ σ = true) ⟪ f := 0 ⟫ᶜ fibPost := by
  intro σ h
  have hn : σ "n" = 0 := by
    simpa [BoolExp.eval, IntExp.eval, Cmp.denoteBool] using h.2
  refine ⟨σ["f" := (0 : Int)], rfl, ?_⟩
  simp [fibPost, hn]

/-- §3.6의 부분 정확성. WHP·DC·CD를 조립하면 종료한 결과는 `fib n`이다. -/
theorem fib_correct :
    PartialCorrectS (fun σ => 0 ≤ σ "n") fibProg
      (fun τ => τ "f" = Nat.fib (τ "n").toNat)
    := by
  apply PartialCorrectS.ite (totalPartial fibZero_total)
  have loop : PartialCorrectS fibInv (.wh ⟪ k ≠ n ⟫ᵇ fibBody) fibPost :=
    PartialCorrectS.conseq (fun _ h => h) (PartialCorrectS.wh fibBody_ok) fibExit
  have straight := PartialCorrectS.seq (totalPartial fibInit_total) loop
  -- 책 p70의 DC 두 단계: k 대입을 접두부에 둔 채 g를 지역화하고, 이어 k를 지역화한다.
  have hg := (dc_sound [⟪ k := 1 ⟫ᶜ] (fun σ => 0 < σ "n") fibPost
    "g" (.num 0) (.seq ⟪ f := 1 ⟫ᶜ (.wh ⟪ k ≠ n ⟫ᵇ fibBody))
    (by intro σ z; simp [fibPost])).1 straight
  have hk := (dc_sound [] (fun σ => 0 < σ "n") fibPost "k" (.num 1)
    (.newvar "g" (.num 0) (.seq ⟪ f := 1 ⟫ᶜ (.wh ⟪ k ≠ n ⟫ᵇ fibBody)))
    (by intro σ z; simp [fibPost])).1 hg
  apply PartialCorrectS.conseq ?_ hk (fun _ h => h)
  intro σ ⟨hn, hb⟩
  have hne : σ "n" ≠ 0 := by
    simpa [BoolExp.eval, IntExp.eval, Cmp.denoteBool] using hb
  omega

/-- §3.6의 전체 정확성. 변항 `n−k`에 WHT를 적용하므로 종료 가정이 필요 없다. -/
theorem fib_total_correct :
    TotalCorrectS (fun σ => 0 ≤ σ "n") fibProg
      (fun τ => τ "f" = Nat.fib (τ "n").toNat)
    := by
  apply cd_sound.2 fibZero_total
  have loop : TotalCorrectS fibInv (.wh ⟪ k ≠ n ⟫ᵇ fibBody) fibPost := by
    apply totalConseq (fun _ h => h) (TotalCorrectS.wh fibBody_total ?_) fibExit
    intro σ ⟨m, hk, hle, hn, hf, hg⟩ _
    omega
  have straight := sq_sound.2 fibInit_total loop
  have hg := (dc_sound [⟪ k := 1 ⟫ᶜ] (fun σ => 0 < σ "n") fibPost
    "g" (.num 0) (.seq ⟪ f := 1 ⟫ᶜ (.wh ⟪ k ≠ n ⟫ᵇ fibBody))
    (by intro σ z; simp [fibPost])).2 straight
  have hk := (dc_sound [] (fun σ => 0 < σ "n") fibPost "k" (.num 1)
    (.newvar "g" (.num 0) (.seq ⟪ f := 1 ⟫ᶜ (.wh ⟪ k ≠ n ⟫ᵇ fibBody)))
    (by intro σ z; simp [fibPost])).2 hg
  apply totalConseq ?_ hk (fun _ h => h)
  intro σ ⟨hn, hb⟩
  have hne : σ "n" ≠ 0 := by
    simpa [BoolExp.eval, IntExp.eval, Cmp.denoteBool] using hb
  omega

end Reynolds.Exercises.Ch03.Examples
