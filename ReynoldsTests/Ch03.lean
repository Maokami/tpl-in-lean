/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Answers.Ch03
public meta import Reynolds.Answers.Ch03.Examples.FastExp

/-!
# 3장 의미 규칙 회귀 검사

Reynolds §3.3–§3.5의 AS·SQ·CD·WHP·WHT를 실제 명령에 적용한다.
3장 전체를 가져오므로 `lake build --wfail ReynoldsTests`가 3장의 정답도 검사한다.

## 확인하는 것

- AS의 갱신 상태와 전체 정확성 성분
- SQ가 연결하는 종료 증인과 CD의 두 가지
- WHP가 발산에 허용하는 거짓 사후조건
- 거짓 조건의 반복이 본체를 실행하지 않는 연료 경계
- WHT의 엄격한 감소와 마지막 음수 변항, 전체 정확성의 극한과 바닥

정리의 적용은 커널이 검사하고, 종료·분기 계산은 실행기의 유한 연료로 확인한다.

## 읽는 순서

`Reynolds/Answers/Ch03/Semantic.lean` → 이 파일.

## 책과의 차이

책의 규칙을 적용하는 저장소 회귀 검사다. 새로운 추론 규칙을 추가하지 않는다.
-/

public section

open Reynolds Reynolds.Answers.Ch01 Reynolds.Answers.Ch02 Reynolds.Answers.Ch03

-- 구문 사전조건 계산의 실패 가능성은 실행 결과의 평평한 순서와 독립적이다.
example : Comm.wp (V := String) .skip .tru = Option.some .tru := rfl
example : Comm.wp (V := String) (.wh .tru .skip) .tru = Option.none := rfl

-- AS의 두 성분과 구문 대입 API가 같은 명령을 다룬다.
example : TotalCorrectS (fun _ : State String => True) (.assign "x" (.num 1)) (fun _ => True) :=
  (as_sound (fun _ => True) "x" (.num 1)).2

example : ｛⟪ x = 1 ⟫ₐ｝⟪ x := x + 1 ⟫ᶜ｛⟪ x = 2 ⟫ₐ｝ := by
  intro σ hp
  apply (as_sound ⟦⟪ x = 2 ⟫ₐ⟧ₐ "x" ⟪ x + 1 ⟫ₑ).1 σ
  simp [Assert.eval, IntExp.eval, IntOp.denote, Cmp.denote] at hp ⊢
  omega

-- 종료 증인을 잇는 SQ와 두 가지를 확인하는 CD.
example : TotalCorrectS (fun _ : State String => True)
    (.seq (.assign "x" (.num 1)) (.assign "y" (.num 2))) (fun _ => True) :=
  sq_sound.2 (as_sound (fun _ => True) "x" (.num 1)).2
    (as_sound (fun _ => True) "y" (.num 2)).2

example (b : BoolExp String) : TotalCorrectS (fun _ => True)
    (.ite b .skip .skip) (fun _ => True) :=
  cd_sound.2 (fun σ _ => ⟨σ, rfl, trivial⟩) (fun σ _ => ⟨σ, rfl, trivial⟩)

-- 발산하는 반복의 부분 정확성은 거짓 사후조건도 허용한다.
example : PartialCorrectS (fun _ : State String => True)
    (.wh (.cmp .eq (.num 0) (.num 0)) .skip) (fun _ => False) := by
  intro σ hi τ hτ
  have hbody : PartialCorrectS (fun σ : State String =>
      True ∧ ⟦BoolExp.cmp .eq (.num 0) (.num 0)⟧ᵇ σ = true) .skip (fun _ => True) :=
    fun _ _ _ _ => trivial
  have h := (PartialCorrectS.wh hbody σ hi τ hτ).2
  simp [BoolExp.eval, IntExp.eval, Cmp.denoteBool] at h

-- 조건이 거짓인 반복은 본체를 실행하지 않는다.
#guard ((Comm.wh (.cmp .eq (.num 0) (.num 1)) (.assign "x" (.num 9))).run 1
  (State.const 0)).map (fun σ => σ "x") == Flat.some 0

-- WHT의 비음수 전제는 조건이 참일 때만 요구된다. -1에서 즉시 끝나도 된다.
example : TotalCorrectS (fun _ : State String => True) (.wh .fls .skip)
    (fun σ => True ∧ ⟦BoolExp.fls⟧ᵇ σ = false) := by
  apply TotalCorrectS.wh (E := fun _ => -1)
  · intro n σ ⟨_, hb, _⟩
    simp [BoolExp.eval] at hb
  · intro σ _ hb
    simp [BoolExp.eval] at hb

-- x=0에서도 한 바퀴 돌고 -1에서 끝난다. 최종 변항의 비음수 조건을 추가하면 안 된다.
example : TotalCorrectS (fun _ : State String => True)
    ⟪ while 0 ≤ x do x := x - 1 ⟫ᶜ
    (fun σ => True ∧ ⟦⟪ 0 ≤ x ⟫ᵇ⟧ᵇ σ = false) := by
  apply TotalCorrectS.wh (E := fun σ => σ "x")
  · intro n σ ⟨_, _, he⟩
    refine ⟨σ["x" := σ "x" - 1], rfl, trivial, ?_⟩
    simp only [State.subst_self]
    omega
  · intro σ _ hb
    change decide (0 ≤ σ "x") = true at hb
    exact of_decide_eq_true hb

#guard (⟪ while 0 ≤ x do x := x - 1 ⟫ᶜ.run 2 (State.const 0)).map (fun σ => σ "x")
  == Flat.some (-1)
#guard (⟪ while 0 ≤ x do x := x - 1 ⟫ᶜ.run 1 (State.const 0)).map (fun σ => σ "x")
  == Flat.none

-- 엄격한 감소가 없는 skip 본체에는 같은 변항 전제를 만들 수 없다.
example : ¬ (∀ n : Int, TotalCorrectS
    (fun σ : State String => σ "x" = n) .skip (fun σ => σ "x" < n)) := by
  intro h
  obtain ⟨τ, hτ, hlt⟩ := h 0 (State.const 0) rfl
  change Flat.some (State.const 0) = Flat.some τ at hτ
  obtain rfl := Flat.some.inj hτ
  change (0 : Int) < 0 at hlt
  omega

-- 상수 사슬도 전체 정확성의 극한 보존을 쓸 수 있다.
example : ∀ σ : State String, True → ∃ τ,
    (Chain.const (fun ρ : State String => Flat.some ρ)).lub σ = Flat.some τ ∧ True :=
  (total_admissible (fun _ => True) (fun _ => True)).1 _ (fun _ σ _ => ⟨σ, rfl, trivial⟩)

-- 사전조건이 비지 않으면 바닥에서 전체 정확성이 실패한다.
example : ¬ (∀ σ : State String, True → ∃ τ,
    (⊥ : State String → SigmaBot String) σ = Flat.some τ ∧ True) :=
  (total_admissible (fun _ => True) (fun _ => True)).2 ⟨State.const 0, trivial⟩

-- 빈 사전조건은 예외다. 이 가정을 빼면 위의 부정 명제가 거짓이 된다.
example : ∀ σ : State String, False → ∃ τ,
    (⊥ : State String → SigmaBot String) σ = Flat.some τ ∧ True := by
  intro _ h
  exact h.elim

-- 기존 구문 WHT의 공개 소비자도 그대로 쓸 수 있다.
example : ［⟪ x ≤ 100 ⟫ₐ］⟪ while x < 100 do x := x + 1 ⟫ᶜ［⟪ x = 100 ⟫ₐ］ :=
  HoareT.sound countTo100_total

end
