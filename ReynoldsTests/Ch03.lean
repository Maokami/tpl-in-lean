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

Reynolds §3.3–§3.5의 AS·SQ·CD·WHP를 실제 명령에 적용한다.
3장 전체를 가져오므로 `lake build --wfail ReynoldsTests`가 3장의 정답도 검사한다.

## 확인하는 것

- AS의 갱신 상태와 전체 정확성 성분
- SQ가 연결하는 종료 증인과 CD의 두 가지
- WHP가 발산에 허용하는 거짓 사후조건
- 거짓 조건의 반복이 본체를 실행하지 않는 연료 경계

정리의 적용은 커널이 검사하고, 종료·분기 계산은 실행기의 유한 연료로 확인한다.

## 읽는 순서

`Reynolds/Answers/Ch03/Semantic.lean` → 이 파일.

## 책과의 차이

책의 규칙을 적용하는 저장소 회귀 검사다. 새로운 추론 규칙을 추가하지 않는다.
-/

public section

open Reynolds Reynolds.Answers.Ch01 Reynolds.Answers.Ch02 Reynolds.Answers.Ch03

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
  (State.const 0)).map (fun σ => σ "x") == some 0

end
