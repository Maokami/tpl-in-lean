/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Answers.Ch01.Depth.LogicFold
public meta import Reynolds.Answers.Ch01.Depth.LogicFold
public meta import Mathlib.Data.Finset.Defs

/-! # 두 정렬 목표 대수의 경계 사례

양화사의 종류, 상태 갱신, 중첩 결합과 비교 정렬을 구분하는 사례다.
-/

open Reynolds Reynolds.Answers.Ch01

-- 전칭 양화사를 존재 양화사로 잘못 해석하면 이 두 결과를 함께 만족하지 못한다.
example : (logicEvalAlg String).foldA
    (.quant .ex "x" (.cmp .eq (.var "x") (.num 7))) (State.const 0) := by
  change ∃ n : Int, n = 7
  exact ⟨7, rfl⟩

example : ¬ (logicEvalAlg String).foldA
    (.quant .all "x" (.cmp .eq (.var "x") (.num 7))) (State.const 0) := by
  change ¬ ∀ n : Int, n = 7
  intro h
  have := h 0
  omega

-- 안쪽 결합은 같은 이름의 바깥 값을 덮어쓴다. 바깥 상태의 x=0도 남지 않는다.
example : (logicEvalAlg String).foldA
    (.quant .all "x" (.quant .ex "x" (.cmp .eq (.var "x") (.num 7))))
    (State.const 0) := by
  change ∀ _ : Int, ∃ n : Int, n = 7
  intro _
  exact ⟨7, rfl⟩

-- 비교의 입력은 정수 식 접기를 거친다. 자유 변수 y는 양화사 밖의 상태를 읽는다.
example : (logicEvalAlg String).foldA
    (.quant .ex "x" (.cmp .eq (.bin .add (.var "x") (.var "y")) (.num 9)))
    (State.const 4) := by
  change ∃ n : Int, n + 4 = 9
  exact ⟨5, rfl⟩

-- 결합 이름만 제거한다. 양화사 종류는 자유 변수 결과를 바꾸지 않는다.
#guard @BEq.beq (Finset String) inferInstance ((logicFvAlg String).foldA
    (.quant .all "x" (.cmp .eq (.var "x") (.var "y")))) {"y"}
#guard @BEq.beq (Finset String) inferInstance ((logicFvAlg String).foldA
    (.quant .ex "x" (.cmp .eq (.var "x") (.var "y")))) {"y"}
#guard @BEq.beq (Finset String) inferInstance ((logicFvAlg String).foldA
    (.quant .all "x" (.quant .ex "x" (.cmp .eq (.var "x") (.var "y"))))) {"y"}

-- 의미가 항상 0인 식도 구문적 자유 변수 x를 가진다.
#guard @BEq.beq (Finset String) inferInstance
    ((logicFvAlg String).foldE (.bin .sub (.var "x") (.var "x"))) {"x"}

-- 유일성은 두 정렬을 함께 식별한다. 임의의 새 구현에도 같은 API를 적용할 수 있다.
example (h : (IntExp String → State String → Int) ×
    (Assert String → State String → Prop)) (hh : (logicEvalAlg String).IsHom h) :
    h.2 = Assert.eval := congrArg Prod.snd (logicEval_unique h hh)

example (h : (IntExp String → Finset String) × (Assert String → Finset String))
    (hh : (logicFvAlg String).IsHom h) : h.2 = Assert.fv :=
  congrArg Prod.snd (logicFv_unique h hh)
