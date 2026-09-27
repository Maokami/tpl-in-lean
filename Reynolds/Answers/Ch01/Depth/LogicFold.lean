/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Answers.Ch01.Depth.Algebra

/-!
# 심화 A · 단언의 의미와 자유 변수를 접기로 읽기

Reynolds §1.2 pp.10–11은 구문 지향 의미 방정식이 함수를 유일하게 정하는 이유를
설명한다. p.11의 대수적 설명에서는 구문에서 목표 대수로 가는 준동형의 유일성을 쓴다.
이 선택 보충에서는 `LogicAlg`의 두 접기로 그 연결을 확인한다.

정수 식의 의미는 `State V → Int`, 단언의 의미는 `State V → Prop`이다.
비교 연산은 앞 정렬의 결과 둘을 받아 뒤 정렬의 결과를 만든다. 양화사는 본문의 의미를
여러 갱신 상태에 적용하므로, 목표 반송자에 상태 하나에서 계산한 값만 담아서는 부족하다.
Lean에서는 책의 진릿값을 `Prop`으로 표현한다.

§1.4 pp.15–16의 자유 변수 방정식도 같은 구문을 접는다. 이때 두 반송자는 모두
`Finset V`이고, 양화 연산은 결합 변수 이름을 지운다. 이는 구문에 나타난 자유 변수의
계산이며, 실제로 의미에 영향을 주는 변수만 추려낸다는 주장은 아니다.

`Algebra.lean`의 초기성에 아래 목표 대수를 넣으면 각 해석 쌍의 유일성이 따른다.
이 유일한 접기를 catamorphism이라고도 부른다. 채점 연습은 단언 의미의 접기 등식
하나이며, 초기성 연습을 풀지 않아도 직접 구조적 귀납법으로 풀 수 있다.
-/

@[expose] public section

namespace Reynolds.Answers.Ch01

open Reynolds

universe u

/-- Reynolds §1.2 pp.8–11의 의미 방정식을 담는 두 정렬 목표 대수다.
양화사는 본문의 상태 함수를 갱신된 상태에서 평가한다. -/
-- ANCHOR: logicEvalAlg
def logicEvalAlg (V : Type u) [DecidableEq V] : LogicAlg V where
  E := State V → Int
  A := State V → Prop
  num n := fun _ => n
  var x := fun σ => σ x
  eneg f := fun σ => -f σ
  ebin op f g := fun σ => op.denote (f σ) (g σ)
  tru := fun _ => True
  fls := fun _ => False
  cmp c f g := fun σ => c.denote (f σ) (g σ)
  anot p := fun σ => ¬ p σ
  abin op p q := fun σ => op.denote (p σ) (q σ)
  quant
    | .all, x, p => fun σ => ∀ n : Int, p (σ[x := n])
    | .ex, x, p => fun σ => ∃ n : Int, p (σ[x := n])
-- ANCHOR_END: logicEvalAlg

/-- 두 정렬 의미 대수의 첫 접기는 기존 정수 식 의미와 같다.
단언의 비교 분기를 위해 제공하는 보조정리다 (§1.2 pp.8–10). -/
theorem IntExp.eval_eq_foldE {V : Type u} [DecidableEq V] (e : IntExp V) :
    e.eval = (logicEvalAlg V).foldE e := by
  induction e with
  | num n => rfl
  | var x => rfl
  | neg e ih => simp only [IntExp.eval, LogicAlg.foldE, logicEvalAlg, ih]
  | bin op a b iha ihb =>
      simp only [IntExp.eval, LogicAlg.foldE, logicEvalAlg, iha, ihb]

/-- Reynolds §1.2 pp.10–11의 구문 지향 정의를 두 정렬 접기로 확인한다.
`cmp`에는 주어진 정수 식 보조정리를, `quant`에는 본문의 함수 등식을 쓴다. -/
-- ANCHOR: Assert.eval_eq_foldA
@[exercise "심화 A1.4" 2]
theorem Assert.eval_eq_foldA {V : Type u} [DecidableEq V] (p : Assert V) :
    p.eval = (logicEvalAlg V).foldA p := by
-- ANCHOR_END: Assert.eval_eq_foldA
  induction p with
  | tru => rfl
  | fls => rfl
  | cmp c a b =>
      simp only [Assert.eval, LogicAlg.foldA, logicEvalAlg, IntExp.eval_eq_foldE]
  | not p ih => simp only [Assert.eval, LogicAlg.foldA, logicEvalAlg, ih]
  | bin op p q ihp ihq =>
      simp only [Assert.eval, LogicAlg.foldA, logicEvalAlg, ihp, ihq]
  | quant q x p ih =>
      cases q <;> simp only [Assert.eval, LogicAlg.foldA, logicEvalAlg, ih]

/-- Reynolds §1.4 pp.15–16의 자유 변수 방정식을 담는 목표 대수다.
양화사의 종류와 무관하게 결합 이름을 지우며, 비교는 두 정수 식의 집합을 합친다. -/
def logicFvAlg (V : Type u) [DecidableEq V] : LogicAlg V where
  E := Finset V
  A := Finset V
  num _ := ∅
  var x := {x}
  eneg s := s
  ebin _ s t := s ∪ t
  tru := ∅
  fls := ∅
  cmp _ s t := s ∪ t
  anot s := s
  abin _ s t := s ∪ t
  quant _ x s := s.erase x

/-- 자유 변수 목표 대수의 첫 접기는 `IntExp.fv`다 (§1.4 pp.15–16). -/
theorem IntExp.fv_eq_foldE {V : Type u} [DecidableEq V] (e : IntExp V) :
    e.fv = (logicFvAlg V).foldE e := by
  induction e with
  | num n => rfl
  | var x => rfl
  | neg e ih => exact ih
  | bin op a b iha ihb =>
      simp only [IntExp.fv, LogicAlg.foldE, logicFvAlg, iha, ihb]

/-- 단언의 자유 변수도 같은 두 정렬 접기의 둘째 성분이다 (§1.4 pp.15–16). -/
theorem Assert.fv_eq_foldA {V : Type u} [DecidableEq V] (p : Assert V) :
    p.fv = (logicFvAlg V).foldA p := by
  induction p with
  | tru => rfl
  | fls => rfl
  | cmp c a b =>
      simp only [Assert.fv, LogicAlg.foldA, logicFvAlg, IntExp.fv_eq_foldE]
  | not p ih => exact ih
  | bin op p q ihp ihq =>
      simp only [Assert.fv, LogicAlg.foldA, logicFvAlg, ihp, ihq]
  | quant q x p ih => simp only [Assert.fv, LogicAlg.foldA, logicFvAlg, ih]

/-- 기존 의미 함수 쌍은 생성자를 보존한다. Reynolds §1.2 p.11의 준동형 조건이다. -/
theorem logicEval_isHom {V : Type u} [DecidableEq V] :
    (logicEvalAlg V).IsHom (IntExp.eval, Assert.eval) where
  num _ := rfl
  var _ := rfl
  eneg _ := rfl
  ebin _ _ _ := rfl
  tru := rfl
  fls := rfl
  cmp _ _ _ := rfl
  anot _ := rfl
  abin _ _ _ := rfl
  quant q _ _ := by cases q <;> rfl

/-- 자유 변수 방정식은 목표 대수의 생성자 보존 등식이다 (§1.4 pp.15–16). -/
theorem logicFv_isHom {V : Type u} [DecidableEq V] :
    (logicFvAlg V).IsHom (IntExp.fv, Assert.fv) where
  num _ := rfl
  var _ := rfl
  eneg _ := rfl
  ebin _ _ _ := rfl
  tru := rfl
  fls := rfl
  cmp _ _ _ := rfl
  anot _ := rfl
  abin _ _ _ := rfl
  quant _ _ _ := rfl

/-- Reynolds §1.2 p.11: 의미 방정식을 만족하는 두 함수는 기존 의미 함수와 같다.
초기성 연습 `LogicAlg.initial`을 이용하는 제공된 귀결이다. -/
-- ANCHOR: logicEval_unique
theorem logicEval_unique {V : Type u} [DecidableEq V]
    (h : (IntExp V → State V → Int) × (Assert V → State V → Prop))
    (hh : (logicEvalAlg V).IsHom h) : h = (IntExp.eval, Assert.eval) := by
-- ANCHOR_END: logicEval_unique
  obtain ⟨_, _, huniq⟩ := LogicAlg.initial (logicEvalAlg V)
  exact (huniq h hh).trans (huniq _ logicEval_isHom).symm

/-- Reynolds §1.4 pp.15–16의 자유 변수 방정식도 해석 쌍을 유일하게 정한다.
초기성 연습을 이용하는 제공된 귀결이며, 의미의 변수 의존성을 판정하는 정리는 아니다. -/
-- ANCHOR: logicFv_unique
theorem logicFv_unique {V : Type u} [DecidableEq V]
    (h : (IntExp V → Finset V) × (Assert V → Finset V))
    (hh : (logicFvAlg V).IsHom h) : h = (IntExp.fv, Assert.fv) := by
-- ANCHOR_END: logicFv_unique
  obtain ⟨_, _, huniq⟩ := LogicAlg.initial (logicFvAlg V)
  exact (huniq h hh).trans (huniq _ logicFv_isHom).symm

end Reynolds.Answers.Ch01
