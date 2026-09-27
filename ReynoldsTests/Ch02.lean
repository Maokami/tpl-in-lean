/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Answers.Ch02.Interpreter
public import Reynolds.Answers.Ch02.FullAbstraction
public import Reynolds.Answers.Ch02.Domain.LiftingLaws
public import Reynolds.Answers.Ch02.SumApproximation
-- `#guard`가 계산에 사용하는 정의를 메타 문맥에도 공개한다.
public meta import Reynolds.Answers.Ch02.Interpreter
public meta import Reynolds.Answers.Ch02.SumApproximation
public meta import Reynolds.Answers.Ch02.Notation
public meta import Reynolds.Answers.Ch02.Semantics
public meta import Reynolds.Answers.Ch01.Semantics
public meta import Reynolds.Prelude

/-!
# 2장 단위 테스트

Reynolds §2.4에 대응하는 계산 가능한 정의를 회귀 테스트한다.

## 확인하는 것

- `whileF`의 조건 거짓, 본체 성공, 본체 실패 분기
- `ite`의 두 갈래와 `newvar`의 바깥 값 복원
- `Comm.run`의 연료 0/1 및 본체 실행 횟수 경계
- 계승 프로그램의 결과와 명백히 발산하는 반복의 유한 근사

표시적 의미에 관한 정리는 커널이 검사하므로 여기서는 직접 계산할 수 있는 함수만
`#guard`로 테스트한다.

## 읽는 순서

`Reynolds/Answers/Ch02/Interpreter.lean` → 이 파일

## 책과의 차이

Reynolds는 유한 근사를 손으로 계산한다. 이 파일은 같은 경계와 생성자별 계산을 빌드 때마다
다시 실행하는 저장소 전용 회귀 테스트다.
-/

public section

namespace Reynolds.Answers.Ch02

open Reynolds Reynolds.Answers.Ch01

/-! ## 일반 `Option`과 평평한 결과의 순서 분리 -/

-- 라이브러리를 import한 뒤에도 일반 Option은 core의 순서를 선택한다.
example : (inferInstance : LE (Option Nat)) = instLEOption := rfl
example : (Option.some 1 : Option Nat) ≤ Option.some 2 :=
  Option.some_le_some.mpr (by decide)

-- 같은 자연수라도 Flat의 서로 다른 종료 결과는 어느 방향으로도 비교되지 않는다.
example : ¬ ((Flat.some 1 : Flat Nat) ≤ Flat.some 2) := by simp
example : ¬ ((Flat.some 2 : Flat Nat) ≤ Flat.some 1) := by simp
example (x : Flat Nat) : Flat.none ≤ x := Flat.none_le x

-- 관찰 경계는 일반 Option으로 돌아간다.
#guard (Flat.some 3).toOption == Option.some 3
#guard (Flat.none : Flat Nat).toOption == Option.none

-- 공개 관찰 함수는 종료 결과를 일반 Option으로 돌려준다.
example (σ : State String) : observe σ "x" .skip = Option.some (σ "x") := rfl

-- 공개 표시적 의미 API가 순차 합성과 상태 전달을 보존한다.
example : (Comm.seq (.assign "x" (.num 3)) .skip).eval (State.const 0) =
    Flat.some ((State.const 0)["x" := (3 : Int)]) := rfl

/-! ## `whileF`의 직접 분기 -/

-- 조건이 거짓이면 본체와 나머지를 실행하지 않고 현재 상태를 돌려준다.
#guard ((whileF (.fls : BoolExp String)
          (fun _ => Flat.none) (fun _ => Flat.none) (State.const 7)).map
          fun σ => σ "x") == Flat.some 7

-- 조건이 참이고 본체가 성공하면 그 상태를 나머지 함수에 넘긴다.
#guard ((whileF (.tru : BoolExp String) (fun _ => Flat.some (State.const 3))
          (fun _ => Flat.some (State.const 4)) (State.const 0)).map fun σ => σ "x") == Flat.some 4

-- 조건이 참이어도 본체가 실패하면 나머지 함수를 실행하지 않는다.
#guard (whileF (.tru : BoolExp String) (fun _ => Flat.none)
          (fun _ => Flat.some (State.const 4)) (State.const 0)).isNone

/-! ## 명령 생성자 -/

-- `ite`는 조건에 따라 해당 갈래만 실행한다.
#guard ((Comm.ite (.tru : BoolExp String) (.assign "x" (.num 1)) (.assign "x" (.num 2))).run
          0 (State.const 0) |>.map fun σ => σ "x") == Flat.some 1
#guard ((Comm.ite (.fls : BoolExp String) (.assign "x" (.num 1)) (.assign "x" (.num 2))).run
          0 (State.const 0) |>.map fun σ => σ "x") == Flat.some 2

-- `newvar`의 본문은 새 값을 보지만, 종료 상태에서는 바깥의 이전 값이 복원된다.
#guard ((Comm.newvar "x" (.num 1) (.assign "y" (.var "x"))).run 0 (State.const 9) |>.map
          fun σ => (σ "x", σ "y")) == Flat.some (9, 1)

/-! ## 연료 경계 -/

-- 연료 0에서는 조건을 검사하지 못한다.
#guard (⟪ while x > 0 do x := x - 1 ⟫ᶜ.run 0 (State.const 0)).isNone

-- 연료 1이면 처음부터 거짓인 조건을 검사하고 종료할 수 있다.
#guard ((⟪ while x > 0 do x := x - 1 ⟫ᶜ.run 1 (State.const 0)).map fun σ => σ "x")
  == Flat.some 0

-- 본체를 다섯 번 실행한 뒤 거짓 조건을 확인하려면 연료 6이 필요하다.
#guard (⟪ while x > 0 do x := x - 1 ⟫ᶜ.run 5 (State.const 5)).isNone
#guard ((⟪ while x > 0 do x := x - 1 ⟫ᶜ.run 6 (State.const 5)).map fun σ => σ "x")
  == Flat.some 0

-- Reynolds §2.1의 계승 프로그램은 x = 5에서 y = 120을 계산한다.
#guard ((⟪ y := 1; while x > 0 do (y := y × x; x := x - 1) ⟫ᶜ.run 10 (State.const 5)).map
          fun σ => (σ "x", σ "y")) == Flat.some (0, 120)

-- 명백히 발산하는 프로그램은 유한 연료 1000으로도 결과를 내지 않는다.
#guard ((⟪ while tt do skip ⟫ᶜ : Comm String).run 1000 (State.const 0)).isNone

/-! ## 책 pp. 37–38의 근사 경계와 전체 상태 -/

open SumApproximation

-- y=10, z=99에서 x만 바꾼다. 책의 결과가 관계없는 변수도 보존하는지 확인한다.
/-- 합산 근사 회귀 검사의 초기 상태. `z`는 보존 여부를 확인하는 변수다. -/
def sumInput (x : Int) : State String :=
  (State.const 99)["x" := x]["y" := (10 : Int)]

/-- 합산 근사의 `x`, `y`, `z` 값을 함께 관찰한다. -/
def sumObserve (n : Nat) (x : Int) : Flat (Int × Int × Int) :=
  (sumApprox n (sumInput x)).map fun σ ↦ (σ "x", σ "y", σ "z")

#guard sumObserve 0 0 == .none
#guard sumObserve 1 0 == .some (0, 10, 99)
#guard sumObserve 3 3 == .none
#guard sumObserve 4 3 == .some (0, 13, 99)
#guard sumObserve 6 3 == .some (0, 13, 99)
#guard sumObserve 8 (-1) == .none

-- 음수 입력의 발산은 유한한 테스트로 추측하지 않고 가설 없는 극한 정리로 확인한다.
example : sumLoop.eval (sumInput (-1)) = .none := by
  rw [sumLoop_eval_closed]
  simp [sumInput, State.subst_def, Function.update]

-- 이산 입력을 평평하지 않은 멱집합 도메인으로 보내도 source-lifting이 가능하다.
example : FlatLift.sourceLift (fun n : Nat ↦ ({n} : Set Nat)) .none = ∅ := rfl
example : FlatLift.sourceLift (fun n : Nat ↦ ({n} : Set Nat)) (.some 2) = {2} := rfl

end Reynolds.Answers.Ch02
