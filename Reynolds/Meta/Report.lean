/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Meta.Exercise
public meta import Reynolds.Meta.Exercise

/-!
# 채점 판정과 리포트

`@[exercise]` 가 붙은 선언마다 커널이 무엇을 믿고 있는지 확인한다.

증명이 참인지는 확인하지 않는다. `lake build` 가 통과했다면 커널이 이미 검사했다.
남는 질문은 그 증명이 `sorry` 나 다른 반칙에 기대는지 하나이고,
`Lean.collectAxioms` 로 답할 수 있다.

## `meta` 가 아닌 이유

`lake exe grade` 는 런타임에 도는 프로그램이고, `meta` 선언은 컴파일 시점 전용이라
런타임 코드에서 참조할 수 없다. `Lean.collectAxioms` 는 평범한 `public def` 이므로
런타임에서 그대로 쓸 수 있다.
-/

@[expose] public section

open Lean

namespace Reynolds

/--
증명에서 허용하는 공리.

Lean 과 Mathlib 에서 일상적으로 쓰이는 넷이다.
`sorryAx`(미완성)와 `Lean.ofReduceBool`(`native_decide` 가 남기는 흔적)은 목록에 없으므로
자동으로 불합격이 된다.
-/
def allowedAxioms : Array Name :=
  #[``Classical.choice, ``Quot.sound, ``propext, ``funext]

/-- 연습 하나에 대한 판정 결과. -/
inductive Verdict where
  /-- 통과. `sorry` 없고 허용 공리만 썼다. -/
  | ok
  /-- 미완성. `sorry` 가 남아 있다. -/
  | unfinished
  /-- 허용되지 않은 공리를 썼다. 보통 `native_decide` 아니면 직접 선언한 `axiom` 이다. -/
  | illegalAxiom (axioms : Array Name)
  deriving Repr

/-- 화면에 찍을 짧은 표식. -/
def Verdict.mark : Verdict → String
  | .ok             => "✅"
  | .unfinished     => "⛔"
  | .illegalAxiom _ => "❌"

/-- 사람이 읽을 설명. -/
def Verdict.describe : Verdict → String
  | .ok              => "통과"
  | .unfinished      => "미완성 (sorry)"
  | .illegalAxiom as => s!"허용되지 않은 공리: {as}"

/-- 통과 여부. CI 의 종료 코드를 정할 때 쓴다. -/
def Verdict.isOk : Verdict → Bool
  | .ok => true
  | _   => false

/-- 채점 대상 한 건. -/
structure Result where
  /-- 선언 이름. -/
  decl : Name
  /-- `@[exercise]` 메타데이터. -/
  info : ExerciseInfo
  /-- 판정. -/
  verdict : Verdict

/-- 별점을 `★★☆` 로 그린다. -/
def stars (n : Nat) : String :=
  let k := min n 3
  String.ofList (List.replicate k '★') ++ String.ofList (List.replicate (3 - k) '☆')

/--
선언 하나를 판정한다.

`collectAxioms` 는 import 된 선언에도 동작한다. 결과가 olean 에 미리 계산되어 있어서
모듈 경계를 넘어 증명 항을 뒤질 필요가 없다.
-/
def verdictOf (declName : Name) : CoreM Verdict := do
  let axs ← collectAxioms declName
  if axs.contains ``sorryAx then
    return .unfinished
  let bad := axs.filter (!allowedAxioms.contains ·)
  if bad.isEmpty then return .ok else return .illegalAxiom bad

end Reynolds
