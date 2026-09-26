/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
import Reynolds

/-!
# 채점 연습과 같은 진술의 완성 정리 검사

완성된 보조정리가 채점 연습과 같은 진술이면, 학생이 그 정리 하나로 연습을
끝낼 수 있다. Answers의 비채점 정리와 채점 연습의 타입을 정의상 비교한다.
-/

open Lean Elab Meta

/-- Answers 이름공간의 선언인가. -/
def isAnswersDecl (n : Name) : Bool :=
  match n.components with
  | `Reynolds :: `Answers :: _ => true
  | _ => false

/-- 우주 변수 이름과 인자 이름에 관계없이 두 선언의 진술을 비교한다. -/
def sameStatement (n1 n2 : Name) : MetaM Bool := do
  try
    let e1 ← mkConstWithFreshMVarLevels n1
    let e2 ← mkConstWithFreshMVarLevels n2
    let t1 ← inferType e1
    let t2 ← inferType e2
    withNewMCtxDepth <| isDefEq t1 t2
  catch _ =>
    return false

#eval show CoreM Unit from do
  let env ← getEnv
  let exercises : Array (String × Name) :=
    Reynolds.exerciseRegistry.filterMap fun (id, _, nm) =>
      let n := nm.toName
      if isAnswersDecl n then some (id, n) else none
  let exerciseNames : NameSet := exercises.foldl (init := {}) fun s (_, n) => s.insert n
  let mut candidates : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if isAnswersDecl n && !exerciseNames.contains n && ci.isTheorem then
      candidates := candidates.push n
  let mut hits : Array (String × Name × Name) := #[]
  for (id, exercise) in exercises do
    for candidate in candidates do
      if ← MetaM.run' (sameStatement exercise candidate) then
        hits := hits.push (id, exercise, candidate)
  logInfo m!"중복 진술 검사: 채점 연습 {exercises.size}개, 비채점 정리 {candidates.size}개, 위반 {hits.size}건"
  for (id, exercise, candidate) in hits do
    logInfo m!"⛔ [{id}] {exercise} ↔ {candidate}"
  if !hits.isEmpty then
    throwError "채점 연습과 진술이 같은 완성 정리가 있다"
