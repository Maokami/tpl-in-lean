/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
import Reynolds

/-!
# 연습 독립성 검사 (`lake env lean scripts/check-independence.lean`)

`AGENTS.md` §1-9 의 **연습 독립성 원칙**을 기계적으로 검사한다: 채점 연습의 정답 증명이
**같은 장의 다른 채점 연습**에 (직접이든, 완성본으로 주어진 보조정리를 거쳐서든) 닿으면 안 된다.
닿으면 Exercises 트리에서 그 연습은 올바르게 풀어도 `sorry` 에 기대는 것으로 채점된다.

## 방법

Exercises 트리는 Answers 트리에서 채점 연습의 증명만 비운 사본이고, 앞 장은 Answers 를 그대로
쓴다(`scripts/gen-exercises.py`). 그러니 오염은 **같은 장 안에서만** 퍼진다. Answers 쪽에서
채점 연습마다 진술과 증명이 쓰는 상수를 같은 장 이름공간 안에서 추이적으로 따라가다가, 다른
채점 연습에 닿으면 그 경로를 보고한다.

## 왜 모듈이 아닌 파일인가

모듈 시스템에서 import 한 정리의 증명 본체는 `ConstantInfo.value?` 로 보이지 않는다
(`collectAxioms` 도 미리 계산된 공리 목록을 쓴다). 모듈이 아닌 파일에서 import 하면 본체가
불투명 상수로 보이므로(`value? (allowOpaque := true)`) 여기서 따라갈 수 있다.

실패하면 오류로 끝나므로 CI 에서 그대로 쓸 수 있다.
-/

open Lean Elab Command

/-- `Reynolds.Answers.Ch02.…` 의 장 이름공간(`Reynolds.Answers.Ch02`). -/
def chapterNs? (n : Name) : Option Name :=
  match n.components with
  | `Reynolds :: `Answers :: ch :: _ =>
      if ch.toString.startsWith "Ch" then some (`Reynolds.Answers ++ ch) else none
  | _ => none

/-- 상수 `c` 가 쓰는 상수들 (진술 + 본체). -/
def usedConsts (env : Environment) (c : Name) : Array Name :=
  match env.find? c with
  | none => #[]
  | some ci =>
    let t := ci.type.getUsedConstants
    match ci.value? (allowOpaque := true) with
    | some v => t ++ v.getUsedConstants
    | none => t

/--
`root` 에서 같은 장 이름공간 `ns` 안의 상수를 너비 우선으로 따라가 다른 채점 연습에 닿는
첫 경로들을 모은다. 채점 연습에 닿으면 거기서 멈춘다(그 너머는 그 연습 자신의 문제다).
-/
def violationsFrom (env : Environment) (exercises : NameSet) (ns : Name) (root : Name) :
    Array (List Name) := Id.run do
  let mut parent : Std.HashMap Name Name := {}
  let mut seen : NameSet := NameSet.empty.insert root
  let mut queue : Array Name := #[root]
  let mut i := 0
  let mut hits : Array (List Name) := #[]
  while i < queue.size do
    let n := queue[i]!
    i := i + 1
    for c in usedConsts env n do
      if seen.contains c || !ns.isPrefixOf c then continue
      seen := seen.insert c
      parent := parent.insert c n
      if exercises.contains c then
        -- 경로를 root 부터 복원한다.
        let mut path : List Name := [c]
        let mut cur := n
        while cur != root do
          path := cur :: path
          cur := parent.getD cur root
        hits := hits.push (root :: path)
      else
        queue := queue.push c
  return hits

/-- 사람이 읽을 짧은 이름: 장 이름공간을 뗀다. -/
def short (ns n : Name) : String := (n.replacePrefix ns .anonymous).toString

#eval show CommandElabM Unit from do
  let env ← getEnv
  let idOf : Std.HashMap Name String := Reynolds.exerciseRegistry.foldl (init := {})
    fun m (id, _, nm) => m.insert nm.toName id
  let exercises : NameSet := Reynolds.exerciseRegistry.foldl (init := {})
    fun s (_, _, nm) => s.insert nm.toName
  let mut total : Nat := 0
  let mut bad : Nat := 0
  let mut report : String := ""
  for (id, _, nm) in Reynolds.exerciseRegistry do
    let n := nm.toName
    let some ns := chapterNs? n | continue
    total := total + 1
    let hits := violationsFrom env exercises ns n
    if hits.isEmpty then continue
    bad := bad + 1
    -- 진술만으로 오염되는지: 진술이 쓰는 상수만으로 다른 연습에 닿는가.
    let typeOnly := (env.find? n).map (·.type.getUsedConstants) |>.getD #[]
    let stmt := typeOnly.any fun c => ns.isPrefixOf c && exercises.contains c && c != n
    report := report ++ s!"\n⛔ [{id}] {short ns n}{if stmt then "  (진술 자체가 다른 연습을 쓴다)" else ""}"
    for p in hits do
      let tgt := p.getLast!
      report := report ++ s!"\n    → [{idOf.getD tgt "?"}] " ++
        " ← ".intercalate (p.reverse.map (short ns))
  logInfo m!"연습 독립성 검사: 채점 연습 {total}개 중 위반 {bad}개{report}"
  if bad > 0 then
    throwError "연습 독립성 원칙 위반 {bad}건 — 위 경로의 선행 연습을 완성본으로 주거나 진술을 고쳐라"
