/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds

/-!
# `lake exe grade` — 연습문제 채점기

```
lake exe grade                  # Exercises 전체
lake exe grade --chapter 1      # 1장만
lake exe grade --answers        # Answers 검증 (CI용. 하나라도 실패하면 exit 1)
lake exe grade --json           # 기계 판독용 (GitHub Actions 진행판)
```

채점은 `Lean.collectAxioms` 하나로 끝난다. 증명이 참인지는 볼 필요가 없다 —
`lake build`가 통과했다면 커널이 이미 확인했다. 남은 질문은
"그 증명이 `sorry`나 다른 반칙에 기대는가" 뿐이다. 자세한 근거는 `Reynolds/Meta/Report.lean`.
-/

@[expose] public section

open Lean Reynolds

/-- 실행 옵션. -/
structure Config where
  /-- `Answers` 트리를 검사한다(CI 모드). 기본은 `Exercises`. -/
  answers : Bool := false
  /-- JSON 으로 출력한다. -/
  json : Bool := false
  /-- 특정 장만 본다. `none` 이면 전부. -/
  chapter : Option Nat := none

/-- 명령줄 인자를 파싱한다. 알 수 없는 인자는 무시하지 않고 알려 준다. -/
def parseArgs (args : List String) : Except String Config :=
  go args {}
where
  go : List String → Config → Except String Config
    | [], c => .ok c
    | "--answers" :: rest, c => go rest { c with answers := true }
    | "--json" :: rest, c => go rest { c with json := true }
    | "--chapter" :: n :: rest, c =>
        match n.toNat? with
        | some k => go rest { c with chapter := some k }
        | none   => .error s!"--chapter 에 숫자가 필요하다: {n}"
    | a :: _, _ => .error s!"알 수 없는 인자: {a}"

/-- 검사 대상 이름공간 접두사. -/
def Config.prefixOf (c : Config) : Name :=
  if c.answers then `Reynolds.Answers else `Reynolds.Exercises

/-- `Reynolds.Answers.Ch01.…` 에서 장 번호를 뽑는다. -/
def chapterOf (n : Name) : Option Nat := do
  let parts := n.componentsRev.reverse.map toString
  let c ← parts.find? fun s => s.startsWith "Ch" && (s.drop 2).toNat?.isSome
  (c.drop 2).toNat?

/--
레지스트리에서 대상을 골라 판정한다.

레지스트리(`Reynolds.exerciseRegistry`)는 컴파일 시점에 `@[exercise]` 애트리뷰트로부터
생성된 **평범한 `def`** 다. 런타임 코드가 `meta` 선언을 참조할 수 없어서 이렇게 우회한다 —
자세한 사정은 `Reynolds.Meta.Exercise` 의 `emit_exercise_registry` 를 보라.
-/
def collect (cfg : Config) : CoreM (Array Result) := do
  let pfx := cfg.prefixOf
  let picked := exerciseRegistry.filter fun (_, _, nm) =>
    let n := nm.toName
    pfx.isPrefixOf n && (match cfg.chapter with
      | none   => true
      | some k => chapterOf n == some k)
  picked.mapM fun (id, st, nm) => do
    let n := nm.toName
    return { decl := n, info := { id, stars := st }, verdict := ← verdictOf n }

/-- 사람이 읽는 표. -/
def render (rs : Array Result) : String := Id.run do
  if rs.isEmpty then
    return "채점 대상이 없다. `@[exercise]` 가 붙은 선언을 찾지 못했다."
  let mut out := "| | 문제 | 난이도 | 선언 | 결과 |\n|---|---|---|---|---|\n"
  for r in rs do
    let row := s!"| {r.verdict.mark} | {r.info.id} | {stars r.info.stars} " ++
               s!"| `{r.decl}` | {r.verdict.describe} |\n"
    out := out ++ row
  let ok := rs.filter (·.verdict.isOk) |>.size
  let pct := if rs.size == 0 then 0 else ok * 100 / rs.size
  return out ++ s!"\n**{ok} / {rs.size} ({pct}%)**\n"

/-- 기계 판독용 JSON. GitHub Actions 진행판이 이걸 읽는다. -/
def renderJson (rs : Array Result) : String :=
  let items := rs.toList.map fun r =>
    Json.mkObj [
      ("id", .str r.info.id),
      ("stars", .num r.info.stars),
      ("decl", .str (toString r.decl)),
      ("ok", .bool r.verdict.isOk),
      ("status", .str r.verdict.describe)]
  (Json.mkObj [
    ("total", .num rs.size),
    ("passed", .num (rs.filter (·.verdict.isOk) |>.size)),
    ("items", .arr items.toArray)]).pretty

/-- 진입점. -/
def main (args : List String) : IO UInt32 := do
  let cfg ← match parseArgs args with
    | .ok c => pure c
    | .error e => IO.eprintln e; return 2
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Reynolds }] {} (trustLevel := 1024)
  let (rs, _) ← (collect cfg).toIO { fileName := "<grade>", fileMap := default } { env }
  IO.println (if cfg.json then renderJson rs else render rs)
  -- Answers 모드에서는 하나라도 실패하면 CI 를 세운다.
  if cfg.answers && rs.any (!·.verdict.isOk) then return 1
  return 0

end
