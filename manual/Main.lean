/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
import VersoManual
import Manual

open Verso.Genre Manual

/-- 출력 설정. HTML 만 만들고 TeX 는 건너뛴다. -/
def config : RenderConfig where
  emitTeX := false
  emitHtmlSingle := .no
  emitHtmlMulti := .immediately
  htmlDepth := 2

/-- 문서 생성 진입점. `lake exe build-manual` 이 이걸 부른다.

`manual/` 은 코드 패키지와 달리 모듈 시스템을 쓰지 않는다 — Verso 관례를 따른다.
자세한 근거는 `AGENTS.md` §1-10. -/
def main := manualMain (%doc Manual) (config := config)
