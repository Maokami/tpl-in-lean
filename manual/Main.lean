/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
import VersoManual
import Manual

open Verso.Genre Manual

/-- 좁은 화면에서 코드와 제목이 본문 폭을 밀어내지 않게 하는 보정 스타일. -/
def responsiveCodeStyle : Verso.Output.Html := open Verso.Output.Html in
  {{<style>{{Verso.Output.Html.text false "
    main section { min-width: 0; }
    main h1, main h2 {
      word-break: keep-all;
      text-wrap: balance;
    }
    main li em, main li strong {
      word-break: keep-all;
    }
    .hl.lean.block {
      box-sizing: border-box;
      max-width: 100%;
      overflow-x: auto;
    }
    .prev-next-buttons > * {
      min-width: 0;
      overflow-wrap: break-word;
      text-wrap: balance;
      word-break: keep-all;
    }
    @media screen and (max-width: 900px) {
      :root {
        --search-bar-width: 12rem;
      }
      .header-title-wrapper,
      .header-title {
        min-width: 0;
      }
      .header-title {
        font-size: 1.25rem;
        margin-right: calc(var(--search-bar-width) + 1rem);
      }
      .header-title h1 {
        font-size: 0;
        overflow: hidden;
        text-overflow: ellipsis;
      }
      .header-title h1::before {
        content: 'tpl-in-lean';
        font-size: 1.25rem;
      }
    }
  "}}</style>}}

/-- 출력 설정. HTML 만 만들고 TeX 는 건너뛴다. -/
def config : RenderConfig where
  emitTeX := false
  emitHtmlSingle := .no
  emitHtmlMulti := .immediately
  htmlDepth := 2
  extraHead := #[responsiveCodeStyle]

/-- 문서 생성 진입점. `lake exe build-manual` 이 이걸 부른다.

`manual/` 은 코드 패키지와 달리 모듈 시스템을 쓰지 않는다 — Verso 관례를 따른다.
자세한 근거는 `AGENTS.md` §1-10. -/
def main := manualMain (%doc Manual) (config := config)
