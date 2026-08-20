/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
import VersoManual
import Manual.Intro

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External

set_option pp.rawOnError true

-- 예제 코드를 끌어올 프로젝트. 이 저장소의 루트(= Lean 라이브러리 패키지)다.
set_option verso.exampleProject ".."
-- 기본 모듈. 각 코드 블록에서 `(module := …)` 로 덮어쓸 수 있다.
set_option verso.exampleModule "Reynolds.Answers.Ch01.Syntax"

#doc (Manual) "Theories of Programming Languages in Lean" =>
%%%
authors := ["tpl-in-lean contributors"]
shortTitle := "tpl-in-lean"
%%%

John C. Reynolds, *Theories of Programming Languages* (Cambridge University Press, 1998)를
Lean 4 로 따라 읽는 스터디 자료다.

이 문서는 **책을 대신하지 않는다.** 책 옆에 두고 읽는 안내서다.
저장소의 Lean 코드를 직접 인용하므로, 코드가 바뀌면 이 문서의 빌드가 깨진다.
그것이 목적이다 — 설명과 코드가 어긋날 수 없다.

{include 1 Manual.Intro}
