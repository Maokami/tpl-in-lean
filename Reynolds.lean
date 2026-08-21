/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Init
public import Reynolds.Compat
public import Reynolds.Prelude
public import Reynolds.Meta.Exercise
public import Reynolds.Meta.Report
public import Reynolds.Answers.Ch01
public import Reynolds.Answers.Ch02
public import Reynolds.Exercises.Ch01
public import Reynolds.Exercises.Ch02
public meta import Reynolds.Meta.Exercise

/-!
# `tpl-in-lean` 루트 모듈

모든 장을 import 하고, 마지막에 채점기가 읽을 **연습 레지스트리**를 굳힌다.
새 파일을 추가하면 여기에 `public import` 를 한 줄 더한다.
-/

@[expose] public section

namespace Reynolds

-- `@[exercise]` 가 붙은 모든 선언의 목록 `exerciseRegistry` 를 생성한다.
-- `lake exe grade` 가 이걸 읽는다.
--
-- **이 파일 맨 아래에 있어야 한다.** 위의 `import` 가 전부 처리된 뒤에야
-- 환경에 모든 연습이 들어와 있기 때문이다. 자세한 사정은
-- `Reynolds.Meta.Exercise` 의 `emit_exercise_registry` docstring 참고.
--
-- (docstring `/-- -/` 은 선언에만 붙는다. 커맨드 앞에는 `--` 주석을 쓴다.)
emit_exercise_registry exerciseRegistry

end Reynolds
