/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Cslib.Init
public import Reynolds.Compat

/-!
# 프로젝트 공통 진입점

`Reynolds/` 아래의 **모든** 파일이 (전이적으로) 이 파일을 import한다.
기본 린터 설정과 CSlib 재수출을 한곳에 모으기 위해서다.
CSlib의 `Cslib/Init.lean`이 같은 역할을 하며, 그 관례를 그대로 따랐다.

여기에 import를 추가할 때는 신중해야 한다. 전 파일의 컴파일 시간에 영향을 준다.
-/
