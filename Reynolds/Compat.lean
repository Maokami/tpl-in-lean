/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Cslib.Foundations.Data.HasFresh
public import Cslib.Foundations.Syntax.HasSubstitution
public import Cslib.Foundations.Syntax.HasAlphaEquiv

/-!
# CSlib 재수출 층 (churn 방어벽)

CSlib 에서 실제로 쓰는 것만 골라 이 파일 하나로 모은다.

CSlib 는 아직 젊은 라이브러리이고 `ORGANISATION.md` 가 스스로
*"still under active discussion and is subject to change"* 라고 밝힌다.
이름이나 경로가 바뀌면 저장소 전체가 아니라 이 파일만 고치면 된다.

## 여기서 끌어오는 것

| CSlib | Reynolds 책에서의 역할 |
|---|---|
| `HasFresh` | §1.1 ⟨var⟩ — "표현이 지정되지 않은 가산 무한 변수 집합" |
| `HasSubstitution` (`t[x := s]`) | §1.2 상태 갱신 `[σ \| v: n]`, §1.4 치환 `p / v → e` |
| `HasAlphaEquiv` (`m =α n`) | §1.4 명제 1.5 이름 바꾸기 정리(α-변환) |

6장(전이 의미론) 이후로는 `Cslib.Foundations.Semantics.LTS`가 추가된다.
-/

@[expose] public section

namespace Reynolds

-- CSlib 이름을 `Reynolds` 이름공간으로 끌어온다. 설명은 `Reynolds.Prelude`.
export Cslib (HasFresh HasSubstitution HasAlphaEquiv)

end Reynolds
