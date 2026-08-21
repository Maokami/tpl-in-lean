/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Lean

/-!
# `@[exercise]` 애트리뷰트 — **선언 전용 모듈**

```lean
@[exercise "Prop 1.1" 2]
theorem coincidence_intExp … := by sorry
```

## 이 파일이 왜 따로 있는가

`initialize` 로 만든 환경 확장(environment extension)은 같은 모듈에서 사용할 수 없다.
그래서 세 모듈로 나뉜다.

| 모듈 | 역할 |
|---|---|
| `Reynolds.Meta.Exercise` (이 파일) | 애트리뷰트 **선언** |
| `Reynolds.Exercises.**`, `Reynolds.Answers.**` | 애트리뷰트 **사용** |
| `Reynolds.Meta.Report`, `Grade` | 애트리뷰트 **판독** |

모듈 시스템에서 기본 가시성은 private이므로 `public initialize`로 명시해야
downstream에서 보인다. 판독하는 쪽은 `public meta import Reynolds.Meta.Exercise`가 필요하다.

셋 다 실제로 겪은 오류다. 자세한 내용은 `AGENTS.md` §10.

## 왜 "본인 sorry"와 "선행 미완성"을 구분하지 않는가

**Lean은 다른 모듈에 있는 정리의 증명 항을 볼 수 없다** (`ConstantInfo.value?`가 `none`).
따라서 `sorry`가 이 선언에서 왔는지 의존하는 선언에서 왔는지 알아낼 방법이 없다.

그래서 구분하는 대신 **구분할 필요가 없게** 설계했다 — `AGENTS.md` §1-9의
**연습 독립성 원칙**: 모든 연습은 주어진 완성 자료만으로 풀 수 있어야 한다.
그러면 `sorry`가 전파될 일이 없고 판정이 정확해진다.
-/

public section

open Lean

namespace Reynolds

/-- `@[exercise]`가 선언에 붙이는 메타데이터. -/
structure ExerciseInfo where
  /-- 책의 문제 번호 또는 명제 번호. 예: `"Prop 1.1"`, `"Ex 2.5"`. -/
  id : String
  /-- 난이도. 1 = 정의를 따라 쓰면 됨, 2 = 구조적 귀납법 + 약간의 궁리,
      3 = 결합 케이스가 까다롭거나 진술의 일반화가 필요. -/
  stars : Nat
  deriving Repr

/--
연습문제 표시. 난이도를 생략하면 1이다.

```lean
@[exercise "Prop 1.1"]      -- ★
@[exercise "Prop 1.3" 3]    -- ★★★
```
-/
syntax (name := exerciseAttr) "exercise" ppSpace str (ppSpace num)? : attr

end Reynolds

end

meta section

open Lean

namespace Reynolds

/-- `getParam?` 가 `[Inhabited]` 를 요구한다. `meta` 코드는 `meta` 인스턴스만 볼 수 있으므로
    여기서 따로 준다 — 런타임 쪽에서는 필요 없다. -/
meta instance : Inhabited ExerciseInfo := ⟨{ id := "", stars := 1 }⟩

/-- `@[exercise]` 애트리뷰트의 환경 확장. -/
public initialize exerciseExt : ParametricAttribute ExerciseInfo ←
  registerParametricAttribute {
    name := `exerciseAttr
    descr := "연습문제 표시: 책의 번호와 난이도(별점)"
    getParam := fun _ stx => match stx with
      | `(attr| exercise $s:str)        => return { id := s.getString, stars := 1 }
      | `(attr| exercise $s:str $n:num) => return { id := s.getString, stars := n.getNat }
      | _ => throwError "잘못된 exercise 애트리뷰트. `@[exercise \"1.4\" 2]` 형태로 써라."
  }

/--
`@[exercise]` 로 표시된 선언 전부를 **런타임에서 읽을 수 있는 `def`** 로 굳힌다.

```lean
emit_exercise_registry exerciseRegistry
```

## 왜 이런 게 필요한가

Lean 4 모듈 시스템에서 애트리뷰트(환경 확장)는 `meta` 여야 컴파일 시점에 `@[exercise …]` 를
해석할 수 있다. 그런데 `lake exe grade` 는 런타임 프로그램이라 `meta` 선언을 참조할 수 없다.

```
error: Invalid definition `collect`, may not access declaration `exerciseExt` marked as `meta`
```

그래서 컴파일 시점에 애트리뷰트를 읽어 평범한 `def` 로 옮겨 놓는다.
이름을 `Name` 이 아니라 `String` 으로 담은 것은 문자열 리터럴이 인용(quotation)하기
가장 안전해서다. 읽는 쪽에서 `String.toName` 으로 되돌린다.
-/
elab "emit_exercise_registry" declId:ident : command => do
  let env ← Lean.Elab.Command.liftCoreM Lean.getEnv
  let mut items : Array (String × Nat × String) := #[]
  for (n, _) in env.constants.toList do
    if let some info := exerciseExt.getParam? env n then
      items := items.push (info.id, info.stars, toString n)
  let sorted := items.qsort fun a b => a.1 < b.1
  let entries ← sorted.mapM fun (id, st, nm) =>
    `(term| ($(Lean.quote id), $(Lean.quote st), $(Lean.quote nm)))
  Lean.Elab.Command.elabCommand <| ←
    `(command| def $declId : Array (String × Nat × String) := #[$entries,*])
  -- 생성된 선언에도 docstring 을 붙인다. `lake lint` 의 `docBlame` 이 이걸 요구한다.
  let full := (← Lean.Elab.Command.liftCoreM Lean.getCurrNamespace) ++ declId.getId
  Lean.Elab.Command.liftCoreM <| Lean.addDocStringCore full
    "`@[exercise]` 가 붙은 모든 선언의 목록: `(책의 번호, 별점, 선언 이름)`. \
     `emit_exercise_registry` 가 컴파일 시점에 자동 생성한다. `lake exe grade` 가 읽는다."

end Reynolds

end
