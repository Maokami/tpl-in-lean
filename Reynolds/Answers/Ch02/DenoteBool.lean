/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Answers.Ch01.Semantics

/-!
# §2.2 비교·논리 연산의 `Bool` 판

`Semantics.lean` 의 `BoolExp.eval` 이 쓰는 두 연산과 그 맞물림 정리다.

## 왜 따로 된 파일인가

이 선언들은 1장 이름공간 `Reynolds.Answers.Ch01` 에 산다 (아래 이유). Exercises 트리는
앞 장의 **Answers** 를 import 하므로 (`DESIGN.md` §3.1), 이것을 2장 Exercises 에 복제하면
두 트리가 같은 이름을 두 번 선언해 루트 모듈에서 충돌한다. 그래서 `Notation.lean` 처럼
**공유 모듈**로 두고 (`scripts/gen-exercises.py` 의 `SHARED`), 두 트리가 이 한 벌을 쓴다.
채점 대상 연습은 없다.
-/

@[expose] public section

/-! ## 불 값으로 가는 확장은 1장 이름공간에 둔다

`Cmp` 와 `LogOp` 는 1장 타입이다. 확장을 2장 이름공간에 두면 `c.denoteBool` 같은 점 표기가
안 되므로, 타입이 사는 곳에 맞춰 1장 이름공간에 넣는다. 파일과 이름공간이 갈리지만
같은 타입에 대한 연산을 한 이름 아래 모으는 쪽이 읽기에 낫다. -/

namespace Reynolds.Answers.Ch01

/-- 비교 기호의 뜻, `Bool` 판. 1장 `Cmp.denote` 의 계산되는 짝이다. -/
def Cmp.denoteBool : Cmp → Int → Int → Bool
  | .eq, a, b => a == b
  | .ne, a, b => a != b
  | .lt, a, b => a < b
  | .le, a, b => a ≤ b
  | .gt, a, b => a > b
  | .ge, a, b => a ≥ b

/-- 논리 기호의 뜻, `Bool` 판. -/
def LogOp.denoteBool : LogOp → Bool → Bool → Bool
  | .and, a, b => a && b
  | .or,  a, b => a || b
  | .imp, a, b => !a || b
  | .iff, a, b => a == b

/-- 비교의 두 뜻이 맞물린다. -/
theorem Cmp.denoteBool_iff (c : Cmp) (a b : Int) :
    c.denoteBool a b = true ↔ c.denote a b := by
  cases c <;> simp [Cmp.denote, Cmp.denoteBool]

/-- 논리 연산의 두 뜻이 맞물린다. 전제는 부분식에 대한 귀납 가설로 들어온다. -/
theorem LogOp.denoteBool_iff (op : LogOp) {a b : Bool} {p q : Prop}
    (hp : a = true ↔ p) (hq : b = true ↔ q) :
    op.denoteBool a b = true ↔ op.denote p q := by
  cases op <;> cases a <;> cases b <;> simp_all [LogOp.denote, LogOp.denoteBool]

end Reynolds.Answers.Ch01
