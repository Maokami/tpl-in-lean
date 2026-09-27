/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Exercises.Ch01.Semantics
public import Reynolds.Meta.Exercise
public import Cslib.Foundations.Data.HasFresh
public import Mathlib.Data.Int.Interval
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
-- `#guard` 는 컴파일 시점에 계산한다 (AGENTS.md §10).
public meta import Reynolds.Prelude
public meta import Reynolds.Exercises.Ch01.Semantics
public meta import Mathlib.Data.Int.Interval
public meta import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # 연습 1.6 (p. 23) — 부정 합의 결합 문제

`Summation.lean`에서 독립된 최소 구문으로 이름 바꾸기 문제를 확인한다.
기존 공개 이름과 채점 문항 `Ex 1.6`은 그대로다.
-/

set_option linter.hashCommand false
attribute [-instance] Int.instConditionallyCompleteLinearOrder

@[expose] public section
namespace Reynolds.Exercises.Ch01.Summation
open Reynolds Reynolds.Exercises.Ch01 Cslib
universe u
variable {V : Type u} [DecidableEq V]

/-! # 연습 1.6 — 부정 합(indefinite summation)

Reynolds 연습 1.6 (p. 23)은 위끝이 같은 이름의 바깥 변수에 의존하는 부정 합을 더한 뒤,
결합과 치환에서 생기는 어려움을 논의하라고 요구한다.

## 무엇이 이상한가

`Σv. e` 의 뜻은 `Σ_{v=0}^{v-1} e` 다. 오른쪽에서 `v` 가 **두 가지 역할**을 한다.

- 아래첨자의 `v` 는 0, 1, …, 로 훑는 묶인 변수다
- 위끝의 `v` 는 바깥에서 값을 읽는 자유 변수다

한 이름이 같은 식 안에서 묶이면서 동시에 자유롭다. §1.4 의 결합 구조는 이런 경우를 허용하지
않는다. `∀v. p` 에서 `v` 는 `p` 전체에서 묶이고, `Σv : e₀ to e₁. e₂` 에서도 `v` 가 묶이는
범위와 자유로운 범위가 부분식으로 갈렸다. 여기서는 갈 곳이 없다.

아래에서 그 결과를 실제로 확인한다.
-/

namespace Indefinite

/-- 부정 합만 있는 최소 언어. 문제를 드러내는 데 필요한 것만 남겼다. -/
inductive ISExp (V : Type u) where
  /-- 정수 상수. -/
  | num : Int → ISExp V
  /-- 변수. -/
  | var : V → ISExp V
  /-- 이항 연산. -/
  | bin : IntOp → ISExp V → ISExp V → ISExp V
  /-- `Σv. e` — 위끝을 `v` 자신이 정하는 합. -/
  | isum : V → ISExp V → ISExp V
  deriving DecidableEq, Repr

/--
부정 합의 뜻. `Σv. e = Σ_{k=0}^{σv - 1} ⟦e⟧ (σ[v := k])`.

위끝 `σ v` 를 **갱신 전** 상태에서 읽는다는 것이 정의의 전부다.
`Finset.Ico 0 (σ v)` 가 `0 ≤ k < σ v` 를 준다.
-/
def ISExp.eval : ISExp V → State V → Int
  | .num n,       _ => n
  | .var v,       σ => σ v
  | .bin op a b,  σ => op.denote (a.eval σ) (b.eval σ)
  | .isum v e,    σ => ∑ k ∈ Finset.Ico 0 (σ v), e.eval (σ[v := k])

@[inherit_doc ISExp.eval]
scoped notation:max "⟦" e "⟧ᵢ" => ISExp.eval e

/--
부정 합의 자유 변수.

`isum` 절에 `insert v` 가 붙는다. 본체에서는 `v` 를 지우지만 위끝으로 다시 들어온다.
`FV(Σv. e) = {v} ∪ (FV(e) \ {v})` 이므로 결과적으로 `v` 는 언제나 자유롭다.
-/
def ISExp.fv : ISExp V → Finset V
  | .num _       => ∅
  | .var v       => {v}
  | .bin _ a b   => a.fv ∪ b.fv
  | .isum v e    => insert v (e.fv.erase v)

-- 결합 변수가 자유 변수 목록에 남는다. `Σi. 1` 조차 `i` 에 의존한다.
#guard (ISExp.isum "i" (.num 1) : ISExp String).fv == {"i"}

/-! ## 어려움 1 — 이름 바꾸기가 뜻을 바꾼다

명제 1.5(이름 바꾸기 정리)는 `vnew ∉ FV(q) \ {v}`이면 결합 변수를 `vnew`로 바꿔도 뜻이
같다고 말한다. 부정 합에서는 그 단서를 만족시켜도 뜻이 달라진다.

`Σi. 1` 을 보자. 본체에 `i` 가 없으므로 `FV(1) \ {i} = ∅` 이고, 어떤 `vnew` 든 단서를
통과한다. `i` 를 `j` 로 바꾸면 `Σj. 1` 이 된다. 위끝이 음이 아니면 각각 `σi`, `σj` 를
세지만, 음수이면 구간이 비어 합은 0이다. `σi = 1`, `σj = 0` 인 상태에서 두 합은 다르다.

무슨 일이 일어났나. 이름 바꾸기는 **묶인** 자리만 건드린다는 전제 위에 서 있는데,
여기서는 같은 이름이 자유로운 자리에도 있어서 그것까지 함께 바뀐다.
-/

/--
**이름 바꾸기 정리가 깨진다.** 명제 1.5 의 단서를 만족하는데도 뜻이 달라지는 예가 있다.

`Σi. 1` 과 `Σj. 1` 을 쓴다. 본체 `1` 에 자유 변수가 없으므로 `j ∉ FV(1) \ {i} = ∅` 이고,
따라서 `Σj. 1` 은 명제 1.5의 이름 바꾸기 단서를 만족한다. 두 합은 각각
`0 ≤ k < σ i`, `0 ≤ k < σ j` 인 정수 `k`의 개수를 세므로 위끝에 따라 뜻이 달라질 수 있다.

증명은 `σ i = 1`, `σ j = 0` 인 상태를 제시하면 된다.
-/
@[exercise "Ex 1.6" 3]
theorem isum_renaming_fails :
    ∃ σ : State String,
      ⟦(ISExp.isum "i" (.num 1) : ISExp String)⟧ᵢ σ
        ≠ ⟦(ISExp.isum "j" (.num 1) : ISExp String)⟧ᵢ σ := by
  -- 힌트: `σ i = 1`, `σ j = 0` 인 상태를 `refine ⟨fun w => …, ?_⟩` 로 제시한다.
  --       그다음은 `simp [ISExp.eval]` 이 계산해 준다.
  sorry

/-! ## 어려움 2 — 치환이 결합 변수를 건너뛸 수 없다

`Assert.subst` 는 `(∀v. p) /ₛ δ` 에서 `δ` 의 `v` 자리를 `var vnew` 로 덮어썼다.
`v` 는 묶여 있으니 `δ v` 를 볼 일이 없다는 판단이었다.

부정 합에서는 그 판단이 틀린다. 위끝의 `v`는 자유롭고, 치환은 그 자리를 `δ v`로 바꿔야 한다.
그런데 위끝은 부분식이 아니라 결합 변수 자체다. `Σv. e` 에 `v ↦ e'` 를 넣으면
"위끝은 `e'` 로, 본체의 `v` 는 그대로" 를 표현해야 하는데, 구문에 그런 자리가 없다.

바꿔 말하면 `Σv. e` 는 `Σv : 0 to (v-1). e` 의 줄임말인데, 줄이면서 위끝 자리를 잃어버렸다.
줄이지 않은 쪽에서는 §1.4 의 정의가 그대로 통한다 — `SExp` 에서 확인한 그대로다.

## 그래서 어떻게 하나

세 가지 길이 있고, Reynolds 가 이후 장들에서 모두 지나간다.

- **위끝을 부분식으로 되돌린다.** `Σv : e₀ to e₁. e₂` 로 돌아가는 것이다.
  `Σv. e` 를 그 위의 파생 형태(derived form)로 정의하면 결합 문제가 사라진다.
- **결합 변수와 자유 변수를 표기로 구분한다.** de Bruijn 색인이 그것이다.
  묶인 자리는 번호로, 자유로운 자리는 이름으로 두면 두 역할이 섞이지 않는다.
  CSlib 의 `Cslib/Languages/LambdaCalculus/LocallyNameless/` 가 이 방식이다.
- **결합 구조가 불분명한 구문을 언어에서 제외한다.** 실제 언어 설계에서도 쓰는 선택이다.

1.6 이 "discuss" 로 끝나는 이유가 이것이다. 정답 하나가 아니라, 결합 구조를 어떻게
설계하느냐에 따라 값을 치르는 자리가 달라진다.
-/

end Indefinite

end Reynolds.Exercises.Ch01.Summation
