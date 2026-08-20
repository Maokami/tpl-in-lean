/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Exercises.Ch01.Semantics
public import Reynolds.Meta.Exercise

/-!
# §1.4 자유 변수와 일치 정리 (Free Variables, Coincidence Theorem)

Reynolds §1.4 (pp. 15–17)의 앞부분에 대응한다.

## 이 파일에서 다루는 것
- 자유 변수 함수 `FV_intexp`
- **명제 1.1 (일치 정리)** — 구의 값은 자유 변수 위의 상태에만 의존한다

## 핵심 아이디어

`FV(e)` 는 순전히 **구문적인** 정의다 — 식을 훑으며 변수를 모을 뿐 뜻을 보지 않는다.
그런데 일치 정리는 이 구문적 개념이 **의미적으로 옳다**고 말한다:
`FV(e)` 밖에서 상태가 아무리 달라도 `⟦e⟧` 는 같다.

이것이 "자유 변수"라는 개념이 임의의 정의가 아니라는 증거이고,
Reynolds가 구조적 귀납법(structural induction)을 처음 쓰는 자리이기도 하다.

## 읽는 순서
`Semantics.lean` → 이 파일
-/

@[expose] public section

namespace Reynolds.Exercises.Ch01

open Reynolds

universe u

variable {V : Type u} [DecidableEq V]

/--
`FV_intexp(e)` — 정수 식에 자유롭게 나타나는 변수. Reynolds §1.4.

정수 식에는 결합자(binder)가 없으므로 "자유"라는 말이 아직 의미를 갖지 않는다.
§1.4의 `Assert`에서 `∀v. p`가 들어오면서 비로소 자유/속박 구분이 생긴다.
-/
def IntExp.fv : IntExp V → Finset V
  | .num _       => ∅
  | .var v       => {v}
  | .neg e       => e.fv
  | .bin _ e₀ e₁ => e₀.fv ∪ e₁.fv

/--
**명제 1.1 (일치 정리, coincidence theorem)** — 정수 식 판.

> Reynolds: *"If p is a phrase of type θ, and σ and σ' are states such that σw = σ'w
> for all w ∈ FV_θ(p), then ⟦p⟧σ = ⟦p⟧σ'."*

증명은 `e`에 대한 구조적 귀납법이다. Reynolds가 이 정리를
*"형식 언어의 성질을 증명하는 중요한 방법"* 의 첫 예로 드는 이유가 여기 있다.

`σ σ'`를 `∀`로 묶어 둔 것이 중요하다. 정수 식에는 결합자가 없어 아직 티가 안 나지만,
`Assert`의 양화사 케이스에서는 귀납 가설을 **원래 상태가 아니라 갱신된 상태**
`σ[v := n]`, `σ'[v := n]` 에 적용해야 한다. 그때 이 일반화가 없으면 증명이 막힌다.
-/
@[exercise "Prop 1.1a" 2]
theorem coincidence_intExp :
    ∀ (e : IntExp V) (σ σ' : State V), (∀ w ∈ e.fv, σ w = σ' w) → ⟦e⟧ₑ σ = ⟦e⟧ₑ σ' := by
  -- 힌트: `intro e` 다음 `induction e with` 로 케이스를 나눈다.
  -- `bin` 케이스에서 `Finset` 합집합 소속을 어떻게 쪼갤지 생각해 볼 것.
  sorry

/-! ## 단언의 자유 변수 — 여기서 결합이 등장한다 -/

/--
`FV_assert(p)` — 단언에 자유롭게 나타나는 변수. Reynolds §1.4.

**양화사 절이 전부다**: `FV(∀v. p) = FV(p) \ {v}`.
`v` 의 결합 발생(binding occurrence)이 `p` 안의 모든 `v` 를 잡아먹는다.
나머지 절은 전부 부분구의 합집합일 뿐이다.

같은 변수가 한 구 안에서 자유롭게도, 속박되어도 나타날 수 있다는 점에 주의할 것.
Reynolds 의 예: `∀x.(x ≠ y ∨ ∀y.(x = y ∨ ∀x. x + y ≠ x))` 에서 `y` 가 그렇다.
-/
def Assert.fv : Assert V → Finset V
  | .tru | .fls  => ∅
  | .cmp _ e₀ e₁ => e₀.fv ∪ e₁.fv
  | .not p       => p.fv
  | .bin _ p q   => p.fv ∪ q.fv
  | .quant _ v p => p.fv.erase v

/--
**명제 1.1 (일치 정리)** — 단언 판.

정수 식 판(`coincidence_intExp`)과 진술은 같지만 **증명의 난이도가 다르다.**
양화사 케이스가 새롭고, Reynolds 가 그 요령을 명시적으로 짚는다:

> *"In applying the induction hypothesis, which holds for arbitrary states σ and σ',
> we take σ and σ' to be **different** states from the σ and σ' for which we are
> trying to prove the conclusion."*

구체적으로 `∀v. p` 를 다룰 때 귀납 가설을 `σ`, `σ'` 가 아니라
**`σ[v := n]`, `σ'[v := n]`** 에 적용한다. `FV(∀v.p) = FV(p) \ {v}` 이므로
`v` 에서만 다르던 두 상태를 `v` 에 같은 값으로 덮으면 `FV(p)` 전체에서 일치하게 된다.

Lean 에서 이 말은 **귀납 가설이 `∀ σ σ'` 로 일반화되어 있어야 한다**는 뜻이다.
`σ σ'` 를 `theorem` 의 인자로 빼 두면 귀납 가설이 그 특정 상태에만 적용되어 증명이 막힌다.
그래서 진술을 `∀ (p) (σ σ')` 꼴로 썼다. **1장에서 가장 중요한 교훈이다.**

**결론이 `=` 가 아니라 `↔` 인 이유**: `Assert.eval` 이 `Prop` 을 돌려주므로,
`propext` 없이 자연스러운 것은 명제 동치다.
-/
@[exercise "Prop 1.1b" 3]
theorem coincidence_assert :
    ∀ (p : Assert V) (σ σ' : State V), (∀ w ∈ p.fv, σ w = σ' w) → (⟦p⟧ₐ σ ↔ ⟦p⟧ₐ σ') := by
  -- 힌트 1: 진술이 `∀ (p) (σ σ')` 꼴인 것이 핵심이다. `σ σ'` 를 인자로 빼면
  --         귀납 가설이 그 특정 상태에만 적용되어 양화사 케이스에서 막힌다.
  -- 힌트 2: `quant` 케이스에서는 귀납 가설을 `σ[v := n]`, `σ'[v := n]` 에 적용한다.
  --         `FV(∀v.p) = FV(p).erase v` 이므로 `v` 를 같은 값으로 덮으면
  --         `FV(p)` 전체에서 두 상태가 일치하게 된다.
  -- 힌트 3: `State.subst_self` / `State.subst_of_ne` 가 `simp` 로 자동 적용된다.
  --         마무리는 `forall_congr'` 와 `exists_congr`.
  sorry

end Reynolds.Exercises.Ch01
