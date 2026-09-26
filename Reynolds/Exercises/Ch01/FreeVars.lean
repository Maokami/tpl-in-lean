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
- 명제 1.1 (일치 정리) — 구의 값은 자유 변수 위의 상태에만 의존한다

## 배경

`FV(e)`는 구문을 따라 변수 발생을 모은다. 일치 정리는 이 구문적 집합이 의미 함수의
지지 집합(support)으로 충분하다고 말한다. 두 상태가 `FV(e)`에서 같으면 `⟦e⟧`의 값도 같다.

이 정리는 `FV(e)`가 의미 의존성의 최소 집합이라는 뜻은 아니다. 예를 들어 `x - x`에는
`x`가 자유롭게 나타나지만 값은 모든 상태에서 `0`이다. 자유 변수는 의미에 영향을 줄 수
있는 구문 위치를 보수적으로 기록한다.

Reynolds 가 구조적 귀납법(structural induction)을 처음 쓰는 자리이기도 하다.

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

`e` 에 대한 구조적 귀납법으로 증명한다.

진술에서 `σ σ'` 를 `∀` 로 묶어 둔 이유는 아래 `coincidence_assert` 에서 드러난다.
정수 식에는 결합자가 없어 여기서는 티가 안 나지만, 양화사 케이스에서는 귀납 가설을
`σ`, `σ'` 가 아니라 `σ[v := n]`, `σ'[v := n]` 에 적용해야 한다.

채점 연습이 아니다. 아래 `coincidence_assert` (명제 1.1b) 와 `Substitution.lean` 의
`substitution_assert` (명제 1.3) 가 둘 다 이 결과를 직접 쓰므로, 완성된 채로 준다
(연습 독립성 원칙, `AGENTS.md` §1-9).
-/
theorem coincidence_intExp :
    ∀ (e : IntExp V) (σ σ' : State V), (∀ w ∈ e.fv, σ w = σ' w) → ⟦e⟧ₑ σ = ⟦e⟧ₑ σ' := by
  intro e
  induction e with
  | num n => intro _ _ _; rfl
  | var v =>
      -- 변수는 자기 자신이 자유 변수이므로 가설이 곧 결론이다.
      intro _ _ h; exact h v (by simp [IntExp.fv])
  | neg e ih =>
      -- FV(-e) = FV(e) 이므로 가설을 그대로 물려준다.
      intro σ σ' h; simp [IntExp.eval, ih σ σ' h]
  | bin op e₀ e₁ ih₀ ih₁ =>
      -- FV(e₀ op e₁) = FV(e₀) ∪ FV(e₁). 양쪽에 각각 귀납 가설을 쓴다.
      intro σ σ' h
      have h₀ := ih₀ σ σ' fun w hw => h w (by simp [IntExp.fv, hw])
      have h₁ := ih₁ σ σ' fun w hw => h w (by simp [IntExp.fv, hw])
      simp [IntExp.eval, h₀, h₁]

/-! ## 단언의 자유 변수 — 여기서 결합이 등장한다 -/

/--
`FV_assert(p)` — 단언에 자유롭게 나타나는 변수. Reynolds §1.4.

내용이 있는 절은 양화사뿐이다. `FV(∀v. p) = FV(p) \ {v}` 이고,
나머지는 부분구의 합집합이다.

같은 변수가 한 구 안에서 자유롭게도 속박되어도 나타날 수 있다.
Reynolds 의 예 `∀x.(x ≠ y ∨ ∀y.(x = y ∨ ∀x. x + y ≠ x))` 에서 `y` 가 그런 경우다.
-/
def Assert.fv : Assert V → Finset V
  | .tru | .fls  => ∅
  | .cmp _ e₀ e₁ => e₀.fv ∪ e₁.fv
  | .not p       => p.fv
  | .bin _ p q   => p.fv ∪ q.fv
  | .quant _ v p => p.fv.erase v

/--
**명제 1.1 (일치 정리)** — 단언 판.

정수 식 판과 진술은 같지만 양화사 케이스가 하나 늘어난다. Reynolds 는 그 케이스의 요령을
직접 적어 둔다.

> *"In applying the induction hypothesis, which holds for arbitrary states σ and σ',
> we take σ and σ' to be different states from the σ and σ' for which we are
> trying to prove the conclusion."*

`∀v. p` 를 다룰 때 귀납 가설을 `σ`, `σ'` 가 아니라 `σ[v := n]`, `σ'[v := n]` 에 적용한다는
말이다. `FV(∀v.p) = FV(p) \ {v}` 이므로, `v` 에서만 다르던 두 상태를 `v` 에 같은 값으로
덮으면 `FV(p)` 전체에서 일치하게 된다.

Lean 으로 옮기면 귀납 가설이 `∀ σ σ'` 로 일반화되어 있어야 한다는 뜻이 된다.
`σ σ'` 를 `theorem` 의 인자로 빼면 귀납 가설이 그 특정 상태에만 붙어서 이 단계가 막힌다.
진술을 `∀ (p) (σ σ')` 꼴로 쓴 이유다.

결론이 `=` 가 아니라 `↔` 인 것은 `Assert.eval` 이 `Prop` 을 돌려주기 때문이다.
`propext` 를 부르지 않고 자연스럽게 쓸 수 있는 쪽이 명제 동치다.
-/
@[exercise "Prop 1.1b" 3]
theorem coincidence_assert :
    ∀ (p : Assert V) (σ σ' : State V), (∀ w ∈ p.fv, σ w = σ' w) → (⟦p⟧ₐ σ ↔ ⟦p⟧ₐ σ') := by
  -- 먼저 볼 것: 바로 위 `coincidence_intExp` 의 완성 증명. 같은 모양이고 케이스만 늘어난다.
  -- 힌트 1: 진술이 `∀ (p) (σ σ')` 꼴인 것이 증명을 좌우한다.
  --         `σ σ'` 를 인자로 빼면 양화사 케이스에서 귀납 가설이 안 맞는다.
  -- 힌트 2: `quant` 케이스에서 귀납 가설을 `σ[v := n]`, `σ'[v := n]` 에 적용한다.
  -- 힌트 3: `State.subst_self` / `State.subst_of_ne` 가 `simp` 로 자동 적용된다.
  --         마무리는 `forall_congr'` 와 `exists_congr`.
  sorry

end Reynolds.Exercises.Ch01
