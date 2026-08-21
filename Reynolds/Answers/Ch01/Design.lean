/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Answers.Ch01.Substitution
public import Reynolds.Answers.Ch01.Notation
public import Reynolds.Meta.Exercise
-- `#guard` 는 컴파일 시점에 계산한다 (AGENTS.md §10).
public meta import Reynolds.Answers.Ch01.Substitution
public meta import Reynolds.Answers.Ch01.Notation

/-!
# 정의를 왜 이렇게 써야 하나

## 이 파일이 있는 이유

1장의 다른 파일에서는 정의가 이미 주어지고, 할 일은 그 정의에 대한 정리를 증명하는 것이다.
그러면 "이 정의가 맞다" 는 것을 받아들이고 시작하게 된다. 그런데 Reynolds 가 §1.4 에서
공들이는 것은 정리 증명이 아니라 **정의를 고르는 일**이다. 포획 회피가 왜 필요한지,
자유 변수 함수가 뜻에 영향을 줄 가능성이 있는 변수를 빠뜨리지 않는지가 그 장의 내용이다.
그 집합이 항상 최소일 필요는 없다. `x - x`에는 `x`가 자유롭게 나타나지만 값은 언제나 0이다.

여기서는 방향을 뒤집는다. **그럴듯하지만 틀린 정의**를 주고, 그것이 무엇을 깨뜨리는지
증명하게 한다. 세 자리에서 하나씩이다.

| 어디를 틀리게 했나 | 무엇이 깨지나 |
|---|---|
| 자유 변수 — 부분식 하나를 빠뜨린다 | 일치 정리 (명제 1.1) |
| 의미 — 양화사에서 상태를 갱신하지 않는다 | 일치 정리 (명제 1.1) |
| 치환 — 결합 변수를 그대로 둔다 | 치환 정리 (명제 1.3) |

셋 다 반례를 하나 짚으면 끝난다. 어려운 것은 증명이 아니라 **어떤 반례를 잡을지 떠올리는
일**이고, 그것이 이 연습이 묻는 것이다.

## 읽는 순서
`FreeVars.lean` 과 `Substitution.lean` 을 끝낸 뒤. 그 두 정리를 알아야 무엇이 깨졌는지 안다.
-/

-- 이 파일은 `#guard` 로 잘못된 정의가 무엇을 내는지 눈으로 본다.
set_option linter.hashCommand false

@[expose] public section

-- `Assert` 를 확장하는 정의들이라 1장 이름공간에 그대로 둔다.
-- 하위 이름공간에 넣으면 `p.fvBad` 같은 점 표기가 안 된다.
namespace Reynolds.Answers.Ch01

open Reynolds

universe u

variable {V : Type u} [DecidableEq V]

/-! ## 1. 자유 변수를 너무 적게 모으면

`Assert.fv` 의 이항 논리 연산 절은 양쪽 부분식의 자유 변수를 합친다. 한쪽을 빠뜨리면
어떻게 되나. 구문을 훑는 함수로서는 아무 문제 없이 돌아가고, 타입도 맞는다.

깨지는 것은 **일치 정리**다. 자유 변수가 뜻이 의존하는 변수를 다 모으지 못하면,
"자유 변수 위에서 같으면 뜻이 같다" 가 성립하지 않는다. -/

/--
자유 변수를 모으는 잘못된 정의. 이항 논리 연산에서 **오른쪽 부분식을 빠뜨렸다.**

`Assert.fv` 와 나란히 놓고 보면 한 줄만 다르다.
-/
def Assert.fvBad : Assert V → Finset V
  | .tru | .fls  => ∅
  | .cmp _ e₀ e₁ => e₀.fv ∪ e₁.fv
  | .not p       => p.fvBad
  | .bin _ p _   => p.fvBad          -- 오른쪽을 빠뜨렸다
  | .quant _ v p => p.fvBad.erase v

-- 옳은 정의는 `x` 를 잡는다. 잘못된 정의는 놓친다.
#guard (⟪ tt ∧ x = 0 ⟫ₐ : Assert String).fv == {"x"}
#guard (⟪ tt ∧ x = 0 ⟫ₐ : Assert String).fvBad == (∅ : Finset String)

/--
**자유 변수를 너무 적게 모으면 일치 정리가 깨진다.**

일치 정리는 두 상태가 `FV(p)` 위에서 같으면 `p` 의 뜻이 같다고 말한다.
`fvBad` 를 쓰면 그것이 성립하지 않는 `p`, `σ`, `σ'` 이 있다.

반례를 고르는 요령은 **빠뜨린 자리에만 변수를 두는 것**이다. `tt ∧ x = 0` 에서
`fvBad` 는 왼쪽 `tt` 만 보므로 빈 집합을 내놓는다. 그러면 전제가 공짜로 성립하는데,
뜻은 `x` 에 따라 달라진다.
-/
@[exercise "설계 fv" 2]
theorem fvBad_breaks_coincidence :
    ∃ (p : Assert String) (σ σ' : State String),
      (∀ w ∈ p.fvBad, σ w = σ' w) ∧ ¬ (⟦p⟧ₐ σ ↔ ⟦p⟧ₐ σ') := by
  refine ⟨⟪ tt ∧ x = 0 ⟫ₐ, State.const 0, State.const 1, ?_, ?_⟩
  · -- `fvBad` 가 빈 집합이라 전제는 확인할 것이 없다.
    intro w hw
    simp [Assert.fvBad] at hw
  · -- 왼쪽은 참, 오른쪽은 거짓.
    simp [Assert.eval, LogOp.denote, Cmp.denote, IntExp.eval, State.const]

/-! ## 2. 양화사에서 상태를 갱신하지 않으면

`⟦∀v. p⟧ σ = ∀ n : ℤ, ⟦p⟧ (σ[v := n])` 에서 갱신을 빼면 `∀ n : ℤ, ⟦p⟧ σ` 가 된다.
`n` 이 어디에도 안 쓰이므로 양화사가 아무 일도 하지 않는다.

이번에도 깨지는 것은 일치 정리다. 다만 이유가 반대다. 앞에서는 `fv` 가 너무 작아서
깨졌고, 여기서는 **의미가 묶인 변수에 여전히 의존해서** 깨진다. `fv` 는 그대로인데
뜻이 달라진 것이다.

두 반례를 나란히 보면 일치 정리가 무엇을 주장하는지가 분명해진다.
`fv` 와 `eval` 이 **서로 맞물려야** 하고, 어느 쪽을 건드려도 맞물림이 풀린다. -/

/--
의미 함수의 잘못된 정의. 양화사 절에서 **상태를 갱신하지 않는다.**

나머지 절은 `Assert.eval` 과 같다.
-/
def Assert.evalBad : Assert V → State V → Prop
  | .tru,            _ => True
  | .fls,            _ => False
  | .cmp c e₀ e₁,    σ => c.denote (⟦e₀⟧ₑ σ) (⟦e₁⟧ₑ σ)
  | .not p,          σ => ¬ p.evalBad σ
  | .bin op p q,     σ => op.denote (p.evalBad σ) (q.evalBad σ)
  | .quant .all _ p, σ => ∀ _ : Int, p.evalBad σ      -- `σ[v := n]` 이어야 한다
  | .quant .ex  _ p, σ => ∃ _ : Int, p.evalBad σ

/--
**양화사가 상태를 갱신하지 않으면 일치 정리가 깨진다.**

`∀x. x = 0` 을 보라. `x` 는 묶여 있으므로 `FV` 는 빈 집합이고, 일치 정리대로라면
어떤 두 상태에서도 뜻이 같아야 한다. 그런데 `evalBad` 로 재면 `∀ n, σx = 0` 이 되어
바깥의 `σx` 에 달린다.

**묶는다는 것은 바깥 값을 가린다는 뜻이고, 가리는 일을 하는 것이 상태 갱신이다.**
그 한 줄을 빼면 양화사가 이름만 양화사가 된다.
-/
@[exercise "설계 eval" 2]
theorem evalBad_breaks_coincidence :
    ∃ (p : Assert String) (σ σ' : State String),
      (∀ w ∈ p.fv, σ w = σ' w) ∧ ¬ (p.evalBad σ ↔ p.evalBad σ') := by
  refine ⟨⟪ ∀ x, x = 0 ⟫ₐ, State.const 0, State.const 1, ?_, ?_⟩
  · intro w hw
    simp [Assert.fv, IntExp.fv] at hw
  · simp [Assert.evalBad, Cmp.denote, IntExp.eval, State.const]

/-! ## 3. 치환에서 결합 변수를 그대로 두면

여기가 §1.4 의 본론이다. `Assert.subst` 의 양화사 절은 결합 변수를 새 이름으로 바꾼 뒤에
치환한다. 그 단계를 빼면 정의가 훨씬 짧아지고, `newBinder` 도 `captureSet` 도 필요 없다.
`HasFresh` 제약조차 사라진다.

무엇이 잘못되었는지 구문만 봐서는 알 수 없다. 뜻을 재 봐야 드러난다. -/

/--
치환의 잘못된 정의. 양화사 절에서 **결합 변수를 그대로 둔다.**

`Assert.subst` 와 비교해 보라. `newBinder` 가 사라졌고, 치환 사상의 `v` 자리를
`var v` 로 덮는 것만 남았다. 정의는 이쪽이 짧고 읽기도 쉽다.
-/
def Assert.substNaive : Assert V → Subst V → Assert V
  | .tru,          _ => .tru
  | .fls,          _ => .fls
  | .cmp c e₀ e₁,  δ => .cmp c (e₀ /ₑ δ) (e₁ /ₑ δ)
  | .not p,        δ => .not (p.substNaive δ)
  | .bin op p q,   δ => .bin op (p.substNaive δ) (q.substNaive δ)
  | .quant q v p,  δ => .quant q v (p.substNaive (Function.update δ v (.var v)))

/-- `x` 를 `y` 로 바꾸는 치환 사상. `y` 는 아래 예제에서 결합 변수이기도 하다. -/
def xToY : Subst String := Function.update IntExp.var "x" (.var "y")

-- `∃y. x < y` 에 `x ↦ y` 를 넣는다. 들어온 `y` 가 양화사에 **잡힌다**.
#guard (⟪ ∃ y, x < y ⟫ₐ : Assert String).substNaive xToY == ⟪ ∃ y, y < y ⟫ₐ

-- 옳은 정의는 결합 변수를 바꿔서 잡히지 않게 한다.
#guard (⟪ ∃ y, x < y ⟫ₐ : Assert String) /ₛ xToY == ⟪ ∃ x, y < x ⟫ₐ

/--
**포획을 막지 않으면 치환 정리가 깨진다.**

치환 정리(명제 1.3)는 치환한 구문을 평가한 결과와, 치환 항의 값으로 상태를 갱신한 뒤
원래 구문을 평가한 결과가 같다고 말한다.
`substNaive` 는 그것을 만족하지 않는다.

반례가 위의 `#guard` 두 줄에 이미 나와 있다. `∃y. x < y` 는 "x 보다 큰 수가 있다" 이므로
어떤 상태에서도 참인데, `x` 를 `y` 로 바꾼 뒤 `substNaive` 가 내놓는 `∃y. y < y` 는
어떤 상태에서도 거짓이다.

**들어온 `y` 가 자유 변수여야 하는데 양화사에 잡혔다.** 이것이 변수 포획(capture)이고,
`newBinder` 가 존재하는 이유 전부다. 짧고 읽기 쉬운 정의를 포기한 대가로 얻는 것이 이 등식이다.
-/
@[exercise "설계 subst" 3]
theorem substNaive_breaks_substitution :
    ∃ (p : Assert String) (δ : Subst String) (σ σ' : State String),
      (∀ w ∈ p.fv, σ w = ⟦δ w⟧ₑ σ') ∧ ¬ (⟦p.substNaive δ⟧ₐ σ' ↔ ⟦p⟧ₐ σ) := by
  refine ⟨⟪ ∃ y, x < y ⟫ₐ, xToY, State.const 0, State.const 0, ?_, ?_⟩
  · -- 전제. 자유 변수는 `x` 하나뿐이고 양쪽 다 0 이다.
    intro w hw
    simp [Assert.fv, IntExp.fv] at hw
    -- `FV(∃y. x < y) = {x}` 이므로 `w` 는 `x` 다.
    have hx : w = "x" := by tauto
    subst hx
    simp [xToY, IntExp.eval, State.const]
  · -- 왼쪽은 `∃n. n < n` 이라 거짓이다.
    have hL : ¬ ⟦(⟪ ∃ y, x < y ⟫ₐ : Assert String).substNaive xToY⟧ₐ (State.const 0) := by
      rintro ⟨n, hn⟩
      simp [Assert.substNaive, Assert.eval, Cmp.denote, IntExp.eval, IntExp.subst, xToY] at hn
    -- 오른쪽은 `∃n. 0 < n` 이라 참이다.
    have hR : ⟦(⟪ ∃ y, x < y ⟫ₐ : Assert String)⟧ₐ (State.const 0) := by
      refine ⟨1, ?_⟩
      simp [Assert.eval, Cmp.denote, IntExp.eval, State.const]
    exact fun hiff => hL (hiff.mpr hR)

/-! ## 4. 왜 동시 치환인가 — 코드로 보일 수 없는 것

세 반례는 전부 "잘못된 정의를 쓰고 반례를 든다" 는 모양이었다. Reynolds 의 설계 결정 중
하나는 그렇게 다룰 수 없다. **동시 치환(simultaneous substitution)을 기본으로 두는 것**이다.

한 변수씩 치환하는 정의를 쓰려고 하면 양화사 절이 이렇게 된다.

```
(∀v. p) / w ↦ e  =  ∀ vnew. ((p / v ↦ var vnew) / w ↦ e)
```

안쪽에서 이름을 바꾸고 바깥에서 다시 치환한다. 재귀 호출의 첫 인자가 `p` 가 아니라
`p / v ↦ var vnew` 이고, 그것은 `p` 의 부분항이 아니다. **구조적 재귀가 아니다.**

Lean은 이 식만 보고 재귀 호출의 인자가 작아진다고 판단할 수 없다. 이 직접 방정식으로 한 변수
치환을 정의하려면 구의 크기가 줄어든다는 보조정리와 정초 재귀(well-founded recursion)가
필요하다. 그래서 앞 절처럼 짧은 정의 하나를 놓고 바로 비교하기는 어렵다.

동시 치환으로 두면 재귀 호출이 `p` 라는 진부분항에서 일어나고, 정지성이 공짜가 된다.
`Substitution.lean` 의 `Assert.subst` 가 그 정의다.

**설계 결정이 값을 치르는 자리가 서로 다르다.** 포획 회피는 정의를 길게 만들고,
동시 치환은 진술을 무겁게 만든다 (한 변수 치환이면 `p / v ↦ e` 로 끝날 것을
`Θ = ⟨var⟩ → ⟨intexp⟩` 전체로 말해야 한다). 어느 쪽도 공짜가 아니고,
Reynolds 는 정지성을 지키는 쪽을 골랐다. -/

end Reynolds.Answers.Ch01
