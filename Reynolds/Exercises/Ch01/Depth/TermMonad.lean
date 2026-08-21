/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Exercises.Ch01.Substitution
public import Reynolds.Exercises.Ch01.Depth.SignatureFunctor

/-!
# 심화 A · 치환은 bind 다

선택 파일이다. `Ch01/Substitution.lean` 을 먼저 읽어야 한다.

## 시작점

Reynolds 는 명제 1.2(b) 에 이런 주석을 단다.

> *"Note that part (b) of this proposition asserts that the constructor `c_var`, which injects
> variables into the corresponding integer expressions, acts as an identity substitution."*

그리고 연습문제 1.7(a) 에서 치환 두 번의 합성을 묻는다.

> *"If `p` is a phrase of type θ, and `δ''w = (δw)/δ'` for all `w ∈ FV_θ(p)`,
> then `p/δ''` is a renaming of `(p/δ)/δ'`."*

두 진술을 나란히 놓으면 모나드 법칙 세 개가 나온다.

| Reynolds | 모나드 |
|---|---|
| `c_var : ⟨var⟩ → ⟨intexp⟩` | `pure` |
| `p / δ` | `p >>= δ` |
| `(c_var v) / δ = δ v` (정의로 성립) | 좌단위 `pure v >>= f = f v` |
| 명제 1.2(b) `p / c_var = p` | 우단위 `m >>= pure = m` |
| 연습 1.7(a) | 결합법칙 `(m >>= f) >>= g = m >>= fun x => f x >>= g` |

## 이 파일이 다루는 것

정수 식에서는 세 법칙이 등식으로 성립한다(§1).
단언에서는 결합법칙이 등식으로 성립하지 않는다(§2). Reynolds 의 진술이
"같다" 가 아니라 "**is a renaming of**" 인 것이 그 때문이다.
대신 뜻은 같고, 그 사실은 치환 정리에서 나온다.

## 사전 지식
`Ch01/Substitution.lean`. 모나드를 몰라도 읽을 수 있게 썼다.
-/

@[expose] public section

namespace Reynolds.Exercises.Ch01

open Reynolds

universe u

variable {V : Type u} [DecidableEq V]

/-! ## 1. 정수 식 — 세 법칙이 등식으로 성립한다

`IntExp V` 를 "변수 자리가 `V` 인 항" 으로 보면, 치환은 그 자리에 다른 항을 끼우는 연산이다.
`Depth/SignatureFunctor.lean` §4 에서 본 `PFunctor.FreeM` 의 구조와 같다 —
`var` 가 잎(`pure`)이고 치환이 `bind` 다. -/

omit [DecidableEq V] in
/--
좌단위 법칙. `pure v >>= δ` 에 해당한다.

정의를 펼치면 바로 나온다. `IntExp.subst` 의 `var` 절이 곧 이 등식이다.
-/
theorem subst_var_left (v : V) (δ : Subst V) : (IntExp.var v) /ₑ δ = δ v := rfl

omit [DecidableEq V] in
/--
우단위 법칙. `m >>= pure = m` 에 해당한다.

명제 1.2(b) 와 같은 정리다. Reynolds 가 *"acts as an identity substitution"* 이라고
말한 것이 이 법칙이다.
-/
theorem subst_pure_right (e : IntExp V) : e /ₑ IntExp.var = e := subst_var_intExp e

omit [DecidableEq V] in
/--
결합법칙. `(m >>= f) >>= g = m >>= (fun x => f x >>= g)` 에 해당한다.

연습문제 1.7(a) 의 정수 식 판이다. 결합자가 없어서 등식으로 성립한다.
-/
@[exercise "심화 A2.1" 2]
theorem subst_assoc_intExp (e : IntExp V) (δ δ' : Subst V) :
    (e /ₑ δ) /ₑ δ' = e /ₑ (fun w => (δ w) /ₑ δ') := by
  -- 힌트: `e` 에 대한 구조적 귀납법. `var` 케이스가 `rfl` 인 것이 좌단위 법칙이다.
  sorry


/-! ## 2. 단언 — 결합법칙이 등식으로 성립하지 않는다

Reynolds 의 연습 1.7(a) 진술을 다시 보자.

> *"then `p/δ''` **is a renaming of** `(p/δ)/δ'`"*

등호가 아니라 "이름 바꾸기" 다. 이유는 `Assert.subst` 의 양화사 절에 있다.

```
(∀v. p) /ₛ δ = ∀ (newBinder p v δ). (p /ₛ δ[v := var (newBinder p v δ)])
```

`newBinder` 가 고르는 이름은 `p`, `v`, `δ` 에 달려 있다. 치환을 두 번 나눠서 하면
중간 단계에서 한 번 이름을 고르고, 합쳐서 한 번에 하면 다른 자료로 다시 고른다.
두 결과의 결합 변수 이름이 갈릴 수 있고, 그러면 구문으로는 다른 항이 된다.

그래서 단언 쪽에서 성립하는 것은 뜻의 일치다. -/

/--
결합법칙의 단언 판. 구문이 아니라 **뜻**이 같다.

치환 정리(명제 1.3)를 두 번 쓰면 나온다. 왼쪽을 두 번 풀어 상태로 옮기고,
오른쪽을 한 번 풀어 상태로 옮긴 다음, 두 상태가 `p.fv` 위에서 같음을 보인다.
그 마지막 단계가 정수 식 판 치환 정리다.

Reynolds 의 "is a renaming of" 를 구문 수준에서 정확히 말하려면 α-동치가 필요하다.
§3 에서 그 이야기를 이어 간다.
-/
theorem subst_assoc_assert_meaning [Cslib.HasFresh V]
    (p : Assert V) (δ δ' : Subst V) (σ : State V) :
    (⟦(p /ₛ δ) /ₛ δ'⟧ₐ σ ↔ ⟦p /ₛ (fun w => (δ w) /ₑ δ')⟧ₐ σ) := by
  -- `δ'` 를 σ 에서 평가해 만든 상태.
  set τ : State V := fun w => ⟦δ' w⟧ₑ σ with hτ
  -- 왼쪽: 바깥 치환을 먼저 풀고, 이어서 안쪽 치환을 푼다.
  have hL : (⟦(p /ₛ δ) /ₛ δ'⟧ₐ σ ↔ ⟦p /ₛ δ⟧ₐ τ) :=
    substitution_assert (p /ₛ δ) δ' τ σ fun w _ => rfl
  have hL2 : (⟦p /ₛ δ⟧ₐ τ ↔ ⟦p⟧ₐ (fun w => ⟦δ w⟧ₑ τ)) :=
    substitution_assert p δ (fun w => ⟦δ w⟧ₑ τ) τ fun w _ => rfl
  -- 오른쪽: 합친 치환을 한 번에 푼다.
  have hR : (⟦p /ₛ (fun w => (δ w) /ₑ δ')⟧ₐ σ ↔ ⟦p⟧ₐ (fun w => ⟦(δ w) /ₑ δ'⟧ₑ σ)) :=
    substitution_assert p _ (fun w => ⟦(δ w) /ₑ δ'⟧ₑ σ) σ fun w _ => rfl
  -- 두 상태가 같다. 정수 식 판 치환 정리가 여기서 쓰인다.
  have hstate : (fun w => ⟦δ w⟧ₑ τ) = (fun w => ⟦(δ w) /ₑ δ'⟧ₑ σ) := by
    funext w
    exact (substitution_intExp (δ w) δ' τ σ fun u _ => rfl).symm
  rw [hL, hL2, hR, hstate]

/-! ## 3. 결합자가 있으면 몫으로 가야 한다

정수 식에는 결합자가 없어서 치환이 항 위에서 그대로 모나드를 이룬다.
단언에는 `∀v` 가 있어서, 같은 뜻을 가진 항이 결합 변수 이름만 다른 채로 여럿 생긴다.
모나드 법칙은 그 이름 차이를 무시해야 성립한다.

이것이 구문을 다루는 세 가지 표준적인 대응이 존재하는 이유다.

| 접근 | 방법 | 이 저장소에서 |
|---|---|---|
| 이름 있는 항 + α-동치 | 항은 그대로 두고 `=α` 로 나눈 몫에서 법칙을 본다 | CSlib `HasAlphaEquiv` (`m =α n`) |
| de Bruijn 색인 | 결합 변수 이름을 없애고 거리로 표시한다 | — |
| locally nameless | 자유 변수는 이름, 속박 변수는 색인 | CSlib `Languages/LambdaCalculus/LocallyNameless/*` |

Reynolds 도 §1.4 끝에서 같은 문제를 짚고 네 번째 길을 언급한다.

> *"a recent trend in semantics and logic is to regard the names of bound variables as an
> aspect of concrete, rather than abstract, syntax. From this viewpoint, called
> **higher-order abstract syntax**, phrases related by renaming … would be different
> representations of the same abstract phrase."*

즉 이름을 아예 구체 구문 쪽으로 밀어 버리는 관점이다.

이 저장소는 이름 있는 항을 그대로 쓴다. Reynolds 의 서술을 따라가는 것이 목적이고,
포획 회피 치환을 직접 정의해 보는 경험이 §1.4 의 내용이기 때문이다.
α-동치로 나눈 몫에서 결합법칙을 등식으로 만드는 것은 연습으로 남긴다.

이론적으로 더 들어가면, 결합자가 있는 구문의 초기 대수는 집합이 아니라
준층(presheaf)에서 산다. Fiore, Plotkin, Turi, *Abstract Syntax with Variable Binding*
(LICS 1999) 이 그 이야기다. `Depth/Algebra.lean` 의 초기 대수가 그 방향으로 확장된다.
-/

/-- 이름 바꾸기 정리(명제 1.5)를 α-동치의 의미론 판으로 다시 읽은 것. -/
theorem quant_rename_meaning [Cslib.HasFresh V] (q : Quant) (v vnew : V) (p : Assert V)
    (hfresh : vnew ∉ p.fv.erase v) (σ : State V) :
    (⟦Assert.quant q vnew (p /[v := IntExp.var vnew] )⟧ₐ σ ↔ ⟦Assert.quant q v p⟧ₐ σ) :=
  renaming_assert q v vnew p hfresh σ

end Reynolds.Exercises.Ch01
