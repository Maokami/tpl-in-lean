/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Answers.Ch01.Substitution
public import Reynolds.Answers.Ch01.Depth.SignatureFunctor

/-!
# 심화 A · 치환과 bind

선택 파일이다. `Ch01/Substitution.lean` 을 먼저 읽어야 한다.

## 시작점

Reynolds 는 명제 1.2(b) 에 이런 주석을 단다.

> *"Note that part (b) of this proposition asserts that the constructor `c_var`, which injects
> variables into the corresponding integer expressions, acts as an identity substitution."*

그리고 연습문제 1.7(a) 에서 치환 두 번의 합성을 묻는다.

> *"If `p` is a phrase of type θ, and `δ''w = (δw)/δ'` for all `w ∈ FV_θ(p)`,
> then `p/δ''` is a renaming of `(p/δ)/δ'`."*

두 진술을 나란히 놓으면 모나드의 단위 법칙과 결합법칙이 보인다. 정확한 모나드 구조라면
`T V := IntExp V`인 자기함자 `T : Type → Type`와 다음 다형적 연산을 함께 가져야 한다.

```
pure_V : V → IntExp V
bind_{V,W} : IntExp V → (V → IntExp W) → IntExp W
```

현재 `Subst V := V → IntExp V`와 `IntExp.subst`는 `V = W`인 성분만 구현한다.
따라서 이 파일은 모나드 구조 전체를 선언하지 않고, Reynolds가 실제로 쓴 동일 변수 타입의
치환 법칙이 모나드 법칙의 해당 성분과 일치함을 확인한다.

| Reynolds | 모나드 |
|---|---|
| `c_var : ⟨var⟩ → ⟨intexp⟩` | `pure` |
| `p / δ` | `p >>= δ` |
| `(c_var v) / δ = δ v` (정의로 성립) | 좌단위 `pure v >>= f = f v` |
| 명제 1.2(b) `p / c_var = p` | 우단위 `m >>= pure = m` |
| 연습 1.7(a) | 결합법칙 `(m >>= f) >>= g = m >>= fun x => f x >>= g` |

## 이 파일이 다루는 것

정수 식에서는 세 등식의 동일 타입 성분이 성립한다(§1).
단언에서는 포획 회피 과정이 고른 새 이름에 따라 결과 구문이 달라질 수 있다(§2).
이 파일은 두 결과의 의미가 같다는 약한 결론을 증명하고, Reynolds의 더 강한
"is a renaming of"를 구문 수준에서 적으려면 α-동치가 필요하다는 경계를 남긴다.

## 사전 지식
`Ch01/Substitution.lean`. 모나드를 몰라도 읽을 수 있게 썼다.
-/

@[expose] public section

namespace Reynolds.Answers.Ch01

open Reynolds

universe u

variable {V : Type u} [DecidableEq V]

/-! ## 1. 정수 식 — 세 법칙이 등식으로 성립한다

`IntExp V` 를 "변수 잎의 타입이 `V`인 항"으로 보면 치환은 각 변수 잎을 다른 항으로
바꾸고 결과를 다시 조립하는 연산이다. `var`가 `pure`의 `V` 성분이고 치환이 `bind`의
`V = W` 성분이다. `Depth/SignatureFunctor.lean` §4의 `PFunctor.FreeM`은 이 대응을 모든
변수 타입에 대해 묶어 주는 일반 구조다. -/

-- ANCHOR: monadLaws
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
  induction e with
  | num n => rfl
  | var v => rfl
  | neg e ih => simp [IntExp.subst, ih]
  | bin op e₀ e₁ ih₀ ih₁ => simp [IntExp.subst, ih₀, ih₁]
-- ANCHOR_END: monadLaws

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

이 파일에서 바로 증명하는 것은 구문적 이름 바꾸기보다 약한, 뜻의 일치다. -/

/--
결합법칙의 단언 판. 구문이 아니라 **뜻**이 같다.

치환 정리(명제 1.3)를 두 번 쓰면 나온다. 왼쪽을 두 번 풀어 상태로 옮기고,
오른쪽을 한 번 풀어 상태로 옮긴 다음, 두 상태가 `p.fv` 위에서 같음을 보인다.
그 마지막 단계가 정수 식 판 치환 정리다.

이 정리는 Reynolds의 "is a renaming of" 자체를 형식화하지 않는다. 이름 바꾸기라면 두
구문의 결합 구조가 α-동치라는 구문적 관계까지 보여야 하고, 의미 일치는 그 결과로 따라오는
성질이다. 이 저장소에는 아직 `Assert`의 α-동치 관계가 없으므로, 여기서는 치환 정리로
얻을 수 있는 의미적 결론까지만 증명한다.
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

/-! ## 3. 결합자가 있는 구문을 다루는 방법

정수 식에는 결합자가 없어서 모나드 법칙과 같은 모양의 치환 법칙이 구문적 등식으로 성립한다.
단언에는 `∀v` 가 있어서, 같은 뜻을 가진 항이 결합 변수 이름만 다른 채로 여럿 생긴다.
현재의 포획 회피 치환에 대해 모나드 법칙을 구문적 등식으로 말하려면 그 이름 차이를
무시하는 표현이 필요하다.

이름 차이를 다루는 표현 방법은 여러 가지이며, 각각 증명 부담을 다른 연산으로 옮긴다.

| 접근 | 방법 | 이 저장소에서 |
|---|---|---|
| 이름 있는 항 + α-동치 | 항은 그대로 두고 `=α` 로 나눈 몫에서 법칙을 본다 | CSlib `HasAlphaEquiv` (`m =α n`) |
| de Bruijn 색인 | 결합 변수 이름을 없애고 거리로 표시한다 | — |
| locally nameless | 자유 변수는 이름, 속박 변수는 색인 | CSlib `Languages/LambdaCalculus/LocallyNameless/*` |
| HOAS | 객체언어의 결합을 메타언어 함수로 표현한다 | — |

Reynolds 도 §1.4 끝에서 같은 문제를 짚고 네 번째 길을 언급한다.

> *"a recent trend in semantics and logic is to regard the names of bound variables as an
> aspect of concrete, rather than abstract, syntax. From this viewpoint, called
> **higher-order abstract syntax**, phrases related by renaming … would be different
> representations of the same abstract phrase."*

Reynolds의 설명은 결합 변수 이름을 추상 구문의 동일성 기준에서 제외한다는 방향을 말한다.
현대의 HOAS는 보통 메타언어의 함수 공간으로 객체언어의 결합을 표현하는 구체적인 기법을
가리키므로, 이름을 무시한다는 원칙과 그 구현 방법을 구분해서 읽어야 한다.

이 저장소는 이름 있는 항을 그대로 쓴다. Reynolds 의 서술을 따라가는 것이 목적이고,
포획 회피 치환을 직접 정의해 보는 경험이 §1.4 의 내용이기 때문이다.
α-동치로 나눈 몫에서 결합법칙을 등식으로 만드는 것은 연습으로 남긴다.

이름을 직접 쓰는 원시 구문(raw named syntax) 자체는 이 저장소가 보였듯 `Type` 위의
귀납 대수로 다룰 수 있다. 문맥 확장, 결합 대수, 치환 구조와 그 호환성까지 한 초기 모델에
담는 한 방법은 변수 문맥 위의 준층(presheaf)을 쓰는 것이다. Fiore, Plotkin, Turi의
*Abstract Syntax with Variable Binding* (LICS 1999)은 이 더 강한 초기성에서 의미론적
치환 보조정리까지 얻는 구성을 제시한다. 현재 파일의 원시 이름 구문 초기성과는 범주와
보편 성질이 다르다.

-/

/-- 이름 바꾸기 정리(명제 1.5)를 α-동치의 의미론 판으로 다시 읽은 것. -/
theorem quant_rename_meaning [Cslib.HasFresh V] (q : Quant) (v vnew : V) (p : Assert V)
    (hfresh : vnew ∉ p.fv.erase v) (σ : State V) :
    (⟦Assert.quant q vnew (p /[v := IntExp.var vnew] )⟧ₐ σ ↔ ⟦Assert.quant q v p⟧ₐ σ) :=
  renaming_assert q v vnew p hfresh σ

end Reynolds.Answers.Ch01
