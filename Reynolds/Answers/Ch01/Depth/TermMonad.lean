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

/-! ## 4. 변수 타입을 바꾸는 치환 — 진짜 `bind`

**2장으로 가는 다리.** 2장의 리프팅 모나드 `Σ⊥ = Flat (State V)`(`Ch02/Semantics.lean`의
`SigmaBot`)도 같은 모양의 구조를 갖는다. `pure`에 해당하는 것은 `Flat.some`, Kleisli
확장에 해당하는 것은 `liftBot`이고, `liftBot_eq_bind`가 그 `liftBot`이 정확히
`Flat.bind`와 같음을 보여 준다. 이 파일의 `IntExp.bind`/`Subst.kleisli`와 2장의
`Flat.bind`/`liftBot`은 "항 모나드"와 "리프팅 모나드"라는 서로 다른 계산 효과가 공유하는
같은 뼈대다. 2장에서 순차 합성 `;`의 결합성을 `Flat.bind`의 결합법칙 한 줄로 증명할 때
이 자리를 가리킨다.

§1 의 `IntExp.subst`는 `V = W`인 성분만 다룬다. 책이 실제로 요구하는 것은 변수 타입이
달라져도 되는 일반형이다 — `IntExp V`를 "변수 잎의 타입이 `V`인 항"으로 보면, 그 잎을
*다른 변수 타입의 식*으로 바꿔 끼우는 연산도 똑같이 정의된다. `V ↦ IntExp V`가 모나드라면
이것이 그 `bind`다. -/

/--
다형 `bind`. `e`의 변수 잎 각각을 `f`가 돌려주는 `IntExp W`로 바꿔 끼운다.

§1 의 `IntExp.subst`(`e /ₑ δ`, `δ : V → IntExp V`)는 이 연산의 `V = W` 성분이다.
`IntExp.subst_eq_bind`가 그 사실을 확인한다.
-/
-- ANCHOR: IntExp.bind
def IntExp.bind {V W : Type u} (e : IntExp V) (f : V → IntExp W) : IntExp W :=
  match e with
  | .num n        => .num n
  | .var v        => f v
  | .neg e        => .neg (e.bind f)
  | .bin op e₀ e₁ => .bin op (e₀.bind f) (e₁.bind f)
-- ANCHOR_END: IntExp.bind

omit [DecidableEq V] in
/--
§1 의 `IntExp.subst`는 `IntExp.bind`의 `V = W` 특수화다.

`pure := IntExp.var`로 두면 `IntExp.subst`와 `IntExp.bind`는 글자 그대로 같은 재귀식을
쓴다. 두 이름이 따로 있는 이유는 역사적이다 — §1 은 Reynolds 가 실제로 쓰는 동일 타입
치환만 다루고, 여기서 변수 타입을 바꾸는 일반형을 더한다.
-/
theorem IntExp.subst_eq_bind (e : IntExp V) (δ : Subst V) : e /ₑ δ = e.bind δ := by
  induction e with
  | num n => rfl
  | var v => rfl
  | neg e ih => simp [IntExp.subst, IntExp.bind, ih]
  | bin op e₀ e₁ ih₀ ih₁ => simp [IntExp.subst, IntExp.bind, ih₀, ih₁]

/-! **`Monad IntExp` 인스턴스를 만들지 않기로 한 이유.**

`IntExp : Type u → Type u`이므로 원리적으로는 `instance : Monad IntExp`를
`pure := IntExp.var`, `bind := IntExp.bind`로 줄 수 있다. 실제로 컴파일도 된다 —
단, `IntExp.bind`를 **타입 서명에 바로 매는 등식(`def f (e) : T | pat => …`) 꼴이 아니라
`:= match e with …` 꼴로 써야 한다.** 두 변수 타입 `V`, `W`가 다를 때(`e : IntExp V`,
결과 `IntExp W`) 전자의 꼴로 쓰면 엘라보레이터가 `.num` 같은 점 표기의 기대 타입을
결과 타입보다 먼저 확정하려다 실패한다(실측 확인됨 — `V = W`로 고정한 `IntExp.subst`는
같은 꼴로도 문제없이 컴파일된다).

그렇더라도 인스턴스를 **선언하지는 않는다.** `Monad`/`Applicative`가 끌고 오는
`Functor.map`·`Seq`·`SeqLeft`·`SeqRight`는 1장 어디에서도 쓰이지 않고, 이 장의 나머지는
`IntExp.bind`와 `Subst.kleisli`를 이름으로 직접 쓴다. 전역 `pure`/`bind`/`>>=` 표기를
열어 두는 대신 구체적인 이름을 쓰는 쪽이, "이것이 모나드다"를 보여 주려는 목적에는
오히려 더 뚜렷하다. -/

/-- Kleisli 합성. 책 연습 1.7(a)의 `δ''`에 해당한다: `δ`로 옮기고 다시 `δ'`로 옮기는 것을
    한 번에 하는 치환. -/
-- ANCHOR: Subst.kleisli
def Subst.kleisli {V W X : Type u} (δ : V → IntExp W) (δ' : W → IntExp X) : V → IntExp X :=
  fun v => (δ v).bind δ'

@[inherit_doc Subst.kleisli] scoped infixr:90 " >=>ₑ " => Subst.kleisli
-- ANCHOR_END: Subst.kleisli

-- ANCHOR: IntExp.bind_pure_left
/-- 좌단위. `pure v >>= f = f v`. `IntExp.bind`의 `var` 절이 곧 이 등식이다. -/
theorem IntExp.bind_pure_left {V W : Type u} (v : V) (f : V → IntExp W) :
    (IntExp.var v).bind f = f v := rfl
-- ANCHOR_END: IntExp.bind_pure_left

-- ANCHOR: IntExp.bind_pure_right
/-- 우단위. `m >>= pure = m`. `subst_pure_right`(§1, `V = W` 판)의 일반화다. -/
theorem IntExp.bind_pure_right {V : Type u} (e : IntExp V) : e.bind IntExp.var = e := by
  induction e with
  | num n => rfl
  | var v => rfl
  | neg e ih => simp [IntExp.bind, ih]
  | bin op e₀ e₁ ih₀ ih₁ => simp [IntExp.bind, ih₀, ih₁]
-- ANCHOR_END: IntExp.bind_pure_right

/--
**결합법칙 — 연습 1.7(a)의 정수 식 판, 변수 타입을 바꾸는 일반형.**

책의 진술은 "`δ''w = (δw)/δ'`이면 `p/δ''`은 `(p/δ)/δ'`의 이름 바꾸기"다. 결합자가 없는
`IntExp`에서는 "이름 바꾸기"가 곧 등식이 되고, `δ'' = δ >=>ₑ δ'`가 정확히
`Subst.kleisli`다.

"심화 A2.1"(`subst_assoc_intExp`, §1 의 `V = W` 고정판)을 먼저 풀어 본 사람은 `var` 케이스가
`rfl`인 이유가 여기서도 그대로임을 알아챈다. 이 정리는 그 결과를 쓰지 않는다 — 구조가
같을 뿐 증명은 독립적으로 다시 한다.
-/
-- ANCHOR: stmtBindAssoc
@[exercise "심화 A2.2" 2]
theorem IntExp.bind_assoc {V W X : Type u} (e : IntExp V) (δ : V → IntExp W) (δ' : W → IntExp X) :
    (e.bind δ).bind δ' = e.bind (δ >=>ₑ δ')
-- ANCHOR_END: stmtBindAssoc
    := by
  induction e with
  | num n => rfl
  | var v => rfl
  | neg e ih => simp [IntExp.bind, ih]
  | bin op e₀ e₁ ih₀ ih₁ => simp [IntExp.bind, ih₀, ih₁]

/-! ## 5. `Assert`에서 결합법칙이 등식으로 깨지는 구체 반례

§2의 `subst_assoc_assert_meaning`은 **뜻**이 같다는 것만 보였다. 여기서는 그보다 강한
"구문이 같다"가 실제로 깨지는 예를 하나 든다 — Reynolds가 "같다"가 아니라 "이름 바꾸기다"
라고 쓴 것이 조심해서 고른 단어라는 증거다. -/

/--
**구체 반례.** `∀y. y > x`를 `x ↦ y`(다른 변수로)치환했다가 다시 `y ↦ 0`을 치환하는 것과,
두 치환을 먼저 합쳐 한 번에 적용하는 것은 **구문으로는** 다른 결과를 낸다.

`δ = [x ↦ y]`를 먼저 적용하면 포획을 피하려고 결합 변수 `y`를 다른 이름으로 바꿔야 한다
(`captureSet (∀y. y>x) y δ = {y}`이기 때문이다). 어떤 이름으로 바뀌든 그 이름은 `y`가 아니므로,
두 번째 치환 `δ' = [y ↦ 0]`을 적용해도 그 결합 변수는 그대로 남는다. 반대로 두 치환을
먼저 합친 `δ >=>ₑ δ' = [x ↦ 0, y ↦ 0]`을 한 번에 적용하면 `y`는 애초에 안전해서
(`δ(δ' 합성)`이 "y"에 보낼 자유 변수가 없다) 결합 변수가 그대로 `y`로 남는다. 두 결과가
결합 변수 이름에서 어긋난다.

증명은 그 어긋남 자체는 쓰지 않는다 — `newBinder_notMem`으로 왼쪽의 새 결합 변수가
`y`가 아니라는 것만 뽑고, 오른쪽의 결합 변수가 `y`로 유지된다는 것은 포획 집합이
비었다는 계산에서 바로 나온다. 둘을 생성자 단사성(`Assert.quant.injEq`)으로 비교하면
끝난다 — `newBinder`가 실제로 어떤 이름을 고르는지는 몰라도 된다.
-/
-- ANCHOR: stmtSubstAssocAssertNotEq
@[exercise "심화 A2.3" 2]
theorem subst_assoc_assert_not_eq :
    ∃ (p : Assert String) (δ δ' : Subst String),
      (p /ₛ δ) /ₛ δ' ≠ p /ₛ (fun w => (δ w) /ₑ δ')
-- ANCHOR_END: stmtSubstAssocAssertNotEq
    := by
  set body : Assert String := .cmp .gt (.var "y") (.var "x") with hbody
  set δ : Subst String := Function.update IntExp.var "x" (.var "y") with hδ
  set δ' : Subst String := Function.update IntExp.var "y" (.num 0) with hδ'
  refine ⟨.quant .all "y" body, δ, δ', ?_⟩
  have hxy : ("x" : String) ≠ "y" := by decide
  -- 왼쪽 첫 치환이 `"y"`를 안전하지 않게 만든다: `δ "x" = y`가 그 포획 집합에 들어간다.
  have hmem1 : ("y" : String) ∈ captureSet body "y" δ := by
    refine Finset.mem_biUnion.mpr ⟨"x", ?_, ?_⟩
    · simp [Assert.fv, IntExp.fv, hbody]
    · simp [hδ, IntExp.fv]
  have hne : newBinder body "y" δ ≠ "y" := by
    intro heq
    have hnotmem := newBinder_notMem body "y" δ
    rw [heq] at hnotmem
    exact hnotmem hmem1
  set v₁ : String := newBinder body "y" δ with hv1
  -- 첫 치환을 전개한다: 결합 변수가 `v₁`로 바뀌고, 본문은 `v₁ > y`가 된다.
  have hL1 : (Assert.quant .all "y" body) /ₛ δ
      = .quant .all v₁ (.cmp .gt (.var v₁) (.var "y")) := by
    simp only [Assert.subst, ← hv1]
    congr 1
  -- 두 번째 치환에서는 `v₁`이 안전하다(포획 집합에 `v₁`이 없다) — 결합 변수가 그대로 유지된다.
  have hsafe2 : v₁ ∉ captureSet (.cmp .gt (.var v₁) (.var "y") : Assert String) v₁ δ' := by
    intro hmem
    obtain ⟨w, hw, hw2⟩ := Finset.mem_biUnion.mp hmem
    simp only [Assert.fv, IntExp.fv, Finset.mem_erase, Finset.mem_union,
      Finset.mem_singleton] at hw
    have hwy : w = "y" := by
      rcases hw with ⟨hwne, hwv₁ | hwy⟩
      · exact absurd hwv₁ hwne
      · exact hwy
    subst hwy
    simp [hδ', IntExp.fv] at hw2
  have hv1safe : newBinder (.cmp .gt (.var v₁) (.var "y") : Assert String) v₁ δ' = v₁ := by
    simp [newBinder, hsafe2]
  have hLfinal : ((Assert.quant .all "y" body) /ₛ δ) /ₛ δ'
      = .quant .all v₁ (.cmp .gt (.var v₁) (.num 0)) := by
    rw [hL1]
    simp only [Assert.subst, hv1safe]
    congr 1
    simp [IntExp.subst, Function.update_self, Function.update_of_ne hne.symm, hδ']
  -- 오른쪽: 합친 치환은 애초에 `"y"`를 안전하게 둔다 — 결합 변수가 그대로 `"y"`로 남는다.
  have hcap3 : ("y" : String) ∉ captureSet body "y" (fun w => (δ w) /ₑ δ') := by
    intro hmem
    obtain ⟨w, hw, hw2⟩ := Finset.mem_biUnion.mp hmem
    simp only [Assert.fv, IntExp.fv, hbody, Finset.mem_erase, Finset.mem_union,
      Finset.mem_singleton] at hw
    have hwx : w = "x" := by
      rcases hw with ⟨hwne, hwy | hwx⟩
      · exact absurd hwy hwne
      · exact hwx
    subst hwx
    simp [hδ, hδ', IntExp.subst, IntExp.fv, Function.update_self] at hw2
  have hysafe : newBinder body "y" (fun w => (δ w) /ₑ δ') = "y" := by
    simp [newBinder, hcap3]
  have hRfinal : (Assert.quant .all "y" body) /ₛ (fun w => (δ w) /ₑ δ')
      = .quant .all "y" (.cmp .gt (.var "y") (.num 0)) := by
    simp only [Assert.subst, hysafe]
    congr 1
  rw [hLfinal, hRfinal]
  intro h
  injection h with _ hv _
  exact hne hv

/-! ## 6. α-동치 — 연습 1.7을 책 그대로 "renaming of"로 진술하기

`subst_assoc_assert_not_eq`가 보인 어긋남은 결합 변수 이름뿐이다. 그 이름 차이를
무시하는 관계가 있으면, Reynolds의 "`p/δ''`은 `(p/δ)/δ'`의 **이름 바꾸기**"를 구문
수준에서 그대로 옮길 수 있다. -/

/--
`Assert`의 α-동치. 구조는 같고 결합 변수 이름만 다른 것을 동일시한다.

`cmp` 절은 정수 식 쪽을 그대로 요구한다 — `IntExp`에는 결합자가 없으므로 비교식 두 자리가
*같은* 정수 식이어야 한다(§1.4는 정수 식의 α-동치를 다루지 않는다). `quant` 절만 결합
변수 이름 차이를 허용한다. `newBinder`가 고르는 이름은 호출마다 달라질 수 있으므로,
등식 대신 이 관계로 §1.4 명제들의 "renaming" 서술을 정확히 옮길 수 있다.
-/
-- ANCHOR: Assert.AlphaEq
inductive Assert.AlphaEq [DecidableEq V] [HasFresh V] : Assert V → Assert V → Prop
  | tru : Assert.AlphaEq .tru .tru
  | fls : Assert.AlphaEq .fls .fls
  | cmp (c : Cmp) (e₀ e₁ : IntExp V) : Assert.AlphaEq (.cmp c e₀ e₁) (.cmp c e₀ e₁)
  | not {p p' : Assert V} : Assert.AlphaEq p p' → Assert.AlphaEq (.not p) (.not p')
  | bin (op : LogOp) {p p' q q' : Assert V} :
      Assert.AlphaEq p p' → Assert.AlphaEq q q' → Assert.AlphaEq (.bin op p q) (.bin op p' q')
  | quant (qt : Quant) (v v' : V) (p p' : Assert V) (w : V)
      (hw : w ∉ p.fv.erase v ∪ p'.fv.erase v') :
      Assert.AlphaEq (p /[v := .var w]) (p' /[v' := .var w]) →
      Assert.AlphaEq (.quant qt v p) (.quant qt v' p')
-- ANCHOR_END: Assert.AlphaEq

/-- `Assert`에 α-동치 표기 `p =α q`를 연결한다. CSlib `HasAlphaEquiv`. -/
instance [HasFresh V] : HasAlphaEquiv (Assert V) := ⟨Assert.AlphaEq⟩

/--
**α-동치는 뜻을 보존한다 — 명제 1.5(이름 바꾸기 정리)의 구문적 일반화.**

명제 1.5는 "결합 변수 하나를 그 자리에서 새 이름으로 바꾼 결과"의 뜻이 같다고 말한다.
`=α`는 그 바꿔치기를 구문의 어느 깊이에서든, 몇 번이든 허용한다. 증명은 `quant` 케이스에서
그 명제 1.5를 양쪽에 한 번씩 쓰고, 합동 보조정리(`Equivalent.bin_congr`,
`Equivalent.quant_congr` — 둘 다 비채점 완성본)로 안쪽 결과를 바깥으로 옮긴다.

**독립성 때문에 명제 1.5를 전역 `renaming_assert`로 직접 부르지 않고 가설
`hrename`으로 받는다.** `Substitution.lean`의 `renaming_assert`는 그 자신의 증명
안에서 `substitution_assert`(`Prop 1.3-assert`, 채점)를 직접 쓴다. 그래서 이 정리가
`renaming_assert`를 전역 이름으로 불러 쓰면, Exercises 트리에서 `Prop 1.3-assert`가
아직 `sorry`인 동안 이 정리의 독립성 검사가 "다른 채점 연습에 의존한다"고 판정한다
(실측 확인됨, `AGENTS.md` §1-9). `Ex/Summation/Substitution.lean`의 `substitution_sExp`가
일치 정리를 `hcoin` 가설로 받는 것과 같은 해법이다 — 실제로 쓸 때는 `renaming_assert`
자체를 그 가설 자리에 넘긴다.

`not` 케이스에서는 `Equivalent.not_congr`(심화 A1.8, 채점)를 **쓰지 않는다** — 채점
연습끼리는 기대지 않는다는 원칙(`AGENTS.md` §1-9) 때문에, 똑같이 한 줄인 증명을 여기서
다시 쓴다.
-/
-- ANCHOR: stmtAlphaEqSound
@[exercise "심화 A2.4" 3]
theorem Assert.AlphaEq.sound [HasFresh V]
    (hrename : ∀ (qt : Quant) (v₀ vnew : V) (body : Assert V), vnew ∉ body.fv.erase v₀ →
      ∀ σ : State V,
        ⟦Assert.quant qt vnew (body /[v₀ := IntExp.var vnew] )⟧ₐ σ ↔ ⟦Assert.quant qt v₀ body⟧ₐ σ)
    {p p' : Assert V} (h : p =α p') :
    Equivalent p p'
-- ANCHOR_END: stmtAlphaEqSound
    := by
  induction h with
  | tru => intro _; rfl
  | fls => intro _; rfl
  | cmp c e₀ e₁ => intro _; rfl
  | not _ ih => intro σ; simp [Assert.eval, ih σ]
  | bin op _ _ ihp ihq => exact Equivalent.bin_congr ihp ihq
  | quant qt v v' p p' w hw _ ih =>
      intro σ
      have hw1 : w ∉ p.fv.erase v := fun hmem => hw (Finset.mem_union.mpr (Or.inl hmem))
      have hw2 : w ∉ p'.fv.erase v' := fun hmem => hw (Finset.mem_union.mpr (Or.inr hmem))
      exact (hrename qt v w p hw1 σ).symm.trans
        ((Equivalent.quant_congr w ih σ).trans (hrename qt v' w p' hw2 σ))

end Reynolds.Answers.Ch01
