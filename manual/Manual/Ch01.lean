/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External

set_option verso.exampleProject ".."
set_option verso.exampleModule "Reynolds.Answers.Ch01.Syntax"

#doc (Manual) "1장 술어 논리" =>
%%%
tag := "ch01"
%%%

Reynolds 1장은 술어 논리를 _언어 하나로_ 다룬다. 논리학 강의처럼 증명 기술을 가르치는 것이
아니라, 구문을 정의하고 뜻을 주고 성질을 증명하는 절차를 술어 논리 위에서 한 번 끝까지
보여 준다. 2장부터 나오는 모든 언어가 같은 절차를 반복하므로, 여기서 익힌 순서가 책 전체의
뼈대가 된다.

이 문서는 책을 대신하지 않는다. 저장소의 Lean 코드가 무엇을 하고 있는지, 그리고
*책이 본문 밖으로 미룬 논의*들이 무엇인지를 잇는 안내서다. 인용한 코드는 전부 저장소에서
그대로 끌어온 것이라, 코드가 바뀌면 이 문서의 빌드가 깨진다.

# 이 장에서 배우는 것
%%%
tag := "ch01-goals"
%%%

* *추상 구문* — 언어를 문자열이 아니라 트리로 정의하는 것, 그리고 그때 필요한 세 조건
* *표시적 의미론* — 구문의 각 절에 뜻을 주는 방정식. 구조적 재귀가 곧 정의다
* *타당성과 추론* — 뜻으로 정의한 참과 규칙으로 유도한 참, 그리고 둘을 잇는 건전성
* *결합과 치환* — 양화사가 들어오면서 생기는 자유·속박 구분, 그리고 변수 포획

마지막 항목이 1장의 무게 중심이다. 앞의 셋은 비교적 곧게 가고, 치환에서 처음으로
"정의를 조심해서 써야 하는" 상황이 나온다.

# 읽는 순서
%%%
tag := "ch01-order"
%%%

파일마다 docstring 첫머리에 "읽는 순서" 가 적혀 있지만, 처음 오는 사람을 위해 한 줄로 모은다.

1. `Background.lean` — *가장 먼저 읽어라.* 선택 사항이 아니다
2. `Syntax.lean` — §1.1 추상 구문
3. `Notation.lean` — §1.1 구체 구문. 객체 언어를 Lean 표기로 쓰는 DSL
4. `Semantics.lean` — §1.2 표시적 의미론
5. `Validity.lean` — §1.3 타당성, 추론 규칙, 건전성
6. `FreeVars.lean` — §1.4 자유 변수와 일치 정리
7. `Substitution.lean` — §1.4 치환, 명제 1.2 ~ 1.5
8. `Realizations.lean`, `Ex.lean`, `Ex/Summation.lean` — 책 연습문제
9. `Depth/` — 심화 트랙. 건너뛰어도 1장은 완결된다

전부 `Reynolds/Answers/Ch01/` 아래에 있고, 같은 구조가 `Reynolds/Exercises/Ch01/` 에도
있다. 그쪽은 연습 지점만 {lit}`sorry` 로 비어 있다.

## 연습은 `Ex.lean` 에만 있지 않다
%%%
tag := "ch01-exercises-are-everywhere"
%%%

이름 때문에 오해하기 쉬운 자리가 있다.
*책의 명제 1.1 ~ 1.5 증명이 본문 파일 안에 연습으로 들어 있다.* `FreeVars.lean` 의 일치 정리, `Substitution.lean` 의 치환 정리,
`Validity.lean` 의 건전성이 그렇다.

순서가 중요하다. `Ex.lean` 의 연습 1.4 는 치환 정리를 _쓴다_. 본문 파일을 건너뛰고
`Ex.lean` 부터 열면 재료가 없는 상태로 문제를 마주하게 된다.
위의 1 ~ 7 을 순서대로 밟는 것이 그래서 권고가 아니라 요구다.

무엇이 어디에 몇 개 있는지는 아래 [연습문제](--tag--ch01-exercise-list) 절에 표로 있다.

# §1.1 추상 구문
%%%
tag := "ch01-syntax"
%%%

Reynolds 는 추상 구문에 세 조건을 손으로 부과한다. 생성자가 단사일 것, 서로 다른 생성자의
치역이 서로소일 것, 모든 원소가 유한 번의 생성자 적용으로 만들어질 것.

Lean 의 {lit}`inductive` 선언은 이 셋을 선언과 동시에 준다. 확인해 보면 이렇다.

```anchor freeConditions (module := Reynolds.Answers.Ch01.Syntax)
/-- 조건 1. 생성자는 단사다. `injection` 이 바로 처리한다. -/
example : Function.Injective (IntExp.var (V := V)) := fun _ _ h => by injection h

/-- 조건 2. 서로 다른 생성자의 치역은 서로소다. -/
example : IntExp.num (V := V) n ≠ IntExp.var v := by nofun

/-- 조건 3. 모든 정수 식은 유한 번의 생성자 적용으로 만들어진다.
    구조적 귀납법(structural induction)이 정당한 근거이고, 재귀자 `IntExp.rec` 가 그 형태다. -/
example : True := trivial
```

세 번째 조건이 특히 중요하다. 구조적 귀납법이 정당한 근거가 그것이고, 1장의 거의 모든
증명이 구조적 귀납법이다.

단언(assertion)의 구문은 이렇게 생겼다.

```anchor Assert (module := Reynolds.Answers.Ch01.Syntax)
inductive Assert (V : Type u) where
  /-- 참 `true`. -/
  | tru
  /-- 거짓 `false`. -/
  | fls
  /-- 정수 비교 `e₀ ∼ e₁`. -/
  | cmp : Cmp → IntExp V → IntExp V → Assert V
  /-- 부정 `¬p`. -/
  | not : Assert V → Assert V
  /-- 이항 논리 연산 `p₀ ∘ p₁`. -/
  | bin : LogOp → Assert V → Assert V → Assert V
  /-- 양화 `∀v. p` / `∃v. p`. **결합 구성자**. -/
  | quant : Quant → V → Assert V → Assert V
  deriving DecidableEq, Repr
```

마지막 절이 이 장에서 유일하게 새로운 것이다. `quant` 는 *변수를 묶는다*.
정수 식에는 결합자가 없어서 자유·속박 구분이 생기지 않았는데, 여기서 생긴다.

_여기서 무엇을 얻었나._ 종이에서 "이런 조건을 만족하는 집합이 있다고 하자" 라고 가정하고
넘어가던 것이, Lean 에서는 선언 한 번으로 실제로 주어진다. 가정과 구성의 차이다.

# §1.2 표시적 의미론
%%%
tag := "ch01-semantics"
%%%

의미 함수는 구문의 절마다 방정식 하나씩이다. 구조적 재귀라서 정의가 곧 증명 도구가 된다 —
정의를 펼치는 것과 귀납법의 한 단계를 밟는 것이 같은 일이다.

```anchor assertEval (module := Reynolds.Answers.Ch01.Semantics)
def Assert.eval {V : Type u} [DecidableEq V] : Assert V → State V → Prop
  | .tru,            _ => True
  | .fls,            _ => False
  | .cmp c e₀ e₁,    σ => c.denote (e₀.eval σ) (e₁.eval σ)
  | .not p,          σ => ¬ p.eval σ
  | .bin op p q,     σ => op.denote (p.eval σ) (q.eval σ)
  | .quant .all v p, σ => ∀ n : Int, p.eval (σ[v := n])
  | .quant .ex  v p, σ => ∃ n : Int, p.eval (σ[v := n])
```

양화사 절을 보라. `∀v. p` 의 뜻은 "모든 정수 `n` 에 대해, `v` 를 `n` 으로 덮은 상태에서
`p` 가 참" 이다. *메타 수준의 `∀` 로 객체 수준의 `∀` 를 설명한다.*

이것이 Reynolds 가 §1.2 에서 계속 경계하는 자리다. 객체 언어의 기호와 메타 언어의 기호가
같은 모양이라 헷갈리기 쉽다. `Background.lean` 이 그 구분만 따로 다루는 이유다.

돌려 보면 이렇다.

```anchor evalExample (module := Reynolds.Answers.Ch01.Semantics)
example : ⟦IntExp.bin .add (.var "x") (.num 1)⟧ₑ (State.const 41) = 42 := by decide
```

_여기서 무엇을 얻었나._ 의미 함수가 *전함수*라는 것. 술어 논리에는 비종료가 없으므로
모든 구에 뜻이 있다. 2장에서 `while` 이 들어오면 이 사정이 무너지고, 그 순간을 위해
도메인 이론이 필요해진다. 1장이 쉬운 이유를 알아 두면 2장이 왜 어려운지가 보인다.

# §1.3 타당성과 추론
%%%
tag := "ch01-validity"
%%%

뜻이 있으면 "언제나 참" 을 말할 수 있다.

```anchor validity (module := Reynolds.Answers.Ch01.Validity)
/-- **타당(valid)** — 모든 상태에서 참. Reynolds §1.3. -/
def Valid (p : Assert V) : Prop := ∀ σ : State V, ⟦p⟧ₐ σ

/-- **충족 불가능(unsatisfiable)** — 어떤 상태에서도 거짓. -/
def Unsat (p : Assert V) : Prop := ∀ σ : State V, ¬ ⟦p⟧ₐ σ

/--
`p` 가 `q` 보다 **강하다(stronger)**. `q` 는 `p` 보다 **약하다(weaker)**.

Reynolds 가 곧바로 붙이는 단서가 있다.

> *"'stronger' and 'weaker' are dual preorders, which does not quite jibe with normal
> English usage. For example, any assertion is both stronger and weaker than itself."*

전순서(preorder)라서 반대칭성이 없다. 어떤 단언이든 자기 자신보다 강하면서 동시에 약하다.
-/
def Stronger (p q : Assert V) : Prop := ∀ σ : State V, ⟦p⟧ₐ σ → ⟦q⟧ₐ σ

/-- **동치(equivalent)** — 같은 뜻. -/
def Equivalent (p q : Assert V) : Prop := ∀ σ : State V, (⟦p⟧ₐ σ ↔ ⟦q⟧ₐ σ)
```

그리고 뜻과 무관하게, 규칙만으로 유도되는 것을 따로 정의한다.

```anchor proofSystem (module := Reynolds.Answers.Ch01.Validity)
/--
술어 논리의 작은 추론 체계. Reynolds §1.3 이 예시로 드는 규칙들이다.

완전한 체계가 아니고 그럴 의도도 없다. 추론 규칙과 건전성이 무엇인지 보이는 데 필요한
최소한만 담았다.
-/
inductive Proof : Assert V → Prop where
  /-- 공리꼴: `e = e`. -/
  | eqRefl (e : IntExp V) : Proof (.cmp .eq e e)
  /-- 한 전제 규칙: `e₀ = e₁` 로부터 `e₁ = e₀`. -/
  | eqSymm {e₀ e₁ : IntExp V} : Proof (.cmp .eq e₀ e₁) → Proof (.cmp .eq e₁ e₀)
  /-- 두 전제 규칙 — 전건 긍정(modus ponens). -/
  | mp {p q : Assert V} : Proof p → Proof (.bin .imp p q) → Proof q
  /-- 두 전제 규칙 — 연언 도입. -/
  | andIntro {p q : Assert V} : Proof p → Proof q → Proof (.bin .and p q)
  /--
  보편 일반화(∀-도입).

  전제가 타당할 때만 결론이 타당해진다. §4 에서 이 규칙과 함의 `p ⇒ ∀v. p` 를
  나란히 놓고 비교한다.
  -/
  | genAll (v : V) {p : Assert V} : Proof p → Proof (.quant .all v p)
```

두 정의는 서로 모른다. 하나는 상태를 훑고 하나는 규칙을 쌓는다. 이 둘을 잇는 것이
*건전성(soundness)* 이고, `Validity.lean` 에서 증명한다.

## 규칙과 함의는 다른 것이다
%%%
tag := "ch01-rule-vs-implication"
%%%

§1.3 에서 가장 헷갈리는 자리다. 보편 일반화 규칙은 건전한데, 같은 재료로 만든 함의는
타당하지 않다. 두 정리를 나란히 놓으면 차이가 드러난다.

```anchor genVsImp (module := Reynolds.Answers.Ch01.Validity)
/-- 규칙 쪽. `p` 가 타당하면 `∀v. p` 도 타당하다. -/
@[exercise "§1.3 gen-sound" 1]
theorem valid_forall_of_valid (v : V) {p : Assert V} (h : Valid p) :
    Valid (.quant .all v p) := fun _ _ => h _

/--
함의 쪽. `x > 0 ⇒ ∀x. x > 0` 은 타당하지 않다.

Reynolds 의 반례를 그대로 쓴다. `x ↦ 3` 인 상태에서 왼쪽은 참이고,
오른쪽은 `x` 에 0 을 넣으면 거짓이다.

같은 재료로 만든 규칙(위)과 함의(여기)의 판정이 갈린다.
-/
@[exercise "§1.3 gen-not-imp" 2]
theorem not_valid_imp_forall :
    ¬ Valid (.bin .imp (.cmp .gt (.var "x") (.num 0))
                       (.quant .all "x" (.cmp .gt (.var "x") (.num 0))) : Assert String) := by
  intro h
  -- x ↦ 3 인 상태를 잡으면 왼쪽은 참이다.
  have h3 := h (State.const 3)
  simp only [Assert.eval, LogOp.denote, Cmp.denote, IntExp.eval, State.const] at h3
  -- 따라서 오른쪽이 성립해야 하는데, n = 0 을 넣으면 거짓이다.
  have := h3 (by decide) 0
  simp at this
```

규칙은 *전제가 타당할 때* 결론이 타당하다고 말한다. 함의는 *한 상태 안에서* 왼쪽이
참이면 오른쪽도 참이라고 말한다. `x ↦ 3` 인 상태 하나만 잡으면 뒤쪽이 무너진다.

## 곁가지 — 완전성과 괴델
%%%
tag := "ch01-completeness"
%%%

Reynolds 는 §1.3 을 닫으면서 이 책이 다루지 않을 것을 알려 준다. 코드로 옮기지 않기로
한 논의라 여기에 산문으로 남긴다.

건전성의 역이 *완전성(completeness)* 이다. 타당한 것은 모두 유도되는가.

답은 "타당" 을 어떻게 정의했느냐에 달렸다.

* 우리처럼 *정수에 대한 고정된 해석*으로 정의하면, 어떤 유한한 규칙 집합도 완전하지
  않다. 괴델의 불완전성 정리가 그것이다. 산술의 참인 문장 전체를 유한한 규칙으로 길어
  올릴 수 없다.
* *논리적 타당성(logical validity)* — 연산 기호의 뜻까지 임의로 바꿔도 성립하는 것 —
  으로 정의하면 완전한 유한 체계가 있다. 괴델의 완전성 정리가 그것이다.

같은 이름의 두 정리가 반대 방향을 말하는 것처럼 보이지만, 두 "타당" 이 다른 것이다.

Reynolds 는 여기에 실용적인 단서를 붙인다. 프로그램 검증에서 논리적 완전성은 별 쓸모가
없다는 것이다. 우리는 `+` 가 정말 덧셈인 해석에만 관심이 있기 때문이다.
그 예외는 §3.8 에서 다룬다.

*왜 코드로 만들지 않았나.* 이 주제를 형식화하려면 증명론 전체가 따라온다 — 산술의
인코딩, 증명 가능성 술어, 대각화. Reynolds 본인이 다루지 않고, 1장의 목표와도 멀다.
Lean 으로 괴델을 보고 싶다면 `mathlib` 밖의 별도 프로젝트를 찾는 편이 낫다.

# §1.4 자유 변수와 일치 정리
%%%
tag := "ch01-freevars"
%%%

자유 변수는 결합자가 있어야 뜻이 생긴다. 정수 식 쪽은 그냥 나오는 변수를 모으면 되고,
단언 쪽에서 한 절만 다르다.

```anchor assertFv (module := Reynolds.Answers.Ch01.FreeVars)
def Assert.fv : Assert V → Finset V
  | .tru | .fls  => ∅
  | .cmp _ e₀ e₁ => e₀.fv ∪ e₁.fv
  | .not p       => p.fv
  | .bin _ p q   => p.fv ∪ q.fv
  | .quant _ v p => p.fv.erase v
```

`erase` 가 붙은 절 하나가 결합의 전부다.

이 정의가 옳다는 근거가 *일치 정리(coincidence theorem, 명제 1.1)* 다. 두 상태가
`FV(p)` 위에서 같으면 `p` 의 뜻이 같다는 것. 뜻이 실제로 의존하는 변수를 `fv` 가
빠짐없이 모으고 있다는 말이다.

증명에서 한 군데가 걸린다. Reynolds 가 직접 적어 둔 요령이다.

> "In applying the induction hypothesis, which holds for arbitrary states σ and σ',
> we take σ and σ' to be different states from the σ and σ' for which we are
> trying to prove the conclusion."

`∀v. p` 를 다룰 때 귀납 가설을 원래 상태가 아니라 `σ[v := n]`, `σ'[v := n]` 에 쓴다는
뜻이다. Lean 으로 옮기면 *진술을 `∀ (p) (σ σ')` 꼴로 써야 한다*는 요구가 된다.
`σ`, `σ'` 를 정리의 인자로 빼면 귀납 가설이 그 특정 상태에만 붙어서 이 단계가 막힌다.

이 패턴은 1장에서 여섯 번 나온다. 한 번 익히면 나머지가 따라온다.

_여기서 무엇을 얻었나._ "진술을 더 일반화해야 귀납이 돈다" 는 증명 실무의 기본기.
2장 명제 2.7 에서 같은 기술이 다시, 더 어려운 모습으로 나온다.

# §1.4 치환
%%%
tag := "ch01-substitution"
%%%

1장에서 가장 손이 많이 가는 곳이다.

````anchor assertSubst (module := Reynolds.Answers.Ch01.Substitution)
/--
`p /ₛ δ` — 단언에 대한 동시 치환.

양화사 절만 특별하다.

```
(∀v. p) /ₛ δ = ∀ vnew. (p /ₛ δ[v := var vnew])
```

`v` 를 새 이름 `vnew` 로 바꾸고, 치환 사상 쪽에서도 `v` 를 `var vnew` 로 보내도록 고친다.
`vnew` 는 `newBinder` 가 골라 주므로 `δ w` 의 자유 변수와 겹치지 않는다.

**정지성**: 재귀 호출이 `p` 라는 진부분항에 대해 일어나므로 구조적 재귀다.
"먼저 이름을 바꾸고 다시 치환한다" 는 식으로 정의하면 여기서 정지성 증명이 필요해진다.
Reynolds 의 정의를 그대로 따르면 그 문제가 없다.
-/
def Assert.subst [HasFresh V] : Assert V → Subst V → Assert V
  | .tru,          _ => .tru
  | .fls,          _ => .fls
  | .cmp c e₀ e₁,  δ => .cmp c (e₀ /ₑ δ) (e₁ /ₑ δ)
  | .not p,        δ => .not (p.subst δ)
  | .bin op p q,   δ => .bin op (p.subst δ) (q.subst δ)
  | .quant q v p,  δ =>
      .quant q (newBinder p v δ) (p.subst (Function.update δ v (.var (newBinder p v δ))))
````

양화사 절만 특별하다. `δ` 가 데려오는 자유 변수가 `v` 에 잡히면(*포획*, capture)
뜻이 달라지므로, 결합 변수를 안전한 이름으로 미리 바꾼다.

Reynolds 가 동시 치환을 기본으로 두는 이유도 여기 있다. 한 변수씩 정의하면
"이름을 바꾸고 다시 치환한다" 가 되어 정지성 증명이 따로 필요해진다.
동시 치환으로 두면 재귀 호출이 진부분항에서 일어나 구조적 재귀로 끝난다.

이 정의 위에서 명제 1.2 부터 1.5 까지가 이어진다. 치환 정리(명제 1.4)가 그중 중심이고,
"치환한 뒤 재기" 와 "재고 나서 상태를 갈아 끼우기" 가 같다는 것을 말한다.

## 곁가지 — 이름을 어떻게 다룰 것인가
%%%
tag := "ch01-binding-representations"
%%%

Reynolds 는 §1.4 끝에서 *고차 추상 구문(higher-order abstract syntax)* 을 언급하고
지나간다. 결합 변수의 이름을 구체 구문의 일부로 보는 관점이다. 이름이 추상 구문에
속하지 않는다고 보면 α-동치인 구들이 애초에 같은 것이 되고, 명제 1.5 가 정리가 아니라
정의가 된다.

이름을 다루는 방식은 크게 셋이고, 각각 값을 치르는 자리가 다르다.

| 방식 | 결합 변수 | 값을 치르는 곳 |
|---|---|---|
| 이름 있는(named) — 우리 방식 | 이름 그대로 | 치환에서 포획 회피. `newBinder` 가 그것이다 |
| de Bruijn 색인 | 번호 | 항을 옮길 때마다 번호 이동(shifting) |
| locally nameless | 묶인 것은 번호, 자유로운 것은 이름 | 두 표현 사이를 오가는 연산 |

우리가 이름 있는 방식을 고른 것은 Reynolds 를 따라간 것이다. 그리고 그 대가가
`Substitution.lean` 의 `captureSet` 과 `newBinder` 로 눈에 보인다. 다른 방식을 골랐다면
그 코드가 사라지는 대신 다른 코드가 생긴다.

*직접 비교해 볼 수 있다.* 이 저장소는 CSlib 를 의존성으로 두므로, locally nameless
구현이 링크가 아니라 실제 파일로 있다.

```
.lake/packages/cslib/Cslib/Languages/LambdaCalculus/LocallyNameless/Untyped/Basic.lean
```

우리의 `Assert.subst` 와 나란히 열어 놓고 "포획 회피가 어디로 갔는지" 를 찾아보는 것이
좋은 스터디 토론거리다. 답을 미리 말하면, 그쪽에는 포획이 *일어날 수 없다* — 묶인 변수에
이름이 없기 때문이다. 대신 `open`/`close` 연산이 생긴다.

## 곁가지 — 이름 바꾸기가 깨지는 언어
%%%
tag := "ch01-dynamic-binding"
%%%

명제 1.5 는 결합 변수의 이름이 뜻에 영향을 주지 않는다고 말한다. Reynolds 는 바로 뒤에
단서를 붙인다.

> "The principle that renaming preserves meaning is a property of all languages with
> well-behaved binding. (We will see in Section 11.7, however, that this does not include
> all well-known programming languages.)"

§11.7 의 *동적 결합(dynamic binding)* 예고다.

정적 결합(static binding)에서 자유 변수는 _그 변수가 쓰인 자리를 둘러싼 코드_에서 뜻을
얻는다. 그래서 결합 변수의 이름을 바꿔도 어느 결합자에 매이는지가 변하지 않는다.

동적 결합에서는 _호출한 쪽_에서 뜻을 얻는다. 그러면 이름이 실행 시점에 의미를 갖게 되고,
결합 변수를 다른 이름으로 바꾸는 순간 어떤 호출자와 만나는지가 달라진다. 명제 1.5 의
결론이 성립하지 않는다.

이 장에서 예고만 하고 넘어가는 이유는, 그것을 말하려면 프로시저와 호출 규약이 먼저
있어야 하기 때문이다. 1장에는 호출이 없다.

기억해 둘 것은 하나다.
*α-변환이 뜻을 보존한다는 것은 공짜가 아니라 언어 설계의 결과다.*
1장의 언어가 그 성질을 갖는 것은 우리가 그렇게 정의했기 때문이고,
모든 언어가 그런 것은 아니다.

# 연습 1.5 · 1.6 — 결합자가 정수 식으로 내려오면
%%%
tag := "ch01-summation"
%%%

지금까지 결합자는 단언 층에만 있었다. 연습 1.5 는 합 식 `Σv : e₀ to e₁. e₂` 를 더해서
*정수 식이면서 변수를 묶는* 경우를 만든다.

새로운 것은 묶는 범위가 부분식마다 다르다는 점이다. `v` 는 `e₂` 안에서만 묶이고,
`e₀` 와 `e₁` 은 밖이다 — 상계와 하계는 합을 시작하기 전에 정해지므로 바깥의 `v` 를 본다.

```anchor sExpFv (module := Reynolds.Answers.Ch01.Ex.Summation)
/-- `FV(e)` — 합 식이 있는 정수 식의 자유 변수. `sum` 절에서 `e₂` 만 `erase` 한다. -/
def SExp.fv : SExp V → Finset V
  | .num _         => ∅
  | .var v         => {v}
  | .neg e         => e.fv
  | .bin _ e₀ e₁   => e₀.fv ∪ e₁.fv
  | .sum v e₀ e₁ e₂ => e₀.fv ∪ e₁.fv ∪ (e₂.fv.erase v)
```

`e₂` 에서만 `erase` 한다. 같은 비대칭이 치환과 의미 방정식에도 그대로 나타난다.

연습 1.6 은 여기서 한 걸음 더 간다. 부정합 `Σv. e` 의 뜻이 `Σ_{v=0}^{v-1} e` 라서,
`v` 가 아래첨자로 묶이면서 동시에 상계로 자유롭다. 한 이름이 한 식 안에서 두 역할을
하고, §1.4 의 결합 구조에는 그럴 자리가 없다. 결과로 *이름 바꾸기 정리가 깨진다* —
`Ex/Summation.lean` 에서 반례를 증명한다.

바로 앞 절의 동적 결합과 짝이 되는 이야기다. 그쪽은 언어 설계가 α-변환을 깨뜨리는 경우이고,
이쪽은 *구문 설탕*이 깨뜨리는 경우다. `Σv. e` 는 `Σv : 0 to v-1. e` 의 줄임말인데,
줄이면서 결합 구조를 잃어버렸다.

# 직접 해 보기
%%%
tag := "ch01-try"
%%%

저장소를 받고 나서:

```
lake exe cache get        # Mathlib 캐시. 처음 한 번만
lake build
lake exe grade --chapter 1
```

`lake exe grade` 가 아직 안 채운 연습을 표로 보여 준다. `Reynolds/Exercises/Ch01/` 에서
{lit}`sorry` 를 찾아 지우고 채운 뒤 다시 돌리면 된다.

막히면 `docs/solving-guide.md` 를 먼저 봐라. 이 저장소가 반복하는 증명 패턴 넷과
자주 만나는 오류 메시지가 정리되어 있다.

# 연습문제
%%%
tag := "ch01-exercise-list"
%%%

1장에는 채점되는 연습이 28 개 있다. 책 연습문제와 본문 명제가 섞여 있다.

| 갈래 | 개수 | 어디에 |
|---|---|---|
| 본문 명제 1.1 ~ 1.5 | 9 | `FreeVars.lean`, `Substitution.lean` |
| §1.3 건전성과 규칙 | 4 | `Validity.lean` |
| 책 연습 1.1 ~ 1.4 | 9 | `Ex.lean`, `Realizations.lean` |
| 책 연습 1.5 · 1.6 | 6 | `Ex/Summation.lean` |
| 심화 트랙 | 4 | `Depth/` |

위 표의 순서가 곧 푸는 순서다. 본문 명제를 건너뛰면 책 연습에서 쓸 재료가 없다.

심화 트랙은 책을 따라가는 데 필요하지 않다. 건너뛰어도 1장은 완결된다.

# 더 읽을거리
%%%
tag := "ch01-further"
%%%

* *일치 정리와 치환 정리* — 이름을 다루는 모든 언어에서 같은 짝으로 나온다.
  CSlib 의 `Cslib/Languages/LambdaCalculus/` 가 λ-계산법에서 같은 일을 한다.
* *초기 대수 의미론* — Reynolds 가 §1.1 각주에서 "다중 정렬 초기 대수" 라고 부르는 것.
  `Depth/Algebra.lean` 에서 이어 간다. 구문에서 의미로 가는 함수가 *왜 유일한지*에
  대한 답이다.
* *치환은 모나드의 bind 다* — `Depth/TermMonad.lean`. 연습 1.7 이 실은
  모나드 결합법칙이라는 것을 보인다.
* *2장으로* — 1장의 의미 함수가 전함수였던 것은 술어 논리에 비종료가 없었기 때문이다.
  `while` 이 들어오면 의미 방정식이 뜻을 유일하게 정하지 못한다. 그 지점이 도메인 이론이
  태어난 자리다.
