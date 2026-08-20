/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Exercises.Ch01.FreeVars
public import Reynolds.Meta.Exercise

/-!
# 심화 A · 대수(algebra)와 초기성 — 의미론은 왜 유일한가

> **선택 파일이다.** 책을 따라가는 데 필요하지 않다. 본문만 읽어도 1장은 완결된다.

## 책의 어디서 시작하나

Reynolds §1.1, 추상 구문 조건을 나열한 직후:

> *"The reader who is familiar with universal algebra will recognize that these conditions
> insure that abstract phrases form a many-sorted **initial algebra** whose operators are
> the constructors."*

이 한 문장을 따라간다.

## 무엇이 되돌아오나

§1.4 에서 Reynolds 는 `FV` 의 방정식을 늘어놓고 이렇게 쓴다:

> *"they are (as the reader may verify) syntax-directed, and thus they
> **define the functions FV uniquely**."*

**왜 유일한가?** 그는 답하지 않는다. 이 파일이 그 답이다.
그리고 그 답이 `eval`, `fv`, 그리고 앞으로 쓸 모든 구문 지향 함수가
**하나의 구성**임을 보여 준다.

덤으로 2장으로 가는 다리가 놓인다. 여기서 "의미 방정식은 함수를 유일하게 정한다"를
증명하는데, 2장 §2.2 에서 `while` 의 **풀기 방정식은 유일한 해를 갖지 않는다.**
그 대조가 도메인 이론이 필요한 이유다.

## 사전 지식
없음. `Ch01/Syntax.lean` 과 `Ch01/Semantics.lean` 만 읽었으면 된다.

## 읽는 순서
`Syntax.lean` → `Semantics.lean` → 이 파일 → `Depth/TermMonad.lean`
-/

@[expose] public section

namespace Reynolds.Exercises.Ch01

open Reynolds

universe u v

/-! ## 1. 관찰 — 세 함수가 같은 모양이다

이미 쓴 것들을 나란히 놓아 보자.

```
IntExp.eval           IntExp.fv
  | .num n,        _ => n              | .num _       => ∅
  | .var v,        σ => σ v            | .var v       => {v}
  | .neg e,        σ => -(e.eval σ)    | .neg e       => e.fv
  | .bin op e₀ e₁, σ => …              | .bin _ e₀ e₁ => e₀.fv ∪ e₁.fv
```

돌려주는 타입도 다르고 하는 일도 다르다. 그런데 **모양이 같다**:

* 생성자마다 절이 정확히 하나
* 재귀 호출은 **부분구에만**
* 각 절은 부분구의 결과를 조합할 뿐, 부분구를 다시 들여다보지 않는다

세 번째가 핵심이다. 이 성질에 이름이 있다 — **합성적(compositional)**.
그리고 "합성적인 함수"를 데이터로 만들 수 있다. -/

/-! ## 2. 이름 붙이기 — 대수 -/

/--
`IntExp` 위의 **대수(algebra)**.

반송자(carrier) 타입 하나와, **생성자마다 연산 하나**로 이루어진다.
`IntExp` 의 생성자가 `num`/`var`/`neg`/`bin` 네 개이므로 연산도 네 개다.

"대수"라는 말이 거창해 보이지만 하는 일은 단순하다 — 위 §1 에서 관찰한
"세 함수가 공유하는 모양"을 **타입으로 적어 놓은 것**이 전부다.

`IntExp V` 자신도 대수다. 생성자를 그대로 연산으로 쓰면 된다 (`termAlg`).
그것을 **항 대수(term algebra)** 라고 부른다.
-/
structure IntExpAlg (V : Type u) where
  /-- 반송자 — 이 대수에서 "값"이 사는 타입. -/
  Carrier : Type v
  /-- 상수 생성자에 대응하는 연산. -/
  num : Int → Carrier
  /-- 변수 생성자에 대응하는 연산. -/
  var : V → Carrier
  /-- 단항 마이너스에 대응하는 연산. -/
  neg : Carrier → Carrier
  /-- 이항 연산에 대응하는 연산. -/
  bin : IntOp → Carrier → Carrier → Carrier

/-- **항 대수** — 생성자를 그대로 연산으로 삼은 대수. Reynolds 의 "abstract phrases". -/
def termAlg (V : Type u) : IntExpAlg V where
  Carrier := IntExp V
  num := .num
  var := .var
  neg := .neg
  bin := .bin

/-! ## 3. 접기(fold) — 구를 대수 안으로 밀어 넣기 -/

/--
`A.fold e` — 구 `e` 의 생성자를 대수 `A` 의 연산으로 **하나씩 갈아 끼운다.**

이것이 §1 에서 본 "모양"을 한 번에 구현한 것이다.
`eval`, `fv`, 그리고 앞으로 쓸 모든 구문 지향 함수가 이것의 특수한 경우다.
-/
def IntExpAlg.fold {V : Type u} (A : IntExpAlg.{u, v} V) : IntExp V → A.Carrier
  | .num n        => A.num n
  | .var v        => A.var v
  | .neg e        => A.neg (A.fold e)
  | .bin op e₀ e₁ => A.bin op (A.fold e₀) (A.fold e₁)

/-! ## 4. 준동형(homomorphism) — "의미 방정식을 만족한다"의 다른 이름 -/

/--
`h` 가 대수 `A` 로의 **준동형(homomorphism)** 이다 — 구조를 보존하는 함수.

**이 정의의 각 절을 소리 내어 읽어 보라.** 그것이 곧 Reynolds 의 "의미 방정식"이다:

```
h (.neg e) = A.neg (h e)        ⟷        ⟦- e⟧ = -⟦e⟧
```

즉 **"의미 함수가 합성적이다" = "의미 함수가 준동형이다"**. 같은 말이다.
심화 트랙 전체에서 가장 중요한 대응이다.
-/
structure IsHom {V : Type u} (A : IntExpAlg.{u, v} V) (h : IntExp V → A.Carrier) : Prop where
  /-- 상수 절. -/
  num : ∀ n, h (.num n) = A.num n
  /-- 변수 절. -/
  var : ∀ v, h (.var v) = A.var v
  /-- 단항 마이너스 절. -/
  neg : ∀ e, h (.neg e) = A.neg (h e)
  /-- 이항 연산 절. -/
  bin : ∀ op e₀ e₁, h (.bin op e₀ e₁) = A.bin op (h e₀) (h e₁)

/-- 접기는 준동형이다 — 정의를 그대로 읽으면 된다. -/
theorem IntExpAlg.fold_isHom {V : Type u} (A : IntExpAlg.{u, v} V) : IsHom A A.fold where
  num _ := rfl
  var _ := rfl
  neg _ := rfl
  bin _ _ _ := rfl

/-! ## 5. ★ 초기성 (initiality) -/

/--
**초기 대수 정리.** 어떤 대수 `A` 를 골라도, `IntExp V` 에서 `A` 로 가는 준동형이
**정확히 하나** 있다.

* **존재** — `A.fold` 다. 4절에서 확인했다.
* **유일성** — 구조적 귀납법. 두 준동형은 모든 생성자에서 같은 규칙을 따르므로
  모든 구에서 값이 같을 수밖에 없다.

이것이 Reynolds 의 각주 *"abstract phrases form a many-sorted initial algebra"* 의 내용이다.
"초기(initial)"는 **모든 대수로 가는 유일한 사상을 갖는다**는 뜻이다.

**왜 이게 중요한가**: 의미론을 준다는 것은 곧 **대수를 하나 고르는 일**이다.
그러면 의미 함수는 자동으로, 그리고 **유일하게** 정해진다. 고를 자유가 없다.
-/
@[exercise "심화 A1.1" 2]
theorem IntExp.initial {V : Type u} (A : IntExpAlg.{u, v} V) :
    ∃! h : IntExp V → A.Carrier, IsHom A h := by
  -- 힌트: 존재는 `A.fold` 다 (`A.fold_isHom`).
  -- 유일성은 `funext` 다음 `induction e with` — 두 준동형이 생성자마다 같은 규칙을
  -- 따르므로 모든 구에서 값이 같을 수밖에 없다.
  sorry

/-! ## 6. 집세 (1) — `eval` 과 `fv` 는 접기다 -/

/--
**의미 대수.** 반송자가 `State V → Int` 라는 점이 중요하다.

§1.2 의 논점 — *"구의 뜻은 값이 아니라 상태의 함수다"* — 가 여기서
**"어떤 반송자를 골랐는가"** 로 다시 나타난다. 의미론을 준다는 것은 대수를 고르는 일이고,
`⟦-⟧` 의 모양은 그 선택에서 따라온다.
-/
def evalAlg (V : Type u) : IntExpAlg V where
  Carrier := State V → Int
  num n := fun _ => n
  var v := fun σ => σ v
  neg f := fun σ => -(f σ)
  bin op f g := fun σ => op.denote (f σ) (g σ)

/-- **자유 변수 대수.** 반송자는 그냥 `Finset V`. 상태가 필요 없다 — 구문적 함수이므로. -/
def fvAlg (V : Type u) [DecidableEq V] : IntExpAlg V where
  Carrier := Finset V
  num _ := ∅
  var v := {v}
  neg s := s
  bin _ s t := s ∪ t

/-- `⟦-⟧ₑ` 는 의미 대수로의 접기다. -/
@[exercise "심화 A1.2" 2]
theorem eval_eq_fold {V : Type u} (e : IntExp V) : ⟦e⟧ₑ = (evalAlg V).fold e := by
  -- 힌트: `e` 에 대한 구조적 귀납법. 각 케이스는 양쪽 정의를 펼치면 같아진다.
  sorry

/-- `FV` 는 자유 변수 대수로의 접기다. -/
theorem fv_eq_fold {V : Type u} [DecidableEq V] (e : IntExp V) : e.fv = (fvAlg V).fold e := by
  induction e with
  | num n => rfl
  | var v => rfl
  | neg e ih => simp [IntExp.fv, IntExpAlg.fold, fvAlg, ih]
  | bin op e₀ e₁ ih₀ ih₁ => simp [IntExp.fv, IntExpAlg.fold, fvAlg, ih₀, ih₁]

/-! ## 7. ★ 집세 (2) — Reynolds 의 "uniquely" 를 증명한다 -/

/--
**의미 방정식을 만족하는 함수는 `⟦-⟧ₑ` 하나뿐이다.**

Reynolds 가 *"they define the functions uniquely"* 라고만 쓰고 지나간 그 주장이다.

증명이 짧다는 점에 주목할 것. **귀납법을 다시 쓰지 않는다.**
"이 가설들 = `IsHom (evalAlg V) f`" 임을 확인하고 초기성의 유일성을 부르면 끝이다.
추상이 집세를 내는 순간이다.

**2장을 여는 대조**: `while` 의 풀기 방정식은 이런 유일성을 **갖지 않는다.**
`⟦while true do skip⟧` 는 `Σ → Σ⊥` 의 **모든** 함수가 해가 된다.
그래서 2장에서는 "방정식을 만족한다"만으로 부족하고 **최소성**이라는 조건이 더 필요해진다.
-/
theorem eval_unique {V : Type u} (f : IntExp V → State V → Int)
    (hnum : ∀ n σ, f (.num n) σ = n)
    (hvar : ∀ v σ, f (.var v) σ = σ v)
    (hneg : ∀ e σ, f (.neg e) σ = -(f e σ))
    (hbin : ∀ op e₀ e₁ σ, f (.bin op e₀ e₁) σ = op.denote (f e₀ σ) (f e₁ σ)) :
    f = fun e => ⟦e⟧ₑ := by
  -- 가설을 모으면 그대로 준동형 조건이다.
  have hf : IsHom (evalAlg V) f :=
    { num := fun n => funext fun σ => hnum n σ
      var := fun v => funext fun σ => hvar v σ
      neg := fun e => funext fun σ => hneg e σ
      bin := fun op e₀ e₁ => funext fun σ => hbin op e₀ e₁ σ }
  have he : IsHom (evalAlg V) (fun e => ⟦e⟧ₑ) := by
    constructor <;> intros <;> simp [IntExp.eval, evalAlg]
  obtain ⟨_, _, huniq⟩ := IntExp.initial (evalAlg V)
  rw [huniq f hf, huniq _ he]

/-! ## 8. "다중 정렬(many-sorted)" 이란 무슨 뜻인가

Reynolds 는 그냥 "초기 대수"가 아니라 **"다중 정렬(many-sorted) 초기 대수"** 라고 쓴다.
정렬(sort)이란 반송자의 종류다. 술어 논리에는 ⟨intexp⟩ 와 ⟨assert⟩ 둘이 있으므로
반송자도 둘이어야 한다.

일반적인 다중 정렬 시그니처 프레임워크를 만들지는 않는다 — 비용에 비해 얻는 것이 적다.
대신 **두 정렬짜리를 구체적으로 한 번 더** 적어 보인다. 패턴은 그것으로 충분히 전달된다. -/

/-- 두 정렬 대수 — 반송자가 `E`(정수 식)와 `A`(단언) 둘이다. -/
structure LogicAlg (V : Type u) where
  /-- ⟨intexp⟩ 정렬의 반송자. -/
  E : Type v
  /-- ⟨assert⟩ 정렬의 반송자. -/
  A : Type v
  /-- `IntExp` 쪽 연산 넷. -/
  num : Int → E
  /-- 변수. -/
  var : V → E
  /-- 단항 마이너스. -/
  eneg : E → E
  /-- 이항 정수 연산. -/
  ebin : IntOp → E → E → E
  /-- 참. -/
  tru : A
  /-- 거짓. -/
  fls : A
  /-- 비교 — **정렬을 넘나드는 연산**이다: `E × E → A`. -/
  cmp : Cmp → E → E → A
  /-- 부정. -/
  anot : A → A
  /-- 이항 논리 연산. -/
  abin : LogOp → A → A → A
  /-- 양화 — 결합 구성자. -/
  quant : Quant → V → A → A

/-- ⟨intexp⟩ 정렬의 접기. -/
def LogicAlg.foldE {V : Type u} (L : LogicAlg.{u, v} V) : IntExp V → L.E
  | .num n        => L.num n
  | .var v        => L.var v
  | .neg e        => L.eneg (L.foldE e)
  | .bin op e₀ e₁ => L.ebin op (L.foldE e₀) (L.foldE e₁)

/--
⟨assert⟩ 정렬의 접기.

`cmp` 절에서 **다른 정렬의 접기를 부른다** (`L.foldE`). 이것이 "다중 정렬"의 실체다 —
반송자가 여럿이고, 연산이 정렬을 넘나든다.
-/
def LogicAlg.foldA {V : Type u} (L : LogicAlg.{u, v} V) : Assert V → L.A
  | .tru           => L.tru
  | .fls           => L.fls
  | .cmp c e₀ e₁   => L.cmp c (L.foldE e₀) (L.foldE e₁)
  | .not p         => L.anot (L.foldA p)
  | .bin op p q    => L.abin op (L.foldA p) (L.foldA q)
  | .quant q v p   => L.quant q v (L.foldA p)

end Reynolds.Exercises.Ch01
