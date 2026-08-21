/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Exercises.Ch01.FreeVars
public import Reynolds.Meta.Exercise

/-!
# 심화 A · 대수와 초기성

선택 파일이다. 본문만 읽어도 1장은 완결된다.

## 시작점

Reynolds 는 §1.1 에서 추상 구문 조건 셋을 나열한 뒤 이런 각주를 단다.

> *"The reader who is familiar with universal algebra will recognize that these conditions
> insure that abstract phrases form a many-sorted initial algebra whose operators are
> the constructors."*

그리고 §1.4 에서 `FV` 의 방정식을 늘어놓은 뒤 한 줄로 넘어간다.

> *"they are (as the reader may verify) syntax-directed, and thus they
> define the functions FV uniquely."*

구문 지향이면 왜 유일해지는지는 설명하지 않는다. 여기서 그 이유를 따라간다.
따라가다 보면 `eval` 과 `fv` 가 같은 구성의 두 사례라는 것도 같이 나온다.

## 사전 지식
`Ch01/Syntax.lean`, `Ch01/Semantics.lean`.

## 읽는 순서
`Syntax.lean` → `Semantics.lean` → 이 파일 → `Depth/SignatureFunctor.lean`
-/

@[expose] public section

namespace Reynolds.Exercises.Ch01

open Reynolds

universe u v

/-! ## 1. 두 함수를 나란히 놓기

```
IntExp.eval                          IntExp.fv
  | .num n,        _ => n              | .num _       => ∅
  | .var v,        σ => σ v            | .var v       => {v}
  | .neg e,        σ => -(e.eval σ)    | .neg e       => e.fv
  | .bin op e₀ e₁, σ => …              | .bin _ e₀ e₁ => e₀.fv ∪ e₁.fv
```

하나는 정수를, 하나는 변수 집합을 돌려준다. 하는 일도 상관이 없다.
그런데 생김새가 겹친다. 생성자마다 절이 하나씩이고, 재귀 호출은 부분구에만 있고,
각 절은 부분구의 **결과**만 받아 조합한다. 부분구 자체를 다시 뜯어보는 절이 없다.

세 번째 성질을 합성적(compositional)이라고 부른다.
그리고 이 생김새는 타입으로 적을 수 있다. -/

/-! ## 2. 생김새에 타입 주기 -/

/--
`IntExp` 위의 대수(algebra).

반송자(carrier) 타입 하나와, 생성자마다 연산 하나로 이루어진다.
`IntExp` 의 생성자가 넷이므로 연산도 넷이다.

§1 에서 본 생김새를 그대로 옮겨 적은 것이다. 대수라는 이름은 보편 대수(universal algebra)
에서 왔지만, 여기서 필요한 뜻은 "반송자 + 연산 목록" 이상이 아니다.

`IntExp V` 자신도 대수다. 생성자를 그대로 연산으로 쓰면 된다.
그것을 항 대수(term algebra)라고 부른다.
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
`A.fold e` — 구 `e` 의 생성자를 대수 `A` 의 연산으로 하나씩 갈아 끼운다.

`eval` 과 `fv` 는 이 함수에 서로 다른 대수를 먹인 결과다. §6 에서 확인한다.
-/
def IntExpAlg.fold {V : Type u} (A : IntExpAlg.{u, v} V) : IntExp V → A.Carrier
  | .num n        => A.num n
  | .var v        => A.var v
  | .neg e        => A.neg (A.fold e)
  | .bin op e₀ e₁ => A.bin op (A.fold e₀) (A.fold e₁)

/-! ## 4. 준동형 -/

/--
`h` 가 대수 `A` 로의 준동형(homomorphism)이라는 조건. 구조를 보존한다는 뜻이다.

각 절이 Reynolds 의 의미 방정식 한 줄과 그대로 대응한다.

```
h (.neg e) = A.neg (h e)        ⟷        ⟦- e⟧ = -⟦e⟧
```

의미 함수가 합성적이라는 말과 준동형이라는 말은 같은 것을 가리킨다.
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

/-! ## 5. 초기성 -/

/--
어떤 대수 `A` 를 골라도, `IntExp V` 에서 `A` 로 가는 준동형이 정확히 하나 있다.

존재하는 쪽은 `A.fold` 이고 §4 에서 이미 확인했다.
유일성은 구조적 귀납법으로 나온다. 두 준동형이 모든 생성자에서 같은 규칙을 따르면
값이 갈라질 자리가 없다.

Reynolds 의 각주가 말하는 "initial algebra" 가 이것이다.
초기(initial)라는 말은 다른 모든 대수로 가는 사상이 유일하게 존재한다는 뜻이다.

실질적인 결과는 이렇다. 의미론을 준다는 것은 대수를 하나 고르는 일이고,
고르고 나면 의미 함수는 더 고를 여지 없이 정해진다.
-/
@[exercise "심화 A1.1" 2]
theorem IntExp.initial {V : Type u} (A : IntExpAlg.{u, v} V) :
    ∃! h : IntExp V → A.Carrier, IsHom A h := by
  -- 먼저 볼 것: 바로 위 `IntExpAlg.fold_isHom`. 존재 쪽은 그것으로 끝난다.
  -- 힌트: 존재는 `A.fold` 이고 `A.fold_isHom` 이 이미 있다.
  -- 유일성은 `funext` 다음 `induction e with`.
  sorry

/-! ## 6. `eval` 과 `fv` 는 접기다 -/

/--
의미 대수. 반송자가 `State V → Int` 다.

§1.2 에서 "구의 뜻은 값이 아니라 상태의 함수" 라고 한 것이 여기서는 반송자 선택으로 나타난다.
`⟦-⟧ₑ` 의 타입은 이 선택에서 따라온 결과다.
-/
def evalAlg (V : Type u) : IntExpAlg V where
  Carrier := State V → Int
  num n := fun _ => n
  var v := fun σ => σ v
  neg f := fun σ => -(f σ)
  bin op f g := fun σ => op.denote (f σ) (g σ)

/-- 자유 변수 대수. 반송자는 `Finset V` 다. 구문만 보는 함수라 상태가 필요 없다. -/
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

/-! ## 7. 유일성 -/

/--
의미 방정식을 만족하는 함수는 `⟦-⟧ₑ` 뿐이다.
Reynolds 가 *"they define the functions uniquely"* 라고만 쓰고 지나간 주장이다.

증명에 귀납법이 없다. 가설 넷을 모으면 그대로 `IsHom (evalAlg V) f` 가 되고,
나머지는 §5 의 유일성이 처리한다.

2장에서 같은 질문이 다른 답을 받는다. `while` 의 풀기(unwinding) 방정식은 이런 유일성이
없어서, `⟦while true do skip⟧` 자리에는 `Σ → Σ⊥` 의 아무 함수나 들어갈 수 있다.
방정식만으로 부족해지는 그 지점에서 최소성이라는 조건이 등장한다.
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

/-! ## 8. 다중 정렬

Reynolds 의 각주는 "초기 대수"가 아니라 "다중 정렬(many-sorted) 초기 대수"다.
정렬(sort)은 반송자의 종류를 말한다. 술어 논리에는 ⟨intexp⟩ 와 ⟨assert⟩ 가 있으니 둘이다.

일반적인 다중 정렬 시그니처 프레임워크는 만들지 않는다. 구현 비용이 크고,
1장에서 필요한 것은 정렬이 둘일 때 무엇이 달라지는지 정도다.
아래에 두 정렬짜리를 구체적으로 적어 둔다. -/

/-- 두 정렬 대수. 반송자가 `E`(정수 식)와 `A`(단언) 둘이다. -/
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
  /-- 비교. 정렬을 넘나든다: `E × E → A`. -/
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

`cmp` 절만 다른 정렬의 접기(`L.foldE`)를 부른다.
반송자가 여럿이고 연산이 그 사이를 넘나드는 것, 그게 다중 정렬이 뜻하는 전부다.
-/
def LogicAlg.foldA {V : Type u} (L : LogicAlg.{u, v} V) : Assert V → L.A
  | .tru           => L.tru
  | .fls           => L.fls
  | .cmp c e₀ e₁   => L.cmp c (L.foldE e₀) (L.foldE e₁)
  | .not p         => L.anot (L.foldA p)
  | .bin op p q    => L.abin op (L.foldA p) (L.foldA q)
  | .quant q v p   => L.quant q v (L.foldA p)

end Reynolds.Exercises.Ch01
