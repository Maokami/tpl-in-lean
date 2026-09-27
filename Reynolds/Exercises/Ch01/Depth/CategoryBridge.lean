/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Exercises.Ch01.Depth.Algebra
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

/-!
# §1.1 선택 심화 — 두 정렬 대수의 범주

Reynolds §1.1의 원시 구문 초기성을 Mathlib의 어휘로 옮긴다.

## 이 파일에서 다루는 것
- 대상: 변수 타입 `V`를 고정한 `LogicAlg`
- 사상(morphism): 열 가지 연산을 보존하는 함수 쌍
- 항등 사상과 합성, 그리고 Mathlib의 `IsInitial`과 `∃!`의 대응

## 핵심 아이디어
`Algebra.lean`에서는 구문에서 출발하는 함수 쌍만 다뤘다. 범주(category)를 만들려면
임의의 두 대수 사이에도 같은 보존 조건을 적어야 한다. 항등 함수 쌍은 이 조건을
만족하고, 보존 함수 두 개를 합성해도 연산이 보존된다. 구문에서 출발하는 사상만
다시 꺼내면 앞 파일의 `LogicAlg.IsHom`이 된다.

## 읽는 순서
`Algebra.lean`의 `LogicAlg.initial` → `Hom` → `syntaxIsInitial` → 마지막 대응 정리.
본문의 귀납법과 접기를 익힌 뒤 선택해서 읽는 파일이다.

## 책과의 차이
**책과의 차이**: Mathlib의 범주 구조를 명시한다. `V : Type u`와 두 반송자를 모두
`Type u`에 고정한다. 서로 다른 우주의 목표까지 허용하던 앞 파일보다 이 범주의
대상 범위는 좁다. 양화사의 변수 이름은 보존하며 α-동치와 치환 법칙은 다루지 않는다.
-/

@[expose] public section

namespace Reynolds.Exercises.Ch01.LogicAlg

open CategoryTheory CategoryTheory.Limits

universe u

variable {V : Type u}

/-- 두 대수 사이의 준동형. 정수 식 성분 `e`와 단언 성분 `a`가 열 연산을 보존한다. -/
structure Hom (L M : LogicAlg.{u, u} V) where
  /-- 정수 식 반송자 사이의 함수. -/
  e : L.E → M.E
  /-- 단언 반송자 사이의 함수. -/
  a : L.A → M.A
  /-- 정수 상수 보존. -/
  num : ∀ n, e (L.num n) = M.num n
  /-- 변수 보존. -/
  var : ∀ x, e (L.var x) = M.var x
  /-- 정수 부호 반전 보존. -/
  eneg : ∀ x, e (L.eneg x) = M.eneg (e x)
  /-- 정수 이항 연산 보존. -/
  ebin : ∀ op x y, e (L.ebin op x y) = M.ebin op (e x) (e y)
  /-- 참 보존. -/
  tru : a L.tru = M.tru
  /-- 거짓 보존. -/
  fls : a L.fls = M.fls
  /-- 비교의 입력과 출력을 각각의 성분으로 옮긴다. -/
  cmp : ∀ c x y, a (L.cmp c x y) = M.cmp c (e x) (e y)
  /-- 논리 부정 보존. -/
  anot : ∀ p, a (L.anot p) = M.anot (a p)
  /-- 논리 이항 연산 보존. -/
  abin : ∀ op p q, a (L.abin op p q) = M.abin op (a p) (a q)
  /-- 양화사 종류와 변수 이름은 고정한다. -/
  quant : ∀ q x p, a (L.quant q x p) = M.quant q x (a p)

/-- 두 함수가 각각 같으면 준동형도 같다. 보존 증명의 선택은 영향을 주지 않는다. -/
@[ext]
theorem Hom.ext {L M : LogicAlg.{u, u} V} {f g : Hom L M}
    (he : f.e = g.e) (ha : f.a = g.a) : f = g := by
  cases f
  cases g
  cases he
  cases ha
  rfl

/-- 항등 준동형은 두 반송자에서 각각 항등 함수다. -/
def Hom.id (L : LogicAlg.{u, u} V) : Hom L L where
  e := fun x ↦ x
  a := fun x ↦ x
  num _ := rfl
  var _ := rfl
  eneg _ := rfl
  ebin _ _ _ := rfl
  tru := rfl
  fls := rfl
  cmp _ _ _ := rfl
  anot _ := rfl
  abin _ _ _ := rfl
  quant _ _ _ := rfl

/-- `f` 다음에 `g`를 적용한다. 보존 등식을 두 번 쓰면 합성도 연산을 보존한다. -/
def Hom.comp {L M N : LogicAlg.{u, u} V} (f : Hom L M) (g : Hom M N) : Hom L N where
  e := g.e ∘ f.e
  a := g.a ∘ f.a
  num n := by simp only [Function.comp_apply, f.num, g.num]
  var x := by simp only [Function.comp_apply, f.var, g.var]
  eneg x := by simp only [Function.comp_apply, f.eneg, g.eneg]
  ebin op x y := by simp only [Function.comp_apply, f.ebin, g.ebin]
  tru := by simp only [Function.comp_apply, f.tru, g.tru]
  fls := by simp only [Function.comp_apply, f.fls, g.fls]
  cmp c x y := by simp only [Function.comp_apply, f.cmp, g.cmp]
  anot p := by simp only [Function.comp_apply, f.anot, g.anot]
  abin op p q := by simp only [Function.comp_apply, f.abin, g.abin]
  quant q x p := by simp only [Function.comp_apply, f.quant, g.quant]

/-- 고정된 우주의 대수와 준동형으로 이루어진 범주. 법칙은 함수 합성의 법칙이다. -/
instance category : Category (LogicAlg.{u, u} V) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp _ := Hom.ext rfl rfl
  comp_id _ := Hom.ext rfl rfl
  assoc _ _ _ := Hom.ext rfl rfl

/-- Reynolds §1.1의 원시 구문을 두 반송자로 가진 대수. 연산은 생성자 자체다. -/
def syntaxAlg (V : Type u) : LogicAlg.{u, u} V where
  E := IntExp V
  A := Assert V
  num := IntExp.num
  var := IntExp.var
  eneg := IntExp.neg
  ebin := IntExp.bin
  tru := Assert.tru
  fls := Assert.fls
  cmp := Assert.cmp
  anot := Assert.not
  abin := Assert.bin
  quant := Assert.quant

/-- 구문에서 출발하는 사상에서 함수 쌍만 꺼낸다. -/
def Hom.pair {L : LogicAlg.{u, u} V} (f : syntaxAlg V ⟶ L) :
    (IntExp V → L.E) × (Assert V → L.A) := (f.e, f.a)

/-- 일반 준동형의 출발점을 구문으로 정하면 앞 파일의 보존 조건이 된다. -/
theorem Hom.isHom {L : LogicAlg.{u, u} V} (f : syntaxAlg V ⟶ L) : L.IsHom f.pair where
  num := f.num
  var := f.var
  eneg := f.eneg
  ebin := f.ebin
  tru := f.tru
  fls := f.fls
  cmp := f.cmp
  anot := f.anot
  abin := f.abin
  quant := f.quant

/-- 앞 파일의 함수 쌍과 보존 증명을 하나의 사상으로 묶는다. -/
def Hom.ofIsHom {L : LogicAlg.{u, u} V}
    (h : (IntExp V → L.E) × (Assert V → L.A)) (hh : L.IsHom h) : syntaxAlg V ⟶ L where
  e := h.1
  a := h.2
  num := hh.num
  var := hh.var
  eneg := hh.eneg
  ebin := hh.ebin
  tru := hh.tru
  fls := hh.fls
  cmp := hh.cmp
  anot := hh.anot
  abin := hh.abin
  quant := hh.quant

/--
`∃!` 초기성을 Mathlib의 초기 대상(initial object)으로 옮긴다.
사상 하나를 고르는 데 `Classical.choose`를 쓴다. 그 뒤 유일성은 주어진 `h`에서 얻는다.
-/
noncomputable def isInitialOfUniqueHom
    (h : ∀ L : LogicAlg.{u, u} V,
      ∃! f : (IntExp V → L.E) × (Assert V → L.A), L.IsHom f) : IsInitial (syntaxAlg V) := by
  classical
  let f (L : LogicAlg.{u, u} V) := Hom.ofIsHom (h L).choose (h L).choose_spec.1
  apply IsInitial.ofUniqueHom f
  intro L g
  have hp : g.pair = (h L).choose := (h L).choose_spec.2 g.pair g.isHom
  exact Hom.ext (congrArg Prod.fst hp) (congrArg Prod.snd hp)

/-- 기존 `LogicAlg.initial`을 적용하면 구문 대수가 이 범주의 초기 대상이 된다. -/
noncomputable def syntaxIsInitial (V : Type u) : IsInitial (syntaxAlg V) :=
  isInitialOfUniqueHom (fun L ↦ L.initial)

/--
Mathlib의 초기성에서 함수 쌍의 존재와 유일성을 되찾는다.
`h.to L`은 존재를, `h.hom_ext`는 유일성을 준다. 초기성은 가설로 주어지므로
앞 파일의 초기성 연습을 풀지 않아도 이 연습을 독립적으로 풀 수 있다.
-/
@[exercise "심화 C1.1" 2]
theorem uniqueHom_of_isInitial (h : IsInitial (syntaxAlg V)) (L : LogicAlg.{u, u} V) :
    ∃! f : (IntExp V → L.E) × (Assert V → L.A), L.IsHom f := by
  -- 힌트: `h.to L`에서 함수 쌍과 보존 증명을 꺼낸다.
  -- 다른 함수 쌍을 `Hom.ofIsHom`으로 묶고 `h.hom_ext`로 비교한다.
  -- 사상의 등식에 `congrArg Hom.pair`를 적용하면 함수 쌍의 등식을 얻는다.
  sorry

/--
두 초기성 표현의 논리적 대응. `IsInitial`은 사상을 고르는 자료를 포함하므로
명제로 비교할 때는 `Nonempty`로 감싼다. 대상은 모두 이 파일의 고정 우주에 있다.
-/
theorem isInitial_iff_uniqueHom :
    Nonempty (IsInitial (syntaxAlg V)) ↔
      ∀ L : LogicAlg.{u, u} V,
        ∃! f : (IntExp V → L.E) × (Assert V → L.A), L.IsHom f := by
  constructor
  · rintro ⟨h⟩ L
    exact uniqueHom_of_isInitial h L
  · intro h
    exact ⟨isInitialOfUniqueHom h⟩

end Reynolds.Exercises.Ch01.LogicAlg
