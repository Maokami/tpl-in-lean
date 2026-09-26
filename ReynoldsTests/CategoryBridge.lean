/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Answers.Ch01.Depth.CategoryBridge
public meta import Reynolds.Answers.Ch01.Depth.CategoryBridge

/-! # 두 정렬 범주: 합성 순서, 초기성 API와 우주 다형성 검사 -/

@[expose] public section

namespace ReynoldsTests.CategoryBridge

open Reynolds.Answers.Ch01 CategoryTheory CategoryTheory.Limits

universe u

/-- 구문에서 생성되지 않는 원소도 갖는 대수. 모든 연산은 0을 돌려준다. -/
abbrev zeroAlg : LogicAlg String where
  E := Nat
  A := Nat
  num _ := 0
  var _ := 0
  eneg _ := 0
  ebin _ _ _ := 0
  tru := 0
  fls := 0
  cmp _ _ _ := 0
  anot _ := 0
  abin _ _ _ := 0
  quant _ _ _ := 0

/-- 0을 보존하는 두 함수는 `zeroAlg`의 준동형을 이룬다. -/
def zeroHom (e a : Nat → Nat) (he : e 0 = 0) (ha : a 0 = 0) :
    zeroAlg ⟶ zeroAlg where
  e := e
  a := a
  num _ := he
  var _ := he
  eneg _ := he
  ebin _ _ _ := he
  tru := ha
  fls := ha
  cmp _ _ _ := ha
  anot _ := ha
  abin _ _ _ := ha
  quant _ _ _ := ha

/-- 두 성분에서 서로 다른 비항등 함수를 사용한다. -/
def first : zeroAlg ⟶ zeroAlg := zeroHom (fun n ↦ 2 * n) (fun n ↦ n * n) rfl rfl

/-- 합성 순서를 바꾸면 양쪽 성분의 계산 결과가 모두 달라진다. -/
def second : zeroAlg ⟶ zeroAlg := zeroHom (fun n ↦ n * n) (fun n ↦ 3 * n) rfl rfl

#guard (first ≫ second).e 2 == 16
#guard (second ≫ first).e 2 == 8
#guard (first ≫ second).a 2 == 12
#guard (second ≫ first).a 2 == 36
#guard (𝟙 zeroAlg : zeroAlg ⟶ zeroAlg).e 7 == 7
#guard (𝟙 zeroAlg : zeroAlg ⟶ zeroAlg).a 11 == 11

-- 구문에서 오는 사상은 비교와 이름을 가진 양화사까지 처리한다.
#guard (LogicAlg.Hom.ofIsHom (zeroAlg.foldE, zeroAlg.foldA) zeroAlg.fold_isHom).a
  (.quant .all "x" (.cmp .eq (.var "x") (.num 3))) == 0

-- 특정 작은 타입뿐 아니라 임의의 Type u에서도 인스턴스와 대응이 작동한다.
example {V : Type u} (L M N P : LogicAlg.{u, u} V)
    (f : L ⟶ M) (g : M ⟶ N) (h : N ⟶ P) : (f ≫ g) ≫ h = f ≫ (g ≫ h) :=
  Category.assoc f g h

example {V : Type u} (L : LogicAlg.{u, u} V) :
    (LogicAlg.syntaxIsInitial V).to L =
      LogicAlg.Hom.ofIsHom (L.foldE, L.foldA) L.fold_isHom :=
  (LogicAlg.syntaxIsInitial V).hom_ext _ _

example {V : Type u} :
    Nonempty (IsInitial (LogicAlg.syntaxAlg V)) ↔
      ∀ L : LogicAlg.{u, u} V,
        ∃! f : (IntExp V → L.E) × (Assert V → L.A), L.IsHom f :=
  LogicAlg.isInitial_iff_uniqueHom

end ReynoldsTests.CategoryBridge
