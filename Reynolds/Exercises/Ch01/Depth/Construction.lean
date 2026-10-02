/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Exercises.Ch01.Syntax
public import Reynolds.Meta.Exercise
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.SetNotation
public import Mathlib.Order.Monotone.Basic

/-!
# 심화 A · 깊이별 구성과 "닫힌 부분집합 = 전체"

선택 파일이다. 본문만 읽어도 1장은 완결된다.

## 시작점

Reynolds §1.1 p.4–5는 추상 구문의 반송자가 만족해야 할 세 조건을 늘어놓은 뒤, 셋째
조건("유한 번의 생성자 적용으로 만들어진다")을 집합으로 직접 구성하는 방법을 식 (1.2)로
적는다.

```
⟨intexp⟩⁽⁰⁾   = ∅
⟨intexp⟩⁽ʲ⁺¹⁾ = {c₀(), c₁(), …} ∪ {c_var(x) | x ∈ ⟨var⟩}
                 ∪ {c₋(e) | e ∈ ⟨intexp⟩⁽ʲ⁾} ∪ …
⟨intexp⟩      = ⋃ⱼ ⟨intexp⟩⁽ʲ⁾
```

Lean의 `inductive`는 이 구성을 전부 생략하고 결과("유한 생성")만 공짜로 준다. 이 파일은
그 생략된 구성을 `IntExp V` 위의 부분집합들로 다시 만들어, 책이 "표준적인 구성 방법"이라
부르는 것을 직접 눈으로 본다.

## 책과의 차이

책은 이 구성을 ⟨intexp⟩와 ⟨assert⟩ 둘 다에 대해 말한다. 여기서는 정수 식만 다룬다 —
`Assert`는 반송자가 둘(정수 식, 단언)이고 `cmp`가 정렬을 건너가므로, 층을 두 반송자에
동시에 매기는 구성이 한 단계 더 필요하다. 패턴은 `IntExp` 하나로도 전달된다.

## 2장으로

아래 `IntExp.layer`는 공집합에서 시작해 생성자 한 단계를 반복 적용한 합집합이다. 이것은
§2.4 끝에서 Reynolds가 명령 의미의 최소 고정점을 만드는 것과 같은 모양이다 — 둘 다
"⊥(또는 ∅)에서 출발해 한 단계 연산자를 반복한 사슬의 합(또는 상한)"이라는 구성을 쓴다.
`Depth/FixpointAlgebraically.lean`(2장, 계획)에서 이 둘을 나란히 놓는다.

## 사전 지식
`Ch01/Syntax.lean`.

## 읽는 순서
`Syntax.lean` → `Depth/Algebra.lean` → 이 파일
-/

@[expose] public section

namespace Reynolds.Exercises.Ch01

universe u

/-! ## 1. 책 식 (1.2) — 깊이별 층

`layer j`는 생성자를 `j`번 이하로 적용해 만들 수 있는 구만 모은다. `num`과 `var`는
자식이 없는 생성자라서 첫 단계부터 나타나고, 그 뒤로는 매 층에서 그대로 다시 나온다.
`neg`와 `bin`은 한 단계 아래 층의 원소를 재료로 쓴다. -/

/-- 책의 `⟨intexp⟩⁽ʲ⁾`. `IntExp V`의 부분집합으로, 생성자를 `j`번 이하로 적용해 만들 수
있는 구만 모은다. 식 (1.2)를 그대로 옮긴 것이다. -/
def IntExp.layer (V : Type u) : ℕ → Set (IntExp V)
  | 0     => ∅
  | j + 1 =>
      Set.range IntExp.num ∪ Set.range IntExp.var
        ∪ IntExp.neg '' IntExp.layer V j
        ∪ ⋃ op : IntOp, Set.image2 (IntExp.bin op) (IntExp.layer V j) (IntExp.layer V j)

/-- 층은 증가한다. `j`층의 원소는 `j+1`층에도 있다. `num`·`var` 쪽은 매 층에서 같은
집합으로 다시 나오는 것으로 확인되고, `neg`·`bin` 쪽은 이 단조성 자체를 증명 재료로
쓴다 — 자식이 한 단계 아래 층에 있으면 그 자식을 한 단계 올려도 같은 층에 머문다.
아래 `mem_layer_succ_depth`(심화 A1.7)가 이 보조정리로 지어졌으므로, 완성된 채로 둔다
(독립성에 대해서는 §3을 보라). -/
theorem IntExp.layer_mono {V : Type u} : Monotone (IntExp.layer V) := by
  apply monotone_nat_of_le_succ
  intro j
  induction j with
  | zero => simp [IntExp.layer]
  | succ j ih =>
      intro e he
      rcases he with ((h | h) | h) | h
      · exact Or.inl (Or.inl (Or.inl h))
      · exact Or.inl (Or.inl (Or.inr h))
      · obtain ⟨e', he', rfl⟩ := h
        exact Or.inl (Or.inr ⟨e', ih he', rfl⟩)
      · obtain ⟨op, h⟩ := Set.mem_iUnion.mp h
        obtain ⟨e₀, he₀, e₁, he₁, rfl⟩ := Set.mem_image2.mp h
        exact Or.inr (Set.mem_iUnion.mpr ⟨op, Set.mem_image2_of_mem (ih he₀) (ih he₁)⟩)

/-- 구의 깊이(depth) — 생성자를 몇 겹 감쌌는지를 센다. 몇 층째부터 그 구가 나타나는지를
아래 `mem_layer_succ_depth`에서 정확히 준다. -/
def IntExp.depth {V : Type u} : IntExp V → ℕ
  | .num _ | .var _ => 0
  | .neg e           => e.depth + 1
  | .bin _ e₀ e₁     => max e₀.depth e₁.depth + 1

/-- 모든 구는 자기 깊이보다 한 층 위에 있다. `layer_mono`로 두 자식을 같은 층에 맞춘 뒤
합치는 것이 유일하게 손이 가는 부분이다(`bin` 케이스). -/
@[exercise "심화 A1.7" 2]
theorem IntExp.mem_layer_succ_depth {V : Type u} (e : IntExp V) :
    e ∈ IntExp.layer V (e.depth + 1) := by
  -- 먼저 볼 것: 완성된 `IntExp.layer_mono`. 두 자식을 같은 층으로 맞추는 데 쓴다.
  -- 힌트 1: `induction e with …`. `num`·`var`는 정의를 펼치면 끝난다.
  -- 힌트 2: `neg` 케이스는 귀납 가설의 층이 그대로 맞는다 — 끌어올릴 필요가 없다.
  -- 힌트 3: `bin` 케이스에서 두 자식을 `max e₀.depth e₁.depth + 1` 층으로 `layer_mono`로
  --         끌어올린 뒤 `Set.mem_image2_of_mem`과 `Set.mem_iUnion`으로 합친다.
  sorry

theorem IntExp.iUnion_layer_eq_univ {V : Type u} : ⋃ j, IntExp.layer V j = Set.univ := by
  ext e
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact ⟨e.depth + 1, e.mem_layer_succ_depth⟩

/-! ## 2. "생성자에 닫힌 부분집합은 전체다" (no junk) -/

/-- 책 p.4의 셋째 조건("유한 생성")을 집합의 말로 다시 적은 것이다. 생성자를 적용해도
빠져나가지 못하는 부분집합은 애초에 전체여야 한다는 뜻이다. `IntExp.rec`가 그대로
증명을 준다 — 그 "당연함" 자체가 요점이다. Reynolds는 이 조건을 구문 반송자에
*부과해야 하는* 조건으로 쓰는데, `inductive`를 쓰면 이 조건이 구성에서 공짜로 따라
나온다. `layer`를 전혀 쓰지 않으므로 `심화 A1.7`과 독립적으로 풀 수 있다. -/
@[exercise "심화 A1.6" 1]
theorem IntExp.eq_univ_of_closed {V : Type u} (S : Set (IntExp V))
    (hnum : ∀ n, IntExp.num n ∈ S) (hvar : ∀ v, IntExp.var v ∈ S)
    (hneg : ∀ e ∈ S, IntExp.neg e ∈ S)
    (hbin : ∀ op, ∀ e₀ ∈ S, ∀ e₁ ∈ S, IntExp.bin op e₀ e₁ ∈ S) :
    S = Set.univ := by
  -- 힌트: `ext e`로 원소 하나의 소속으로 바꾼 뒤 `e`에 대한 구조적 귀납법.
  -- 각 케이스는 가설 `hnum … hbin` 중 하나를 그대로 적용하면 끝난다.
  sorry

/-! ## 3. 독립성

`심화 A1.6`(`eq_univ_of_closed`)과 `심화 A1.7`(`mem_layer_succ_depth`)은 서로 쓰지
않는다. `eq_univ_of_closed`는 `layer`를 전혀 참조하지 않는 직접 귀납이고,
`mem_layer_succ_depth`는 완성된 `layer_mono`만 쓴다 — `LogicAlg.initial`(심화 A1.3)을
완성된 `logicEval_unique`가 쓰는 것(`Depth/LogicFold.lean`)과 같은 모양이다. -/

end Reynolds.Exercises.Ch01
