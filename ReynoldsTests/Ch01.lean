/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Answers.Ch01
-- `#guard` 는 **컴파일 시점에** 계산한다. 즉 meta 문맥이므로, 계산에 쓰이는 정의들이
-- meta 로도 보여야 한다. 이것이 `public meta import` 가 필요한 이유다.
public meta import Reynolds.Answers.Ch01
public meta import Mathlib.Data.Finset.Defs
public meta import Reynolds.Answers.Ch01.Substitution

/-!
# 1장 단위 테스트

**계산 가능한 것만** 여기서 테스트한다. 정리는 그 자체가 스펙이므로
테스트가 필요 없다 — `lake build` 가 통과하면 참이다.

`#guard` 는 실패하면 **빌드를 실패시킨다.** 그래서 CI 에 따로 붙일 것이 없다.

주의: `/-- … -/` docstring 은 선언에만 붙는다. `#guard` 같은 커맨드 앞에는 `--` 를 쓴다.
-/

public section

namespace Reynolds.Answers.Ch01

open Reynolds

-- `⟦x + 1⟧` — 모든 변수가 41인 상태에서.
#guard ⟦IntExp.bin .add (.var "x") (.num 1)⟧ₑ (State.const 41) == 42

-- 0으로 나누기 규약 (§1.2, §2.7). Lean 의 `Int` 는 `x / 0 = 0`.
#guard ⟦IntExp.bin .div (.var "x") (.num 0)⟧ₑ (State.const (7 : Int)) == 0

-- 단항 마이너스.
#guard ⟦IntExp.neg (.var "x")⟧ₑ (State.const (5 : Int)) == -5

-- 자유 변수 계산.
#guard (IntExp.bin .add (.var "x") (.bin .mul (.var "y") (.num 2)) : IntExp String).fv
        == ({"x", "y"} : Finset String)

-- 상수에는 자유 변수가 없다.
#guard (IntExp.num 3 : IntExp String).fv == (∅ : Finset String)

-- 일치 정리를 구체적인 상태에 적용해 본다: `x` 밖에서 상태가 달라도 값이 같다.
example :
    ⟦IntExp.var "x"⟧ₑ (fun v => if v == "x" then 7 else 1)
      = ⟦IntExp.var "x"⟧ₑ (fun v => if v == "x" then 7 else 99) := by
  apply coincidence_intExp
  intro w hw
  simp [IntExp.fv] at hw
  simp [hw]

/-! ## 단언 -/

-- Reynolds의 결합 규칙대로 같은 논리 연산자를 왼쪽부터 묶는다.
#guard (⟪ tt ∧ ff ∧ tt ⟫ₐ : Assert String)
        == .bin .and (.bin .and .tru .fls) .tru
#guard (⟪ tt ∨ ff ∨ tt ⟫ₐ : Assert String)
        == .bin .or (.bin .or .tru .fls) .tru
#guard (⟪ tt ⇒ ff ⇒ tt ⟫ₐ : Assert String)
        == .bin .imp (.bin .imp .tru .fls) .tru
#guard (⟪ tt ⇔ ff ⇔ tt ⟫ₐ : Assert String)
        == .bin .iff (.bin .iff .tru .fls) .tru

-- 단언의 뜻은 `Prop`이므로 명제와 증명으로 확인한다. 결정 가능한 구체적 명제라면
-- `#guard decide ...`도 가능하지만, 정수 양화를 포함한 언어 전체의 판정기는 없다.

-- `∀y. y ≤ y` 는 어떤 상태에서도 참이다.
example : ⟦Assert.quant .all "y" (.cmp .le (.var "y") (.var "y"))⟧ₐ (State.const 0) := by
  intro n; simp [Assert.eval, Cmp.denote, IntExp.eval]

-- `x` 의 자유 발생은 양화 밖에 있다: FV(∀y. y ≤ x) = {x}.
#guard (Assert.quant .all "y" (.cmp .le (.var "y") (.var "x")) : Assert String).fv
        == ({"x"} : Finset String)

-- 같은 변수가 자유롭게도, 속박되어도 나타날 수 있다 (Reynolds §1.4 의 논점).
-- ¬(y = 0) ∧ (∀y. y = 0)  에서 앞의 y 는 자유, 뒤의 y 는 속박.
#guard (Assert.bin .and
          (.not (.cmp .eq (.var "y") (.num 0)))
          (.quant .all "y" (.cmp .eq (.var "y") (.num 0))) : Assert String).fv
        == ({"y"} : Finset String)

-- 양화사가 자유 변수를 제거한다.
#guard (Assert.quant .ex "y" (.cmp .eq (.var "y") (.var "y")) : Assert String).fv
        == (∅ : Finset String)

-- 일치 정리(단언 판)를 구체적으로 적용해 본다: FV 밖의 변수 z 를 아무리 바꿔도 뜻이 같다.
example (σ : State String) (k : Int) :
    ⟦Assert.quant .all "y" (.cmp .le (.var "y") (.var "x"))⟧ₐ σ
      ↔ ⟦Assert.quant .all "y" (.cmp .le (.var "y") (.var "x"))⟧ₐ (σ["z" := k]) := by
  refine coincidence_assert _ σ _ ?_
  intro w hw
  simp [Assert.fv, IntExp.fv] at hw
  simp [hw]

/-! ## 치환 — 포획을 실제로 피하는지

Reynolds 가 §1.4 를 여는 반례를 그대로 돌려 본다.
`(∃y. y > x) / x ↦ y+1` 이 `∃y. y > y+1` 이 되면 안 된다.

변수를 `ℕ` 으로 쓰는 이유는 `HasFresh` 가 계산 가능해야 `#guard` 가 돌기 때문이다.
`0 = x`, `1 = y` 로 읽는다. -/

/-- 테스트용 `HasFresh ℕ`. `Nat.find` 로 새 이름을 찾으므로 계산된다. -/
instance : Cslib.HasFresh ℕ := Cslib.HasFresh.ofNatEmbed (Function.Embedding.refl ℕ)

/-- `∃y. y > x` — Reynolds 의 반례에 나오는 단언. `x = 0`, `y = 1`. -/
def existsGt : Assert ℕ := .quant .ex 1 (.cmp .gt (.var 1) (.var 0))

/-- `y + 1` — 밀어 넣을 식. 자유 변수 `y` 가 `∃y` 에 잡히면 안 된다. -/
def yPlus1 : IntExp ℕ := .bin .add (.var 1) (.num 1)

-- 순진하게 밀어 넣었을 때 나올 결과. 이것이 되면 안 된다.
def naiveBad : Assert ℕ := .quant .ex 1 (.cmp .gt (.var 1) yPlus1)

-- 포획이 실제로 회피된다.
#guard (existsGt /[0 := yPlus1] ) != naiveBad

-- 결합 변수가 `y`(=1) 가 아닌 새 이름으로 바뀐다.
#guard (existsGt /[0 := yPlus1] ) matches .quant .ex _ _

-- 자유 변수는 `y`(=1) 하나다. `x` 는 사라지고 `y+1` 의 `y` 가 들어왔다.
#guard (existsGt /[0 := yPlus1] ).fv == ({1} : Finset ℕ)

/-! ## 연습 1.4 — 동시 치환과 필요한 이름 바꾸기 (Reynolds p. 23) -/

-- (a) 합이 들어가지 않는 존재 양화사의 본문에서는 y를 바꿀 필요가 없다.
#guard (Ex.e14a /ₛ Ex.e14aSubst) ==
  ⟪ ∀ xx, ∀ xxx, xx < x + y + z ∧ x + y + z < xxx
    ⇒ (∃ y, xx < y ∧ y < xxx) ⟫ₐ
#guard (Ex.e14a /ₛ Ex.e14aSubst).fv == ({"x", "y", "z"} : Finset String)

-- (b) 두 ∃n 중 n이 새로 들어오는 첫 번째에서만 이름을 바꾼다.
#guard (Ex.e14b /ₛ Ex.e14bSubst) ==
  ⟪ ∀ x, (∃ xx, n = xx × x) ⇒ (∃ n, d = n × x) ⟫ₐ
#guard (Ex.e14b /ₛ Ex.e14bSubst).fv == ({"n", "d"} : Finset String)

-- (c) 속박된 x와 y에는 원래 치환을 적용하지 않고, 자유로운 z에 들어온 x도 다시 치환하지 않는다.
#guard (Ex.e14c /ₛ Ex.e14cSubst) == ⟪ ∀ xx, ∃ y, xx < x ⇒ xx < y ∧ y < x ⟫ₐ
#guard (Ex.e14c /ₛ Ex.e14cSubst).fv == ({"x"} : Finset String)

-- 연습 1.1(p. 22)의 실제 끝점을 대입해 단언 구문을 확인한다.
example : Ex.e11aAnswer.val 0 2 = ⟪ ∃ x, 0 < x ∧ x < 2 ⟫ₐ := rfl
example : Ex.e11bAnswer.val 0 2 =
    ⟪ ∀ x, ∀ y, (0 < x ∧ x < 2) ∧ (0 < y ∧ y < 2) ⇒ x = y ⟫ₐ := rfl
example : Ex.e11cAnswer.val 0 3 =
    ⟪ ∃ x, ∃ y, x ≠ y ∧ (0 < x ∧ x < 3) ∧ (0 < y ∧ y < 3) ⟫ₐ := rfl
example : Ex.e11dAnswer.val 0 3 =
    ⟪ ∀ x, ∀ y, ∀ z, (0 < x ∧ x < 3) ∧ (0 < y ∧ y < 3)
      ∧ (0 < z ∧ z < 3) ⇒ (x = y ∨ x = z ∨ y = z) ⟫ₐ := rfl

-- 구간이 바뀌면 항상 참인 단언으로는 답할 수 없다.
example (σ : State String) : ¬⟦Ex.e11aAnswer.val 0 1⟧ₐ σ := by
  rw [Ex.e11aAnswer.property]
  simp [Ex.intervalCount]
example (σ : State String) : ¬⟦Ex.e11bAnswer.val 0 3⟧ₐ σ := by
  rw [Ex.e11bAnswer.property]
  simp [Ex.intervalCount]
example (σ : State String) : ¬⟦Ex.e11cAnswer.val 0 2⟧ₐ σ := by
  rw [Ex.e11cAnswer.property]
  simp [Ex.intervalCount]
example (σ : State String) : ¬⟦Ex.e11dAnswer.val 0 4⟧ₐ σ := by
  rw [Ex.e11dAnswer.property]
  simp [Ex.intervalCount]

-- 연습 1.2의 금지된 연산과 범위 밖 상수는 구문 검사에서 탈락한다.
#guard Ex.naturalSyntax ⟪ a ÷ b = 0 ⟫ₐ == false
#guard Ex.naturalSyntax ⟪ a rem b = 0 ⟫ₐ == false
#guard Ex.naturalArithmetic (.num (-1)) == false
#guard Ex.naturalArithmetic (.bin .sub (.var "a") (.var "b")) == false
example : Ex.e12aAnswer.val = ⟪ ∃ k, b = a × k ⟫ₐ := rfl
example : Ex.e12bAnswer.val = ⟪ (∃ k, b = a × k) ∧ (∃ k, c = a × k) ⟫ₐ := rfl
example : Ex.e12cAnswer.val =
    ⟪ ((∃ k, b = a × k) ∧ (∃ k, c = a × k))
      ∧ (∀ d, ((∃ k, b = d × k) ∧ (∃ k, c = d × k)) ⇒ d ≤ a) ⟫ₐ := rfl
example : Ex.e12dAnswer.val =
    ⟪ p > 1 ∧ (∀ d, (∃ k, p = d × k) ⇒ (d = 1 ∨ d = p)) ⟫ₐ := rfl

-- (0,0)의 최대 원소 부재는 Nat.gcd의 함수 규약과 구별된다.
example : ¬Ex.evalNat Ex.e12cAnswer.val (fun _ => 0) := by
  rw [Ex.e12cAnswer.property.2]
  exact Ex.no_greatestCommonDivisor_zero_zero 0
#guard Nat.gcd 0 0 == 0
example : Ex.GreatestCommonDivisor 6 12 18 := by
  refine ⟨⟨by decide, by decide⟩, ?_⟩
  intro d hd
  have hdiv := Nat.dvd_gcd hd.1 hd.2
  change d ∣ 6 at hdiv
  exact Nat.le_of_dvd (by decide) hdiv
example : ¬Ex.evalNat Ex.e12dAnswer.val (fun _ => 0) := by
  rw [Ex.e12dAnswer.property.2]
  decide
example : ¬Ex.evalNat Ex.e12dAnswer.val (fun _ => 1) := by
  rw [Ex.e12dAnswer.property.2]
  decide
example : Ex.evalNat Ex.e12dAnswer.val (fun _ => 2) := by
  rw [Ex.e12dAnswer.property.2]
  decide
example : ¬Ex.evalNat Ex.e12dAnswer.val (fun _ => 4) := by
  rw [Ex.e12dAnswer.property.2]
  decide

-- 단언 접두 표기는 양화자의 이름과 각 생성자 머리 토큰을 보존한다.
#guard (⟪ ∀ x, ¬(x = 0) ∨ tt ⟫ₐ).toPrefix ==
  [.quant .all, .var "x", .log .or, .assertNot, .cmp .eq, .var "x", .num 0, .truth true]
#guard (⟪ ff ⟫ₐ).toPrefix == [.truth false]
example (p : Assert String) : p.toPrefix ≠ [] := by
  cases p <;> simp [Assert.toPrefix]
example (p : AssertPrefixPhrase) (x y : String)
    (h : AssertPrefixPhrase.quant .all x p = AssertPrefixPhrase.quant .all y p) : x = y := by
  have hp : (x, p) = (y, p) := prefixConstructors_injective.quant .all h
  exact congrArg Prod.fst hp

-- 합의 경계는 바깥 변수를 읽고 본체만 결합한다. 포획 회피가 없으면 14가 아니라 3이 된다.
open Summation in
#guard (SExp.subst (.sum "i" (.num 1) (.num 2) (.var "a"))
  (Function.update SExp.var "a" (.var "i"))).eval (State.const 7) == 14

open Summation in
#guard (SExp.subst (.sum "i" (.num 1) (.var "i") (.var "i"))
  (Function.update SExp.var "i" (.num 3))).eval (State.const 9) == 6

-- 같은 이름의 중첩 결합에서도 안쪽 상계는 바깥 결합의 값을 읽는다.
open Summation in
#guard (SExp.sum "i" (.num 1) (.num 2)
  (.sum "i" (.num 1) (.var "i") (.var "i"))).eval (State.const 99) == 4

open Summation in
example (e : SExp String) (δ : SSubst String) (σ : State String) :
    (e.subst δ).eval σ = e.eval (fun w => (δ w).eval σ) :=
  substitution_sExp coincidence_sExp e δ _ σ (fun _ _ => rfl)

-- 이름 바꾸기의 신선성은 본체에만 적용한다. 새 이름이 상계에 있어도 그 상계는 그대로다.
open Summation in
example (σ : State String) :
    (SExp.sum "j" (.num 1) (.var "j")
      ((SExp.var "i").subst (Function.update SExp.var "i" (.var "j")))).eval σ =
    (SExp.sum "i" (.num 1) (.var "j") (.var "i")).eval σ := by
  apply renaming_sum
  simp [SExp.fv]

open Summation in
example (e : SExp String) : e.subst SExp.var = e := subst_var_sExp e

open Summation in
example (e : SExp String) (δ : SSubst String) :
    (e.subst δ).fv = e.fv.biUnion (fun w => (δ w).fv) := fv_subst_sExp e δ

-- `Depth/Construction.lean` — 깊이(depth)는 계산 가능하다.
#guard (IntExp.num (1 : ℤ) : IntExp String).depth == 0
#guard (IntExp.neg (IntExp.neg (IntExp.num 1)) : IntExp String).depth == 2

-- 책 식 (1.2): 층은 ∅ 에서 시작한다.
example : IntExp.layer String 0 = (∅ : Set (IntExp String)) := rfl

-- 원자(atom)는 첫 층부터 있고, 그보다 앞선 층(∅)에는 없다.
example : (IntExp.num (1 : ℤ) : IntExp String) ∈ IntExp.layer String 1 := by
  simp [IntExp.layer]
example : (IntExp.num (1 : ℤ) : IntExp String) ∉ IntExp.layer String 0 := by
  simp [IntExp.layer]

-- 깊이 2 식 `- (-1)` 은 자기 깊이 + 1 = 3층에 있다(`mem_layer_succ_depth`).
example : (IntExp.neg (IntExp.neg (IntExp.num (1 : ℤ))) : IntExp String) ∈
    IntExp.layer String 3 :=
  IntExp.mem_layer_succ_depth _

-- 같은 식은 1층에는 없다 — 1층은 원자(`num`/`var`)만 모은다.
example : (IntExp.neg (IntExp.neg (IntExp.num (1 : ℤ))) : IntExp String) ∉
    IntExp.layer String 1 := by
  simp [IntExp.layer]

end Reynolds.Answers.Ch01
