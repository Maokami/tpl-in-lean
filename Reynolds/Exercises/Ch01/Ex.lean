/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Answers.Ch01.Notation
public import Reynolds.Exercises.Ch01.Substitution
-- `#guard` 는 컴파일 시점에 계산하므로 meta 문맥이다 (AGENTS.md §10).
public meta import Reynolds.Answers.Ch01.Notation
public meta import Reynolds.Exercises.Ch01.Substitution
public meta import Mathlib.Data.Finset.Defs

/-!
# 1장 연습문제

Reynolds §1 의 연습문제 1.1~1.7 에 대응한다.

## 종이 문제를 어떻게 채점 가능하게 만드나

1.1 과 1.2 는 "다음을 술어 논리로 표현하라" 다. 종이에서는 답이 맞았는지 사람이 읽고 판단한다.
여기서는 두 단계로 나눈다.

1. 객체 언어로 단언을 쓴다 (`⟪ … ⟫ₐ`)
2. **그 단언의 뜻이 의도한 메타 수준 명제와 같음을 증명한다**

2번이 있으면 답이 맞았는지가 기계적으로 판정된다.
잘못 쓴 식은 의미 정리가 안 붙는다.

## 읽는 순서
1장 본문을 다 읽은 뒤. `Notation.lean` 의 표기를 쓴다.
-/

-- 이 파일은 `#guard` 로 계산을 확인한다.
set_option linter.hashCommand false

@[expose] public section

namespace Reynolds.Exercises.Ch01.Ex

open Reynolds Reynolds.Exercises.Ch01

/-! ## 연습 1.1 — 개수 세기

정수의 개수를 술어 논리로 말하는 문제다. `=` 와 `≠` 만으로 "적어도 n 개", "많아야 n 개" 를
표현하는 것이 요령이다. -/

/-- 1.1(a) 0 보다 크고 2 보다 작은 정수가 **적어도 하나** 있다. -/
def e11a : Assert String := ⟪ ∃ x, 0 < x ∧ x < 2 ⟫ₐ

@[exercise "Ex 1.1a" 1]
theorem e11a_correct (σ : State String) :
    (⟦e11a⟧ₐ σ ↔ ∃ n : Int, 0 < n ∧ n < 2) := by
  -- 힌트: `simp [e11a, Assert.eval, LogOp.denote, Cmp.denote, IntExp.eval]`
  sorry

/-- 1.1(b) 0 보다 크고 2 보다 작은 정수가 **많아야 하나** 있다. -/
def e11b : Assert String := ⟪ ∀ x, ∀ y, (0 < x ∧ x < 2) ∧ (0 < y ∧ y < 2) ⇒ x = y ⟫ₐ

@[exercise "Ex 1.1b" 2]
theorem e11b_correct (σ : State String) :
    (⟦e11b⟧ₐ σ ↔ ∀ m n : Int, (0 < m ∧ m < 2) ∧ (0 < n ∧ n < 2) → m = n) := by
  sorry

/-- 1.1(c) 0 보다 크고 3 보다 작은 **서로 다른** 정수가 적어도 둘 있다. -/
def e11c : Assert String :=
  ⟪ ∃ x, ∃ y, (x ≠ y) ∧ (0 < x ∧ x < 3) ∧ (0 < y ∧ y < 3) ⟫ₐ

@[exercise "Ex 1.1c" 2]
theorem e11c_correct (σ : State String) :
    (⟦e11c⟧ₐ σ ↔ ∃ m n : Int, m ≠ n ∧ (0 < m ∧ m < 3) ∧ (0 < n ∧ n < 3)) := by
  sorry

/--
1.1(d) 0 보다 크고 3 보다 작은 서로 다른 정수가 **많아야 둘** 있다.

셋을 잡으면 그중 둘은 같아야 한다는 식으로 쓴다.
-/
def e11d : Assert String :=
  ⟪ ∀ x, ∀ y, ∀ z,
      (0 < x ∧ x < 3) ∧ (0 < y ∧ y < 3) ∧ (0 < z ∧ z < 3)
        ⇒ (x = y ∨ x = z ∨ y = z) ⟫ₐ

@[exercise "Ex 1.1d" 2]
theorem e11d_correct (σ : State String) :
    (⟦e11d⟧ₐ σ ↔ ∀ l m n : Int,
      (0 < l ∧ l < 3) ∧ (0 < m ∧ m < 3) ∧ (0 < n ∧ n < 3) →
        (l = m ∨ l = n ∨ m = n)) := by
  sorry

/-! ## 연습 1.2 — 나눗셈 없이 정수론 말하기

Reynolds 의 단서: 변수와 식이 자연수만 훑는다고 가정하고, `÷` 와 `rem` 을 쓰지 말 것.

`÷` 없이 "나눈다" 를 말하는 방법이 이 문제의 전부다. `a` 가 `b` 를 나눈다는 것은
`b = a × k` 인 `k` 가 있다는 뜻이고, 그 `k` 를 양화사로 잡으면 된다.

**책과의 차이**: 우리 의미론에서 변수는 ℤ 를 훑는다. (a)(b) 는 ℤ 에서도 그대로 맞고,
Mathlib 의 `∣`(나눗셈 관계)가 정확히 같은 정의라서 의미 정리가 거의 `rfl` 이다.
(c)(d) 는 음수 때문에 뜻이 달라질 수 있어서, 양수 조건을 식 안에 명시했다.
-/

/-- 1.2(a) `a` 가 `b` 를 나눈다. -/
def e12a : Assert String := ⟪ ∃ k, b = a × k ⟫ₐ

@[exercise "Ex 1.2a" 1]
theorem e12a_correct (σ : State String) :
    (⟦e12a⟧ₐ σ ↔ σ "a" ∣ σ "b") := by
  -- 힌트: `dvd_def` 가 `a ∣ b ↔ ∃ c, b = a * c` 다. `IntOp.denote` 도 펼쳐야 한다.
  sorry

/-- 1.2(b) `a` 가 `b` 와 `c` 의 공약수다. -/
def e12b : Assert String := ⟪ (∃ k, b = a × k) ∧ (∃ k, c = a × k) ⟫ₐ

@[exercise "Ex 1.2b" 1]
theorem e12b_correct (σ : State String) :
    (⟦e12b⟧ₐ σ ↔ (σ "a" ∣ σ "b" ∧ σ "a" ∣ σ "c")) := by
  sorry

/--
1.2(c) `a` 가 `b` 와 `c` 의 최대공약수다.

"공약수이면서, 모든 공약수보다 크거나 같다" 로 쓴다.
-/
def e12c : Assert String :=
  ⟪ ((∃ k, b = a × k) ∧ (∃ k, c = a × k))
      ∧ (∀ d, ((∃ k, b = d × k) ∧ (∃ k, c = d × k)) ⇒ d ≤ a) ⟫ₐ

@[exercise "Ex 1.2c" 2]
theorem e12c_correct (σ : State String) :
    (⟦e12c⟧ₐ σ ↔
      ((σ "a" ∣ σ "b" ∧ σ "a" ∣ σ "c")
        ∧ ∀ d : Int, (d ∣ σ "b" ∧ d ∣ σ "c") → d ≤ σ "a")) := by
  sorry

/--
1.2(d) `p` 가 소수다.

`1` 보다 크고, 양의 약수가 `1` 과 자기 자신뿐이라는 뜻이다.
양수 조건을 명시한 것은 ℤ 에서 `-1` 과 `-p` 도 약수이기 때문이다.
-/
def e12d : Assert String :=
  ⟪ p > 1 ∧ (∀ d, (d > 0 ∧ (∃ k, p = d × k)) ⇒ (d = 1 ∨ d = p)) ⟫ₐ

@[exercise "Ex 1.2d" 2]
theorem e12d_correct (σ : State String) :
    (⟦e12d⟧ₐ σ ↔
      (σ "p" > 1 ∧ ∀ d : Int, (d > 0 ∧ d ∣ σ "p") → (d = 1 ∨ d = σ "p"))) := by
  sorry

/-! ## 연습 1.4 — 치환 계산하기

Reynolds 연습 1.4(a)–(c) (p. 23). 각 문항의 동시 치환 결과를 구문으로 제시한다.
`newBinder`는 포획 위험이 없으면 원래 결합 변수를 유지한다.

**책과의 차이**: 책은 신선한 이름의 철자를 정하지 않는다. 여기서는 `hasFreshString`이
정한 `x`, `xx`, `xxx`, … 순서로 고른 결과를 검사한다. 다른 안전한 이름도 책의 답이지만,
이 실습의 구문 등식에는 그 순서가 필요하다.

`{q : Assert String // 원래식 /ₛ 치환 = q}`는 결과 `q`와 계산이 맞다는 증명을 함께 담는다.
학생은 `⟨⟪ … ⟫ₐ, 증명⟩`에서 생략된 단언을 직접 쓴다.
아래 이름 선택 보조정리는 저장소의 계산 지원 자료이며 책의 추가 연습이 아니다. -/

/-- 연습 1.4 (p. 23)의 계산 지원: 후보 번호와 그 이전 후보의 부적합성을 주면 이름을 확정한다. -/
theorem freshString_eq (s : Finset String) (n : Nat) (hn : natToString n ∉ s)
    (hprev : ∀ m < n, natToString m ∈ s) : Cslib.fresh s = natToString n := by
  change natToString (Nat.find _) = natToString n
  congr 1
  exact (Nat.find_eq_iff _).mpr ⟨hn, fun m hm hmem ↦ hmem (hprev m hm)⟩

/-- 연습 1.4 (p. 23)의 계산 지원: 첫 후보 `x`가 안전하면 선택된다. -/
theorem freshString_zero (s : Finset String) (h : "x" ∉ s) :
    Cslib.fresh s = "x" :=
  freshString_eq s 0 h (by omega)

/-- 연습 1.4 (p. 23)의 계산 지원: `x`가 금지되고 `xx`가 안전하면 선택된다. -/
theorem freshString_one (s : Finset String) (h₀ : "x" ∈ s) (h₁ : "xx" ∉ s) :
    Cslib.fresh s = "xx" := by
  apply freshString_eq s 1 h₁
  intro m hm
  have : m = 0 := by omega
  subst m
  exact h₀

/-- 연습 1.4 (p. 23)의 계산 지원: 앞의 두 후보가 금지되고 `xxx`가 안전하면 선택된다. -/
theorem freshString_two (s : Finset String)
    (h₀ : "x" ∈ s) (h₁ : "xx" ∈ s) (h₂ : "xxx" ∉ s) :
    Cslib.fresh s = "xxx" := by
  apply freshString_eq s 2 h₂
  intro m hm
  have : m = 0 ∨ m = 1 := by omega
  rcases this with rfl | rfl
  · exact h₀
  · exact h₁

/-- Reynolds 연습 1.4(a) (p. 23)의 입력 단언. `t`의 자유 발생에 합을 넣는다. -/
def e14a : Assert String :=
  ⟪ ∀ x, ∀ z, x < t ∧ t < z ⇒ (∃ y, x < y ∧ y < z) ⟫ₐ

/-- Reynolds 연습 1.4(a) (p. 23)의 치환 사상. `t ↦ x + y + z`. -/
def e14aSubst : Subst String := Function.update IntExp.var "t" ⟪ x + y + z ⟫ₑ

/--
Reynolds 연습 1.4(a) (p. 23). 결과 단언과 구문 등식의 증명을 함께 제시한다.
먼저 각 양화사의 본문에서 실제로 치환되는 자유 발생을 찾는다.
-/
@[exercise "Ex 1.4a" 2]
noncomputable def e14aResult : {q : Assert String // e14a /ₛ e14aSubst = q} := by
  -- 먼저 손으로 결과를 쓴 뒤 `refine ⟨⟪ … ⟫ₐ, ?_⟩`로 그 구문을 제시한다.
  -- 힌트: 각 결합자의 본문에서 자유롭게 나타나는 변수에만 치환이 들어간다.
  -- 이름 선택 계산에는 위의 `freshString_zero/one/two`를 쓸 수 있다.
  -- `simp [e14a, e14aSubst, Assert.subst, newBinder, captureSet, Assert.fv,
  --   IntExp.fv, IntExp.subst, Finset.erase_insert_of_ne, Finset.erase_insert_eq_erase, …]`
  sorry

/-- Reynolds 연습 1.4(b) (p. 23)의 입력 단언. 두 존재 양화사의 범위는 서로 다르다. -/
def e14b : Assert String := ⟪ ∀ d, (∃ n, x = n × d) ⇒ (∃ n, y = n × d) ⟫ₐ

/-- Reynolds 연습 1.4(b) (p. 23)의 동시 치환. `x ↦ n`, `y ↦ d`, 나머지는 그대로다. -/
def e14bSubst : Subst String :=
  Function.update (Function.update IntExp.var "x" ⟪ n ⟫ₑ) "y" ⟪ d ⟫ₑ

-- 들어온 n과 d가 속박되지 않고 자유 변수로 남는지 확인한다.
#guard (e14b /ₛ e14bSubst).fv == ({"n", "d"} : Finset String)

/--
Reynolds 연습 1.4(b) (p. 23). 결과 단언과 구문 등식의 증명을 함께 제시한다.
같은 이름의 두 양화사도 각각 자기 본문의 자유 발생으로 포획 위험을 판단한다.
-/
@[exercise "Ex 1.4b" 2]
noncomputable def e14bResult : {q : Assert String // e14b /ₛ e14bSubst = q} := by
  -- 먼저 손으로 결과를 쓴 뒤 `refine ⟨⟪ … ⟫ₐ, ?_⟩`로 그 구문을 제시한다.
  -- 힌트: 각 결합자의 본문에서 자유롭게 나타나는 변수에만 치환이 들어간다.
  -- 이름 선택 계산에는 위의 `freshString_zero/one/two`를 쓸 수 있다.
  -- `simp [e14b, e14bSubst, Assert.subst, newBinder, captureSet, Assert.fv,
  --   IntExp.fv, IntExp.subst, Finset.erase_insert_of_ne, Finset.erase_insert_eq_erase, …]`
  sorry

/-- Reynolds 연습 1.4(c) (p. 23)의 입력 단언. `x`, `y`는 속박되고 `z`는 자유롭다. -/
def e14c : Assert String := ⟪ ∀ x, ∃ y, x < z ⇒ x < y ∧ y < z ⟫ₐ

/-- Reynolds 연습 1.4(c) (p. 23)의 동시 치환. `x ↦ y`, `y ↦ z`, `z ↦ x`. -/
def e14cSubst : Subst String :=
  Function.update (Function.update (Function.update IntExp.var "x" ⟪ y ⟫ₑ)
    "y" ⟪ z ⟫ₑ) "z" ⟪ x ⟫ₑ

/--
Reynolds 연습 1.4(c) (p. 23). 결과 단언과 구문 등식의 증명을 함께 제시한다.
동시 치환에서 들어온 식에는 치환을 다시 적용하지 않는다.
-/
@[exercise "Ex 1.4c" 2]
noncomputable def e14cResult : {q : Assert String // e14c /ₛ e14cSubst = q} := by
  -- 먼저 손으로 결과를 쓴 뒤 `refine ⟨⟪ … ⟫ₐ, ?_⟩`로 그 구문을 제시한다.
  -- 힌트: 각 결합자의 본문에서 자유롭게 나타나는 변수에만 치환이 들어간다.
  -- 이름 선택 계산에는 위의 `freshString_zero/one/two`를 쓸 수 있다.
  -- `simp [e14c, e14cSubst, Assert.subst, newBinder, captureSet, Assert.fv,
  --   IntExp.fv, IntExp.subst, Finset.erase_insert_of_ne, Finset.erase_insert_eq_erase, …]`
  sorry

/--
Reynolds 명제 1.3 (§1.4, p. 20)을 연습 1.4(b) (p. 23)에 적용한 의미 등식.

위의 구문 계산과 달리 치환 정리에 의존한다. 연습 독립성을 지키려고
완성 자료로 제공하며, 채점 대상으로 두지 않는다 (`AGENTS.md` §1-9).
-/
theorem e14b_meaning (σ : State String) :
    (⟦e14b /ₛ e14bSubst⟧ₐ σ ↔ ⟦e14b⟧ₐ (fun w => ⟦e14bSubst w⟧ₑ σ)) :=
  substitution_assert e14b e14bSubst _ σ fun _ _ => rfl

/-! ## 연습 1.3 · 1.5 · 1.6 · 1.7 — 어디에 있나

**1.3** (괄호 없는 접두 표기와 생성자 단사성) 은 `Realizations.lean` 에 있다.

**1.5** (합 식 `Σv : e₀ to e₁. e₂` 추가) 와 **1.6** (부정 합 `Σv. e`) 은
`Ex/Summation.lean` 에 있다. 문법·의미·자유 변수·치환·추론 규칙을 전부 새로 얹어야 해서
축소판 언어 `SExp` 를 따로 세웠다.

**1.7** (치환 합성 법칙) 은 `Depth/TermMonad.lean` 에 있다.
그 파일에서 이 문제가 모나드 결합법칙이라는 것과, Reynolds 의 진술이 "같다" 가 아니라
"is a renaming of" 인 이유를 함께 다룬다. (a) 만 다루고 (b) 는 아직 없다.
-/

end Reynolds.Exercises.Ch01.Ex
