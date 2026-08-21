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

Reynolds 는 세 개의 치환을 손으로 계산하라고 한다. 여기서는 `#guard` 로 확인한다.
불필요한 이름 바꾸기를 하지 말라는 단서가 붙어 있는데, `newBinder` 가 그 조건을
그대로 구현한다 — 안전하면 원래 이름을 그대로 쓴다. -/

/-- 1.4(b) `∀d. ((∃n. x = n × d) ⇒ (∃n. y = n × d))` 에서 `x ↦ n`, `y ↦ d`. -/
def e14b : Assert String := ⟪ ∀ d, (∃ n, x = n × d) ⇒ (∃ n, y = n × d) ⟫ₐ

/-- 1.4(b) 의 치환 사상. `x ↦ n`, `y ↦ d`, 나머지는 그대로. -/
def e14bSubst : Subst String :=
  Function.update (Function.update IntExp.var "x" ⟪ n ⟫ₑ) "y" ⟪ d ⟫ₑ

-- 치환 결과를 직접 본다. `x ↦ n`, `y ↦ d` 를 넣으면 `n` 과 `d` 가 자유 변수로 들어오는데,
-- 바깥에 `∀d`, 안쪽에 `∃n` 이 있어서 둘 다 잡힐 위험이 있다.
-- 결과의 자유 변수가 `{n, d}` 로 남는다는 것이 포획이 없었다는 증거다.
#guard (e14b /ₛ e14bSubst).fv == ({"n", "d"} : Finset String)

/--
치환한 단언의 뜻은 상태를 바꿔 평가한 것과 같다.

명제 1.3 을 이 구체적인 예에 적용한 것이다. `#guard` 는 구문이 어떻게 생겼는지 보여 주고,
이 정리는 그 구문이 뜻하는 바를 말한다.

연습으로 빼지 않았다. 명제 1.3 자체가 연습이라 그것을 쓰는 이 정리까지 비우면
연습끼리 의존하게 된다 (`AGENTS.md` §1-9).
-/
theorem e14b_meaning (σ : State String) :
    (⟦e14b /ₛ e14bSubst⟧ₐ σ ↔ ⟦e14b⟧ₐ (fun w => ⟦e14bSubst w⟧ₑ σ)) :=
  substitution_assert e14b e14bSubst _ σ fun _ _ => rfl

/-! ## 연습 1.3 · 1.5 · 1.6 · 1.7 — 어디에 있나

**1.3** (괄호 없는 접두 표기와 생성자 단사성) 은 `Realizations.lean` 에 있다.

**1.5** (합 식 `Σv : e₀ to e₁. e₂` 추가) 는 문법·의미·자유 변수·치환·추론 규칙을 전부
새로 얹어야 하는 큰 문제라 별도 파일로 뺄 예정이다. 아직 없다.

**1.6** (부정합 합 `Σv. e` 의 문제점) 은 논의 문제다. 상계가 변수 자신에 의존하면
결합 구조가 무너진다는 것이 요점이고, 코드로 옮길 것이 마땅치 않아 남겨 둔다.

**1.7** (치환 합성 법칙) 은 `Depth/TermMonad.lean` 에 있다.
그 파일에서 이 문제가 모나드 결합법칙이라는 것과, Reynolds 의 진술이 "같다" 가 아니라
"is a renaming of" 인 이유를 함께 다룬다.
-/

end Reynolds.Exercises.Ch01.Ex
