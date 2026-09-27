/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Answers.Ch01.Notation
public import Reynolds.Exercises.Ch01.Substitution
public import Reynolds.Exercises.Ch01.Ex.Specifications
-- `#guard` 는 컴파일 시점에 계산하므로 meta 문맥이다 (AGENTS.md §10).
public meta import Reynolds.Answers.Ch01.Notation
public meta import Reynolds.Exercises.Ch01.Substitution
public meta import Mathlib.Data.Finset.Defs

/-!
# 1장 연습문제

Reynolds §1 의 연습문제 1.1~1.7 에 대응한다.

## 종이 문제를 어떻게 채점 가능하게 만드나

Reynolds 연습 1.1·1.2(p. 22)는 단언을 직접 쓰는 문제다.
각 답은 객체 언어 구문(`⟪ … ⟫ₐ`)과 그 뜻을 확인하는 증명을 함께 담는다.
학생 파일에서는 두 부분을 함께 비우므로 정답 단언이 미리 주어지지 않는다.
명세와 계산 보조 자료는 `Ex/Specifications.lean`에 있다.

## 읽는 순서
1장 본문을 다 읽은 뒤. `Notation.lean` 의 표기를 쓴다.
-/

-- 이 파일은 `#guard` 로 계산을 확인한다.
set_option linter.hashCommand false

@[expose] public section

namespace Reynolds.Exercises.Ch01.Ex

open Reynolds Reynolds.Exercises.Ch01

/-! ## 연습 1.1 — 개수 세기

Reynolds p. 22의 고정 구간을 임의의 열린 구간 `(lo, hi)`로 일반화한 보조 실습이다.
책의 구간만 검사하면 네 문장이 모두 참이라 `tt`를 답으로 쓸 수 있다.
여기서는 끝점이 달라져도 개수를 올바르게 표현해야 한다.
답의 첫 칸에 `fun lo hi => ⟪ … ⟫ₐ`를 쓰고, 둘째 칸에서 원소 수 명세를 증명한다.
메타 수준 정수 `lo`는 `%(.num lo)`로 객체 언어에 넣는다. -/

/-- Reynolds 연습 1.1(a)(p. 22). 구간에 적어도 하나의 정수가 있다는 단언을 만든다.
책은 `(0,2)`다. -/
@[exercise "Ex 1.1a" 1]
noncomputable def e11aAnswer :
    {p : Int → Int → Assert String //
      ∀ lo hi σ, ⟦p lo hi⟧ₐ σ ↔ 1 ≤ intervalCount lo hi} := by
  -- `refine ⟨fun lo hi => ⟪ … ⟫ₐ, ?_⟩`로 단언을 직접 쓴다.
  -- 힌트: `Finset.one_le_card`로 원소 수 명세를 존재 명제로 바꾼다.
  sorry

/-- Reynolds 연습 1.1(b)(p. 22). 구간에 많아야 하나의 정수가 있다는 단언을 만든다.
책은 `(0,2)`다. -/
@[exercise "Ex 1.1b" 2]
noncomputable def e11bAnswer :
    {p : Int → Int → Assert String //
      ∀ lo hi σ, ⟦p lo hi⟧ₐ σ ↔ intervalCount lo hi ≤ 1} := by
  -- 단언을 직접 쓰고 `Finset.card_le_one`과 연결한다.
  sorry

/-- Reynolds 연습 1.1(c)(p. 22). 구간에 서로 다른 정수가 적어도 둘 있다는 단언을 만든다.
책은 `(0,3)`다. -/
@[exercise "Ex 1.1c" 2]
noncomputable def e11cAnswer :
    {p : Int → Int → Assert String //
      ∀ lo hi σ, ⟦p lo hi⟧ₐ σ ↔ 2 ≤ intervalCount lo hi} := by
  -- 단언을 직접 쓴다. 힌트: `Finset.one_lt_card_iff`.
  sorry

/-- Reynolds 연습 1.1(d)(p. 22). 구간에 서로 다른 정수가 많아야 둘이라는 단언을 만든다.
책은 `(0,3)`다. -/
@[exercise "Ex 1.1d" 2]
noncomputable def e11dAnswer :
    {p : Int → Int → Assert String //
      ∀ lo hi σ, ⟦p lo hi⟧ₐ σ ↔ intervalCount lo hi ≤ 2} := by
  -- 단언을 직접 쓴다. 힌트: `Finset.two_lt_card_iff`와 `not_lt`.
  sorry

/-! ## 연습 1.2 — 나눗셈 없이 정수론 말하기

Reynolds p. 22는 변수와 식의 범위를 자연수로 제한하고 `÷`·`rem`을 금한다.
각 `NatAnswer`의 첫 칸에 단언을 쓰고, 허용 구문 검사와 모든 자연수 상태에서의 뜻을 증명한다.
자연수 양화는 `evalNat`가 맡으므로 답 안에 정수 양화의 범위 제한을 덧붙일 필요가 없다.
네 문항에 충분한 자연수 산술 조각과 그 선택의 범위는 `Specifications.lean`에 설명한다.
-/

/-- Reynolds 연습 1.2(a)(p. 22). 자연수 `a`가 `b`의 약수라는 단언을 직접 만든다. -/
@[exercise "Ex 1.2a" 1]
noncomputable def e12aAnswer : NatAnswer (fun σ => σ "a" ∣ σ "b") := by
  -- `refine ⟨⟪ … ⟫ₐ, rfl, ?_⟩`: 구문을 쓰고 허용 구문 검사와 의미를 증명한다.
  -- 힌트: `dvd_def`, `evalNat`. 양화된 변수도 자연수다.
  sorry

/-- Reynolds 연습 1.2(b)(p. 22). 자연수 `a`가 `b`, `c`의 공약수라는 단언을 만든다. -/
@[exercise "Ex 1.2b" 1]
noncomputable def e12bAnswer :
    NatAnswer (fun σ => σ "a" ∣ σ "b" ∧ σ "a" ∣ σ "c") := by
  -- 단언을 직접 쓴다. 다른 연습의 답을 쓰지 않아도 풀 수 있다.
  sorry

/--
Reynolds 연습 1.2(c)(p. 22). 자연수 공약수 집합의 최대 원소라는 단언을 만든다.
`b = c = 0`이면 최대가 없으므로 어떤 `a`에서도 거짓이어야 한다.
이는 `Nat.gcd 0 0 = 0`이라는 별도 규약과 다르다.
-/
@[exercise "Ex 1.2c" 2]
noncomputable def e12cAnswer :
    NatAnswer (fun σ => GreatestCommonDivisor (σ "a") (σ "b") (σ "c")) := by
  -- 공약수라는 조건과 모든 공약수보다 크거나 같다는 조건을 단언으로 쓴다.
  -- `GreatestCommonDivisor`, `IsGreatest`, `upperBounds`를 펼쳐 비교한다.
  sorry

/--
Reynolds 연습 1.2(d)(p. 22). 자연수 `p`가 소수라는 단언을 만든다.
명세는 Mathlib의 `Nat.Prime`이다. `0`, `1`이 소수가 아니라는 조건도 표현해야 한다.
-/
@[exercise "Ex 1.2d" 2]
noncomputable def e12dAnswer : NatAnswer (fun σ => Nat.Prime (σ "p")) := by
  -- 단언을 직접 쓴다. `Nat.prime_def`로 의미 명세를 펼친다.
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
