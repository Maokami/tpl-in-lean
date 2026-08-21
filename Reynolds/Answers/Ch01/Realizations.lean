/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Answers.Ch01.Syntax
-- Notation 은 두 트리가 공유한다 (scripts/gen-exercises.py 의 SHARED).
-- 구문 범주가 전역이라 복제할 수 없고, 매크로가 이름을 쓰는 자리에서 해석하므로
-- 위의 Syntax import 가 어느 트리의 정의를 쓸지 정한다.
public import Reynolds.Answers.Ch01.Notation
public import Reynolds.Meta.Exercise
-- `#guard` 는 컴파일 시점에 계산한다 (AGENTS.md §10).
public meta import Reynolds.Answers.Ch01.Syntax
public meta import Reynolds.Answers.Ch01.Notation

/-!
# §1.1 실현 (realization) — 연습 1.3

Reynolds §1.1 은 같은 추상 구문의 여러 실현을 든다. 괄호 붙인 중위 문자열,
괄호 붙인 접두 문자열, 구문 트리. 그리고 연습 1.3 에서 하나를 더 요구한다.

> *"Define a universe of phrases, and the constructors displayed in (1.1) in Section 1.1,
> to obtain an unparenthesized prefix notation. For instance,
> `c₊(c₋ᵦ(c₀(), c₁()), c₋ᵤ(c₂()))` should be the string "add, subtract, 0, 1, negate, 0".
> Be sure that the universe of phrases is defined so that the constructors are injective."*

괄호가 없다는 것이 요점이다. 괄호 없이도 읽을 수 있으려면 연산자마다 인자 개수가 고정되어
있어야 하고, 그 사실이 곧 §1.1 의 세 조건 중 첫째(생성자 단사성)로 이어진다.

## 무대를 문자열이 아니라 토큰 열로 잡은 이유

Reynolds 는 문자열이라고 말하지만, 문자열로 하면 `"x1"` 이 변수 이름 하나인지
`"x"` 와 `"1"` 인지 같은 문제가 따라온다. 그건 어휘 분석(lexing)의 문제이지
이 연습이 묻는 것이 아니다. 토큰 열로 두면 물어야 할 것만 남는다.

## 읽는 순서
`Syntax.lean` → 이 파일. `Ex.lean` 의 연습 1.3 이 여기를 가리킨다.
-/

-- 실현이 실제로 무엇을 뱉는지 눈으로 본다.
set_option linter.hashCommand false

@[expose] public section

namespace Reynolds.Answers.Ch01

open Reynolds

/-! ## 토큰과 접두 표기 -/

/-- 접두 표기의 토큰. Reynolds 의 `"add"`, `"subtract"`, `"0"`, `"negate"` 에 해당한다. -/
inductive Tok where
  /-- 정수 상수. -/
  | num : Int → Tok
  /-- 변수 이름. -/
  | var : String → Tok
  /-- 단항 마이너스. Reynolds 의 `negate`. -/
  | neg : Tok
  /-- 이항 연산자. -/
  | op : IntOp → Tok
  deriving DecidableEq, Repr

/--
괄호 없는 접두 표기.

연산자를 먼저 쓰고 인자를 이어 붙인다. 괄호가 없어도 되는 이유는 연산자마다
인자 개수가 고정되어 있어서다 — `neg` 뒤에는 식 하나, `op` 뒤에는 식 둘.
-/
def IntExp.toPrefix : IntExp String → List Tok
  | .num n        => [.num n]
  | .var v        => [.var v]
  | .neg e        => .neg :: e.toPrefix
  | .bin op e₀ e₁ => .op op :: (e₀.toPrefix ++ e₁.toPrefix)

-- Reynolds 의 예제. `(0 - 1) + (-2)` 가 "add, subtract, 0, 1, negate, 2" 가 된다.
#guard ⟪ (0 - 1) + (-2) ⟫ₑ.toPrefix
        == [.op .add, .op .sub, .num 0, .num 1, .neg, .num 2]

/-! ## 접두 표기는 접두사 자유(prefix-free)다

접두 표기가 애매하지 않다는 것을 어떻게 보이나. 파서를 짜서 되돌리는 방법도 있지만,
더 짧은 길이 있다. **한 식의 토큰 열은 다른 식의 토큰 열의 진접두사가 될 수 없다** 는
사실을 직접 증명하면 단사성이 따라온다.

진술을 "뒤에 아무거나 붙여도" 형태로 일반화해야 귀납이 돈다.
이것도 §1.4 의 일치 정리와 같은 종류의 일반화다. -/

/--
접두사 자유성. 두 식의 접두 표기에 아무 꼬리나 붙여 같아지면, 식도 꼬리도 같다.

`e₁` 에 대한 구조적 귀납법이고, 각 단계에서 `e₂` 를 케이스로 나눈다.
생성자가 다르면 첫 토큰이 달라서 바로 모순이고, 같으면 꼬리를 벗겨 귀납 가설을 쓴다.

`bin` 절이 유일하게 손이 가는 곳이다. 인자가 둘이라 귀납 가설을 두 번 쓰는데,
첫 번째가 "앞 인자가 같고 나머지 열이 같다" 를 주고 두 번째가 그 나머지를 처리한다.
-/
theorem IntExp.toPrefix_prefixFree :
    ∀ (e₁ e₂ : IntExp String) (r₁ r₂ : List Tok),
      e₁.toPrefix ++ r₁ = e₂.toPrefix ++ r₂ → e₁ = e₂ ∧ r₁ = r₂ := by
  intro e₁
  induction e₁ with
  | num n =>
      intro e₂ r₁ r₂ h
      cases e₂ with
      | num m =>
          simp only [IntExp.toPrefix, List.cons_append, List.nil_append] at h
          injection h with hd tl
          injection hd with hn
          exact ⟨by rw [hn], tl⟩
      | var _ | neg _ | bin _ _ _ => simp [IntExp.toPrefix] at h
  | var v =>
      intro e₂ r₁ r₂ h
      cases e₂ with
      | var w =>
          simp only [IntExp.toPrefix, List.cons_append, List.nil_append] at h
          injection h with hd tl
          injection hd with hv
          exact ⟨by rw [hv], tl⟩
      | num _ | neg _ | bin _ _ _ => simp [IntExp.toPrefix] at h
  | neg e ih =>
      intro e₂ r₁ r₂ h
      cases e₂ with
      | neg e' =>
          simp only [IntExp.toPrefix, List.cons_append] at h
          injection h with _ tl
          obtain ⟨he, hr⟩ := ih _ _ _ tl
          exact ⟨by rw [he], hr⟩
      | num _ | var _ | bin _ _ _ => simp [IntExp.toPrefix] at h
  | bin op e₀ e₁ ih₀ ih₁ =>
      intro e₂ r₁ r₂ h
      cases e₂ with
      | bin op' e₀' e₁' =>
          -- 첫 토큰이 연산자를 정하고, 남은 열을 앞 인자부터 차례로 맞춘다.
          simp only [IntExp.toPrefix, List.cons_append, List.append_assoc] at h
          injection h with hd tl
          injection hd with hop
          subst hop
          obtain ⟨he₀, hrest⟩ := ih₀ _ _ _ tl
          obtain ⟨he₁, hr⟩ := ih₁ _ _ _ hrest
          exact ⟨by rw [he₀, he₁], hr⟩
      | num _ | var _ | neg _ => simp [IntExp.toPrefix] at h

/--
접두 표기 생성자가 단사다. Reynolds 가 연습 1.3 에서 확인하라고 하는 것이다.

꼬리를 빈 열로 두면 접두사 자유성에서 바로 나온다.
-/
@[exercise "Ex 1.3" 3]
theorem IntExp.toPrefix_injective : Function.Injective IntExp.toPrefix := by
  intro e₁ e₂ h
  exact (IntExp.toPrefix_prefixFree e₁ e₂ [] [] (by simpa using h)).1

/-! ## 왜 이것이 "실현" 인가

Reynolds 의 관점에서 실현이란 추상 구문 조건을 만족하는 구체적인 집합과 함수들이다.
여기서는 반송자가 `List Tok` 이고 생성자가 이렇게 된다.

```
c₀()            = [Tok.num 0]
c_var(v)        = [Tok.var v]
c₋ᵤ(x)          = Tok.neg :: x
c₊(x, y)        = Tok.op .add :: (x ++ y)
```

`toPrefix_injective` 가 세 조건 중 첫째를 확인한 것이다.
치역이 서로소라는 둘째 조건도 첫 토큰이 결정하므로 같은 증명 안에 들어 있다.

`Depth/Algebra.lean` 의 어휘로 다시 읽으면, `toPrefix` 는 반송자가 `List Tok` 인
대수로 가는 유일한 준동형이다. 실현을 하나 고른다는 것이 대수를 하나 고른다는 뜻이다.
-/

end Reynolds.Answers.Ch01
