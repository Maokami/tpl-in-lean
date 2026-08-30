/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Answers.Ch02.Domain

/-!
# §2.4 최소 고정점 정리 (Least Fixed-Point Theorem)

Reynolds §2.4 에 대응한다. 2장이 여기까지 걸어온 이유가 이 정리다.

## 되짚기 — 왜 고정점인가

§2.2 에서 `while b do c` 의 뜻은 정의가 아니라 방정식이었고, 그 방정식은 해를 유일하게
정하지 못했다 (`unwinding_not_unique`). 방정식을 함수로 다시 읽으면

```
F(w) = fun σ => if ⟦b⟧ σ then ⟦c⟧ σ >>= w else some σ
```

이고, 해는 `F` 의 **고정점** — `F(w) = w` 인 `w` — 다. 고정점이 여럿이므로 고르는 원리가
필요했고, §2.3 이 그 원리의 재료인 순서를 만들었다. "계산이 알려 주지 않는 것을 주장하지
않는 해", 곧 순서에서 **가장 아래**에 있는 고정점이 뜻이다.

이 파일이 증명하는 것: 도메인 위의 연속 함수는 최소 고정점을 가지며, 그것은

```
⊥ ⊑ F(⊥) ⊑ F(F(⊥)) ⊑ ⋯
```

의 극한이다.

## 반복이 뜻하는 것

`while` 로 돌아가 읽으면 `Fⁿ(⊥)` 는 "본체를 최대 `n` 번까지만 도는 반복문" 의 뜻이다.
`⊥` 는 한 번도 못 도는 반복문 — 아무 상태에서도 답하지 않는다 — 이고, `F` 를 한 번 적용할
때마다 한 바퀴를 더 감당한다. 극한은 "몇 바퀴가 걸리든, 유한하게 끝나기만 하면 답하는"
함수다. 끝나지 않는 상태에서는 어느 단계도 답하지 않으므로 극한도 `⊥` 다 — `decrTrue` 가
바로 이 모양이었다.

## Reynolds 의 세 단계

책의 증명이 세 단계이고, 그대로 세 정리가 된다.

1. 반복이 사슬을 이룬다 — `iterChain`
2. 극한이 고정점이다 — `fix_eq`
3. 그 고정점이 최소다 — `fix_least`

마지막에 **Scott 귀납법**을 더한다. 책에는 §2.4 본문에 없지만, 연습 2.3 과 2.5 가
사실상 이것을 요구하고, `while` 에 대한 성질 증명은 대부분 이 원리로 돈다.

## 읽는 순서
`Domain/FunctionSpace.lean` → 이 파일 → `Semantics2.lean` (다음 PR, `Comm.eval` 정의)
-/

@[expose] public section

namespace Reynolds.Answers.Ch02

open Reynolds

universe u

variable {α : Type u} [PartialOrder α] [OrderBot α] [Predomain α]

/-! ## 1. 반복이 사슬을 이룬다

`F` 가 단조라는 것만으로 충분하다. 첫 걸음 `⊥ ⊑ F(⊥)` 는 `⊥` 가 최소원이라 공짜이고,
그다음부터는 단조성이 걸음을 이어 준다. -/

omit [Predomain α] in
/-- 각 단계는 다음 단계 아래에 있다. `n` 에 대한 귀납이고, 걸음마다 `F` 를 한 번 입힌다. -/
theorem iterate_le_succ {F : α → α} (hF : Monotone F) (n : ℕ) :
    F^[n] ⊥ ≤ F^[n + 1] ⊥ := by
  induction n with
  | zero => exact bot_le
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact hF ih

-- ANCHOR: iterChain
/-- 반복의 사슬. `⊥ ⊑ F(⊥) ⊑ F(F(⊥)) ⊑ ⋯`. Reynolds 세 단계의 첫째다. -/
def iterChain {F : α → α} (hF : Monotone F) : Chain α :=
  ⟨fun n => F^[n] ⊥, monotone_nat_of_le_succ (iterate_le_succ hF)⟩
-- ANCHOR_END: iterChain

omit [Predomain α] in
@[simp] theorem iterChain_seq {F : α → α} (hF : Monotone F) (n : ℕ) :
    (iterChain hF).seq n = F^[n] ⊥ := rfl

/-! ## 2. 극한이 고정점이다

연속성이 처음이자 마지막으로 쓰이는 자리다. §2.3 에서 단조와 연속이 다르다는 것을
확인해 두었으므로, 여기서 연속을 요구하는 것이 공짜 가정이 아님을 안다.

증명의 모양: `F` 를 사슬에 입히면 사슬이 한 칸 밀린다. 밀린 사슬의 극한은 원래 극한과
같다 — 빠진 것이 맨 앞의 `⊥` 하나뿐인데, `⊥` 는 극한에 아무 기여도 하지 않는다.
그러면 연속성이 `F(극한) = 밀린 사슬의 극한 = 극한` 을 준다. -/

/-- 최소 고정점. 반복의 극한이다. Reynolds 의 `Y_D F`. -/
noncomputable def fix (F : α → α) (hF : Monotone F) : α := (iterChain hF).lub

/-- 밀린 사슬 `F(⊥), F²(⊥), …` 의 극한도 `fix` 다. 맨 앞의 `⊥` 는 극한에 기여하지 않는다. -/
theorem isLUB_shifted {F : α → α} (hF : Monotone F) :
    IsLUB (Set.range fun n => F^[n + 1] ⊥) (fix F hF) := by
  constructor
  · -- 위: 밀린 사슬의 항은 전부 원래 사슬의 항이다.
    rintro _ ⟨n, rfl⟩
    exact (iterChain hF).le_lub (n + 1)
  · -- 아래: 밀린 사슬의 상계는 원래 사슬의 상계이기도 하다. `⊥` 는 어차피 아래에 있다.
    intro b hb
    refine (iterChain hF).lub_le fun n => ?_
    cases n with
    | zero => exact bot_le
    | succ n => exact hb ⟨n, rfl⟩

-- ANCHOR: fixEq
/--
**최소 고정점 정리, 둘째 단계 — 극한은 고정점이다.**

`F` 의 연속성을 반복의 사슬에 적용하면 `F(fix)` 가 "F 를 입힌 사슬" 의 극한이 된다.
그 사슬은 원래 사슬을 한 칸 민 것이고, 밀어도 극한은 그대로다. 극한의 유일성으로 끝난다.
-/
@[exercise "§2.4 fix-eq" 3]
theorem fix_eq {F : α → α} (hF : Continuous F) :
    F (fix F hF.monotone) = fix F hF.monotone := by
  -- 연속성: `F(fix)` 는 `F '' (사슬의 값들)` 의 극한이다.
  have h₁ := hF (iterChain hF.monotone)
  -- 그 상은 밀린 사슬의 값들과 같다.
  have himg : F '' Set.range (iterChain hF.monotone).seq
      = Set.range fun n => F^[n + 1] ⊥ := by
    ext y
    constructor
    · rintro ⟨_, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, Function.iterate_succ_apply' F n ⊥⟩
    · rintro ⟨n, rfl⟩
      exact ⟨F^[n] ⊥, ⟨n, rfl⟩, (Function.iterate_succ_apply' F n ⊥).symm⟩
  rw [himg] at h₁
  -- 밀린 사슬의 극한은 `fix` 이기도 하다. 극한은 유일하다.
  exact h₁.unique (isLUB_shifted hF.monotone)
-- ANCHOR_END: fixEq

/-! ## 3. 그 고정점이 최소다

사실 더 강하게 나온다. `F(x) ⊑ x` 인 모든 `x` — 고정점이 아니라 **전고정점**(pre-fixed
point) — 위에서도 `fix` 가 아래에 있다. 반복의 각 단계가 `x` 아래에 머무는 것을 귀납으로
확인하면 극한도 `x` 아래다. -/

-- ANCHOR: fixLeast
/--
**최소 고정점 정리, 셋째 단계 — 전고정점 아래에 있다.**

`F(x) ⊑ x` 이면 `fix ⊑ x` 다. 고정점은 전고정점이므로, `fix` 는 모든 고정점 아래에 있다.

§2.2 의 두 해로 돌아가면: `decrFake` 도 풀기 방정식의 해이므로 전고정점이고, 따라서
`fix ⊑ decrFake`. "계산이 알려 주지 않는 것을 주장하지 않는 쪽" 을 고르는 원칙이
이 정리로 실행된다. `fix` 가 정확히 `decrTrue` 라는 것은 다음 파일에서 `Comm.eval` 을
정의하면서 확인한다.
-/
@[exercise "§2.4 fix-least" 2]
theorem fix_least {F : α → α} (hF : Monotone F) {x : α} (hx : F x ≤ x) :
    fix F hF ≤ x := by
  refine (iterChain hF).lub_le fun n => ?_
  induction n with
  | zero => exact bot_le
  | succ n ih =>
      calc F^[n + 1] ⊥ = F (F^[n] ⊥) := Function.iterate_succ_apply' F n ⊥
        _ ≤ F x := hF ih
        _ ≤ x := hx
-- ANCHOR_END: fixLeast

/-- 두 단계를 합친 진술. `fix` 는 고정점이고, 모든 고정점 아래에 있다. -/
theorem fix_isLeast {F : α → α} (hF : Continuous F) {x : α} (hx : F x = x) :
    F (fix F hF.monotone) = fix F hF.monotone ∧ fix F hF.monotone ≤ x :=
  ⟨fix_eq hF, fix_least hF.monotone (le_of_eq hx)⟩

/-! ## 4. Scott 귀납법

`fix` 에 대한 성질을 증명하는 유일한 일반 원리다. `fix` 는 극한이라서 유한한 계산으로
닿을 수 없고, 성질을 옮기려면 성질 자체가 극한을 통과해야 한다.

극한을 통과하는 성질을 **허용 가능(admissible)** 하다고 부른다. 세 가지를 확인하면
`P (fix F)` 가 나온다.

1. `P ⊥` — 바닥에서 성립하고
2. `P x → P (F x)` — 걸음마다 보존되고
3. 사슬의 모든 항에서 성립하면 극한에서도 성립한다 (허용 가능성)

3 이 공짜가 아니라는 것이 이 원리의 요점이다. "어떤 상태에서 `⊥` 다" 라는 성질을 보라.
모든 상태에서 끝나는 반복문이라도 유한 풀기 `Fⁿ(⊥)` 는 `n` 바퀴 넘게 걸리는 상태에서
`⊥` 이므로, 이 성질은 매 단계 성립한다. 그런데 극한은 모든 바퀴를 감당하므로 성질이
깨진다. 존재 주장이 섞인 성질은 대개 이렇게 극한에서 무너지고, 그런 성질에는 Scott
귀납법을 쓸 수 없다.
-/

-- ANCHOR: scott
/--
**Scott 귀납법.** 허용 가능한 성질이 `⊥` 에서 성립하고 `F` 가 보존하면, `fix F` 에서
성립한다.

증명은 두 줄이다. 반복의 각 단계에서 성질이 성립함을 자연수 귀납으로 확인하고,
허용 가능성이 그것을 극한으로 넘긴다. 어려움이 전부 "허용 가능한가" 를 확인하는 쪽에
있다는 것이 이 원리의 특징이고, §2.5 부터 그 확인이 실제 일이 된다.
-/
@[exercise "§2.4 scott" 2]
theorem scott_induction {F : α → α} (hF : Monotone F) {P : α → Prop}
    (hadm : ∀ c : Chain α, (∀ n, P (c.seq n)) → P c.lub)
    (hbot : P ⊥) (hstep : ∀ x, P x → P (F x)) : P (fix F hF) := by
  refine hadm (iterChain hF) fun n => ?_
  induction n with
  | zero => exact hbot
  | succ n ih =>
      rw [iterChain_seq, Function.iterate_succ_apply']
      exact hstep _ ih
-- ANCHOR_END: scott

/-! ## 5. 여기서 어디로 가나

정리가 손에 들어왔다. 남은 것은 적용이다.

`Σ → Σ⊥` 는 도메인이고 (§2.3), `while` 의 함수자 `F` 는 그 위의 연속 함수다
(연속성 증명이 다음 파일의 일이다). 그러면

```
⟦while b do c⟧ = fix F
```

로 **정의**할 수 있고, `fix_eq` 가 풀기 방정식을, `fix_least` 가 "여러 해 중 가장 아래" 를
준다. §2.2 에서 적어 둔 명세 `IsSemantics` 를 만족하는 `Comm.eval` 이 드디어 정의된다.

그다음이 연료(fuel) 해석기다. `Fⁿ(⊥)` 가 "본체를 최대 n 번 도는 반복문" 이라는 위의
직관을 실행 가능한 프로그램으로 만들고, 표시적 의미와 일치함을 증명한다. -/

end Reynolds.Answers.Ch02
