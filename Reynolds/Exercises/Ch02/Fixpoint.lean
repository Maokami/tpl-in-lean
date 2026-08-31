/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Exercises.Ch02.Domain

/-!
# §2.4 최소 고정점 정리 (Least Fixed-Point Theorem)

Reynolds §2.4에 대응한다.

## 이 파일에서 다루는 것

- 반복 근사 `⊥ ⊑ F(⊥) ⊑ F²(⊥) ⊑ ⋯`와 그 극한 `fix`
- 연속 함수에서 그 극한이 고정점이라는 `fix_eq`
- 모든 전고정점 아래에 있다는 `fix_least`
- 반복 근사의 성질을 극한으로 옮기는 Scott 귀납법(Scott induction)

## 핵심 아이디어

§2.2에서 `while b do c`의 뜻은 다음 방정식의 해여야 했지만, 해가 하나뿐이지는 않았다.

```
F(w) = fun σ => if ⟦b⟧ σ then ⟦c⟧ σ >>= w else some σ
```

해는 `F(w) = w`인 고정점이다. §2.3의 정보 순서에서 반복 근사의 극한을 취하면,
연속인 `F`에 대해 모든 고정점 아래에 있는 해를 얻는다.

`while`에서 `Fⁿ(⊥)`는 조건을 최대 `n`번 검사하도록 `n`단계 푼 근사다. 따라서 본체를
`n`번 미만 실행하고 끝나는 경우까지 답한다. 본체를 최대 `n`번 실행하고 끝나는 경우까지
포착하는 근사는 `Fⁿ⁺¹(⊥)`다.

## 읽는 순서
`Domain/FunctionSpace.lean` → 이 파일 → `Eval.lean`

## 책과의 차이

- `fix`는 단조 함수에도 정의하지만, 연속성을 가정한 `fix_eq`에서야 고정점임을 얻는다.
- Reynolds는 Scott 귀납법을 이 절에서 이름 붙여 제시하지 않는다. 이후 증명에 사용할
  반복 근사의 귀납 원리를 여기서 명시했다.
-/

@[expose] public section

namespace Reynolds.Exercises.Ch02

open Reynolds

universe u

variable {α : Type u} [PartialOrder α] [OrderBot α] [Predomain α]

/-! ## 1. 반복이 사슬을 이룬다

`F`가 단조라는 것만으로 충분하다. 첫 걸음 `⊥ ⊑ F(⊥)`는 `⊥`가 최소원이라 공짜이고,
그다음부터는 단조성이 걸음을 이어 준다. -/

omit [Predomain α] in
/-- 각 단계는 다음 단계 아래에 있다. `n`에 대한 귀납이고, 걸음마다 `F`를 한 번 입힌다. -/
theorem iterate_le_succ {F : α → α} (hF : Monotone F) (n : ℕ) :
    F^[n] ⊥ ≤ F^[n + 1] ⊥ := by
  induction n with
  | zero => exact bot_le
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact hF ih

/-- 반복의 사슬. `⊥ ⊑ F(⊥) ⊑ F(F(⊥)) ⊑ ⋯`. Reynolds 세 단계의 첫째다. -/
def iterChain {F : α → α} (hF : Monotone F) : Chain α :=
  ⟨fun n => F^[n] ⊥, monotone_nat_of_le_succ (iterate_le_succ hF)⟩

omit [Predomain α] in
/-- `iterChain`의 `n`번째 항은 정의대로 `Fⁿ(⊥)`다. -/
@[simp] theorem iterChain_seq {F : α → α} (hF : Monotone F) (n : ℕ) :
    (iterChain hF).seq n = F^[n] ⊥ := rfl

/-! ## 2. 극한이 고정점이다

연속성이 처음이자 마지막으로 쓰이는 자리다. §2.3에서 단조와 연속이 다르다는 것을
확인해 두었으므로, 여기서 연속을 요구하는 것이 공짜 가정이 아님을 안다.

증명의 모양: `F`를 사슬에 입히면 사슬이 한 칸 밀린다. 밀린 사슬의 극한은 원래 극한과
같다. 빠진 것은 맨 앞의 `⊥` 하나뿐이고, `⊥`는 극한에 아무 기여도 하지 않는다.
그러면 연속성이 `F(극한) = 밀린 사슬의 극한 = 극한`을 준다. -/

/--
반복 사슬의 극한 `⨆ₙ Fⁿ(⊥)`.

`hF`는 단조성만 주므로 이 정의만으로 고정점이라고 할 수는 없다. `F`가 연속이면
`fix_eq`가 고정점임을, `fix_least`가 모든 전고정점 아래에 있음을 보인다. 그 경우가
Reynolds의 `Y_D F`다.
-/
noncomputable def fix (F : α → α) (hF : Monotone F) : α := (iterChain hF).lub

/-- 밀린 사슬 `F(⊥), F²(⊥), …`의 극한도 `fix`다. 맨 앞의 `⊥`는 극한에 기여하지 않는다. -/
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

/--
**최소 고정점 정리, 둘째 단계 — 극한은 고정점이다.**

`F`의 연속성을 반복의 사슬에 적용하면 `F(fix)`가 "F를 입힌 사슬"의 극한이 된다.
그 사슬은 원래 사슬을 한 칸 민 것이고, 밀어도 극한은 그대로다. 극한의 유일성으로 끝난다.
-/
@[exercise "§2.4 fix-eq" 3]
theorem fix_eq {F : α → α} (hF : Continuous F) :
    F (fix F hF.monotone) = fix F hF.monotone := by
  -- 먼저 볼 것: 바로 위의 `isLUB_shifted`. 밀린 사슬의 극한도 `fix` 라는 사실이 완성되어 있다.
  -- 힌트 1: `hF (iterChain hF.monotone)`이 `F(fix)`를 "F를 입힌 상"의 극한으로 만든다.
  -- 힌트 2: 그 상이 밀린 사슬의 값들과 같음을 `ext`로 보여라.
  --         양방향 모두 `Function.iterate_succ_apply'` 하나로 잇는다.
  -- 힌트 3: 극한은 유일하다 — `IsLUB.unique`.
  sorry


/-! ## 3. 그 고정점이 최소다

사실 더 강하게 나온다. `F(x) ⊑ x`인 모든 `x` — 고정점이 아니라 **전고정점**(pre-fixed
point) — 위에서도 `fix`가 아래에 있다. 반복의 각 단계가 `x` 아래에 머무는 것을 귀납으로
확인하면 극한도 `x` 아래다. -/

/--
**최소 고정점 정리, 셋째 단계 — 전고정점 아래에 있다.**

`F(x) ⊑ x`이면 `fix ⊑ x`다. 특히 `F(x) = x`이면 `F(x) ⊑ x`이므로, `fix`는 모든
고정점 아래에 있다.

§2.2의 두 해로 돌아가면 `decrFake`도 풀기 방정식의 해이므로 `fix ⊑ decrFake`다.
구체적인 감소 반복문의 뜻이 `decrTrue`와 같다는 계산은 책의 연습 2.3에 해당한다.
-/
@[exercise "§2.4 fix-least" 2]
theorem fix_least {F : α → α} (hF : Monotone F) {x : α} (hx : F x ≤ x) :
    fix F hF ≤ x := by
  -- 힌트 1: `lub_le`로 "각 단계가 x 아래"로 줄인 뒤 `n`에 대한 귀납.
  -- 힌트 2: 걸음은 `Fⁿ⁺¹(⊥) = F(Fⁿ(⊥)) ⊑ F(x) ⊑ x`. `calc`로 쓰면 그대로 읽힌다.
  sorry


/-- 두 단계를 합친 진술. `fix`는 고정점이고, 모든 고정점 아래에 있다. -/
theorem fix_isLeast {F : α → α} (hF : Continuous F) {x : α} (hx : F x = x) :
    F (fix F hF.monotone) = fix F hF.monotone ∧ fix F hF.monotone ≤ x :=
  ⟨fix_eq hF, fix_least hF.monotone (le_of_eq hx)⟩

/-! ## 4. Scott 귀납법

반복 근사에서 `fix`로 성질을 옮기는 일반 원리다. `fix`는 극한이므로, 근사의 성질을
옮기려면 그 성질 자체가 극한을 통과해야 한다.

극한을 통과하는 성질을 **허용 가능(admissible)** 하다고 부른다. 세 가지를 확인하면
`P (fix F)`가 나온다.

1. `P ⊥` — 바닥에서 성립하고
2. `P x → P (F x)` — 걸음마다 보존되고
3. 사슬의 모든 항에서 성립하면 극한에서도 성립한다 (허용 가능성)

3은 자동으로 따라오지 않는다. `while x > 0 do x := x - 1`은 모든 정수 상태에서 끝나지만,
입력 전체에 통하는 반복 횟수 상한은 없다. 각 `n`에 대해 충분히 큰 `x`를 고르면 `Fⁿ(⊥)`는
그 상태에서 `⊥`이고, 극한은 모든 상태에서 값을 낸다. 따라서
`P(w) := ∃ σ, w σ = ⊥`는 각 근사에서 성립하지만 극한에서는 깨진다. 단계마다 증인 `σ`가
달라질 수 있는 이 존재 성질은 허용 가능하지 않으므로 Scott 귀납법에 쓸 수 없다.
-/

/--
**Scott 귀납법.** 허용 가능한 성질이 `⊥`에서 성립하고 `F`가 보존하면, `fix F`에서
성립한다.

증명은 두 단계다. 반복의 각 단계에서 성질이 성립함을 자연수 귀납으로 확인하고,
허용 가능성이 그것을 극한으로 넘긴다. 어려움은 "허용 가능한가"를 확인하는 쪽에
있다는 것이 이 원리의 특징이고, §2.5부터 그 확인이 실제 일이 된다.
-/
@[exercise "§2.4 scott" 2]
theorem scott_induction {F : α → α} (hF : Monotone F) {P : α → Prop}
    (hadm : ∀ c : Chain α, (∀ n, P (c.seq n)) → P c.lub)
    (hbot : P ⊥) (hstep : ∀ x, P x → P (F x)) : P (fix F hF) := by
  -- 힌트: 허용 가능성을 반복의 사슬에 적용하고, 각 단계는 `n` 에 대한 귀납으로.
  --       걸음에서 `Function.iterate_succ_apply'` 로 모양을 맞춘다.
  sorry


/-! ## 5. 여기서 어디로 가나

`Σ → Σ⊥`는 도메인이고 (§2.3), `while`의 함수 연산자 `F`는 그 위의 연속 함수다.
`Eval.lean`에서 연속성을 증명하면

```
⟦while b do c⟧ = fix F
```

로 정의할 수 있다. `fix_eq`는 풀기 방정식을, `fix_least`는 여러 해 중 최소인 해를 고른다는
사실을 준다. `Interpreter.lean`은 같은 유한 근사 관점을 연료 해석기로 구현하고, 그 실행
결과와 표시적 의미가 일치함을 증명한다. -/

end Reynolds.Exercises.Ch02
