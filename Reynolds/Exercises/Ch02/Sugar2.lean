/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Exercises.Ch02.Sugar
-- `#guard`는 컴파일 시점에 계산한다 (AGENTS.md §10).
public meta import Reynolds.Exercises.Ch02.Sugar
public meta import Reynolds.Exercises.Ch02.Interpreter
public meta import Reynolds.Answers.Ch02.Notation
public meta import Reynolds.Exercises.Ch02.Semantics
public meta import Reynolds.Prelude

/-!
# §2.6 문법 설탕 (2) — 판본 3 이 정확히 구간 크기만큼 돈다

`Sugar.lean` 이 전반부다. 거기서 `for` 의 세 판본과 두 결함(제어 변수 누수, 상한
재평가)을 막았고, 마지막 결함 하나가 남았다.

## 남은 결함과 그 해법

본문 `c` 가 제어 변수 `v` 를 바꾸면 루프가 연속된 값으로 돌지 않는다. Reynolds 의 예:

```
for x := 1 to 10 do (c'; x := 2 × x)
```

`x` 는 1 → 3 → 7 → 15 로 뛰고, `c'` 는 열 번이 아니라 세 번만 실행된다. 구문을 더
고쳐서 막을 수 있는 종류가 아니다 — 본문이 무엇을 하는지는 구문이 통제할 수 없다.
그래서 **제약**으로 막는다: `v ∉ FA(c)`.

§2.5 에서 만든 `FA` 가 여기서 값을 한다. "본문이 제어 변수에 대입하지 않는다" 를
문장으로 쓸 수 있어야 이 제약을 정리의 가정으로 올릴 수 있다.

## 정확 반복 정리

제약이 있으면 판본 3 이 정확히 `e₁ - e₀ + 1` 번 돈다는 것을 증명한다. "정확히 몇 번"
을 말하려면 비교 대상이 있어야 하므로, 기준(reference)이 되는 함수 `forFold` 를 둔다 —
본문을 `n` 번 돌리며 매번 제어 변수를 한 칸 올리는, 반복 횟수가 **눈에 보이는** 함수다.
그러면 정리는 이렇게 읽힌다.

```
⟦while v ≤ w do (c; v := v+1)⟧ σ = forFold v c (σ w - σ v + 1).toNat σ
```

오른쪽의 `(σ w - σ v + 1).toNat` 이 곧 반복 횟수이고, 그것이 구간 크기다.
`σ v > σ w` 면 `0` 이므로 "빈 구간이면 한 번도 안 돈다" 도 같은 식에 들어 있다.

증명은 그 횟수에 대한 귀납이다. 한 바퀴를 돌면 `v` 가 하나 늘고 `w` 는 그대로이므로
(여기서 `v, w ∉ FA(c)` 가 쓰인다 — 명제 2.6(b)) 측도가 정확히 하나 줄어든다.

## 읽는 순서
`Sugar.lean` → 이 파일. 이후는 §2.7 (산술 오류).
-/

-- 이 파일의 `#guard` 가 제약이 있을 때와 없을 때의 차이를 보여 준다.
set_option linter.hashCommand false

@[expose] public section

namespace Reynolds.Exercises.Ch02

open Reynolds Reynolds.Exercises.Ch01

universe u

variable {V : Type u} [DecidableEq V]

/-! ## 1. 기준 함수 — 반복 횟수가 눈에 보이는 판

`forFold v c n σ` 는 본문 `c` 를 **정확히 `n` 번** 돌린다. 한 바퀴마다 `c` 를 실행하고
제어 변수를 한 칸 올린다. `n` 이 인자로 드러나 있으므로, 이 함수와 같다는 말이 곧
"몇 번 도는지" 에 대한 진술이 된다. -/

/--
본문 `c` 를 `n` 번 돌리며 매번 `v` 를 한 칸 올린다. 판본 3 의 기준(reference).

`while` 이 아니라 `Nat` 에 대한 구조적 재귀라서 반복 횟수가 정의에 박혀 있다.
`Comm.eval` 을 쓰므로 계산되지는 않는다.
-/
noncomputable def forFold (v : V) (c : Comm V) : Nat → State V → SigmaBot V
  | 0,     σ => some σ
  | n + 1, σ => Option.bind (c.eval σ) (fun σ' => forFold v c n (σ'[v := σ' v + 1]))

/-! ## 2. 정확 반복 정리

판본 3 의 안쪽 while 이 기준 함수와 같다. 반복 횟수는 `(σ w - σ v + 1).toNat` —
`v` 가 `w` 를 넘었으면 `0` 이다. -/

/--
**정확 반복 정리.** 본문이 제어 변수 `v` 와 상한 변수 `w` 중 어느 것에도 대입하지
않으면, `while v ≤ w do (c; v := v+1)` 은 본문을 정확히 `(σ w - σ v + 1).toNat` 번
돌린다.

가정 셋이 각각 하는 일이 다르다.

- `v ∉ FA(c)` — 한 바퀴를 돌 때 `v` 가 **정확히 하나만** 는다는 것을 보장한다.
  본문이 `v` 를 건드리면 측도가 하나씩 줄지 않아 귀납이 무너진다. 이것이 막으려던
  마지막 결함이다.
- `w ∉ FA(c)` — 상한이 루프 도중 움직이지 않게 한다. 판본 2 에서 상한 재평가로 겪은
  것을, 판본 3 은 `w` 에 얼려 두고 이 가정으로 지킨다.
- `v ≠ w` — 제어 변수와 상한 변수가 같은 칸을 쓰면 증가가 상한도 밀어 올린다.

증명은 반복 횟수 `m` 에 대한 귀납이다. 한 바퀴 돌면 `v` 는 `σ v + 1`, `w` 는 그대로
(둘 다 명제 2.6(b) `eval_agree_outside_fa` 로 얻는다)이므로 측도가 정확히 하나 준다.
-/
@[exercise "§2.6 for-exact" 3]
theorem forWhile_eq_fold (v w : V) (c : Comm V)
    (hv : v ∉ c.fa) (hw : w ∉ c.fa) (hvw : v ≠ w) :
    ∀ (m : Nat) (σ : State V), (σ w - σ v + 1).toNat = m →
      (forWhile v (.var w) c).eval σ = forFold v c m σ := by
  -- 먼저 볼 것: `Comm.eval_isSemantics` 의 `wh` 절과 `Comm.eval_agree_outside_fa` (명제 2.6(b)).
  -- 힌트 1: 보조 등식 셋을 `have` 로 깔아 두면 본 증명이 짧아진다. 셋 다 `rfl` 로 된다.
  --         (a) while 한 바퀴 펼치기 — `Comm.eval_isSemantics.2.2.2.2.1 _ _ σ`
  --         (b) 조건의 값 — `⟦cmp le (var v) (var w)⟧ᵇ σ = decide (σ v ≤ σ w)`
  --         (c) 본체 — `⟦forBody v c⟧ᶜ σ = Option.bind (⟦c⟧ᶜ σ) fun σ'' => some σ''[v := σ'' v + 1]`
  -- 힌트 2: `m` 에 대한 귀납. `σ` 는 `intro m` 뒤에 남겨 두어야 귀납 가설이 다음 상태에 쓰인다.
  -- 힌트 3: `if` 는 `if_pos`/`if_neg` 로 가른다. 조건이 `decide _ = true` 꼴이라
  --         `(by simp [hle])` / `(by simp [hgt])` 로 증거를 만든다. 두 부등식은 `omega`.
  -- 힌트 4: 한 바퀴 뒤 `σ'' v = σ v` 와 `σ'' w = σ w` 를 `eval_agree_outside_fa` 로 얻고,
  --         다음 상태의 측도가 `n` 임을 `State.subst_self` · `State.subst_of_ne` · `omega` 로 보인다.
  sorry


/-! ## 3. 판본 3 전체로 올리기

안쪽 while 의 결과를 `newvar` 두 겹이 감싼다. 상한 변수 `w` 가 초기값 식 `e₀` 에
나오지 않아야(`w ∉ FV(e₀)`) `w` 를 먼저 깔아도 `e₀` 의 값이 변하지 않는다 — 판본 3 이
`w` 를 신선하게 골라야 하는 이유가 여기서 가정으로 드러난다. -/

/--
**판본 3 의 정확 반복.** 제약 아래에서 `for v := e₀ to e₁ do c` 는 본문을 정확히
`(⟦e₁⟧ - ⟦e₀⟧ + 1).toNat` 번 돌리고, 두 제어 변수를 원래대로 되돌린다.

오른쪽의 `forFold` 에 그 횟수가 인자로 적혀 있다 — 이것이 "반복 횟수가 구간 크기와
같다" 의 형식화다. 구간이 비었으면(`⟦e₀⟧ > ⟦e₁⟧`) 횟수가 `0` 이고 본문은 한 번도
실행되지 않는다.

채점 연습이 아니다. `forWhile_eq_fold` 가 이미 연습이라 비우면 비운 것끼리 의존한다
(연습 독립성 원칙, `AGENTS.md` §1-9).
-/
theorem forV3_eq_fold (v w : V) (e₀ e₁ : IntExp V) (c : Comm V)
    (hv : v ∉ c.fa) (hw : w ∉ c.fa) (hvw : v ≠ w) (hwe₀ : w ∉ e₀.fv) (σ : State V) :
    (forV3 v w e₀ e₁ c).eval σ
      = restore w σ (restore v (σ[w := ⟦e₁⟧ₑ σ])
          (forFold v c (⟦e₁⟧ₑ σ - ⟦e₀⟧ₑ σ + 1).toNat
            ((σ[w := ⟦e₁⟧ₑ σ])[v := ⟦e₀⟧ₑ σ]))) := by
  have hwv : w ≠ v := Ne.symm hvw
  -- `w` 를 깔아도 초기값 식의 값은 그대로다.
  have ha : ⟦e₀⟧ₑ (σ[w := ⟦e₁⟧ₑ σ]) = ⟦e₀⟧ₑ σ := by
    refine coincidence_intExp e₀ _ σ ?_
    intro u hu
    have hune : u ≠ w := fun h => hwe₀ (h ▸ hu)
    exact State.subst_of_ne _ _ _ _ hune
  -- 바깥 `newvar w`, 안쪽 `newvar v` 를 차례로 편다.
  have e1 : (forV3 v w e₀ e₁ c).eval σ
      = restore w σ ((Comm.newvar v e₀ (forWhile v (.var w) c)).eval (σ[w := ⟦e₁⟧ₑ σ])) :=
    Comm.eval_isSemantics.2.2.2.2.2 _ _ _ _
  have e2 : (Comm.newvar v e₀ (forWhile v (.var w) c)).eval (σ[w := ⟦e₁⟧ₑ σ])
      = restore v (σ[w := ⟦e₁⟧ₑ σ])
          ((forWhile v (.var w) c).eval ((σ[w := ⟦e₁⟧ₑ σ])[v := ⟦e₀⟧ₑ (σ[w := ⟦e₁⟧ₑ σ])])) :=
    Comm.eval_isSemantics.2.2.2.2.2 _ _ _ _
  -- 안쪽 while 에 정확 반복 정리를 쓴다. 측도가 구간 크기다.
  have hinner : (forWhile v (.var w) c).eval ((σ[w := ⟦e₁⟧ₑ σ])[v := ⟦e₀⟧ₑ σ])
      = forFold v c (⟦e₁⟧ₑ σ - ⟦e₀⟧ₑ σ + 1).toNat
          ((σ[w := ⟦e₁⟧ₑ σ])[v := ⟦e₀⟧ₑ σ]) := by
    refine forWhile_eq_fold v w c hv hw hvw _ _ ?_
    rw [State.subst_self, State.subst_of_ne _ _ _ _ hwv, State.subst_self]
  rw [e1, e2, ha, hinner]

/-! ## 4. 제약이 없으면 무너진다

가정 `v ∉ FA(c)` 가 장식이 아님을 확인한다. 본문이 제어 변수를 두 배로 만들면
반복 횟수가 구간 크기와 달라진다. -/

/-- 제어 변수 `i` 자신에 대입하는 본문. `s` 는 실행 횟수를 센다. -/
def doublingBody : Comm String := ⟪ s := s + 1; i := 2 × i ⟫ᶜ

/-- 제어 변수에 대입하지 않는 본문. 같은 자리에서 비교하려고 둔다. -/
def countingBody : Comm String := ⟪ s := s + 1 ⟫ᶜ

-- 제약을 지키는 본문: 구간 [1,3] 을 세 번 돈다.
#guard ((forV3 "i" "hi" (.num 1) (.num 3) countingBody).run 8 (State.const 0)).map
        (fun σ => σ "s") == some 3

-- 제약을 어기는 본문: 같은 구간인데 두 번만 돈다. i 가 1 → 3 → 7 로 뛴다.
#guard ((forV3 "i" "hi" (.num 1) (.num 3) doublingBody).run 8 (State.const 0)).map
        (fun σ => σ "s") == some 2

/--
**제약을 어기면 반복 횟수가 구간 크기와 다르다.**

`for i := 1 to 3 do (s := s+1; i := 2×i)` 에서 `i` 는 1 → 3 → 7 로 뛴다. 구간 [1,3] 의
크기는 3 인데 본문은 두 번만 실행된다. 정확 반복 정리의 `v ∉ FA(c)` 가 바로 이것을
막는 가정이고, 여기서는 그 가정이 깨져 있다 (`"i" ∈ doublingBody.fa`).

`while` 이 있으므로 `run` 으로 계산한 뒤 `run_sound` 로 표시적 의미에 옮긴다.
결과 상태를 손으로 적지 않으려고 `Option.map` 으로 `s` 만 뽑아 본다.
-/
@[exercise "§2.6 for-broken" 2]
theorem forV3_broken_by_assigning_control :
    "i" ∈ doublingBody.fa ∧
      ∃ τ, (forV3 "i" "hi" (.num 1) (.num 3) doublingBody).eval (State.const 0) = some τ
        ∧ τ "s" = 2 := by
  -- 힌트 1: 첫 성분은 `simp [doublingBody, Comm.fa]`.
  -- 힌트 2: 둘째 성분은 연료 8 로 실행한 뒤 `Comm.run_sound` 로 옮긴다.
  --         결과 상태를 손으로 적지 않으려면 `Option.map` 으로 `s` 만 뽑아
  --         `(run 8 _).map (fun σ => σ "s") = some 2` 를 `simp [...]` 로 계산하고,
  --         `Option.map_eq_some_iff` 로 상태를 되찾는다.
  -- 힌트 3: simp 인자에 `forV3, forWhile, forBody, incr, doublingBody, Comm.run, restore,`
  --         `BoolExp.eval, IntExp.eval, IntOp.denote, Cmp.denoteBool, State.const` 를 준다.
  sorry


/-! ## 5. 여기서 어디로 가나

§2.6 이 닫혔다. `for` 는 새 구문이 아니라 번역이고, 그 번역을 세 번 고쳐서야 쓸 만해
졌다 — 제어 변수를 감추고(`newvar`), 상한을 얼리고(`w`), 본문에 제약을 걸었다
(`v ∉ FA(c)`). 앞의 둘은 구문으로 막았고 마지막 하나는 구문으로 막을 수 없어 가정이
되었다는 것이 이 절의 마지막 교훈이다.

다음은 §2.7 이다. 0 으로 나누기 같은 산술 오류를 어떻게 다룰지 — 검사하지 않기로 한
연산도 입력마다 결과 하나를 주는 전함수여야 한다는 요구가, 어떤 등식이 그 선택을
실제로 관찰하는지로 갈린다. -/

end Reynolds.Exercises.Ch02
