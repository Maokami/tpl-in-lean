/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Exercises.Ch02.Ex.SubstWeak
-- `#guard`는 컴파일 시점에 계산한다 (AGENTS.md §10).
public meta import Reynolds.Exercises.Ch02.Interpreter
public meta import Reynolds.Answers.Ch02.Notation
public meta import Reynolds.Exercises.Ch02.Semantics
public meta import Reynolds.Prelude

/-!
# 연습 2.9 — 제어 변수가 구간 밖으로 나가지 않는 `for`

Reynolds 연습 2.9 에 대응한다.

## 문제

§2.6 의 판본 3 은 이렇게 돈다.

```
newvar w := e₁ in newvar v := e₀ in while v ≤ w do (c; v := v + 1)
```

마지막 바퀴가 끝나면 `v` 가 `e₁ + 1` 이 되고, 그 값으로 조건을 검사한 뒤 멈춘다.
**제어 변수가 상계를 한 칸 넘어선다.** 정수가 무한하면 아무 일도 아니지만, 고정폭
정수라면 `e₁` 이 최댓값일 때 넘침이 난다. 넘지 않는 판본을 설계하는 것이 이 연습이다.

## 설계

상계에 **닿기 전까지만** 돌고, 마지막 한 번을 밖에서 돌린다.

```
newvar w := e₁ in newvar v := e₀ in
  if v ≤ w then (while v < w do (c; v := v + 1); c) else skip
```

`v` 는 `e₀` 에서 `e₁` 까지만 올라간다. 마지막 증가가 `v` 를 `e₁` 로 만들면 조건
`v < w` 가 거짓이 되어 루프가 끝나고, 본문이 `v = e₁` 에서 한 번 더 돈다.
구간이 비면(`e₀ > e₁`) `skip` 이라 본문이 한 번도 안 돈다.

## 그런데 두 판본은 **뜻이 같다**

이 연습의 진짜 교훈이 여기 있다. 넘어선 값 `e₁ + 1` 은 마지막 본문 실행 **뒤**에만
나타나고, 제어 변수는 `newvar` 안에 있어 밖에서 복원된다. 그래서

```
⟦판본 3⟧ = ⟦판본 4⟧
```

이고, 둘을 **구별할 문맥이 없다.** §2.8 의 말로 하면, 넘침은 우리가 관찰하기로 한
것 바깥의 일이다 — 중간 상태도, 정수의 표현도 보지 않기로 했기 때문이다.

> 그러므로 판본 4 를 고를 이유는 의미론이 아니라 **구현**이다. 의미론이 같다고
> 말해 주는 것과, 그래서 아무래도 좋다는 것은 다르다.

## 증명의 재료

- **보조정리 A** — `<` 판 루프도 정확히 센다. §2.6 의 `forWhile_eq_fold` 와 같은 측도
  귀납이고 측도가 `(σ w - σ v).toNat` 로 하나 줄었다.
- **보조정리 B** — `forFold` 를 **뒤에서** 한 겹 푼다. 판본 3 의 마지막 바퀴를 떼어
  내어 판본 4 의 "루프 뒤 한 번" 과 맞춘다.
- 남는 차이는 마지막 증가 하나뿐이고, `restore` 가 그것을 지운다.

## 읽는 순서
`Ex/SubstWeak.lean` 다음. §2.6 의 `forV3_eq_fold` 와 `forFold` 가 재료다.
-/

-- 두 판본이 같은 답을 낸다는 것을 `#guard` 로도 본다.
set_option linter.hashCommand false

@[expose] public section

namespace Reynolds.Exercises.Ch02.Ex

open Reynolds Reynolds.Answers.Ch01 Reynolds.Exercises.Ch02

universe u

variable {V : Type u} [DecidableEq V]

/-! ## 1. 재료 두 개 -/

/-- `while v < w do (c; v := v+1)` — 상계에 **닿기 전까지만** 돈다. -/
def forWhileLt (v w : V) (c : Comm V) : Comm V :=
  .wh (.cmp .lt (.var v) (.var w)) (forBody v c)

/--
**보조정리 A.** `<` 판 루프도 정확히 센다.

§2.6 의 `forWhile_eq_fold` 와 같은 측도 귀납이다. 측도가 `(σ w - σ v).toNat` 로 하나
줄었는데, 상계에 닿으면 멈추므로 한 바퀴를 덜 도는 것이 그대로 나타난다.
-/
theorem forWhileLt_eq_fold (v w : V) (c : Comm V)
    (hv : v ∉ c.fa) (hw : w ∉ c.fa) (hvw : v ≠ w) :
    ∀ (m : Nat) (σ : State V), (σ w - σ v).toNat = m →
      (forWhileLt v w c).eval σ = forFold v c m σ := by
  have hwv : w ≠ v := Ne.symm hvw
  have whileEq : ∀ σ : State V, (forWhileLt v w c).eval σ
      = if ⟦(.cmp .lt (.var v) (.var w) : BoolExp V)⟧ᵇ σ
        then Option.bind ((forBody v c).eval σ) (forWhileLt v w c).eval
        else some σ := fun σ => Comm.eval_isSemantics.2.2.2.2.1 _ _ σ
  have hBeval : ∀ σ : State V,
      ⟦(.cmp .lt (.var v) (.var w) : BoolExp V)⟧ᵇ σ = decide (σ v < σ w) := fun _ => rfl
  have bodyEq : ∀ σ : State V, (forBody v c).eval σ
      = Option.bind (c.eval σ) (fun σ'' => some (σ''[v := σ'' v + 1])) := fun _ => rfl
  intro m
  induction m with
  | zero =>
      intro σ hm
      have hge : ¬ (σ v < σ w) := by omega
      rw [whileEq σ, hBeval σ, if_neg (by simp [hge])]
      rfl
  | succ n ih =>
      intro σ hm
      have hlt : σ v < σ w := by omega
      rw [whileEq σ, hBeval σ, if_pos (by simp [hlt]), bodyEq σ, forFold]
      cases hc : c.eval σ with
      | none => rfl
      | some σ'' =>
          have hv'' : σ'' v = σ v := Comm.eval_agree_outside_fa c σ σ'' hc v hv
          have hw'' : σ'' w = σ w := Comm.eval_agree_outside_fa c σ σ'' hc w hw
          have hnext : ((σ''[v := σ'' v + 1]) w - (σ''[v := σ'' v + 1]) v).toNat = n := by
            rw [State.subst_self, State.subst_of_ne _ _ _ _ hwv, hv'', hw'']
            omega
          exact ih (σ''[v := σ'' v + 1]) hnext

/--
**보조정리 B.** `forFold` 를 **뒤에서** 한 겹 푼다.

정의는 앞에서 푼다 — "본문 한 번, 증가 한 번, 그리고 나머지". 여기서는 반대로 읽는다:
"나머지를 다 돌고, 본문 한 번, 증가 한 번". 판본 4 가 루프를 끝낸 뒤 본문을 한 번 더
도는 모양과 맞추려면 이 방향이 필요하다.
-/
theorem forFold_succ_back (v : V) (c : Comm V) :
    ∀ (n : Nat) (σ : State V), forFold v c (n + 1) σ
      = Option.bind (Option.bind (forFold v c n σ) c.eval)
          (fun τ => some (τ[v := τ v + 1])) := by
  intro n
  induction n with
  | zero => intro σ; rfl
  | succ n ih =>
      intro σ
      rw [forFold]
      rcases hc : c.eval σ with _ | σ'
      · simp [forFold, hc]
      · change forFold v c (n + 1) (σ'[v := σ' v + 1]) = _
        rw [ih (σ'[v := σ' v + 1]), forFold, hc]
        rfl

/-- 복원이 마지막 증가를 지운다. 두 판본의 유일한 차이가 여기서 사라진다. -/
theorem restore_bind_incr (v : V) (σ₁ : State V) (X : SigmaBot V) :
    restore v σ₁ (Option.bind X (fun τ => some (τ[v := τ v + 1]))) = restore v σ₁ X := by
  cases X with
  | none => rfl
  | some τ => simp [restore, State.subst_def, Function.update_idem]

/-! ## 2. 판본 4 -/

/--
**연습 2.9 의 답.** 제어 변수가 `[e₀, e₁]` 밖으로 나가지 않는 `for`.

상계에 닿기 전까지만 돌고 마지막 한 번을 루프 밖에서 돌린다. 구간이 비면 `skip` 이다.
-/
def forV4 (v w : V) (e₀ e₁ : IntExp V) (c : Comm V) : Comm V :=
  .newvar w e₁ (.newvar v e₀
    (.ite (.cmp .le (.var v) (.var w)) (.seq (forWhileLt v w c) c) .skip))

-- 두 판본이 같은 답을 낸다. 1 부터 3 까지 더하면 6.
#guard ((forV3 "i" "hi" (.num 1) (.num 3) (.assign "s" (.bin .add (.var "s") (.var "i")))).run
          20 (State.const 0)).map (fun σ => σ "s") == some 6
#guard ((forV4 "i" "hi" (.num 1) (.num 3) (.assign "s" (.bin .add (.var "s") (.var "i")))).run
          20 (State.const 0)).map (fun σ => σ "s") == some 6

-- 구간이 비면 둘 다 본문을 한 번도 안 돈다.
#guard ((forV4 "i" "hi" (.num 5) (.num 3) (.assign "s" (.bin .add (.var "s") (.num 1)))).run
          20 (State.const 0)).map (fun σ => σ "s") == some 0

/-! ## 3. 두 판본의 뜻이 같다 -/

/--
**연습 2.9 — 판본 4 는 판본 3 과 뜻이 같다.**

넘어선 값 `e₁ + 1` 은 마지막 본문 실행 **뒤**에만 나타나고, 제어 변수는 `newvar` 안에
있어 복원된다. 그래서 **두 판본을 구별할 문맥이 없다** — §2.8 의 말로 하면 넘침은
우리가 관찰하기로 한 것 바깥의 일이다.

증명은 세 조각이다.

1. 구간이 차 있으면(`⟦e₀⟧ ≤ ⟦e₁⟧`) 보조정리 A 로 루프가 `(b - a).toNat` 번 돌고,
   그 뒤 본문이 한 번 더 돈다.
2. 판본 3 은 `(b - a + 1).toNat` 번 도는데, 보조정리 B 로 마지막 바퀴를 떼어 내면
   똑같은 모양이 된다. 남는 차이는 **마지막 증가 하나**뿐이다.
3. `restore` 가 그 증가를 지운다.

구간이 비면 양쪽 다 본문을 한 번도 안 돈다.

> 그러므로 판본 4 를 고를 이유는 의미론이 아니라 구현이다. 의미론이 같다고 말해 주는
> 것과, 그래서 아무래도 좋다는 것은 다르다.
-/
@[exercise "Ex 2.9" 3]
theorem forV4_eval_eq_forV3 (v w : V) (e₀ e₁ : IntExp V) (c : Comm V)
    (hv : v ∉ c.fa) (hw : w ∉ c.fa) (hvw : v ≠ w) (hwe₀ : w ∉ e₀.fv) (σ : State V) :
    (forV4 v w e₀ e₁ c).eval σ = (forV3 v w e₀ e₁ c).eval σ := by
  -- 먼저 볼 것: 바로 위 보조정리 셋(`forWhileLt_eq_fold`, `forFold_succ_back`,
  --            `restore_bind_incr`)과 §2.6 의 `forV3_eq_fold`.
  -- 힌트 1: 오른쪽은 `forV3_eq_fold` 가 이미 푼다. 왼쪽의 `newvar` 두 겹을
  --         `Comm.eval_isSemantics.2.2.2.2.2` 로 펴고 `w ∉ FV(e₀)` 로 초기값을 맞춘다.
  -- 힌트 2: 안쪽 상태에서 `v` 는 `⟦e₀⟧σ`, `w` 는 `⟦e₁⟧σ` 다
  --         (`State.subst_self`, `State.subst_of_ne`). 조건이 `⟦e₀⟧σ ≤ ⟦e₁⟧σ` 로 읽힌다.
  -- 힌트 3: 구간이 차 있으면 보조정리 A 가 루프를 `(b-a).toNat` 번으로 세고,
  --         보조정리 B 가 판본 3 의 마지막 바퀴를 떼어 내어 모양을 맞춘다.
  --         `(b-a).toNat + 1 = (b-a+1).toNat` 은 `omega` 다.
  -- 힌트 4: 남는 차이는 **마지막 증가 하나**뿐이고 `restore_bind_incr` 이 그것을 지운다.
  -- 힌트 5: 구간이 비면 `(b-a+1).toNat = 0` 이라 양쪽 다 본문을 안 돈다.
  sorry


/-! ## 여기서 어디로 가나

남은 것은 연습 2.10 이다 — `dotwice` 의 디슈가링이 왜 유효한가. 앞의 연습들과 결이
전혀 다르다. 명령 하나의 뜻이 아니라 **디슈가링 함수 자체가 잘 정의되는가** 를 묻는
메타 수준의 물음이고, Lean 에서는 그 답이 종료 증명이다. -/

end Reynolds.Exercises.Ch02.Ex
