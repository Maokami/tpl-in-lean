/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Answers.Ch02.FullAbstraction
-- `#guard`는 컴파일 시점에 계산한다 (AGENTS.md §10).
public meta import Reynolds.Answers.Ch02.Interpreter
public meta import Reynolds.Answers.Ch02.Notation
public meta import Reynolds.Answers.Ch02.Semantics
public meta import Reynolds.Prelude

/-!
# §2.8 건전성과 완전 추상성 (2) — 무엇을 관찰하기로 했는가

`FullAbstraction.lean` 이 전반부다. 거기서 `⟦-⟧` 가 건전하고 완전 추상임을 보였다.
그런데 그 답 전체가 **무엇을 관찰하기로 했는가** 에 매달려 있다. 이 파일은 그 의존을
눈에 보이게 만든다.

## 우리 의미론이 같다고 보는 것들

세 쌍을 증명한다. 셋 다 "뜻이 같다" 이므로 §2.8 전반부의 건전성에 의해 **어떤 문맥에서도**
구별되지 않는다.

```
x := x+1; x := x+1                ≡  x := x+2
x := 0; while x < 100 do x := x+1 ≡  x := 100
x := x+1; y := y×2                ≡  y := y×2; x := x+1
```

두 번째가 특별하다. 왼쪽은 백 번 도는 반복이고 오른쪽은 대입 하나인데 뜻이 같다 —
최소 고정점을 실제로 계산해야 나오는 등식이다. §2.6 의 정확 반복 정리와 같은 기법
(측도에 대한 귀납)을 쓴다.

## 그런데 관찰을 바꾸면 무너진다

세 등식이 성립하는 것은 우리가 **최종 상태만** 보기로 했기 때문이다. 관찰을 늘리면
같은 쌍이 갈라진다.

- **실행 시간** — 두 번째 쌍은 한쪽이 백 번 돌고 한쪽이 한 번에 끝난다. "몇 걸음 안에
  끝나는가" 를 관찰에 넣으면 건전성이 곧바로 깨진다. 아래에서 정리로 증명한다.
- **별칭** (13장) — 세 번째 쌍은 `x` 와 `y` 가 **다른 칸**이라는 데 기대고 있다.
  프로시저 호출이 둘을 같은 칸으로 묶으면 갈라진다. §2.5 의 치환으로 그 상황을 만들어
  정리로 증명한다.
- **병행 합성** (8장) — `c₀ ∥ c₁` 이 생기면 문맥이 늘어난다. 다른 스레드가 중간 상태를
  들여다볼 수 있으므로 세 쌍이 **모두** 갈라진다. 그때는 다른 의미론으로 갈아타야 한다.

## 읽는 순서
`FullAbstraction.lean` → 이 파일. 2장의 마지막이다.
-/

-- 이 파일의 `#guard` 가 반복이 실제로 백 번 도는 것을 보여 준다.
set_option linter.hashCommand false

@[expose] public section

namespace Reynolds.Answers.Ch02

open Reynolds Reynolds.Answers.Ch01

/-! ## 1. 예제 프로그램

셋 다 `String` 을 변수로 쓴다. 구체적인 프로그램이라야 "실제로 이만큼 돈다" 를 말할 수
있기 때문이다. -/

/-- `x := x+1; x := x+1` -/
def incTwice : Comm String := ⟪ x := x + 1; x := x + 1 ⟫ᶜ

/-- `x := x+2` -/
def incByTwo : Comm String := ⟪ x := x + 2 ⟫ᶜ

/-- `while x < 100 do x := x+1` — 두 번째 쌍의 반복 부분. -/
def countLoop : Comm String := ⟪ while x < 100 do x := x + 1 ⟫ᶜ

/-- `x := 0; while x < 100 do x := x+1` -/
def countTo100 : Comm String := ⟪ x := 0; while x < 100 do x := x + 1 ⟫ᶜ

/-- `x := 100` -/
def setTo100 : Comm String := ⟪ x := 100 ⟫ᶜ

/-- `x := x+1; y := y×2` -/
def incThenDouble : Comm String := ⟪ x := x + 1; y := y × 2 ⟫ᶜ

/-- `y := y×2; x := x+1` -/
def doubleThenInc : Comm String := ⟪ y := y × 2; x := x + 1 ⟫ᶜ

-- 반복은 실제로 백 번 돈다. 연료가 모자라면 `none` 이다.
#guard (countTo100.run 100 (State.const 0)).isNone
#guard (countTo100.run 102 (State.const 0)).map (fun σ => σ "x") == some 100

/-! ## 2. 첫째 쌍 — 대입 두 번은 대입 한 번이다

`while` 이 없으므로 의미 방정식만으로 끝까지 계산된다. 같은 자리에 두 번 대입한 것이
한 번 대입한 것과 같다는 `Function.update_idem` 이 핵심이다. -/

-- ANCHOR: obsEq1
/--
**`x := x+1; x := x+1 ≡ x := x+2`.**

왼쪽은 `x` 를 두 번 덮어쓴다. 두 번째 대입이 읽는 `x` 는 이미 한 번 올라간 값이므로
`σ x + 1 + 1` 이고, 앞의 대입은 덮어써져 사라진다.
-/
@[exercise "§2.8 obs-eq-inc" 1]
theorem incTwice_eq_incByTwo : incTwice.eval = incByTwo.eval := by
  funext σ
  change some ((σ["x" := σ "x" + 1])["x" := (σ["x" := σ "x" + 1]) "x" + 1])
      = some (σ["x" := σ "x" + 2])
  rw [State.subst_self]
  simp only [State.subst_def, Function.update_idem]
  norm_num [add_assoc]
-- ANCHOR_END: obsEq1

/-! ## 3. 둘째 쌍 — 백 번 도는 반복이 대입 하나다

이 절에서 가장 손이 많이 가는 자리다. `while` 의 뜻은 최소 고정점이므로, 그것이 구체적인
값이라고 말하려면 실제로 계산해야 한다.

기법은 §2.6 의 정확 반복 정리와 같다 — 남은 반복 횟수를 측도로 삼아 귀납한다. 여기서는
측도가 `(100 - σ x).toNat` 이다. 한 바퀴 돌면 `x` 가 하나 늘어 측도가 정확히 하나 준다. -/

-- ANCHOR: loopEval
/--
**반복의 최소 고정점을 계산한다.** `x ≤ 100` 인 상태에서 출발하면 `x = 100` 으로 끝난다.

`while` 의 뜻을 구체적으로 계산해 내는 첫 자리다. §2.4 에서 `fix` 로 정의만 해 두었던
것이, 측도에 대한 귀납으로 닫힌 꼴을 얻는다.

증명의 뼈대는 §2.6 의 `forWhile_eq_fold` 와 같다.

1. `while` 한 바퀴를 펼치는 방정식을 `Comm.eval_isSemantics` 에서 꺼낸다.
2. 남은 횟수 `(100 - τ x).toNat` 에 대해 귀납한다.
3. 0 이면 `τ x = 100` 이라 조건이 거짓이고, 상태가 그대로다.
4. 아니면 한 바퀴 돌아 `x` 가 하나 늘고 측도가 하나 준다.
-/
@[exercise "§2.8 loop-eval" 3]
theorem countLoop_eval (σ : State String) (h : σ "x" ≤ 100) :
    countLoop.eval σ = some (σ["x" := (100 : Int)]) := by
  have whileEq : ∀ τ : State String, countLoop.eval τ
      = if ⟦(.cmp .lt (.var "x") (.num 100) : BoolExp String)⟧ᵇ τ
        then Option.bind ((Comm.assign "x" (.bin .add (.var "x") (.num 1))).eval τ) countLoop.eval
        else some τ := fun τ => Comm.eval_isSemantics.2.2.2.2.1 _ _ τ
  have hB : ∀ τ : State String,
      ⟦(.cmp .lt (.var "x") (.num 100) : BoolExp String)⟧ᵇ τ = decide (τ "x" < 100) :=
    fun _ => rfl
  have key : ∀ (m : Nat) (τ : State String), (100 - τ "x").toNat = m → τ "x" ≤ 100 →
      countLoop.eval τ = some (τ["x" := (100 : Int)]) := by
    intro m
    induction m with
    | zero =>
        -- 남은 횟수가 0 이면 이미 `x = 100` 이다. 조건이 거짓이라 그대로 끝난다.
        intro τ hm hle
        have heq : τ "x" = 100 := by omega
        rw [whileEq τ, hB τ, if_neg (by simp; omega), ← heq]
        simp [State.subst_def, Function.update_eq_self]
    | succ n ih =>
        -- 한 바퀴 돌면 `x` 가 하나 늘고 측도가 하나 준다.
        intro τ hm hle
        have hlt : τ "x" < 100 := by omega
        rw [whileEq τ, hB τ, if_pos (by simp [hlt])]
        have hbody : (Comm.assign "x" (.bin .add (.var "x") (.num 1))).eval τ
            = some (τ["x" := τ "x" + 1]) := rfl
        rw [hbody]
        have hnext : (100 - (τ["x" := τ "x" + 1]) "x").toNat = n := by
          rw [State.subst_self]; omega
        have hih := ih (τ["x" := τ "x" + 1]) hnext (by rw [State.subst_self]; omega)
        change countLoop.eval (τ["x" := τ "x" + 1]) = some (τ["x" := (100 : Int)])
        rw [hih]
        simp [State.subst_def, Function.update_idem]
  exact key _ σ rfl h
-- ANCHOR_END: loopEval

/--
**`x := 0; while x < 100 do x := x+1 ≡ x := 100`.**

`x := 0` 이 초기 상태를 만들고, 거기서 `countLoop_eval` 이 닫힌 꼴을 준다.
백 번 도는 반복과 대입 하나가 **뜻으로는 같다** — 우리가 최종 상태만 보기로 했기
때문이다. §5 에서 이 등식이 관찰을 늘리면 어떻게 무너지는지 본다.

채점 연습이 아니다. `countLoop_eval` 이 이미 연습이라 비우면 비운 것끼리 의존한다
(연습 독립성 원칙, `AGENTS.md` §1-9).
-/
theorem countTo100_eq_setTo100 : countTo100.eval = setTo100.eval := by
  funext σ
  change Option.bind (some (σ["x" := (0 : Int)])) countLoop.eval = some (σ["x" := (100 : Int)])
  change countLoop.eval (σ["x" := (0 : Int)]) = some (σ["x" := (100 : Int)])
  rw [countLoop_eval _ (by rw [State.subst_self]; omega)]
  simp [State.subst_def, Function.update_idem]

/-! ## 4. 셋째 쌍 — 서로 다른 변수에 쓰는 일은 순서를 바꿔도 된다

`x` 와 `y` 가 **다른 칸**이라는 것에 기대는 등식이다. 그 전제가 깨지는 자리가 §6 이다. -/

-- ANCHOR: obsEq3
/--
**`x := x+1; y := y×2 ≡ y := y×2; x := x+1`.**

한쪽이 읽는 변수를 다른 쪽이 쓰지 않으므로 순서가 중요하지 않다. 서로 다른 자리에 대한
갱신이 교환된다는 `Function.update_comm` 이 그 사실을 담고 있다.

§2.5 의 명제 2.6 으로 말하면 `FV(c₀) ∩ FA(c₁) = FA(c₀) ∩ FV(c₁) = ∅` 인 경우다.
-/
@[exercise "§2.8 obs-eq-comm" 1]
theorem incThenDouble_eq_doubleThenInc : incThenDouble.eval = doubleThenInc.eval := by
  funext σ
  change some ((σ["x" := σ "x" + 1])["y" := (σ["x" := σ "x" + 1]) "y" * 2])
      = some ((σ["y" := σ "y" * 2])["x" := (σ["y" := σ "y" * 2]) "x" + 1])
  rw [State.subst_of_ne _ _ _ _ (by decide : ("y" : String) ≠ "x"),
    State.subst_of_ne _ _ _ _ (by decide : ("x" : String) ≠ "y")]
  simp only [State.subst_def]
  rw [Function.update_comm (by decide : ("x" : String) ≠ "y")]
-- ANCHOR_END: obsEq3

/-! ## 5. 실행 시간을 보면 건전성이 깨진다

둘째 쌍은 뜻이 같다. 그런데 한쪽은 백 번 돌고 한쪽은 한 번에 끝난다. "몇 걸음 안에
끝나는가" 를 관찰에 넣으면 두 프로그램이 곧바로 갈린다 — 즉 그 관찰에 대해서는
우리 의미론이 **건전하지 않다**. -/

-- ANCHOR: stepsBreak
/--
**실행 시간을 관찰에 넣으면 건전성이 깨진다.**

뜻이 같은 두 프로그램인데, 연료 0 으로 돌리면 한쪽만 끝난다. `Comm.run` 의 연료가
"몇 걸음" 의 대역이다.

건전성은 `⟦c⟧ = ⟦c'⟧ → (모든 문맥에서 같게 관찰됨)` 이었다. 관찰을 "연료 0 으로 끝나는가"
로 바꾸면 전제는 그대로인데 결론이 거짓이다. **의미론이 틀린 것이 아니라, 그 관찰에
맞지 않는 것이다** — 실행 시간을 보고 싶으면 걸음 수를 세는 다른 의미론이 필요하다.

채점 연습이 아니다. `countTo100_eq_setTo100` 을 통해 `countLoop_eval` (연습) 에 의존한다.
-/
theorem steps_break_soundness :
    countTo100.eval = setTo100.eval
      ∧ countTo100.run 0 (State.const 0) = none
      ∧ (setTo100.run 0 (State.const 0)).isSome := by
  refine ⟨countTo100_eq_setTo100, ?_, ?_⟩
  · simp [countTo100, Comm.run]
  · simp [setTo100, Comm.run]
-- ANCHOR_END: stepsBreak

/-! ## 6. 별칭이 생기면 셋째 쌍이 깨진다 (13장 예고)

셋째 쌍은 `x` 와 `y` 가 다른 칸이라는 데 기대고 있었다. 프로시저 호출이 두 인자를
같은 변수로 묶으면 — §2.5 에서 본 별칭이다 — 그 전제가 사라진다.

§2.5 의 치환으로 그 상황을 만들 수 있다. 두 변수를 같은 이름으로 보내는 이름 바꾸기가
곧 별칭이고, 그것을 양쪽에 걸면 두 프로그램이 갈라진다. -/

-- ANCHOR: aliasBreak
/-- `x`, `y` 를 둘 다 `z` 로 보낸다. 단사가 아니다 — 별칭을 만드는 이름 바꾸기다. -/
def aliasXY : Ren String := fun w => if w = "x" then "z" else if w = "y" then "z" else w

/--
**별칭이 생기면 순서 교환이 깨진다.** 13장 예고.

`x := x+1; y := y×2` 와 `y := y×2; x := x+1` 은 뜻이 같다. 그런데 `x` 와 `y` 를 둘 다
`z` 로 보내면

```
z := z+1; z := z×2      vs      z := z×2; z := z+1
```

가 되고, `z = 0` 에서 각각 `2` 와 `1` 로 갈린다. 순서가 중요해진 것이다.

**§2.8 의 완전 추상성이 틀린 것이 아니다.** 이름 바꾸기는 우리 언어의 문맥이 아니다 —
문맥은 명령을 끼워 넣을 뿐 자유 변수를 다시 이름 짓지 않는다. 13장에서 프로시저가
생기면 호출이 이 이름 바꾸기를 **문맥 안에서** 할 수 있게 되고, 그때 이 쌍은 진짜로
구별된다. 완전 추상성은 언어에 대한 상대적인 성질이다.
-/
@[exercise "§2.8 alias-break" 2]
theorem alias_breaks_commutation :
    (incThenDouble /ᶜ aliasXY).eval (State.const 0)
      ≠ (doubleThenInc /ᶜ aliasXY).eval (State.const 0) := by
  intro hEq
  have h := congrArg (fun o => o.map (fun τ => τ "z")) hEq
  simp [incThenDouble, doubleThenInc, aliasXY, Comm.subst, Comm.eval, IntExp.subst,
    IntExp.eval, IntOp.denote, Ren.toSubst, State.subst_def, Function.update,
    State.const] at h
-- ANCHOR_END: aliasBreak

/-! ## 7. 2장을 닫으며

`while` 의 뜻이 무엇인지 묻는 데서 시작했다. 풀기 방정식에 해가 여럿이라는 것을 보고
(§2.2), 도메인과 연속성을 직접 만들고(§2.3), 최소 고정점으로 답을 정하고(§2.4),
그 답이 실행과 맞는지 확인했다(연료 해석기). 자유 변수를 읽기와 쓰기로 갈라(§2.5)
치환과 별칭을 다루고, 그 구분 위에서 `for` 를 설계하고(§2.6), 산술 오류의 선택이 무엇을
바꾸는지 보고(§2.7), 마지막으로 의미론 자체가 옳은 추상 수준인지 물었다(§2.8).

마지막 답이 **조건부**라는 것이 이 장의 결말이다. `⟦-⟧` 는 완전 추상이다 — *우리가
정한 관찰과 우리가 가진 문맥에 대해서.* 실행 시간을 보면 깨지고(§5), 프로시저가 별칭을
만들면 깨지고(§6), 8장에서 `c₀ ∥ c₁` 이 생기면 중간 상태가 보여 세 쌍이 모두 깨진다.

> 의미론이 옳은가는 혼자서는 답할 수 없는 물음이다. **무엇을 관찰할 것인가** 를 먼저
> 정해야 답이 있다.

6장 이후 CSlib 의 `LTS/TraceEq.lean`(트레이스 동치)과 `LTS/Bisimulation.lean`
(이중시뮬레이션)에서 같은 논점이 **서로 다른 프로그램 동치**로 다시 나타난다. -/

end Reynolds.Answers.Ch02
