/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Answers.Ch02.Substitution
-- `#guard`는 컴파일 시점에 계산한다 (AGENTS.md §10).
public meta import Reynolds.Answers.Ch02.Interpreter
public meta import Reynolds.Answers.Ch02.Notation
public meta import Reynolds.Answers.Ch02.Semantics
public meta import Reynolds.Prelude

/-!
# §2.6 문법 설탕 (1) — `for` 명령과 세 가지 결함

Reynolds §2.6 전반부에 대응한다. 정확 반복 정리(결함 3의 해결)와 연습 2.9·2.10 은
다음 파일 `Sugar2.lean` 이다.

## 문법 설탕은 무엇을 늘리지 않는가

`for` 는 새 구문이 아니다. 이미 있는 `assign`·`while`·`newvar` 로 **번역**된다.
Landin 의 표현대로 설탕은 표현력을 늘리지 않고 계산을 더 간결하게 적게 해 줄 뿐이다.
그래서 `for` 를 `Comm` 의 새 생성자로 두지 않고, `Comm` 을 만드는 **함수**로 정의한다 —
디슈가링(desugaring) 자체가 그 함수다.

## 잘못 설계된 설탕이 어떻게 버그를 부르는가

이 절의 진짜 교훈이다. Reynolds 는 `for` 의 디슈가링을 세 번 고쳐 쓰고, 매번 남는
결함을 짚는다. 여기서는 각 결함을 **정리로 증명**한다.

- **판본 1** — 제어 변수가 밖으로 샌다. 루프가 끝난 뒤 `v` 가 입력과 다른 값을 갖는다.
- **판본 2** — 상한이 매 반복 재평가된다. `for v := 1 to v do skip` 은 종료하지 않는다.
- **판본 3** — Reynolds 의 최종안. 상한을 미리 얼려 둔다. 남는 결함(본문이 `v` 를 바꾸면
  연속 값으로 돌지 않음)은 `v ∉ FA(c)` 제약으로 막고, 그 정확성은 다음 파일에서 증명한다.

각 결함의 진단과 해결이 §2.5 에서 만든 `FA` 와 `eval_agree_outside_fa` 위에 그대로
선다 — 판본 1 의 누수는 `v ∈ FA`, 판본 2·3 의 국소성은 `v ∉ FA` 로 적힌다.

## 읽는 순서
`Substitution.lean` → 이 파일 → `Sugar2.lean` (정확 반복과 연습 2.9·2.10)
-/

-- 이 파일의 `#guard` 가 `for` 세 판본이 실제로 어떻게 도는지 보여 준다.
set_option linter.hashCommand false

@[expose] public section

namespace Reynolds.Answers.Ch02

open Reynolds Reynolds.Answers.Ch01

universe u

variable {V : Type u} [DecidableEq V]

/-! ## 1. 공통 조각 — 루프 본체와 조건

세 판본이 공유하는 것: 조건 `v ≤ e₁` 과 본체 `c; v := v + 1`. 판본마다 `e₁` 을 어디서
읽는지, 제어 변수를 감싸는지가 다르다. -/

/-- `v := v + 1`. 제어 변수를 한 칸 올린다. -/
def incr (v : V) : Comm V := .assign v (.bin .add (.var v) (.num 1))

/-- 루프 한 바퀴: 본체를 돌고 제어 변수를 올린다. -/
def forBody (v : V) (c : Comm V) : Comm V := .seq c (incr v)

/-- `for` 의 while 부분. 상한 식 `bnd` 를 받는다 — 판본마다 다른 것을 넣는다. -/
def forWhile (v : V) (bnd : IntExp V) (c : Comm V) : Comm V :=
  .wh (.cmp .le (.var v) bnd) (forBody v c)

/-! ## 2. 판본 1 — 가장 순진한 정의

`v := e₀` 뒤에 while 을 놓는다. 상한은 매번 `e₁` 을 다시 읽는다. -/

-- ANCHOR: forV1
/-- 판본 1. `for v := e₀ to e₁ do c` 를 가장 곧이곧대로 옮긴 것. -/
def forV1 (v : V) (e₀ e₁ : IntExp V) (c : Comm V) : Comm V :=
  .seq (.assign v e₀) (forWhile v e₁ c)
-- ANCHOR_END: forV1

-- 판본 1 은 실제로 돈다. `for i := 1 to 3 do skip` 은 i 를 1,2,3 에서 돌고 4 에서 멈춘다.
#guard ((forV1 "i" (.num 1) (.num 3) .skip).run 10 (State.const 0)).map (fun σ => σ "i")
  == some 4

/-- **판본 1 의 결함: 제어 변수가 밖으로 샌다.** `v` 가 `FA` 에 들어 있다. -/
theorem forV1_assigns_control (v : V) (e₀ e₁ : IntExp V) (c : Comm V) :
    v ∈ (forV1 v e₀ e₁ c).fa := by
  simp [forV1, forWhile, forBody, incr, Comm.fa]

-- ANCHOR: forV1Leaks
/--
**판본 1 의 결함, 실행으로.** 루프가 끝난 뒤 제어 변수가 입력과 다른 값을 갖는다.

증인 하나면 충분하다. `for i := 1 to 1 do skip` 을 `i = 0` 에서 돌리면, 한 바퀴 돈 뒤
`i` 가 `2` 로 남는다 — 원래 `0` 이 사라졌다. `while` 이 없는 게 아니므로 `run` 으로
계산한 뒤 `run_sound` 로 표시적 의미에 옮긴다.
-/
@[exercise "§2.6 for-leaks" 1]
theorem forV1_leaks :
    ∃ (σ τ : State String),
      (forV1 "i" (.num 1) (.num 1) .skip).eval σ = some τ ∧ τ "i" ≠ σ "i" := by
  -- 연료 2 로 실행하면 종료하고, 그 결과 상태에서 i = 2 다.
  have hrun : (forV1 "i" (.num 1) (.num 1) .skip).run 2 (State.const 0)
      = some (((State.const 0)["i" := (1 : Int)])["i" := (2 : Int)]) := by
    simp [forV1, forWhile, forBody, incr, Comm.run, BoolExp.eval, IntExp.eval,
      IntOp.denote, Cmp.denoteBool]
  exact ⟨State.const 0, _, Comm.run_sound hrun, by decide⟩
-- ANCHOR_END: forV1Leaks

/-! ## 3. 판본 2 — `newvar` 로 감싼다

제어 변수를 지역으로 만들면 누수가 막힌다. `newvar v := e₀ in while …`. 이제 `v` 는
`FA` 에서 지워진다. 그런데 새 결함이 드러난다 — 상한 `e₁` 이 while 안에 있어 매 반복
다시 평가된다. -/

-- ANCHOR: forV2
/-- 판본 2. 제어 변수를 `newvar` 로 감싼다. -/
def forV2 (v : V) (e₀ e₁ : IntExp V) (c : Comm V) : Comm V :=
  .newvar v e₀ (forWhile v e₁ c)
-- ANCHOR_END: forV2

/-- **판본 2 는 판본 1 의 누수를 고친다.** 제어 변수가 `FA` 에서 사라진다. -/
theorem forV2_no_leak (v : V) (e₀ e₁ : IntExp V) (c : Comm V) :
    v ∉ (forV2 v e₀ e₁ c).fa := by
  simp [forV2, Comm.fa, Finset.mem_erase]

-- `for i := 1 to 3 do skip` 을 판본 2 로 돌리면 i 는 밖으로 새지 않는다 (입력 0 그대로).
#guard ((forV2 "i" (.num 1) (.num 3) .skip).run 10 (State.const 0)).map (fun σ => σ "i")
  == some 0

-- 그러나 상한이 제어 변수를 가리키면 발산한다. `for i := 1 to i do skip`.
#guard ((forV2 "i" (.num 1) (.var "i") .skip).run 1000 (State.const 0)).isNone

-- ANCHOR: forV2Diverges
/--
**판본 2 의 결함: 상한이 매 반복 재평가된다.**

Reynolds 의 극단적인 예다. `for v := 1 to v do skip` 은 상한이 제어 변수 자신이라,
`v` 를 올릴 때마다 상한도 같이 올라간다. 조건 `v ≤ v` 는 언제나 참이고 루프는 멈추지
않는다 — 어떤 입력에서도 `⊥` 다.

증명의 뼈대: 안쪽 while 이 어떤 연료로도 `none` 임을 연료에 대한 귀납으로 보인다.
조건이 항상 참(`v ≤ v`)이라 한 바퀴 돌 때마다 남은 루프로 넘어가고, 귀납 가설이
그것을 `none` 으로 만든다. 그다음 적합성(`run_complete`)으로 표시적 의미가 `none`
임을 얻고, `newvar` 의 복원이 `none` 을 그대로 통과시킨다.
-/
@[exercise "§2.6 for-diverges" 2]
theorem forV2_diverges (v : V) (σ : State V) :
    (forV2 v (.num 1) (.var v) .skip).eval σ = none := by
  -- 안쪽 while 은 어떤 상태·연료에서도 종료하지 않는다.
  have hrun : ∀ (n : ℕ) (σ' : State V),
      (forWhile v (.var v) (.skip : Comm V)).run n σ' = none := by
    intro n
    induction n with
    | zero => intro σ'; simp [forWhile, Comm.run]
    | succ n ih =>
        intro σ'
        rw [forWhile, Comm.run]
        by_cases hb : ⟦(.cmp .le (.var v) (.var v) : BoolExp V)⟧ᵇ σ'
        · simp only [if_pos hb]
          have hbody : (forBody v (.skip : Comm V)).run (n + 1) σ'
              = some (σ'[v := σ' v + 1]) := by
            simp [forBody, incr, Comm.run, IntExp.eval, IntOp.denote]
          rw [hbody]
          exact ih (σ'[v := σ' v + 1])
        · simp [BoolExp.eval, IntExp.eval, Cmp.denoteBool] at hb
  -- 표시적 의미도 `none`.
  have heval : ∀ σ', (forWhile v (.var v) (.skip : Comm V)).eval σ' = none := by
    intro σ'
    rcases h : (forWhile v (.var v) (.skip : Comm V)).eval σ' with _ | τ
    · rfl
    · obtain ⟨n, hn⟩ := Comm.run_complete h
      rw [hrun n σ'] at hn
      exact absurd hn (by simp)
  -- `newvar` 는 `none` 을 그대로 내보낸다.
  change restore v σ
    ((forWhile v (.var v) (.skip : Comm V)).eval (σ[v := ⟦(.num 1 : IntExp V)⟧ₑ σ])) = none
  rw [heval]
  simp [restore]
-- ANCHOR_END: forV2Diverges

/-! ## 4. 판본 3 — 상한을 얼린다

Reynolds 의 최종안이다. 상한을 먼저 새 지역 변수 `w` 에 담아 두고, while 은 `w` 와
비교한다. `w` 는 루프 안에서 아무도 바꾸지 않으므로 상한이 고정된다. 제어 변수 `v` 도
지역이라 누수가 없다. -/

-- ANCHOR: forV3
/--
판본 3. Reynolds 의 최종 디슈가링.

```
newvar w := e₁ in newvar v := e₀ in while v ≤ w do (c; v := v + 1)
```

`w` 는 상한을 담는 신선한 변수다 — `w ≠ v` 이고 `c`·`e₀` 에 나오지 않아야 제 몫을 한다.
그 조건 아래에서의 정확성은 `Sugar2.lean` 에서 증명한다.
-/
def forV3 (v w : V) (e₀ e₁ : IntExp V) (c : Comm V) : Comm V :=
  .newvar w e₁ (.newvar v e₀ (forWhile v (.var w) c))
-- ANCHOR_END: forV3

-- 상한이 얼어 있으므로 합이 제대로 계산된다. `for i := 1 to 3 do s := s + i` → s = 6.
#guard ((forV3 "i" "hi" (.num 1) (.num 3)
          (.assign "s" (.bin .add (.var "s") (.var "i")))).run 20 (State.const 0)).map
        (fun σ => σ "s") == some 6

-- ANCHOR: forV3NoLeak
/--
**판본 3 은 두 제어 변수를 모두 감춘다.** `v` 도 `w` 도 `FA` 에서 지워진다.

`newvar` 두 겹이 각각 하나씩 지운다. 판본 1 이 누수하던 제어 변수(`v ∈ FA`)와,
판본 3 이 새로 들여온 상한 변수(`w`)가 함께 국소화된다.
-/
theorem forV3_fa (v w : V) (e₀ e₁ : IntExp V) (c : Comm V) :
    v ∉ (forV3 v w e₀ e₁ c).fa ∧ w ∉ (forV3 v w e₀ e₁ c).fa := by
  constructor <;> simp [forV3, Comm.fa, Finset.mem_erase]
-- ANCHOR_END: forV3NoLeak

/--
**국소성의 실행판.** 판본 3 이 종료하면 두 제어 변수는 입력값 그대로다.

§2.5 의 `eval_agree_outside_fa` 를 `forV3_fa` 와 맞물린 것이다 — `FA` 밖의 변수는
명령이 건드리지 않는다는 명제 2.6(b) 가, 여기서 "루프의 제어 변수는 새지 않는다" 가
된다.
-/
theorem forV3_control_restored (v w : V) (e₀ e₁ : IntExp V) (c : Comm V)
    (σ τ : State V) (h : (forV3 v w e₀ e₁ c).eval σ = some τ) :
    τ v = σ v ∧ τ w = σ w :=
  ⟨Comm.eval_agree_outside_fa _ _ _ h v (forV3_fa v w e₀ e₁ c).1,
   Comm.eval_agree_outside_fa _ _ _ h w (forV3_fa v w e₀ e₁ c).2⟩

/-! ## 5. 여기서 어디로 가나

세 판본, 세 결함. 누수는 `newvar` 로, 재평가는 상한 동결로 막았다. 마지막 결함 —
본문이 제어 변수를 바꾸면 연속된 값으로 돌지 않는다 — 만 남았다. 이것은 구문이 아니라
**제약**으로 막는다: `v ∉ FA(c)`. 그 제약 아래에서 판본 3 이 정확히 구간 크기만큼
반복한다는 것을 다음 파일에서 증명하고, 연습 2.9(제어 변수가 구간 밖으로 나가지 않음)와
2.10(`dotwice` 디슈가링의 종료성)으로 잇는다. -/

end Reynolds.Answers.Ch02
