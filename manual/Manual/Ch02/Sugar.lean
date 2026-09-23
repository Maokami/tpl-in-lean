/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External

set_option verso.exampleProject ".."
set_option verso.exampleModule "Reynolds.Answers.Ch02.Sugar"

#doc (Manual) "§2.6 문법 설탕과 `for` 명령" =>
%%%
tag := "ch02-sugar"
file := "ch02-sugar"
number := false
%%%

`for`는 새 구문이 아니다. 이미 있는 `assign`·`while`·`newvar`로 _번역_된다. 그래서
`Comm`의 새 생성자로 두지 않고 `Comm`을 만드는 함수로 정의한다. 디슈가링 자체가 그
함수다.

Landin의 표현대로 설탕은 표현력을 늘리지 않고 계산을 더 간결하게 적게 해 줄 뿐이다.
이 절의 진짜 교훈은 다른 데 있다. *잘못 설계된 설탕이 어떻게 버그를 부르는가*다.
Reynolds는 `for`의 디슈가링을 세 번 고쳐 쓰고 매번 남는 결함을 짚는데, 여기서는 각
결함을 정리로 증명한다.

# 판본 1 — 제어 변수가 밖으로 샌다
%%%
tag := "ch02-forv1"
file := "ch02-forv1"
number := false
%%%

가장 곧이곧대로 옮긴 것이다.

```anchor forV1 (module := Reynolds.Answers.Ch02.Sugar)
/-- 판본 1. `for v := e₀ to e₁ do c` 를 가장 곧이곧대로 옮긴 것. -/
def forV1 (v : V) (e₀ e₁ : IntExp V) (c : Comm V) : Comm V :=
  .seq (.assign v e₀) (forWhile v e₁ c)
```

루프가 끝난 뒤 제어 변수가 입력과 다른 값으로 남는다. Reynolds가 "제어 변수를 다시
설정하는 부작용"이라 부르는 것이다.

```anchor forV1Leaks (module := Reynolds.Answers.Ch02.Sugar)
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
```

구조적으로는 `v ∈ FA(forV1 …)`이 그 진단이다. §2.5에서 만든 `FA`가 여기서 바로 값을
한다.

# 판본 2 — 상한이 매 반복 재평가된다
%%%
tag := "ch02-forv2"
file := "ch02-forv2"
number := false
%%%

제어 변수를 `newvar`로 감싸면 누수가 막힌다.

```anchor forV2 (module := Reynolds.Answers.Ch02.Sugar)
/-- 판본 2. 제어 변수를 `newvar` 로 감싼다. -/
def forV2 (v : V) (e₀ e₁ : IntExp V) (c : Comm V) : Comm V :=
  .newvar v e₀ (forWhile v e₁ c)
```

이제 `v ∉ FA(forV2 …)`다. 그런데 새 결함이 드러난다. 상한 식이 while 안에 있어 매 반복
다시 평가되는 것이다. Reynolds의 극단적인 예는 상한이 제어 변수 자신인 경우다.

```anchor forV2Diverges (module := Reynolds.Answers.Ch02.Sugar)
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
```

증명이 짧은 구조를 눈여겨볼 것. 조건이 언제나 참이라 한 바퀴 돌 때마다 남은 루프로
넘어가고, 연료에 대한 귀납이 그것을 `none`으로 만든다. 그다음 적합성의 대우로 표시적
의미가 `⊥`임을 얻는다.

# 판본 3 — 상한을 얼린다
%%%
tag := "ch02-forv3"
file := "ch02-forv3"
number := false
%%%

Reynolds의 최종안이다. 상한을 먼저 새 지역 변수에 담아 두고 while은 그것과 비교한다.

````anchor forV3 (module := Reynolds.Answers.Ch02.Sugar)
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
````

두 제어 변수가 모두 감춰진다.

```anchor forV3NoLeak (module := Reynolds.Answers.Ch02.Sugar)
/--
**판본 3 은 두 제어 변수를 모두 감춘다.** `v` 도 `w` 도 `FA` 에서 지워진다.

`newvar` 두 겹이 각각 하나씩 지운다. 판본 1 이 누수하던 제어 변수(`v ∈ FA`)와,
판본 3 이 새로 들여온 상한 변수(`w`)가 함께 국소화된다.
-/
theorem forV3_fa (v w : V) (e₀ e₁ : IntExp V) (c : Comm V) :
    v ∉ (forV3 v w e₀ e₁ c).fa ∧ w ∉ (forV3 v w e₀ e₁ c).fa := by
  constructor <;> simp [forV3, Comm.fa, Finset.mem_erase]
```

`Comm.eval_agree_outside_fa`(명제 2.6(b))와 맞물리면 "루프의 제어 변수는 새지 않는다"가
실행판으로 나온다(`forV3_control_restored`).

# 남은 결함은 구문으로 막을 수 없다
%%%
tag := "ch02-for-exact"
file := "ch02-for-exact"
number := false
%%%

본문이 제어 변수를 바꾸면 루프가 연속된 값으로 돌지 않는다. Reynolds의 예에서 `x`는
1 → 3 → 7 → 15로 뛰고 본문은 열 번이 아니라 세 번만 실행된다.

이것은 구문을 더 고쳐서 막을 수 있는 종류가 아니다. 본문이 무엇을 하는지는 구문이
통제할 수 없기 때문이다. 그래서 _제약_으로 막는다. `v ∉ FA(c)`.

§2.5에서 만든 `FA`가 여기서 다시 값을 한다. "본문이 제어 변수에 대입하지 않는다"를
문장으로 쓸 수 있어야 이 제약을 정리의 가정으로 올릴 수 있다.

"정확히 몇 번 도는가"를 말하려면 비교 대상이 필요하다. 반복 횟수가 _눈에 보이는_
기준 함수를 둔다.

```anchor forFold (module := Reynolds.Answers.Ch02.Sugar2)
/--
본문 `c` 를 `n` 번 돌리며 매번 `v` 를 한 칸 올린다. 판본 3 의 기준(reference).

`while` 이 아니라 `Nat` 에 대한 구조적 재귀라서 반복 횟수가 정의에 박혀 있다.
`Comm.eval` 을 쓰므로 계산되지는 않는다.
-/
noncomputable def forFold (v : V) (c : Comm V) : Nat → State V → SigmaBot V
  | 0,     σ => some σ
  | n + 1, σ => Option.bind (c.eval σ) (fun σ' => forFold v c n (σ'[v := σ' v + 1]))
```

그러면 정확 반복 정리(`forWhile_eq_fold`)가 이렇게 읽힌다.

```
⟦while v ≤ w do (c; v := v+1)⟧ σ = forFold v c (σ w - σ v + 1).toNat σ
```

오른쪽의 `(σ w - σ v + 1).toNat`이 곧 반복 횟수이고 그것이 구간 크기다. `σ v > σ w`면
`0`이므로 "빈 구간이면 한 번도 안 돈다"도 같은 식에 들어 있다.

가정 셋이 각각 다른 일을 한다.

: `v ∉ FA(c)`

  한 바퀴를 돌 때 `v`가 _정확히 하나만_ 는다는 것을 보장한다. 본문이 `v`를 건드리면
  측도가 하나씩 줄지 않아 귀납이 무너진다. 이것이 막으려던 마지막 결함이다.

: `w ∉ FA(c)`

  상한이 루프 도중 움직이지 않게 한다. 판본 2에서 겪은 것을 판본 3은 `w`에 얼려 두고
  이 가정으로 지킨다.

: `v ≠ w`

  제어 변수와 상한 변수가 같은 칸을 쓰면 증가가 상한도 밀어 올린다.

증명은 반복 횟수에 대한 귀납이다. 한 바퀴 돌면 `v`는 하나 늘고 `w`는 그대로임을 명제
2.6(b)로 얻으므로 측도가 정확히 하나 준다. `forV3_eq_fold`가 이것을 판본 3 전체로
올리고, 거기서 `w ∉ FV(e₀)`가 새로 필요해진다. 판본 3이 상한 변수를 신선하게 골라야
하는 이유가 가정으로 드러나는 자리다.

마지막으로 제약이 장식이 아님을 확인한다.

```anchor broken (module := Reynolds.Answers.Ch02.Sugar2)
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
  refine ⟨by simp [doublingBody, Comm.fa], ?_⟩
  have h : ((forV3 "i" "hi" (.num 1) (.num 3) doublingBody).run 8 (State.const 0)).map
      (fun σ => σ "s") = some 2 := by
    simp [forV3, forWhile, forBody, incr, doublingBody, Comm.run, restore,
      BoolExp.eval, IntExp.eval, IntOp.denote, Cmp.denoteBool, State.const]
  obtain ⟨τ, hτ, hs⟩ := Option.map_eq_some_iff.mp h
  exact ⟨τ, Comm.run_sound hτ, hs⟩
```

앞의 두 결함은 구문으로 막았고 마지막 하나는 구문으로 막을 수 없어 가정이 되었다는
것이 이 절의 교훈이다.
