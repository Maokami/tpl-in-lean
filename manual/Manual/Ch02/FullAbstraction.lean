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
set_option verso.exampleModule "Reynolds.Answers.Ch02.FullAbstraction"

#doc (Manual) "§2.8 건전성과 완전 추상성" =>
%%%
tag := "ch02-full-abstraction"
file := "ch02-full-abstraction"
number := false
%%%

지금까지 만든 `⟦-⟧`가 _옳은 추상 수준인가_? 두 방향으로 나뉜다.

: 건전성(soundness)

  뜻이 같다고 한 것들이 정말 구별되지 않는가? 어떤 문맥에 넣어도 다르게 행동하지
  않아야 한다. 의미론이 _너무 거칠지_ 않다는 뜻이다.

: 완전 추상성(full abstraction)

  건전하면서, 구별되지 않는 것은 뜻도 같은가? 의미론이 _너무 섬세하지_ 않다는 뜻이다.

둘 다 성립하면 "뜻이 같다"와 "어떤 프로그램에 끼워 넣어도 똑같이 행동한다"가 정확히
같은 말이 된다.

# 문맥은 치환이 아니다
%%%
tag := "ch02-ctx"
file := "ch02-ctx"
number := false
%%%

문맥은 구멍이 하나 뚫린 명령이다.

```anchor Ctx (module := Reynolds.Answers.Ch02.FullAbstraction)
/--
문맥 — 구멍(`−`)이 하나 있는 명령. Reynolds §2.8.

`seq` 는 구멍이 왼쪽에 있는 경우와 오른쪽에 있는 경우가 다르므로 둘로 나뉜다.
`ite` 도 마찬가지다.
-/
inductive Ctx (V : Type u) where
  /-- 구멍 그 자체. `−` -/
  | hole
  /-- `− ; c₁` -/
  | seqL : Ctx V → Comm V → Ctx V
  /-- `c₀ ; −` -/
  | seqR : Comm V → Ctx V → Ctx V
  /-- `if b then − else c₁` -/
  | iteL : BoolExp V → Ctx V → Comm V → Ctx V
  /-- `if b then c₀ else −` -/
  | iteR : BoolExp V → Comm V → Ctx V → Ctx V
  /-- `while b do −` -/
  | wh : BoolExp V → Ctx V → Ctx V
  /-- `newvar v := e in −` -/
  | newvar : V → IntExp V → Ctx V → Ctx V

/--
`C[c]` — 구멍에 `c` 를 끼워 넣는다.

**치환이 아니다.** 이름 바꾸기를 하지 않으므로 `c` 의 자유 변수가 문맥의 `newvar` 에
포획될 수 있다. §2.5 에서 치환이 애써 피하던 바로 그 일이 여기서는 일부러 허용된다 —
프로그램 조각이 어떤 선언 아래 놓이느냐가 문맥이 하는 일이기 때문이다.
-/
def Ctx.fill : Ctx V → Comm V → Comm V
  | .hole,         c => c
  | .seqL C c₁,    c => .seq (C.fill c) c₁
  | .seqR c₀ C,    c => .seq c₀ (C.fill c)
  | .iteL b C c₁,  c => .ite b (C.fill c) c₁
  | .iteR b c₀ C,  c => .ite b c₀ (C.fill c)
  | .wh b C,       c => .wh b (C.fill c)
  | .newvar v e C, c => .newvar v e (C.fill c)
```

`C[c]`는 구멍에 `c`를 _끼워 넣는다_. 이름 바꾸기를 하지 않으므로 `c`의 자유 변수가
문맥의 `newvar`에 잡힐 수 있다. §2.5에서 치환이 애써 피하던 바로 그 일이 여기서는
일부러 허용된다. 프로그램 조각이 어떤 선언 아래 놓이느냐가 문맥이 하는 일이기 때문이다.

# 무엇을 볼 것인가
%%%
tag := "ch02-observe"
file := "ch02-observe"
number := false
%%%

관찰은 밖에서 볼 수 있는 것이다. 두 가지를 둔다.

```anchor observe (module := Reynolds.Answers.Ch02.FullAbstraction)
/-- 풍부한 관찰 — 종료 여부와 변수 `v` 의 최종 값. 발산은 `none` 이다. -/
noncomputable def observe (σ : State V) (v : V) (c : Comm V) : Option Int :=
  (c.eval σ).map (fun τ => τ v)

/-- 빈약한 관찰 — **종료했는가만** 본다. 최종 값은 보지 않는다. -/
noncomputable def observeHalt (σ : State V) (c : Comm V) : Bool := (c.eval σ).isSome

/-- 어떤 문맥·초기 상태·변수에서도 같게 관찰된다. -/
def ObsEq (c c' : Comm V) : Prop :=
  ∀ (C : Ctx V) (σ : State V) (v : V), observe σ v (C.fill c) = observe σ v (C.fill c')

/-- 어떤 문맥·초기 상태에서도 **종료 여부**가 같다. `ObsEq` 보다 훨씬 약해 보인다. -/
def HaltEq (c c' : Comm V) : Prop :=
  ∀ (C : Ctx V) (σ : State V), observeHalt σ (C.fill c) = observeHalt σ (C.fill c')
```

두 번째가 훨씬 빈약한데도 구별하는 힘이 같다는 것이 이 절의 놀라운 결과다.

건전성은 합성성의 따름정리다. `⟦-⟧`는 부분의 뜻으로부터 전체의 뜻을 만들므로, 부분을
뜻이 같은 것으로 갈아 끼워도 전체가 안 변한다(`Ctx.fill_congr`). 문맥에 대한 구조적
귀납이고, `wh` 절만 `fix`를 지나므로 따로 보조정리가 필요하다.

# 발산하는 명령
%%%
tag := "ch02-diverge"
file := "ch02-diverge"
number := false
%%%

완전 추상성의 증명에서 "값이 다르면 발산시킨다"는 문맥을 만들려면 발산하는 명령이
하나 필요하다.

```anchor diverge (module := Reynolds.Answers.Ch02.FullAbstraction)
/-- `while true do skip` — 절대 끝나지 않는 명령. -/
def diverge : Comm V := .wh .tru .skip

/--
**발산한다.** 어떤 상태에서도 `⊥` 다.

증명이 짧은 이유를 보아 둘 것. 이 반복의 함수 연산자는 **항등 함수**다 —
조건이 늘 참이고 본체가 아무것도 안 하므로 `whileF tru ⟦skip⟧ w = w` 이다.
항등 함수는 `⊥` 를 `⊥` 로 보내므로 `⊥` 가 전고정점이고, 최소 고정점은 그보다 아래다
(`fix_least`). 사슬을 펼쳐 볼 필요가 없다.

"최소" 고정점을 택한 것이 여기서 값을 한다. 이 반복의 풀기 방정식은 §2.2 에서 보았듯
**모든** 함수가 해이지만(`unwinding_trivial`), 그중 가장 작은 것이 `⊥` 다.
-/
@[exercise "§2.8 diverge" 2]
theorem eval_diverge (σ : State V) : (diverge : Comm V).eval σ = none := by
  have hbot : Comm.eval (V := V) diverge ≤ ⊥ :=
    fix_least (whileF_monotone _ _) (le_of_eq rfl)
  simpa using hbot σ
```

증명이 짧은 이유를 눈여겨볼 것. 이 반복의 함수 연산자는 _항등 함수_다. 조건이 늘 참이고
본체가 아무것도 안 하기 때문이다. 항등 함수는 `⊥`를 `⊥`로 보내므로 `⊥`가 전고정점이고,
최소 고정점은 그보다 아래다. 사슬을 펼쳐 볼 필요가 없다.

§2.2에서 이 풀기 방정식은 _모든_ 함수가 해였다. 그중 가장 작은 것이 `⊥`라는 것,
곧 §2.4에서 "최소"를 택한 결정이 여기서 값을 한다.

# 종료 여부만 보아도 충분하다
%%%
tag := "ch02-halt-complete"
file := "ch02-halt-complete"
number := false
%%%

여기가 이 절의 놀라운 대목이다. 최종 값을 전혀 보지 않고 _끝났는지만_ 보아도 구별하는
힘이 줄지 않는다. 열쇠는 값의 차이를 종료의 차이로 _바꾸는_ 문맥이다.

```
− ; if v = κ then skip else (while true do skip)
```

```anchor haltComplete (module := Reynolds.Answers.Ch02.FullAbstraction)
/--
**종료 여부만 보아도 구별되지 않으면 뜻이 같다.**

세 갈래다.

- 한쪽만 발산 — 빈 문맥이 이미 구별한다.
- 둘 다 발산 — 뜻이 같다.
- 둘 다 종료하는데 상태가 다름 — 다른 변수 `v` 와 그 값 `κ = τ v` 를 잡아
  `− ; if v = κ then skip else diverge` 를 씌운다. 왼쪽은 `κ` 를 맞혀 끝나고,
  오른쪽은 못 맞혀 발산한다.

채점 연습이 아니다. `eval_diverge` 가 이미 연습이라 비우면 비운 것끼리 의존한다.
대신 이 구성은 읽어 둘 값이 크다 — 빈약한 관찰이 풍부한 관찰만큼 강해지는 이유가
"프로그램을 장치로 쓸 수 있다" 는 데 있다는 것이 여기서 눈에 보인다.
-/
theorem haltEq_imp_eval_eq {c c' : Comm V} (h : HaltEq c c') : c.eval = c'.eval := by
  funext σ
  have hhole := h .hole σ
  simp only [observeHalt, Ctx.fill] at hhole
  rcases h1 : c.eval σ with _ | τ <;> rcases h2 : c'.eval σ with _ | τ'
  · rfl
  · rw [h1, h2] at hhole; simp at hhole
  · rw [h1, h2] at hhole; simp at hhole
  · -- 둘 다 종료한다. 상태가 다르면 갈리는 변수를 잡아 종료 여부로 바꾼다.
    have hττ' : τ = τ' := by
      by_contra hne
      obtain ⟨v, hv⟩ : ∃ v, τ v ≠ τ' v := by
        by_contra hall
        exact hne (funext fun v => not_not.mp fun hv => hall ⟨v, hv⟩)
      -- 관찰 장치: 값이 `τ v` 면 끝나고 아니면 발산한다.
      have hdev := h (.seqL .hole
        (.ite (.cmp .eq (.var v) (.num (τ v))) .skip diverge)) σ
      simp only [observeHalt, Ctx.fill] at hdev
      have hleft : (Comm.seq c (.ite (.cmp .eq (.var v) (.num (τ v))) .skip diverge)).eval σ
          = some τ := by
        change Option.bind (c.eval σ) _ = some τ
        rw [h1]
        change (if ⟦(.cmp .eq (.var v) (.num (τ v)) : BoolExp V)⟧ᵇ τ then _ else _) = some τ
        rw [if_pos (by simp [BoolExp.eval, IntExp.eval, Cmp.denoteBool])]
        rfl
      have hright : (Comm.seq c' (.ite (.cmp .eq (.var v) (.num (τ v))) .skip diverge)).eval σ
          = none := by
        change Option.bind (c'.eval σ) _ = none
        rw [h2]
        change (if ⟦(.cmp .eq (.var v) (.num (τ v)) : BoolExp V)⟧ᵇ τ' then _ else _) = none
        have hcond : ¬ (⟦(.cmp .eq (.var v) (.num (τ v)) : BoolExp V)⟧ᵇ τ' = true) := by
          simpa [BoolExp.eval, IntExp.eval, Cmp.denoteBool] using Ne.symm hv
        rw [if_neg hcond]
        exact eval_diverge τ'
      rw [hleft, hright] at hdev
      simp at hdev
    rw [hττ']
```

프로그램을 관찰 장치로 쓰는 것이다. 재미있는 비대칭이 하나 있다. 풍부한 관찰 판본은
`Inhabited V`가 필요하다. 변수가 하나도 없으면 "변수의 최종 값"이라는 관찰이 발산과
종료조차 못 가르기 때문이다. 그런데 이 종료 관찰 판본은 필요 없다. 종료는 변수를
지목하지 않고도 보이고, 값이 갈리는 경우엔 갈리는 변수가 저절로 주어진다.

두 관찰의 힘이 같으므로(`obsEq_iff_haltEq`) 관찰을 _줄여도_ 완전 추상성이 유지된다.
다음 절에서는 반대로 _늘리면_ 무엇이 깨지는지 본다.

# 무엇을 관찰하기로 했는가
%%%
tag := "ch02-observation-choice"
file := "ch02-observation-choice"
number := false
%%%

우리 의미론이 같다고 보는 프로그램 쌍이 있다.

```
x := x+1; x := x+1                ≡  x := x+2
x := 0; while x < 100 do x := x+1 ≡  x := 100
x := x+1; y := y×2                ≡  y := y×2; x := x+1
```

두 번째가 특별하다. 왼쪽은 백 번 도는 반복이고 오른쪽은 대입 하나인데 뜻이 같다.
최소 고정점을 실제로 계산해야 나오는 등식이고(`countLoop_eval`), §2.6의 정확 반복
정리와 같은 측도 귀납을 쓴다.

세 등식이 성립하는 것은 우리가 _최종 상태만_ 보기로 했기 때문이다. 관찰을 늘리면 같은
쌍이 갈라진다.

실행 시간을 관찰에 넣으면 곧바로 갈린다. 두 번째 쌍은 한쪽이 백 번 돌고 한쪽이 한 번에
끝나기 때문이다.

```anchor stepsBreak (module := Reynolds.Answers.Ch02.FullAbstraction2)
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
```

의미론이 틀린 것이 아니라 그 관찰에 맞지 않는 것이다. 실행 시간을 보고 싶으면 걸음 수를
세는 다른 의미론이 필요하다.

세 번째 쌍은 `x`와 `y`가 _다른 칸_이라는 데 기대고 있다. §2.5의 치환으로 둘을 같은
칸으로 묶으면 갈라진다.

````anchor aliasBreak (module := Reynolds.Answers.Ch02.FullAbstraction2)
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
````

이름 바꾸기는 _지금 언어의 문맥이 아니므로_ §2.8의 완전 추상성이 틀린 것은 아니다.
13장에서 프로시저가 생기면 호출이 이 이름 바꾸기를 문맥 안에서 하게 되고, 그때 이 쌍은
진짜로 구별된다. 완전 추상성은 언어에 대한 상대적인 성질이다.

8장의 병행 합성도 마찬가지다. `c₀ ∥ c₁`이 생기면 다른 스레드가 중간 상태를 들여다볼 수
있어 세 쌍이 모두 갈라진다.

# 2장을 닫으며
%%%
tag := "ch02-closing"
file := "ch02-closing"
number := false
%%%

`while`의 뜻이 무엇인지 묻는 데서 시작했다. 풀기 방정식에 해가 여럿이라는 것을 보고,
도메인과 연속성을 직접 만들고, 최소 고정점으로 답을 정하고, 그 답이 실행과 맞는지
확인했다. 자유 변수를 읽기와 쓰기로 갈라 치환과 별칭을 다루고, 그 구분 위에서 `for`를
설계하고, 산술 오류의 선택이 무엇을 바꾸는지 보고, 마지막으로 의미론 자체가 옳은 추상
수준인지 물었다.

마지막 답이 _조건부_라는 것이 이 장의 결말이다. `⟦-⟧`는 완전 추상이다. 우리가 정한
관찰과 우리가 가진 문맥에 대해서.

의미론이 옳은가는 혼자서는 답할 수 없는 물음이다. *무엇을 관찰할 것인가*를 먼저 정해야
답이 있다.
