/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Answers.Ch02.FullAbstraction2

/-!
# 2장 연습문제 (1) — 새 명령에 뜻을 주는 두 가지 방법

Reynolds 연습 2.1 과 2.2 에 대응한다.

## 두 연습이 같은 것을 묻는다

언어에 명령을 하나 더하려 한다. 뜻을 어떻게 줄 것인가? 길이 둘이다.

- **직접 준다** — 의미 방정식을 새로 쓴다. `while` 처럼 자기 자신을 다시 부르면
  최소 고정점이 필요하다.
- **번역한다** — 이미 있는 구문으로 옮긴다 (§2.6 의 문법 설탕).

연습 2.1(이중 대입)은 번역으로 푼다. 연습 2.2(`repeat`)는 **둘 다** 하고 나서
같다는 것을 증명한다 — 그 증명이 이 장에서 가장 볼 만한 연습이다.

## 연습 2.2(c) 가 왜 좋은가

최소 고정점을 두 번, **반대 방향으로** 쓴다.

- `⟦repeat⟧ ⊑ ⟦설탕⟧` — 설탕 쪽이 `repeat` 의 풀기 방정식을 만족하므로,
  최소성(`fix_least`)이 곧바로 준다.
- `⟦설탕⟧ ⊑ ⟦repeat⟧` — 이번에는 `while` 쪽의 최소성을 쓴다. `repeat` 쪽으로 만든
  함수가 `while` 의 풀기 방정식을 만족함을 보이면 된다.

"최소 고정점" 의 최소성이 양쪽에서 한 번씩 일을 한다. §2.4 에서 왜 하필 최소를 골랐는지에
대한 가장 좋은 답이다.

## 읽는 순서
2장 본문을 다 읽은 뒤. `Eval.lean` 의 `whileF` 와 `Fixpoint.lean` 의 `fix_least` 를 쓴다.
-/

@[expose] public section

namespace Reynolds.Answers.Ch02.Ex

open Reynolds Reynolds.Answers.Ch01 Reynolds.Answers.Ch02

universe u

variable {V : Type u} [DecidableEq V]

/-! ## 연습 2.1 — 이중 대입 `v₀, v₁ := e₀, e₁`

두 식을 **먼저 모두 평가하고** 나서 두 변수에 넣는다. 그래야 `x, y := y, x` 가 맞바꾸기가
된다 — 순서대로 하면 첫 대입이 두 번째 식이 읽을 값을 망가뜨린다.

그 "먼저 모두 평가" 를 지역 변수 하나로 산다. 둘째 식의 값만 미리 담아 두면 충분하다. -/

-- ANCHOR: simulAssign
/--
이중 대입의 디슈가링. 둘째 식의 값을 임시 변수 `t` 에 담아 두고 차례로 대입한다.

```
v₀, v₁ := e₀, e₁   ⟹   newvar t := e₁ in (v₀ := e₀; v₁ := t)
```

임시 변수가 하나면 되는 이유: 망가질 수 있는 것은 `e₁` 뿐이다. `e₀` 는 아직 아무것도
바뀌기 전에 평가된다.
-/
def simulAssign (v₀ v₁ t : V) (e₀ e₁ : IntExp V) : Comm V :=
  .newvar t e₁ (.seq (.assign v₀ e₀) (.assign v₁ (.var t)))

-- `x, y := y, x` 는 맞바꾸기다. §2.5 의 `swap` 과 달리 임시 변수가 구문에 드러나지 않는다.
example : simulAssign "x" "y" "t" (.var "y") (.var "x")
    = ⟪ newvar t := x in (x := y; y := t) ⟫ᶜ := rfl

/--
**연습 2.1 — 이중 대입의 의미 방정식.**

```
⟦v₀, v₁ := e₀, e₁⟧ σ = some σ[v₀ := ⟦e₀⟧σ][v₁ := ⟦e₁⟧σ]
```

두 식 모두 **원래 상태** `σ` 에서 평가된다는 것이 요점이다.

임시 변수에 붙는 조건 셋이 각각 다른 일을 한다.

- `t ∉ FV(e₀)` — `t` 를 깔아도 `e₀` 의 값이 안 변한다.
- `t ≠ v₀` — `v₀` 에 대입해도 `t` 에 담아 둔 값이 안 망가진다.
- `t ≠ v₁` — 마지막 복원이 `v₁` 을 건드리지 않는다.

**`v₀ = v₁` 이면?** 위 식이 그대로 답한다 — 같은 자리에 두 번 쓰면 나중 것이 남으므로
`σ[v₀ := ⟦e₁⟧σ]` 다. 정의를 고치지 않고도 경계 경우가 결정되어 있다는 것이, 뜻을
식으로 적어 두는 것의 이득이다. 아래 `simulAssign_eval_self` 가 그 따름정리다.
-/
@[exercise "Ex 2.1" 2]
theorem simulAssign_eval (v₀ v₁ t : V) (e₀ e₁ : IntExp V)
    (ht : t ∉ e₀.fv) (htv₀ : t ≠ v₀) (htv₁ : t ≠ v₁) (σ : State V) :
    (simulAssign v₀ v₁ t e₀ e₁).eval σ
      = some ((σ[v₀ := ⟦e₀⟧ₑ σ])[v₁ := ⟦e₁⟧ₑ σ]) := by
  -- `t` 를 깔아도 `e₀` 의 값은 그대로다.
  have he₀ : ⟦e₀⟧ₑ (σ[t := ⟦e₁⟧ₑ σ]) = ⟦e₀⟧ₑ σ := by
    refine coincidence_intExp e₀ _ σ ?_
    intro u hu
    exact State.subst_of_ne _ _ _ _ (fun hEq => ht (hEq ▸ hu))
  -- 담아 둔 값은 `t ≠ v₀` 덕분에 `v₀` 대입을 지나도 그대로다.
  have hlook : ((σ[t := ⟦e₁⟧ₑ σ])[v₀ := ⟦e₀⟧ₑ σ]) t = ⟦e₁⟧ₑ σ := by
    rw [State.subst_of_ne _ _ _ _ htv₀, State.subst_self]
  -- `newvar` 를 펴고, 안쪽 두 대입을 차례로 계산한다.
  have hnv : (simulAssign v₀ v₁ t e₀ e₁).eval σ
      = restore t σ ((Comm.seq (.assign v₀ e₀) (.assign v₁ (.var t))).eval
          (σ[t := ⟦e₁⟧ₑ σ])) := Comm.eval_isSemantics.2.2.2.2.2 _ _ _ _
  rw [hnv, Comm.eval_isSemantics.2.2.1, Comm.eval_isSemantics.1, he₀]
  change restore t σ
      ((Comm.assign v₁ (.var t)).eval ((σ[t := ⟦e₁⟧ₑ σ])[v₀ := ⟦e₀⟧ₑ σ])) = _
  rw [Comm.eval_isSemantics.1]
  simp only [IntExp.eval]
  rw [hlook]
  -- 남은 것은 복원이다. `t` 에 대한 갱신을 앞으로 옮겨 상쇄한다.
  simp only [restore, Option.map_some, Option.some.injEq, State.subst_def]
  rw [Function.update_comm (Ne.symm htv₁), Function.update_comm (Ne.symm htv₀),
    Function.update_idem, Function.update_eq_self]
-- ANCHOR_END: simulAssign

/--
**같은 변수에 두 번 쓰면 나중 것이 남는다.** 연습 2.1 이 남기는 논의거리의 답.

Reynolds 가 `v₀ = v₁` 일 때를 정하라고 하는데, 디슈가링을 정하면 답도 정해진다.
`v₁ := t` 가 뒤에 오므로 `e₁` 이 이긴다.
-/
theorem simulAssign_eval_self (v t : V) (e₀ e₁ : IntExp V)
    (ht : t ∉ e₀.fv) (htv : t ≠ v) (σ : State V) :
    (simulAssign v v t e₀ e₁).eval σ = some (σ[v := ⟦e₁⟧ₑ σ]) := by
  rw [simulAssign_eval v v t e₀ e₁ ht htv htv σ]
  simp [State.subst_def, Function.update_idem]

/-! ## 연습 2.2 — `repeat c until b`

본체를 **먼저 한 번 돌리고**, 조건이 참이 될 때까지 되돌아간다. `while` 과 달리 본체가
적어도 한 번은 실행된다.

풀기 방정식은 이렇다.

```
⟦repeat c until b⟧ σ = ⟦c⟧ σ >>= fun σ' => if ⟦b⟧ σ' then some σ' else ⟦repeat c until b⟧ σ'
```

양변에 같은 구가 나오므로 §2.2 에서 `while` 이 겪은 일을 그대로 겪는다 — 정의가 되지
못한다. §2.4 의 답을 다시 쓴다. -/

/-! ### (a) 최소 고정점으로 주기 -/

-- ANCHOR: repeatF
/--
`repeat` 한 바퀴. `w` 가 "되돌아갔을 때의 나머지" 다.

`whileF` 와 모양이 다르다. 조건 검사가 본체 **뒤**에 오고, 조건이 참일 때 **끝난다**
(`while` 은 참일 때 계속한다).
-/
def repeatF (b : BoolExp V) (s : State V → SigmaBot V)
    (w : State V → SigmaBot V) : State V → SigmaBot V :=
  fun σ => Option.bind (s σ) (fun σ' => if ⟦b⟧ᵇ σ' then some σ' else w σ')

omit [DecidableEq V] in
/-- `repeatF` 는 단조다. `w` 가 자라면 "되돌아간 자리" 만 자란다. -/
theorem repeatF_monotone (b : BoolExp V) (s : State V → SigmaBot V) :
    Monotone (repeatF b s) := by
  intro w w' hw σ
  unfold repeatF
  rcases hs : s σ with _ | τ
  · simp
  · by_cases hb : ⟦b⟧ᵇ τ
    · simp [hb]
    · simpa [hb] using hw τ

omit [DecidableEq V] in
/--
`repeatF` 는 연속이다. 연습 2.4(`whileF`)와 같은 모양이고, 갈래를 나누는 순서만 다르다 —
본체를 먼저 돌리므로 `s σ` 로 먼저 나눈다.
-/
theorem repeatF_continuous (b : BoolExp V) (s : State V → SigmaBot V) :
    Continuous (repeatF b s) := by
  intro c
  constructor
  · rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
    exact repeatF_monotone b s (c.le_lub n)
  · intro g hg σ
    unfold repeatF
    rcases hs : s σ with _ | τ
    · simp
    · change (if ⟦b⟧ᵇ τ then some τ else c.lub τ) ≤ g σ
      by_cases hb : ⟦b⟧ᵇ τ
      · rw [if_pos hb]
        calc (some τ : SigmaBot V) = repeatF b s (c.seq 0) σ := by simp [repeatF, hs, hb]
          _ ≤ g σ := (hg ⟨c.seq 0, ⟨0, rfl⟩, rfl⟩) σ
      · rw [if_neg hb]
        change (c.apply τ).lub ≤ g σ
        refine Chain.lub_le fun n => ?_
        calc (c.apply τ).seq n = repeatF b s (c.seq n) σ := by simp [repeatF, hs, hb]
          _ ≤ g σ := (hg ⟨c.seq n, ⟨n, rfl⟩, rfl⟩) σ

/-- **연습 2.2(a).** `repeat` 의 뜻 — 풀기 방정식의 최소 해. -/
noncomputable def repeatEval (b : BoolExp V) (c : Comm V) : State V → SigmaBot V :=
  fix (repeatF b c.eval) (repeatF_monotone b c.eval)

/-- (a) 가 풀기 방정식을 만족한다. `fix_eq` 를 상태 하나에서 읽은 것이다. -/
theorem repeatEval_unwind (b : BoolExp V) (c : Comm V) (σ : State V) :
    repeatEval b c σ
      = Option.bind (c.eval σ) (fun σ' => if ⟦b⟧ᵇ σ' then some σ' else repeatEval b c σ') :=
  (congrFun (fix_eq (repeatF_continuous b c.eval)) σ).symm
-- ANCHOR_END: repeatF

/-! ### (b) 구문 설탕으로 주기 -/

-- ANCHOR: repeatSugar
/--
**연습 2.2(b).** 같은 것을 이미 있는 구문으로 옮긴다.

```
repeat c until b   ⟹   c; while ¬b do c
```

본체를 한 번 돌리고, 조건이 **거짓인 동안** 계속 돈다. `repeat` 의 "참이면 끝" 이
`while` 의 "거짓인 동안 계속" 으로 뒤집힌다.
-/
def repeatSugar (b : BoolExp V) (c : Comm V) : Comm V :=
  .seq c (.wh (.not b) c)
-- ANCHOR_END: repeatSugar

/-! ### (c) 둘이 같다

이 장에서 가장 볼 만한 연습이다. 최소성을 **양쪽에서 한 번씩** 쓴다. -/

-- ANCHOR: repeatEquiv
/--
**연습 2.2(c) — 두 정의가 같다.**

```
⟦repeat c until b⟧ = ⟦c; while ¬b do c⟧
```

증명이 대칭이라 아름답다. 양쪽 다 `fix_least` 인데, 최소성을 쓰는 고정점이 다르다.

- `⊑` — 설탕 쪽 함수가 **`repeat` 의** 풀기 방정식을 만족함을 보인다. 그러면
  `repeat` 의 최소성이 곧바로 준다.
- `⊒` — `repeat` 쪽으로 만든 함수가 **`while` 의** 풀기 방정식을 만족함을 보인다.
  그러면 `while` 의 최소성이 준다.

양쪽 모두, 후보가 단순히 전고정점인 것이 아니라 **정확한 고정점**임이 계산으로 나온다.
조건이 참인 갈래와 거짓인 갈래에서 `repeat` 와 `while` 의 방정식이 서로를 메운다.

§2.4 에서 왜 하필 **최소** 고정점이었는지에 대한 답이 여기 있다. 다른 해를 골랐다면
두 정의가 어긋났을 것이다.
-/
@[exercise "Ex 2.2c" 3]
theorem repeatEval_eq_repeatSugar (b : BoolExp V) (c : Comm V) :
    repeatEval b c = (repeatSugar b c).eval := by
  -- 설탕 쪽을 풀어 둔다. `W` 가 안쪽 `while` 의 뜻이다.
  set W : State V → SigmaBot V := (Comm.wh (.not b) c).eval with hW
  have hsugar : (repeatSugar b c).eval = fun σ => Option.bind (c.eval σ) W := rfl
  -- `while` 의 풀기 방정식. 조건이 `¬b` 임에 주의.
  have hWeq : ∀ σ : State V, W σ
      = if ⟦(.not b : BoolExp V)⟧ᵇ σ then Option.bind (c.eval σ) W else some σ :=
    fun σ => Comm.eval_isSemantics.2.2.2.2.1 _ _ σ
  -- 조건의 값을 `b` 로 바꿔 읽는다.
  have hnot : ∀ σ : State V, ⟦(.not b : BoolExp V)⟧ᵇ σ = !(⟦b⟧ᵇ σ) := fun _ => rfl
  rw [hsugar]
  refine le_antisymm ?_ ?_
  · -- `⊑` — 설탕 쪽이 `repeat` 의 고정점이므로 최소성이 준다.
    refine fix_least (repeatF_monotone b c.eval) (le_of_eq ?_)
    funext σ
    change Option.bind (c.eval σ) (fun σ' => if ⟦b⟧ᵇ σ' then some σ' else Option.bind (c.eval σ') W)
        = Option.bind (c.eval σ) W
    rcases hs : c.eval σ with _ | τ
    · simp
    · change (if ⟦b⟧ᵇ τ then some τ else Option.bind (c.eval τ) W) = W τ
      rw [hWeq τ, hnot τ]
      by_cases hb : ⟦b⟧ᵇ τ <;> simp [hb]
  · -- `⊒` — `repeat` 쪽으로 만든 함수가 `while` 의 고정점이므로 `while` 의 최소성이 준다.
    have hWle : W ≤ fun σ' => if ⟦b⟧ᵇ σ' then some σ' else repeatEval b c σ' := by
      refine fix_least (whileF_monotone _ _) (le_of_eq ?_)
      funext σ'
      change (if ⟦(.not b : BoolExp V)⟧ᵇ σ' then
              Option.bind (c.eval σ') (fun σ'' => if ⟦b⟧ᵇ σ'' then some σ'' else repeatEval b c σ'')
            else some σ')
          = (if ⟦b⟧ᵇ σ' then some σ' else repeatEval b c σ')
      rw [hnot σ']
      by_cases hb : ⟦b⟧ᵇ σ' <;> simp [hb, (repeatEval_unwind b c σ').symm]
    intro σ
    calc Option.bind (c.eval σ) W
        ≤ Option.bind (c.eval σ) (fun σ' => if ⟦b⟧ᵇ σ' then some σ' else repeatEval b c σ') :=
          Option.bind_le_bind (le_refl _) hWle
      _ = repeatEval b c σ := (repeatEval_unwind b c σ).symm
-- ANCHOR_END: repeatEquiv

/-! ## 여기서 어디로 가나

연습 2.1 과 2.2 로 "명령을 더하는 두 길" 을 다 걸어 보았다. 번역은 값싸고, 직접 정의는
`while` 이 그랬듯 고정점을 요구한다. 그리고 둘이 만나는 자리에서 **최소성이 양쪽으로**
일한다는 것을 보았다.

다음 묶음은 `while` 자체에 대한 두 어려운 연습이다 — 구체적인 반복의 닫힌 꼴(연습 2.3)과
`while b do c ≡ while b do (c; if b then c else skip)`(연습 2.5). -/

end Reynolds.Answers.Ch02.Ex
