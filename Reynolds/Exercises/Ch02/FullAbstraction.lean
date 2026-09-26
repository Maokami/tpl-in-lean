/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Exercises.Ch02.ArithErrors

/-!
# §2.8 건전성과 완전 추상성 (1) — 문맥, 관찰, 그리고 두 방향

Reynolds §2.8 전반부에 대응한다. "무엇을 관찰하기로 했는가" 가 모든 것을 좌우한다는
이 장의 마지막 교훈은 `FullAbstraction2.lean` 이다.

## 묻는 것

지금까지 만든 표시적 의미 `⟦-⟧` 가 **옳은 추상 수준인가**? 두 방향으로 나뉜다.

- **건전성(soundness)** — 뜻이 같다고 한 것들이 정말 구별되지 않는가? 어떤 문맥에
  넣어도 다르게 행동하지 않아야 한다. 의미론이 **너무 거칠지** 않다는 뜻이다.
- **완전 추상성(full abstraction)** — 건전하면서, 구별되지 않는 것은 뜻도 같은가?
  의미론이 **너무 섬세하지** 않다는 뜻이다.

둘 다 성립하면 "뜻이 같다" 와 "어떤 프로그램에 끼워 넣어도 똑같이 행동한다" 가 정확히
같은 말이 된다.

## 문맥과 관찰

**문맥(context)** 은 구멍이 하나 뚫린 명령이다. `C[c]` 는 그 구멍에 `c` 를 **끼워 넣은**
것이고, 치환이 아니다 — 이름 바꾸기를 하지 않으므로 `c` 의 자유 변수가 문맥의 `newvar`
에 **잡힐 수 있다**. 그것이 문맥의 요점이다. 프로그램 조각은 자기가 어디에 놓일지 모른다.

**관찰(observation)** 은 밖에서 볼 수 있는 것이다. 두 가지를 둔다.

- `observe σ v c` — 초기 상태 `σ` 에서 돌려 종료 여부와 변수 `v` 의 최종 값을 본다.
- `observeHalt σ c` — **종료했는지만** 본다.

두 번째가 훨씬 빈약한데도 구별하는 힘이 같다는 것이 이 절의 놀라운 결과다.

## 이 파일의 결론

1. `⟦-⟧` 는 **합성적(compositional)** 이다 — `⟦c⟧ = ⟦c'⟧` 이면 어느 문맥에서도 같다.
   여기서 건전성이 곧바로 나온다.
2. `⟦-⟧` 는 풍부한 관찰에 대해 **완전 추상**이다. 빈 문맥 하나면 충분하다.
3. `⟦-⟧` 는 **종료 여부만** 보는 관찰에 대해서도 완전 추상이다. 값의 차이를 종료의
   차이로 바꾸는 문맥 `− ; if v = κ then skip else (while true do skip)` 이 열쇠다.

## 읽는 순서
`ArithErrors.lean` → 이 파일 → `FullAbstraction2.lean` (관찰의 선택과 세 등식)
-/

@[expose] public section

namespace Reynolds.Exercises.Ch02

open Reynolds Reynolds.Answers.Ch01

universe u

variable {V : Type u} [DecidableEq V]

/-! ## 1. 문맥

구멍이 하나 있는 명령이다. 명령을 부분으로 갖는 생성자마다 "구멍이 그 안에 있는" 경우를
하나씩 둔다. `assign` 과 `skip` 은 명령을 품지 않으므로 나오지 않는다. -/

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

/-! ## 2. 합성성

`⟦-⟧` 는 부분의 뜻으로부터 전체의 뜻을 만든다. 그래서 부분을 뜻이 같은 것으로 바꾸면
전체의 뜻도 안 바뀐다. 건전성이 여기서 곧바로 나온다. -/

/--
`while` 의 뜻은 본체의 **뜻에만** 의존한다.

`fix` 가 받는 단조성 증명이 본체의 뜻으로부터 계산되므로, 뜻을 바꿔 쓰면 증명도 따라
바뀐다 — 그래서 `rw` 한 번으로 끝난다. 구문이 달라도 뜻이 같으면 반복의 뜻도 같다는,
합성성의 `wh` 절이다.
-/
theorem Comm.eval_wh_congr {b : BoolExp V} {d d' : Comm V} (h : d.eval = d'.eval) :
    (Comm.wh b d).eval = (Comm.wh b d').eval := by
  change fix (whileF b d.eval) (whileF_monotone b d.eval)
      = fix (whileF b d'.eval) (whileF_monotone b d'.eval)
  rw [h]

/--
**합성성.** 뜻이 같은 조각은 어느 문맥에서도 바꿔 끼울 수 있다.

문맥에 대한 구조적 귀납이다. 각 절은 그 생성자의 의미 방정식을 한 번 쓰는 계산이고,
`wh` 절만 `eval_wh_congr` 가 필요하다 — 거기서만 뜻이 `fix` 를 통과하기 때문이다.

이것이 표시적 의미론의 정의적 성질이다. 뜻이 **부분의 뜻으로부터** 만들어지므로, 부분을
뜻이 같은 것으로 갈아 끼워도 전체가 안 변한다.
-/
@[exercise "§2.8 fill-congr" 2]
theorem Ctx.fill_congr (C : Ctx V) {c c' : Comm V} (h : c.eval = c'.eval) :
    (C.fill c).eval = (C.fill c').eval := by
  -- 먼저 볼 것: 바로 위 `Comm.eval_wh_congr` (완성되어 있다). `wh` 절이 그것을 쓴다.
  -- 힌트 1: 문맥에 대한 구조적 귀납. `newvar` 분기는 `«newvar»` 로 쓴다.
  -- 힌트 2: `wh` 를 뺀 각 절은 `funext σ` 뒤에 `change` 로 그 생성자의 의미 방정식을
  --         펼치고 귀납 가설을 `rw` 하면 끝난다 (`Option.bind`, `if`, `restore`).
  -- 힌트 3: `wh` 절만 `fix` 를 지나므로 `Comm.eval_wh_congr` 가 필요하다.
  sorry


/-! ## 3. 관찰

밖에서 볼 수 있는 것을 정한다. 무엇을 보기로 하느냐가 "구별된다" 의 뜻을 정하고,
따라서 완전 추상성의 뜻을 정한다. -/

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

/-! ## 4. 건전성

합성성의 따름정리다. 뜻이 같으면 어느 문맥에 넣어도 결과가 같고, 따라서 무엇을
관찰하든 같다. -/

/-- **건전성.** 뜻이 같으면 어떤 문맥에서도 구별되지 않는다. 두 관찰 모두에 대해. -/
theorem eval_sound {c c' : Comm V} (h : c.eval = c'.eval) : ObsEq c c' ∧ HaltEq c c' := by
  refine ⟨fun C σ v => ?_, fun C σ => ?_⟩ <;>
    simp only [observe, observeHalt, Ctx.fill_congr C h]

/-! ## 5. 발산하는 명령

완전 추상성의 증명에서 "값이 다르면 발산시킨다" 는 문맥을 만들려면 발산하는 명령이
하나 필요하다. -/

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
  -- 힌트 1: 이 반복의 함수 연산자는 항등 함수다 — `whileF tru ⟦skip⟧ w = w` 가 `rfl` 로 된다.
  -- 힌트 2: 그러면 `⊥` 가 전고정점이므로 `fix_least` 가 `⟦diverge⟧ ≤ ⊥` 를 준다.
  --         사슬을 펼칠 필요가 없다.
  -- 힌트 3: 함수 공간의 `≤` 는 점별이므로 그 부등식을 `σ` 에 적용한 뒤 `simpa`.
  sorry


/-! ## 6. 완전 추상성 — 풍부한 관찰

빈 문맥 하나면 충분하다. 관찰이 사실상 뜻을 그대로 읽어 내기 때문이다.

`V` 가 비어 있지 않아야 한다. 변수가 하나도 없으면 "변수의 최종 값" 이라는 관찰이
아무것도 보지 못해서, 발산과 종료조차 구별하지 못한다 — 관찰이 빈약하면 완전 추상성이
깨진다는 것을 가장 값싸게 보여 주는 예다. 바로 아래 §7 은 이 가정이 필요 없다. -/

/--
**구별되지 않으면 뜻이 같다** (풍부한 관찰).

빈 문맥에서 각 초기 상태를 본다. 한쪽만 발산하면 `none` 과 `some _` 로 갈리고, 둘 다
종료하면 두 최종 상태가 모든 변수에서 같으므로 함수 외연성으로 상태가 같다.
-/
@[exercise "§2.8 obs-complete" 2]
theorem obsEq_imp_eval_eq [Inhabited V] {c c' : Comm V} (h : ObsEq c c') : c.eval = c'.eval := by
  -- 힌트 1: 빈 문맥(`Ctx.hole`) 하나면 충분하다. `funext σ` 로 상태를 고정한다.
  -- 힌트 2: 두 결과를 `rcases h1 : c.eval σ with _ | τ` 로 네 갈래로 나눈다.
  -- 힌트 3: 한쪽만 발산하는 갈래는 아무 변수(`default`)에서 `none` 과 `some _` 로 갈린다.
  --         둘 다 종료하는 갈래는 모든 변수에서 값이 같으므로 `funext` 로 상태가 같다.
  sorry


/--
**`⟦-⟧` 는 완전 추상이다** (풍부한 관찰).

"뜻이 같다" 와 "어떤 문맥에서도 같게 관찰된다" 가 정확히 같은 말이다.

채점 연습이 아니다. 두 방향이 각각 `Ctx.fill_congr` 와 `obsEq_imp_eval_eq` 이고 둘 다
이미 연습이라, 비우면 비운 것끼리 의존한다 (연습 독립성 원칙, `AGENTS.md` §1-9).
-/
theorem eval_fullyAbstract [Inhabited V] (c c' : Comm V) : c.eval = c'.eval ↔ ObsEq c c' :=
  ⟨fun h => (eval_sound h).1, obsEq_imp_eval_eq⟩

/-! ## 7. 완전 추상성 — 종료 여부만 보는 관찰

여기가 이 절의 놀라운 대목이다. 최종 값을 전혀 보지 않고 **끝났는지만** 보아도 구별하는
힘이 줄지 않는다.

열쇠는 값의 차이를 종료의 차이로 **바꾸는** 문맥이다.

```
− ; if v = κ then skip else (while true do skip)
```

두 결과가 변수 `v` 에서 갈린다면, `κ` 를 한쪽 값으로 잡아 두면 한쪽만 이 문맥에서
끝난다. 프로그램을 관찰 장치로 쓰는 것이다.

그리고 이 판본은 `Inhabited V` 가 필요 없다. 종료 여부는 변수를 지목하지 않고도 볼 수
있고, 값이 갈리는 경우에는 갈리는 변수가 **저절로 주어지기** 때문이다. -/

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

/--
**`⟦-⟧` 는 종료 관찰에 대해서도 완전 추상이다.**

`ObsEq` 와 `HaltEq` 는 겉보기에 힘이 아주 다른데 같은 것을 갈라낸다. 둘 다 "뜻이 같다"
와 동치이므로 서로 동치이기도 하다 — 아래 `obsEq_iff_haltEq` 가 그것이다.
-/
theorem eval_fullyAbstract_halt (c c' : Comm V) : c.eval = c'.eval ↔ HaltEq c c' :=
  ⟨fun h => (eval_sound h).2, haltEq_imp_eval_eq⟩

/--
**두 관찰의 힘이 같다.** 최종 값을 보든 종료 여부만 보든 갈라내는 것이 정확히 같다.

값을 보는 쪽이 당연히 더 강할 것 같지만, 종료만 보는 쪽도 문맥을 써서 값을 종료로
번역할 수 있으므로 손해가 없다. 관찰을 **줄여도** 완전 추상성이 유지되는 예다.
다음 파일에서는 반대로 관찰을 **늘리면** 무엇이 깨지는지 본다.
-/
theorem obsEq_iff_haltEq [Inhabited V] (c c' : Comm V) : ObsEq c c' ↔ HaltEq c c' := by
  rw [← eval_fullyAbstract c c', eval_fullyAbstract_halt c c']

/-! ## 8. 여기서 어디로 가나

`⟦-⟧` 가 옳은 추상 수준이라는 것을 확인했다 — 너무 거칠지도(건전성), 너무 섬세하지도
(완전 추상성) 않다.

그런데 이 답 전체가 **무엇을 관찰하기로 했는가** 에 매달려 있다. 관찰을 바꾸면 답도
바뀐다. `FullAbstraction2.lean` 에서 우리 의미론이 같다고 보는 프로그램 쌍들을 실제로
증명한 뒤, 실행 시간이나 중간 상태를 관찰에 넣으면 그 등식들이 어떻게 무너지는지,
그리고 8장의 병행 합성과 13장의 프로시저 별칭이 왜 다른 의미론을 요구하는지 짚는다. -/

end Reynolds.Exercises.Ch02
