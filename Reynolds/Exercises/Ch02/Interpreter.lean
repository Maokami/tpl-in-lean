/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Exercises.Ch02.Eval
public import Reynolds.Answers.Ch02.Notation
-- `#guard` 는 컴파일 시점에 계산한다 (AGENTS.md §10).
public meta import Reynolds.Answers.Ch02.Notation
public meta import Reynolds.Exercises.Ch02.Semantics
public meta import Reynolds.Exercises.Ch01.Semantics
public meta import Reynolds.Prelude

/-!
# §2.4 연료 해석기 — 실행과 증명이 만난다

`Comm.eval` 은 `Classical.choice` 로 극한을 고르므로 실행할 수 없다. 증명에는 그것으로
충분하지만, 이 장의 언어는 명령형 프로그램이고 프로그램은 돌려 보고 싶어진다.

`Fixpoint.lean` 의 읽기가 길을 준다. `Fⁿ(⊥)` 는 "본체를 최대 `n` 바퀴 도는 반복문" 이었다.
바퀴 수에 상한을 두면 극한이 필요 없어지고, 남는 것은 전부 계산이다. 그 상한이
**연료(fuel)** 다.

## `none` 이 두 가지를 뜻하게 된다

`c.run n σ = none` 은 "정말 발산한다" 일 수도, "연료가 모자랐다" 일 수도 있다.
둘을 가르는 것이 이 파일의 두 정리다.

- `run_mono` — 연료를 늘려서 나빠지지 않는다. `none` 이 `some` 으로 바뀔 수는 있어도
  `some` 이 사라지지는 않는다.
- `eval_eq_run` (적합성, adequacy) — `⟦c⟧ σ = some σ'` ⟺ 어떤 연료로든
  `c.run n σ = some σ'`. 왼쪽은 증명용, 오른쪽은 실행용이고, 둘이 같다는 것을 커널이
  보증한다.

완전성 방향이 **Scott 귀납법의 첫 실전**이다. "결과를 내면 어떤 연료로 재현된다" 는
성질이 허용 가능한 이유가 정확히 `Σ⊥` 의 평평함이다 — 극한이 `some` 이면 어느 단계가
이미 `some` 이다 (`Chain.flat_lub_mem_range`).

## 읽는 순서
`Eval.lean` → 이 파일. 2장 본문 §2.4 는 여기서 끝난다.
-/

-- 이 파일은 `#guard` 로 해석기를 실제로 돌린다.
set_option linter.hashCommand false

@[expose] public section

namespace Reynolds.Exercises.Ch02

open Reynolds Reynolds.Exercises.Ch01

universe u

variable {V : Type u} [DecidableEq V]

/-! ## 1. 해석기

연료는 `while` 을 풀 때만 소모한다. 반복이 없는 명령은 연료와 무관하게 그냥 실행된다 —
발산의 근원이 `while` 하나뿐이기 때문이다. -/

/--
연료 해석기. Reynolds §2.4 의 근사 명령 `wₙ` 을 실행 가능하게 옮긴 것이다.

`wh` 절만 연료를 쓴다. 연료가 남았으면 조건을 보고, 본체를 돈 뒤 연료 하나를 태우고
계속한다. 연료가 바닥나면 `none` — 그 `none` 은 발산일 수도 연료 부족일 수도 있고,
구분은 아래 두 정리가 맡는다.

`Comm.eval` 과 달리 전부 계산이다. `#eval` 과 `#guard` 가 돌아간다.
-/
def Comm.run : Comm V → ℕ → State V → SigmaBot V
  | .assign v e,   _, σ => some (σ[v := ⟦e⟧ₑ σ])
  | .skip,         _, σ => some σ
  | .seq c₀ c₁,    n, σ => Option.bind (c₀.run n σ) (c₁.run n)
  | .ite b c₀ c₁,  n, σ => if ⟦b⟧ᵇ σ then c₀.run n σ else c₁.run n σ
  | .newvar v e c, n, σ => restore v σ (c.run n (σ[v := ⟦e⟧ₑ σ]))
  | .wh _ _,       0, _ => none
  | .wh b c,   n + 1, σ =>
      if ⟦b⟧ᵇ σ then Option.bind (c.run (n + 1) σ) ((Comm.wh b c).run n) else some σ

-- 계승. Reynolds §2.1 의 예제 프로그램이 실제로 돈다. x ↦ 5 에서 y = 120.
#guard ((⟪ y := 1; while x > 0 do (y := y × x; x := x - 1) ⟫ᶜ.run 10 (State.const 5)).map
          fun σ => (σ "x", σ "y")) == some (0, 120)

-- 연료가 모자라면 `none`. 다섯 바퀴가 필요한데 셋만 줬다.
#guard (⟪ while x > 0 do x := x - 1 ⟫ᶜ.run 3 (State.const 5)).isNone

-- 발산하는 프로그램은 어떤 연료로도 `none`. (전부 시험할 수는 없으니 하나만 본다.)
#guard ((⟪ while tt do skip ⟫ᶜ : Comm String).run 1000 (State.const 0)).isNone

/-! ## 2. 연료를 늘려서 나빠지지 않는다

`Σ → Σ⊥` 의 순서로 말하면 `c.run n ⊑ c.run (n+1)` — 연료 축은 정확히 §2.3 의
정보 순서를 따라 올라간다. `Fⁿ(⊥)` 의 사슬과 같은 모양이다. -/

/-- `bind` 는 평평한 순서에서 양쪽 인자에 대해 단조다. -/
theorem Option.bind_le_bind {α β : Type u} {x x' : Option α} {f f' : α → Option β}
    (hx : x ≤ x') (hf : ∀ a, f a ≤ f' a) : Option.bind x f ≤ Option.bind x' f' := by
  rcases hx with h | h
  · rw [h]; simp
  · rw [h]
    rcases x' with _ | a
    · simp
    · exact hf a

/--
**연료 단조성.** 결과가 나빠지지 않는다 — `none` 이 `some` 이 될 수는 있어도
`some` 이 흔들리지는 않는다.

`while` 이 아닌 절은 부분 명령에 넘기면 끝난다. `wh` 절이 유일하게 손이 가는 곳인데,
연료가 하나 늘면 본체와 이어지는 반복 양쪽의 연료가 늘고, `bind` 가 그 둘을 함께 올린다.
-/
@[exercise "§2.4 run-mono" 2]
theorem Comm.run_le_succ : ∀ (c : Comm V) (n : ℕ) (σ : State V),
    c.run n σ ≤ c.run (n + 1) σ := by
  -- 먼저 볼 것: 바로 위의 `Option.bind_le_bind`. `seq` 와 `wh` 절이 그것으로 돈다.
  -- 힌트 1: 명령에 대한 구조적 귀납. `skip` 과 `newvar` 는 DSL 이 키워드로 만들었으니
  --         분기 이름을 `«skip»`, `«newvar»` 로 써야 한다.
  -- 힌트 2: `run` 은 연료도 매칭하므로 자유 변수 연료로는 저절로 줄지 않는다.
  --         분기마다 `simp only [Comm.run]` 이나 `rw [Comm.run]` 으로 방정식을 펴라.
  -- 힌트 3: `wh` 절 안에서 연료에 대한 귀납을 겹친다. 0 은 `none ⊑ 무엇이든`.
  sorry


/-- 단조성의 쓰기 좋은 꼴. `some` 은 연료를 아무리 부어도 그대로다. -/
theorem Comm.run_stable {c : Comm V} {n m : ℕ} {σ σ' : State V}
    (h : c.run n σ = some σ') (hnm : n ≤ m) : c.run m σ = some σ' := by
  induction m, hnm using Nat.le_induction with
  | base => exact h
  | succ m _ ih =>
      have hs := Comm.run_le_succ c m σ
      rw [ih] at hs
      simpa using hs

/-! ## 3. 적합성 — 건전성 방향

해석기가 답하면 표시적 의미도 같은 답을 한다. 명령에 대한 구조적 귀납이고,
`wh` 절에서만 연료에 대한 귀납이 겹친다. 각 갈래는 `eval_isSemantics` 의 방정식에
결과를 맞춰 넣는 계산이다. -/

/-- 건전성. `run` 이 `some` 이면 `eval` 도 같은 `some` 이다. -/
theorem Comm.run_sound {c : Comm V} :
    ∀ {n : ℕ} {σ σ' : State V}, c.run n σ = some σ' → c.eval σ = some σ' := by
  induction c with
  | assign v e => intro n σ σ' h; rw [Comm.run] at h; exact h
  | «skip» => intro n σ σ' h; rw [Comm.run] at h; exact h
  | seq c₀ c₁ ih₀ ih₁ =>
      intro n σ σ' h
      rw [Comm.run, Option.bind_eq_some_iff] at h
      obtain ⟨τ, h₀, h₁⟩ := h
      change Option.bind (c₀.eval σ) c₁.eval = some σ'
      rw [ih₀ h₀]
      exact ih₁ h₁
  | ite b c₀ c₁ ih₀ ih₁ =>
      intro n σ σ' h
      rw [Comm.run] at h
      change (if ⟦b⟧ᵇ σ then c₀.eval σ else c₁.eval σ) = some σ'
      by_cases hb : ⟦b⟧ᵇ σ
      · rw [if_pos hb] at h ⊢; exact ih₀ h
      · rw [if_neg hb] at h ⊢; exact ih₁ h
  | «newvar» v e c ih =>
      intro n σ σ' h
      rw [Comm.run] at h
      change restore v σ (c.eval (σ[v := ⟦e⟧ₑ σ])) = some σ'
      rcases hc : c.run n (σ[v := ⟦e⟧ₑ σ]) with _ | τ
      · rw [hc] at h; simp [restore] at h
      · rw [ih hc]
        rw [hc] at h
        exact h
  | wh b c ihc =>
      intro n
      induction n with
      | zero => intro σ σ' h; simp [Comm.run] at h
      | succ n ihn =>
          intro σ σ' h
          -- `eval` 쪽을 풀기 방정식으로 벗긴다.
          have heq := Comm.eval_isSemantics.2.2.2.2.1 b c σ
          rw [Comm.run] at h
          by_cases hb : ⟦b⟧ᵇ σ
          · rw [if_pos hb] at h
            rw [Option.bind_eq_some_iff] at h
            obtain ⟨τ, hbody, hrest⟩ := h
            rw [heq, if_pos hb, ihc hbody]
            exact ihn hrest
          · rw [if_neg hb] at h
            rw [heq, if_neg hb]
            exact h

/-! ## 4. 적합성 — 완전성 방향, Scott 귀납법의 첫 실전

표시적 의미가 답하면 어떤 연료가 그 답을 재현한다. `wh` 절에서 `⟦while⟧ = fix F` 이므로
`fix` 에 대한 성질을 증명해야 하고, 그 도구가 `Fixpoint.lean` 의 Scott 귀납법이다.

성질 `P w` : "`w` 가 답하면 어떤 연료의 `run` 이 재현한다".

- **허용 가능한가** — 여기가 요점이다. 사슬의 극한이 `some` 이면, `Σ⊥` 가 평평하므로
  **어느 단계가 이미 그 `some` 이다** (`Chain.flat_lub_mem_range`). 극한에서의 주장이
  단계 하나의 주장으로 내려오고, 그 단계는 가정이 처리한다. 평평하지 않았다면 극한이
  단계들 밖의 값일 수 있어 이 성질은 허용 가능하지 않았을 것이다.
- **`⊥` 에서** — `⊥` 는 답하지 않으므로 확인할 것이 없다.
- **걸음에서** — `F` 한 바퀴가 답했으면, 조건이 거짓이면 연료 1 로 충분하고, 참이면
  본체의 연료(구조적 귀납 가설)와 나머지의 연료(Scott 가설)를 합쳐 하나 태운다.
-/

/-- 완전성. `eval` 이 `some` 이면 어떤 연료의 `run` 이 같은 `some` 이다. -/
theorem Comm.run_complete {c : Comm V} :
    ∀ {σ σ' : State V}, c.eval σ = some σ' → ∃ n, c.run n σ = some σ' := by
  induction c with
  | assign v e => exact fun h => ⟨0, by rw [Comm.run]; exact h⟩
  | «skip» => exact fun h => ⟨0, by rw [Comm.run]; exact h⟩
  | seq c₀ c₁ ih₀ ih₁ =>
      intro σ σ' h
      rw [show Comm.eval (.seq c₀ c₁) σ = Option.bind (c₀.eval σ) c₁.eval from rfl,
        Option.bind_eq_some_iff] at h
      obtain ⟨τ, h₀, h₁⟩ := h
      obtain ⟨n₀, hr₀⟩ := ih₀ h₀
      obtain ⟨n₁, hr₁⟩ := ih₁ h₁
      refine ⟨max n₀ n₁, ?_⟩
      rw [Comm.run, Comm.run_stable hr₀ (le_max_left _ _)]
      exact Comm.run_stable hr₁ (le_max_right _ _)
  | ite b c₀ c₁ ih₀ ih₁ =>
      intro σ σ' h
      rw [show Comm.eval (.ite b c₀ c₁) σ
          = if ⟦b⟧ᵇ σ then c₀.eval σ else c₁.eval σ from rfl] at h
      by_cases hb : ⟦b⟧ᵇ σ
      · rw [if_pos hb] at h
        obtain ⟨n, hr⟩ := ih₀ h
        exact ⟨n, by rw [Comm.run, if_pos hb]; exact hr⟩
      · rw [if_neg hb] at h
        obtain ⟨n, hr⟩ := ih₁ h
        exact ⟨n, by rw [Comm.run, if_neg hb]; exact hr⟩
  | «newvar» v e c ih =>
      intro σ σ' h
      rw [show Comm.eval (.newvar v e c) σ
          = restore v σ (c.eval (σ[v := ⟦e⟧ₑ σ])) from rfl] at h
      rcases hc : c.eval (σ[v := ⟦e⟧ₑ σ]) with _ | τ
      · rw [hc] at h; simp [restore] at h
      · rw [hc] at h
        obtain ⟨n, hr⟩ := ih hc
        exact ⟨n, by rw [Comm.run, hr]; exact h⟩
  | wh b c ihc =>
      -- Scott 귀납법. `⟦while⟧ = fix (whileF b ⟦c⟧)` 이므로 성질을 `fix` 로 옮긴다.
      have key : ∀ σ σ', fix (whileF b c.eval) (whileF_monotone b c.eval) σ = some σ'
          → ∃ n, (Comm.wh b c).run n σ = some σ' := by
        refine scott_induction (whileF_monotone b c.eval)
          (P := fun w => ∀ σ σ', w σ = some σ' → ∃ n, (Comm.wh b c).run n σ = some σ')
          (fun d hd σ σ' hlub => ?_) (fun σ σ' h => by simp at h) (fun w hw σ σ' h => ?_)
        · -- 허용 가능성. 평평해서 극한의 `some` 은 어느 단계의 `some` 이다.
          rw [Chain.lub_apply] at hlub
          obtain ⟨k, hk⟩ := (d.apply σ).flat_lub_mem_range
          rw [hlub] at hk
          exact hd k σ σ' hk
        · -- 걸음. `whileF` 한 바퀴를 벗긴다.
          rw [whileF] at h
          by_cases hb : ⟦b⟧ᵇ σ
          · rw [if_pos hb, Option.bind_eq_some_iff] at h
            obtain ⟨τ, hbody, hrest⟩ := h
            obtain ⟨m, hm⟩ := ihc hbody
            obtain ⟨k, hk⟩ := hw τ σ' hrest
            refine ⟨max m k + 1, ?_⟩
            rw [Comm.run, if_pos hb,
              Comm.run_stable hm (le_trans (le_max_left _ _) (Nat.le_succ _))]
            exact Comm.run_stable hk (le_max_right _ _)
          · rw [if_neg hb] at h
            exact ⟨1, by rw [Comm.run, if_neg hb]; exact h⟩
      intro σ σ' h
      exact key σ σ' h

/--
**적합성(adequacy)** — 표시적 의미와 해석기가 일치한다.

왼쪽은 증명용이고 오른쪽은 실행용이다. 이 정리가 있어서 `#guard` 로 확인한 계산이
`⟦-⟧ᶜ` 에 대한 사실이 되고, `⟦-⟧ᶜ` 로 증명한 성질이 실행에 대한 보증이 된다.

채점 연습이 아니다 — 증명이 Scott 귀납법과 `fix_eq` 위에 서 있어서, 비우면 비운 것끼리
의존한다 (연습 독립성 원칙). 완전성 방향의 Scott 귀납법 적용을 완성본으로 읽는 것이
이 파일의 목적이다.
-/
theorem Comm.eval_eq_run {c : Comm V} {σ σ' : State V} :
    c.eval σ = some σ' ↔ ∃ n, c.run n σ = some σ' := by
  constructor
  · exact Comm.run_complete
  · rintro ⟨n, hn⟩
    exact Comm.run_sound hn

/-! ## 5. 2장 본문이 닫혔다

§2.2 의 물음 — `while` 의 뜻은 무엇인가 — 에 대한 답이 완성됐다.

| 물음 | 답 | 어디서 |
|---|---|---|
| 방정식은 뜻을 정하나 | 못 정한다. 해가 여럿이다 | §2.2 `unwinding_not_unique` |
| 어느 해를 고르나 | 정보 순서의 최소 해 | §2.3 순서, §2.4 `fix` |
| 그 해는 존재하나 | 연속이면 반복의 극한으로 | `fix_eq` · `fix_least` |
| 실행은 어떻게 하나 | 연료 해석기로, 적합성이 다리 | 이 파일 |

남은 §2.5 ~ §2.8 은 이 의미 함수 위의 이야기다 — 자유 변수와 별칭(§2.5),
구문 설탕(§2.6), 산술 오류(§2.7), 완전 추상성(§2.8). 책 연습문제 2.1 ~ 2.10 도
이제 재료가 전부 있다. -/

end Reynolds.Exercises.Ch02
