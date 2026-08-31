/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Exercises.Ch02.Eval
public import Reynolds.Answers.Ch02.Notation
-- `#guard`는 컴파일 시점에 계산한다 (AGENTS.md §10).
public meta import Reynolds.Answers.Ch02.Notation
public meta import Reynolds.Exercises.Ch02.Semantics
public meta import Reynolds.Exercises.Ch01.Semantics
public meta import Reynolds.Prelude

/-!
# §2.4 연료 해석기와 적합성

`Comm.eval`은 `Classical.choice`로 극한을 고르므로 직접 실행할 수 없다. 이 파일은 모든
`while`에 유한한 단계 상한을 주는 연료 해석기(fuel interpreter) `Comm.run`을 정의한다.

`run n`은 조건을 처음부터 거짓으로 판정하는 데도 연료 1이 필요하다. 따라서 본체를
`k`번 실행하고 끝나는 반복에는 적어도 `k + 1`의 연료가 필요하다. 본체에 중첩된
`while`이 있으면 그 반복도 같은 연료 상한 아래에서 실행된다. 그러므로 `run n`은
Reynolds의 근사 명령 `wₙ`이나 `Fⁿ(⊥)`와 단계마다 같지는 않다. 세 구성은 유한한 근사라는
역할을 공유한다.

`c.run n σ = none`만으로는 발산과 연료 부족을 구분할 수 없다. `Comm.run_le_succ`는 연료를
늘려 얻은 결과가 사라지지 않음을 보이고, 적합성(adequacy) 정리 `Comm.eval_eq_run`은

```text
c.eval σ = some σ' ↔ ∃ n, c.run n σ = some σ'
```

를 증명한다. 단계별 등식이 아니라, 종료 결과 전체가 일치한다는 뜻이다.
완전성(completeness) 방향은 Scott 귀납법을 사용한다. 사슬의 극한이 `some`이면 평평한
`Σ⊥`에서는 어느 단계가 이미
같은 `some`이기 때문이다 (`Chain.flat_lub_mem_range`).

## 읽는 순서

`Eval.lean` → 이 파일

## 책과의 차이

Reynolds는 근사 명령 `wₙ`의 의미를 사용한다. 여기서는 중첩 반복까지 계산할 수 있도록
구문에 직접 연료를 주고, 두 접근이 같은 종료 결과를 낸다는 것을 적합성 정리로 연결한다.
-/

-- 이 파일은 `#guard`로 해석기를 실제로 돌린다.
set_option linter.hashCommand false

@[expose] public section

namespace Reynolds.Exercises.Ch02

open Reynolds Reynolds.Exercises.Ch01

universe u

variable {V : Type u} [DecidableEq V]

/-! ## 1. 해석기

연료는 `while`을 풀 때만 소모한다. 반복이 없는 명령은 연료와 무관하게 실행된다.
이 언어에서는 `while`만 비종료를 일으킬 수 있기 때문이다. -/

/--
연료 해석기. Reynolds §2.4의 유한 근사와 같은 역할을 하는 실행 가능한 정의다.

`wh` 절만 연료를 쓴다. 연료가 남았으면 조건을 검사하고, 참이면 본체와 나머지 반복을
실행한다. 바깥 반복을 한 번 풀 때 나머지 반복의 연료는 하나 줄지만, 본체에는 현재 연료를
그대로 준다. 본체에 중첩된 반복이 있으면 그 반복도 유한하게 실행하기 위해서다.

연료가 바닥나면 `none`을 돌려준다. 이 값은 발산과 연료 부족을 구분하지 않는다.
`Comm.eval`과 달리 정의 전체를 계산할 수 있어 `#eval`과 `#guard`에서 사용할 수 있다.
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

-- 계승. Reynolds §2.1의 예제 프로그램이 실제로 돈다. x ↦ 5에서 y = 120.
#guard ((⟪ y := 1; while x > 0 do (y := y × x; x := x - 1) ⟫ᶜ.run 10 (State.const 5)).map
          fun σ => (σ "x", σ "y")) == some (0, 120)

-- 본체를 다섯 번 실행하려면 마지막 거짓 조건 검사까지 합쳐 연료 6이 필요하다.
#guard (⟪ while x > 0 do x := x - 1 ⟫ᶜ.run 5 (State.const 5)).isNone
#guard ((⟪ while x > 0 do x := x - 1 ⟫ᶜ.run 6 (State.const 5)).map fun σ => σ "x")
  == some 0

-- 발산하는 프로그램은 어떤 연료로도 `none`. (전부 시험할 수는 없으니 하나만 본다.)
#guard ((⟪ while tt do skip ⟫ᶜ : Comm String).run 1000 (State.const 0)).isNone

/-! ## 2. 연료를 늘려도 결과가 사라지지 않는다

`Σ → Σ⊥`의 순서로 말하면 `c.run n ⊑ c.run (n+1)`이다. 연료에 따른 근사는 §2.3의
정보 순서를 따라 올라가며, `Fⁿ(⊥)`의 반복 사슬과 같은 역할을 한다. -/

/-- `bind`는 평평한 순서에서 양쪽 인자에 대해 단조다. -/
theorem Option.bind_le_bind {α β : Type u} {x x' : Option α} {f f' : α → Option β}
    (hx : x ≤ x') (hf : ∀ a, f a ≤ f' a) : Option.bind x f ≤ Option.bind x' f' := by
  rcases hx with h | h
  · rw [h]; simp
  · rw [h]
    rcases x' with _ | a
    · simp
    · exact hf a

/--
**연료 단조성.** 연료를 늘리면 `none`이 `some`으로 바뀔 수 있지만, 이미 얻은 `some`은
사라지거나 다른 결과로 바뀌지 않는다.

`while`이 아닌 절은 부분 명령의 귀납 가설로 처리한다. `wh` 절에서는 연료 귀납을 한 번 더
사용한다. 연료가 하나 늘면 본체와 이어지는 반복 양쪽의 연료가 늘고, `bind`가 두 결과를
함께 올린다.
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


/-- 단조성의 쓰기 좋은 꼴. `some`은 연료를 아무리 늘려도 그대로다. -/
theorem Comm.run_stable {c : Comm V} {n m : ℕ} {σ σ' : State V}
    (h : c.run n σ = some σ') (hnm : n ≤ m) : c.run m σ = some σ' := by
  induction m, hnm using Nat.le_induction with
  | base => exact h
  | succ m _ ih =>
      have hs := Comm.run_le_succ c m σ
      rw [ih] at hs
      simpa using hs

/-! ## 3. 적합성의 건전성(soundness) 방향

해석기가 답하면 표시적 의미도 같은 답을 한다. 명령에 대한 구조적 귀납이고,
`wh` 절에서만 연료에 대한 귀납이 겹친다. 각 갈래는 `eval_isSemantics`의 방정식에
결과를 맞춰 넣는 계산이다. -/

/-- 건전성. `run`이 `some`이면 `eval`도 같은 `some`이다. -/
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

/-! ## 4. 적합성의 완전성 방향

표시적 의미가 답하면 어떤 유한 연료가 그 답을 재현한다. `wh` 절에서
`⟦while⟧ = fix F`이므로 `fix`에 대한 성질을 증명해야 하고, 그 도구가 `Fixpoint.lean`의
Scott 귀납법이다.

성질 `P w`: "`w`가 답하면 어떤 연료의 `run`이 재현한다".

- **허용 가능한가** — 여기가 요점이다. 사슬의 극한이 `some`이면, `Σ⊥`가 평평하므로
  **어느 단계가 이미 그 `some`이다** (`Chain.flat_lub_mem_range`). 극한에서의 주장이
  단계 하나의 주장으로 내려오고, 그 단계는 가정이 처리한다. 평평하지 않다면 이 단계 선택
  논증은 쓸 수 없으며, 허용 가능성은 다른 방법으로 따로 증명해야 한다.
- **`⊥`에서** — `⊥`는 답하지 않으므로 확인할 것이 없다.
- **걸음에서** — `F` 한 바퀴가 답했으면, 조건이 거짓이면 연료 1로 충분하고, 참이면
  본체의 연료(구조적 귀납 가설)와 나머지의 연료(Scott 가설)를 합쳐 하나 태운다.
-/

/-- 완전성. `eval`이 `some`이면 어떤 연료의 `run`이 같은 `some`이다. -/
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
      -- Scott 귀납법. `⟦while⟧ = fix (whileF b ⟦c⟧)`이므로 성질을 `fix`로 옮긴다.
      have key : ∀ σ σ', fix (whileF b c.eval) (whileF_monotone b c.eval) σ = some σ'
          → ∃ n, (Comm.wh b c).run n σ = some σ' := by
        refine scott_induction (whileF_monotone b c.eval)
          (P := fun w => ∀ σ σ', w σ = some σ' → ∃ n, (Comm.wh b c).run n σ = some σ')
          (fun d hd σ σ' hlub => ?_) (fun σ σ' h => by simp at h) (fun w hw σ σ' h => ?_)
        · -- 허용 가능성. 평평해서 극한의 `some`은 어느 단계의 `some`이다.
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

왼쪽은 증명용이고 오른쪽은 실행용이다. `#guard`로 확인한 종료 결과는 건전성 방향을 통해
`⟦-⟧ᶜ`의 결과가 된다. 반대로 표시적 의미에서 증명한 종료 결과는 충분한 연료의 `run`에서
재현된다. 이 정리는 `none`에 관한 임의의 성질까지 옮긴다고 주장하지 않는다.

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

/-! ## 5. 이후 절로 이어지는 기반

§2.5 이후에는 `Comm.eval`을 바탕으로 자유 변수와 별칭, 구문 설탕, 산술 오류,
완전 추상성을 다룬다. -/

end Reynolds.Exercises.Ch02
