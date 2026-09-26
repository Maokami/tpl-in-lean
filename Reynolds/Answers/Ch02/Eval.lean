/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Answers.Ch02.Fixpoint
public import Reynolds.Answers.Ch02.Domain.FunctionSpace

/-!
# §2.4 `while`의 뜻 — `Comm.eval`

Reynolds §2.4의 의미 방정식 (2.4)에 대응한다.

## 이 파일에서 다루는 것

- `while`의 풀기 방정식을 함수 연산자(functional) `whileF`로 표현한다.
- Reynolds 연습 2.4에 따라 `whileF`의 연속성을 증명한다.
- 명령의 표시적 의미 `Comm.eval`을 정의하고 §2.2의 명세를 만족함을 증명한다.
- `while`의 뜻이 풀기 방정식의 최소 해임을 증명한다.

## 핵심 아이디어

`while`이 아닌 다섯 절은 §2.2의 의미 방정식을 구문에 대한 재귀로 옮긴다. `while b do c`
절에서는 풀기 방정식의 우변을 함수로 만든 뒤 최소 고정점을 취한다.

```
⟦while b do c⟧ = fix (whileF b ⟦c⟧)
```

재귀 호출은 진부분항 `c`의 뜻에만 일어나고, `while` 자신을 다시 부르는 자리는 `fix`가
맡는다. `fix`의 극한이 `Classical.choice`를 거치므로 `Comm.eval`은 실행할 수 없다.

## 읽는 순서
`Fixpoint.lean` → 이 파일 → `Interpreter.lean`

## 책과의 차이

Reynolds는 의미 방정식과 최소 고정점 논의를 같은 절에서 전개한다. 여기서는 §2.2의 명세,
이 파일의 정의, `Interpreter.lean`의 실행 가능한 근사를 나누어 각 경계를 정리로 연결한다.
-/

@[expose] public section

namespace Reynolds.Answers.Ch02

open Reynolds Reynolds.Answers.Ch01

universe u

variable {V : Type u} [DecidableEq V]

/-! ## 1. `while`의 함수 연산자

풀기 방정식의 우변에서 `⟦while b do c⟧` 자리를 구멍 `w`로 뚫으면 이 함수가 남는다. -/

-- ANCHOR: whileF
/--
`while` 한 바퀴. `w`가 "반복의 나머지"다.

조건이 거짓이면 그 자리에서 끝나고, 참이면 본체를 한 번 돈 뒤 나머지 `w`에 넘긴다.
`s`는 본체의 뜻 — `Comm.eval`에서 `⟦c⟧`가 들어올 자리다.
-/
def whileF (b : BoolExp V) (s : State V → SigmaBot V)
    (w : State V → SigmaBot V) : State V → SigmaBot V :=
  fun σ => if ⟦b⟧ᵇ σ then Option.bind (s σ) w else some σ
-- ANCHOR_END: whileF

omit [DecidableEq V] in
/-- `whileF`는 단조다. `w`가 자라면 "나머지에 넘긴 자리"만 자라고, 나머지는 그대로다. -/
theorem whileF_monotone (b : BoolExp V) (s : State V → SigmaBot V) :
    Monotone (whileF b s) := by
  intro w w' hw σ
  unfold whileF
  by_cases hb : ⟦b⟧ᵇ σ
  · simp only [if_pos hb]
    rcases hs : s σ with _ | τ
    · simp
    · exact hw τ
  · simp [if_neg hb]

-- ANCHOR: whileF_continuous
omit [DecidableEq V] in
/--
**Reynolds 연습 2.4.** `whileF`는 연속이다.

함수상의 최소 상계인지 확인할 때 상태 `σ`를 고정하고 세 갈래로 나눈다.

- 조건이 거짓 — 상의 모든 함수가 `some σ`를 내므로 그 값이 최소 상계다.
- 본체가 `⊥` — 상의 모든 함수가 `⊥`를 내므로 확인할 것이 없다.
- 본체가 `some τ` — 왼쪽은 `(⨆wₙ) τ = ⨆(wₙ τ)`이고, 그 사슬의 각 항
  `wₙ τ`가 함수상의 `n`번째 항과 같다.
-/
@[exercise "Ex 2.4" 3]
theorem whileF_continuous (b : BoolExp V) (s : State V → SigmaBot V) :
    Continuous (whileF b s) := by
  intro c
  constructor
  · -- 상계: `whileF`의 단조성을 사슬의 각 항과 극한에 적용한다.
    rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
    exact whileF_monotone b s (c.le_lub n)
  · intro g hg σ
    unfold whileF
    by_cases hb : ⟦b⟧ᵇ σ
    · simp only [if_pos hb]
      rcases hs : s σ with _ | τ
      · simp
      · change (c.apply τ).lub ≤ g σ
        refine Chain.lub_le fun n => ?_
        calc
          (c.apply τ).seq n = whileF b s (c.seq n) σ := by simp [whileF, hb, hs]
          _ ≤ g σ := (hg ⟨c.seq n, ⟨n, rfl⟩, rfl⟩) σ
    · simp only [if_neg hb]
      calc
        some σ = whileF b s (c.seq 0) σ := by simp [whileF, hb]
        _ ≤ g σ := (hg ⟨c.seq 0, ⟨0, rfl⟩, rfl⟩) σ
-- ANCHOR_END: whileF_continuous

/-! ## 1.5 `whileF` 전용 도구 — 채점 연습을 부르지 않는 판

`Comm.eval_isSemantics`(풀기 방정식)와 `Comm.eval_while_least`(최소성),
`Comm.coincidence_general`·`Comm.eval_agree_outside_fa`·`Comm.run_complete`(Scott 귀납법)는
모두 채점 연습이 아니고, 학생에게 완성본으로 주어진다. 그런데 그 완성본들이 각각
`fix_eq`·`whileF_continuous`·`fix_least`·`scott_induction` 이라는 **채점 연습**을 부르면,
그 완성본을 재료로 쓰는 다른 채점 연습(§2.6·§2.8의 여러 연습, Ex 2.1 등)이 결국 두 채점
연습에 동시에 걸리게 된다 — 연습 독립성 원칙(`AGENTS.md` §1-9) 위반이다.

아래 세 정리는 그 네 연습을 부르지 않고 `whileF` 하나로 좁혀 같은 결론을 다시 증명한다.
`fix_eq`·`fix_least`의 **일반적인** 진술을 그대로 복사한 보조정리를 따로 두지 않는 이유는,
그러면 그 복사본이 `fix_eq`·`fix_least` 연습 자신을 그대로 닫아버리기 때문이다 — 대상을
`whileF` 하나로 좁힌 진술이라야 그 연습을 대신 풀어주지 않는다.
-/

omit [DecidableEq V] in
/--
연습 독립성(`AGENTS.md` §1-9): `while`의 풀기 방정식을 채점 연습 `fix_eq`·
`whileF_continuous` 없이 직접 증명한다. `Comm.eval_isSemantics`의 `wh` 절이 이것을 쓴다.

증명의 얼개는 `whileF_continuous`와 같지만 대상을 반복 사슬 하나 — `⊥, F(⊥), F²(⊥), …` —
로 좁혔다. 상태 `σ`를 고정하면 `fix F hm σ`는 그 사슬을 점별로 잰 극한(`Chain.lub_apply`)
이고, 그 값을 `⟦b⟧ σ`와 `⟦c⟧ σ`로 갈래를 나눠 직접 계산할 수 있다 — `whileF_continuous`처럼
공역이 프리도메인이라는 것 말고 아무 사슬에나 통하는 일반적인 연속성을 세울 필요가 없다.
-/
theorem whileF_fix_unfold (b : BoolExp V) (s : State V → SigmaBot V) (σ : State V) :
    fix (whileF b s) (whileF_monotone b s) σ
      = if ⟦b⟧ᵇ σ then Option.bind (s σ) (fix (whileF b s) (whileF_monotone b s)) else some σ := by
  have hm := whileF_monotone b s
  have hW : ∀ ρ : State V, fix (whileF b s) hm ρ = ((iterChain hm).apply ρ).lub :=
    fun ρ => Chain.lub_apply _ ρ
  rw [hW σ]
  by_cases hb : ⟦b⟧ᵇ σ
  · rcases hs : s σ with _ | τ
    · -- 본체가 ⊥. `n ≥ 1`인 항은 모두 ⊥ — 조건이 참인 자리는 언제나 본체의 값을 되묻는다.
      have hstep : ∀ n, ((iterChain hm).apply σ).seq (n + 1) = none := by
        intro n
        change (whileF b s)^[n + 1] ⊥ σ = none
        rw [Function.iterate_succ_apply']
        simp [whileF, hb, hs]
      have hle : ((iterChain hm).apply σ).lub ≤ none := by
        refine Chain.lub_le fun n => ?_
        cases n with
        | zero => exact bot_le
        | succ n => exact le_of_eq (hstep n)
      -- `rcases hs : s σ with _ | τ`가 이미 이 갈래의 목표에서 `s σ`를 `none`으로 바꿔 두었다.
      rw [le_antisymm hle bot_le, if_pos hb]
      rfl
    · -- 본체가 `some τ`. 이 사슬은 `τ`에서 시작한 반복 사슬을 한 칸 민 것과 같다.
      have hshift : ∀ n, ((iterChain hm).apply σ).seq (n + 1) = ((iterChain hm).apply τ).seq n := by
        intro n
        change (whileF b s)^[n + 1] ⊥ σ = (whileF b s)^[n] ⊥ τ
        rw [Function.iterate_succ_apply']
        simp [whileF, hb, hs]
      have h0 : ((iterChain hm).apply σ).seq 0 = none := rfl
      have hlub : ((iterChain hm).apply σ).lub = ((iterChain hm).apply τ).lub := by
        refine le_antisymm (Chain.lub_le fun n => ?_) (Chain.lub_le fun n => ?_)
        · cases n with
          | zero => rw [h0]; exact bot_le
          | succ n => rw [hshift]; exact ((iterChain hm).apply τ).le_lub n
        · rw [← hshift]; exact ((iterChain hm).apply σ).le_lub (n + 1)
      rw [if_pos hb]
      change ((iterChain hm).apply σ).lub = fix (whileF b s) hm τ
      rw [hW τ]
      exact hlub
  · -- 조건이 거짓. `n ≥ 1`인 항은 모두 `some σ` — 그 자리에서 즉시 끝난다.
    have hstep : ∀ n, ((iterChain hm).apply σ).seq (n + 1) = some σ := by
      intro n
      change (whileF b s)^[n + 1] ⊥ σ = some σ
      rw [Function.iterate_succ_apply']
      simp [whileF, hb]
    have hge : some σ ≤ ((iterChain hm).apply σ).lub := by
      rw [← hstep 0]; exact ((iterChain hm).apply σ).le_lub 1
    have hle : ((iterChain hm).apply σ).lub ≤ some σ := by
      refine Chain.lub_le fun n => ?_
      cases n with
      | zero => exact bot_le
      | succ n => exact le_of_eq (hstep n)
    rw [le_antisymm hle hge, if_neg hb]

omit [DecidableEq V] in
/--
연습 독립성(`AGENTS.md` §1-9): `whileF`의 고정점이 전고정점 아래에 있다는 것을 채점 연습
`fix_least`를 부르지 않고 증명한다. `Comm.eval_while_least`가 이것을 쓴다.

증명은 `fix_least`의 반복-사슬 귀납과 같은 모양이지만, 대상을 `whileF` 하나로 좁혔다.
`fix_least`의 **일반적인** 진술을 그대로 복사하지 않는 이유는 §1.5 첫머리에 적어 두었다 —
일반적인 복사본은 `fix_least` 연습 자체를 곧바로 닫아버린다.
-/
theorem whileF_fix_le (b : BoolExp V) (s : State V → SigmaBot V) {w : State V → SigmaBot V}
    (hw : whileF b s w ≤ w) :
    fix (whileF b s) (whileF_monotone b s) ≤ w := by
  refine (iterChain (whileF_monotone b s)).lub_le fun n => ?_
  induction n with
  | zero => exact bot_le
  | succ n ih =>
      calc (whileF b s)^[n + 1] ⊥ = whileF b s ((whileF b s)^[n] ⊥) :=
            Function.iterate_succ_apply' (whileF b s) n ⊥
        _ ≤ whileF b s w := whileF_monotone b s ih
        _ ≤ w := hw

omit [DecidableEq V] in
/--
연습 독립성(`AGENTS.md` §1-9): 채점 연습 `scott_induction`을 부르지 않고 증명하는,
`whileF`의 고정점에 대한 Scott 귀납법. 증명은 `scott_induction`과 글자까지 같다 —
대상을 `whileF` 하나로 좁혔을 뿐이다. `Comm.coincidence_general`·`Comm.eval_agree_outside_fa`
(둘 다 `FreeVars.lean`)와 `Comm.run_complete`(`Interpreter.lean`)처럼 `while`의 뜻에 대해
귀납하는 완성본 증명들이 이것을 쓴다.
-/
theorem whileF_scott_induction (b : BoolExp V) (s : State V → SigmaBot V)
    {P : (State V → SigmaBot V) → Prop}
    (hadm : ∀ c : Chain (State V → SigmaBot V), (∀ n, P (c.seq n)) → P c.lub)
    (hbot : P ⊥) (hstep : ∀ w, P w → P (whileF b s w)) :
    P (fix (whileF b s) (whileF_monotone b s)) := by
  refine hadm (iterChain (whileF_monotone b s)) fun n => ?_
  induction n with
  | zero => exact hbot
  | succ n ih =>
      rw [iterChain_seq, Function.iterate_succ_apply']
      exact hstep _ ih

/-! ## 2. 의미 함수

여섯 절 중 다섯은 §2.2의 방정식을 받아 적은 것이다. `wh` 절만 `fix`를 부른다. -/

-- ANCHOR: Comm.eval
/--
`⟦c⟧ᶜ` — 명령의 뜻. Reynolds §2.2의 `⟦-⟧comm ∈ ⟨comm⟩ → Σ → Σ⊥`, §2.4에서 완성된 판.

여섯 절 가운데 `wh` 절에서만 최소 고정점이 필요하다. 반복의 뜻은 `whileF`의 최소
고정점이고, "최소"가 §2.2에서 확인한 여러 해 중 하나를 고르는 원리다.

`Classical.choice`를 거치므로 계산되지 않는다. 실행은 연료 해석기가 맡는다.
-/
noncomputable def Comm.eval : Comm V → State V → SigmaBot V
  | .assign v e   => fun σ => some (σ[v := ⟦e⟧ₑ σ])
  | .skip         => fun σ => some σ
  | .seq c₀ c₁    => fun σ => Option.bind (c₀.eval σ) c₁.eval
  | .ite b c₀ c₁  => fun σ => if ⟦b⟧ᵇ σ then c₀.eval σ else c₁.eval σ
  | .wh b c       => fix (whileF b c.eval) (whileF_monotone b c.eval)
  | .newvar v e c => fun σ => restore v σ (c.eval (σ[v := ⟦e⟧ₑ σ]))
-- ANCHOR_END: Comm.eval

@[inherit_doc Comm.eval]
scoped notation:max "⟦" c "⟧ᶜ" => Comm.eval c

/-! ## 3. 명세를 만족한다

§2.2의 `IsSemantics`는 여섯 방정식이었다. 다섯은 정의 그대로이고,
`wh` 방정식이 `whileF_fix_unfold` — 극한이 고정점이라는 사실을 `whileF`에 대해 직접
증명한 것 — 로 나온다. (일반적인 `fix_eq`가 아닌 이유는 §1.5 참고.) -/

-- ANCHOR: Comm.eval_isSemantics
/--
**`Comm.eval`은 §2.2의 의미 방정식을 전부 만족한다.**

`while` 절을 풀어 쓰면 `fix`는 `whileF`의 고정점이므로

```
⟦while b do c⟧ σ = whileF b ⟦c⟧ ⟦while b do c⟧ σ
                 = if ⟦b⟧ σ then ⟦c⟧ σ >>= ⟦while b do c⟧ else some σ
```

§2.2에서 정의가 되지 못했던 풀기 방정식이 정의(`fix`)와 정리(`whileF_fix_unfold`)로
갈라져서 돌아왔다.
-/
theorem Comm.eval_isSemantics : IsSemantics (V := V) Comm.eval := by
  refine ⟨fun v e σ => rfl, fun σ => rfl, fun c₀ c₁ σ => rfl, fun b c₀ c₁ σ => rfl,
    fun b c σ => ?_, fun v e c σ => rfl⟩
  -- `wh` 방정식. `whileF_fix_unfold`가 상태 `σ`에서 바로 읽어 준다.
  exact whileF_fix_unfold b c.eval σ
-- ANCHOR_END: Comm.eval_isSemantics

/-! ## 4. 어떤 해보다도 아래에 있다

§2.2의 `unwinding_not_unique`는 풀기 방정식에 해가 여럿임을 보였다. 여기서는 방정식을
만족하는 어떤 `w`를 가져와도 `⟦while b do c⟧ ⊑ w`임을 보여 어느 해를 택하는지 답한다. -/

-- ANCHOR: Comm.eval_while_least
/--
**`while`의 뜻은 풀기 방정식의 최소 해다.**

`w`가 방정식을 만족하면 `whileF`의 고정점이고, 고정점은 전고정점이므로
`whileF_fix_le`가 바로 준다.

채점 연습이 아니다. `fix_least`가 이미 연습이라, 이것까지 비우면 비운 것끼리
의존하게 된다 (연습 독립성 원칙, `AGENTS.md` §1-9). 그래서 `fix_least`도, 그 일반적인
진술을 그대로 복사한 판도 아니라 — 복사본은 `fix_least` 연습을 그대로 닫아버린다 — §1.5
의 `whileF` 전용 판 `whileF_fix_le`를 쓴다. 완성본을 읽는 자리로 남긴다.
-/
theorem Comm.eval_while_least {b : BoolExp V} {c : Comm V} {w : State V → SigmaBot V}
    (hw : ∀ σ, w σ = if ⟦b⟧ᵇ σ then Option.bind (c.eval σ) w else some σ) :
    Comm.eval (.wh b c) ≤ w :=
  whileF_fix_le b c.eval (le_of_eq (funext fun σ => (hw σ).symm))
-- ANCHOR_END: Comm.eval_while_least

/-! ## 5. 여기서 어디로 가나

`Comm.eval`은 `Classical.choice` 때문에 실행할 수 없다. `Interpreter.lean`은 유한한 연료로
계산하는 `Comm.run`을 정의하고 다음 적합성(adequacy) 정리로 실행과 표시적 의미를 잇는다.

```lean
c.eval σ = some τ ↔ ∃ n, c.run n σ = some τ
```

필요한 연료 `n`은 명령과 입력, 종료 실행에 따라 달라진다. -/

end Reynolds.Answers.Ch02
