/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Answers.Ch02.Fixpoint
public import Reynolds.Answers.Ch02.Domain.FunctionSpace

/-!
# §2.4 `while` 의 뜻 — `Comm.eval` 이 드디어 정의된다

§2.2 는 명세(`IsSemantics`)만 적고 의미 함수를 정의하지 못한 채 끝났다. 이제 재료가
전부 모였다. `Σ → Σ⊥` 는 도메인이고 (§2.3), 최소 고정점 정리가 있다 (`Fixpoint.lean`).

## 정의의 모양

`while` 이 아닌 다섯 절은 §2.2 의 의미 방정식을 그대로 옮겨 적는다. 구문 지향적이라
정의가 곧바로 선다. `while b do c` 절만 다르다.

```
⟦while b do c⟧ = fix (whileF b ⟦c⟧)
```

`whileF b s` 는 §2.2 의 풀기 방정식을 함수로 읽은 것이다 — "반복의 나머지를 `w` 라고
하면 전체는 이렇다" 를 받아 적으면 나온다. 재귀 호출이 `c` 라는 진부분항의 뜻 `⟦c⟧` 에만
일어나므로 구조적 재귀이고, `while` 자신을 부르는 자리는 `fix` 가 흡수한다.

## 이 파일이 증명하는 것

1. `whileF` 가 단조이고 연속이다 — 명제 2.1 이 실제로 일하는 자리
2. `Comm.eval` 이 §2.2 의 명세 `IsSemantics` 를 만족한다 — 여섯 방정식 전부
3. 풀기 방정식의 **어떤** 해보다도 아래에 있다 — §2.2 의 두 해 문제가 닫힌다

## 계산은 안 된다

`fix` 는 `Classical.choice` 로 극한을 고르므로 `Comm.eval` 은 계산되지 않는다.
`#eval` 로 돌려 보는 일은 다음 파일의 연료(fuel) 해석기가 맡고, 둘이 일치한다는
정리가 그 파일의 본론이다.

## 읽는 순서
`Fixpoint.lean` → 이 파일 → `Interpreter.lean` (다음 PR)
-/

@[expose] public section

namespace Reynolds.Answers.Ch02

open Reynolds Reynolds.Answers.Ch01

universe u

variable {V : Type u} [DecidableEq V]

/-! ## 1. `while` 의 함수자

풀기 방정식의 우변에서 `⟦while b do c⟧` 자리를 구멍 `w` 로 뚫으면 이 함수가 남는다. -/

-- ANCHOR: whileF
/--
`while` 한 바퀴. `w` 가 "반복의 나머지" 다.

조건이 거짓이면 그 자리에서 끝나고, 참이면 본체를 한 번 돈 뒤 나머지 `w` 에 넘긴다.
`s` 는 본체의 뜻 — `Comm.eval` 에서 `⟦c⟧` 가 들어올 자리다.
-/
def whileF (b : BoolExp V) (s : State V → SigmaBot V)
    (w : State V → SigmaBot V) : State V → SigmaBot V :=
  fun σ => if ⟦b⟧ᵇ σ then Option.bind (s σ) w else some σ
-- ANCHOR_END: whileF

omit [DecidableEq V] in
/-- `whileF` 는 단조다. `w` 가 자라면 "나머지에 넘긴 자리" 만 자라고, 나머지는 그대로다. -/
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

-- ANCHOR: whileFCont
omit [DecidableEq V] in
/--
`whileF` 는 연속이다 — **명제 2.1 이 일하는 자리**.

단조성은 위에서 끝났으므로 확인할 것은 부등식 한 방향뿐이다:
`whileF(⨆wₙ) ⊑ ⨆ whileF(wₙ)`. 상태 `σ` 를 고정하고 세 갈래로 나눈다.

- 조건이 거짓 — 왼쪽은 `some σ`. 오른쪽 사슬의 **모든** 항이 `some σ` 이므로
  0 번째 항이 이미 극한 아래에 있다.
- 본체가 `⊥` — 왼쪽이 `⊥` 라서 무엇보다도 아래다.
- 본체가 `some τ` — 왼쪽은 `(⨆wₙ) τ = ⨆(wₙ τ)` 이고, 그 사슬의 각 항
  `wₙ τ` 가 오른쪽 사슬의 `n` 번째 항과 정확히 같다.
-/
theorem whileF_continuous (b : BoolExp V) (s : State V → SigmaBot V) :
    Continuous (whileF b s) := by
  rw [continuous_iff_le (whileF_monotone b s)]
  intro c σ
  rw [Chain.lub_apply]
  unfold whileF
  by_cases hb : ⟦b⟧ᵇ σ
  · simp only [if_pos hb]
    rcases hs : s σ with _ | τ
    · simp
    · -- 왼쪽 `(⨆wₙ) τ` 의 각 항이 오른쪽 사슬의 항이다.
      change (c.apply τ).lub ≤ ((c.map (whileF_monotone b s)).apply σ).lub
      refine Chain.lub_le fun n => ?_
      have : (c.map (whileF_monotone b s)).seq n σ
          = Option.bind (s σ) (c.seq n) := by
        simp [whileF, if_pos hb]
      refine le_trans (le_of_eq ?_) (((c.map (whileF_monotone b s)).apply σ).le_lub n)
      simp [this, hs]
  · simp only [if_neg hb]
    -- 오른쪽 사슬의 0 번째 항이 이미 `some σ` 다.
    refine le_trans (le_of_eq ?_) (((c.map (whileF_monotone b s)).apply σ).le_lub 0)
    simp [whileF, if_neg hb]
-- ANCHOR_END: whileFCont

/-! ## 2. 의미 함수

여섯 절 중 다섯은 §2.2 의 방정식을 받아 적은 것이다. `wh` 절만 `fix` 를 부른다. -/

-- ANCHOR: commEval
/--
`⟦c⟧ᶜ` — 명령의 뜻. Reynolds §2.2 의 `⟦-⟧comm ∈ ⟨comm⟩ → Σ → Σ⊥`, §2.4 에서 완성된 판.

`wh` 절이 이 장의 전부다. 반복의 뜻은 `whileF` 의 **최소** 고정점이고,
"최소" 가 §2.2 에서 확인한 여러 해 중 하나를 고르는 원리다.

`Classical.choice` 를 거치므로 계산되지 않는다. 실행은 연료 해석기가 맡는다.
-/
noncomputable def Comm.eval : Comm V → State V → SigmaBot V
  | .assign v e   => fun σ => some (σ[v := ⟦e⟧ₑ σ])
  | .skip         => fun σ => some σ
  | .seq c₀ c₁    => fun σ => Option.bind (c₀.eval σ) c₁.eval
  | .ite b c₀ c₁  => fun σ => if ⟦b⟧ᵇ σ then c₀.eval σ else c₁.eval σ
  | .wh b c       => fix (whileF b c.eval) (whileF_monotone b c.eval)
  | .newvar v e c => fun σ => restore v σ (c.eval (σ[v := ⟦e⟧ₑ σ]))
-- ANCHOR_END: commEval

@[inherit_doc Comm.eval]
scoped notation:max "⟦" c "⟧ᶜ" => Comm.eval c

/-! ## 3. 명세를 만족한다

§2.2 의 `IsSemantics` 는 여섯 방정식이었다. 다섯은 정의 그대로이고,
`wh` 방정식이 `fix_eq` — 극한이 고정점이라는 사실 — 로 나온다. -/

-- ANCHOR: evalIsSemantics
/--
**`Comm.eval` 은 §2.2 의 의미 방정식을 전부 만족한다.**

`while` 절을 풀어 쓰면: `fix` 는 `whileF` 의 고정점이므로

```
⟦while b do c⟧ σ = whileF b ⟦c⟧ ⟦while b do c⟧ σ
                 = if ⟦b⟧ σ then ⟦c⟧ σ >>= ⟦while b do c⟧ else some σ
```

— §2.2 에서 정의가 되지 못했던 풀기 방정식이, 정의(`fix`)와 정리(`fix_eq`)로
갈라져서 돌아왔다.
-/
theorem Comm.eval_isSemantics : IsSemantics (V := V) Comm.eval := by
  refine ⟨fun v e σ => rfl, fun σ => rfl, fun c₀ c₁ σ => rfl, fun b c₀ c₁ σ => rfl,
    fun b c σ => ?_, fun v e c σ => rfl⟩
  -- `wh` 방정식. 고정점 등식을 상태 `σ` 에서 읽는다.
  have h := fix_eq (whileF_continuous b c.eval)
  calc Comm.eval (.wh b c) σ
      = whileF b c.eval (fix (whileF b c.eval) (whileF_monotone b c.eval)) σ :=
        (congrFun h σ).symm
    _ = if ⟦b⟧ᵇ σ then Option.bind (c.eval σ) (Comm.eval (.wh b c)) else some σ := rfl
-- ANCHOR_END: evalIsSemantics

/-! ## 4. 어떤 해보다도 아래에 있다

§2.2 의 `unwinding_not_unique` 가 남긴 물음 — 해가 여럿인데 어느 것이 뜻인가 — 을 닫는다.
풀기 방정식을 만족하는 **어떤** `w` 를 가져와도 `⟦while b do c⟧ ⊑ w` 다.
`decrFake` 처럼 없는 답을 지어내는 해는 전부 위쪽에 있고, 뜻은 그 아래에서 유일하다. -/

-- ANCHOR: whileLeast
/--
**`while` 의 뜻은 풀기 방정식의 최소 해다.**

`w` 가 방정식을 만족하면 `whileF` 의 고정점이고, 고정점은 전고정점이므로
`fix_least` 가 바로 준다.

채점 연습이 아니다 — `fix_least` 가 이미 연습이라, 이것까지 비우면 비운 것끼리
의존하게 된다 (연습 독립성 원칙, `AGENTS.md` §1-9). 완성본을 읽는 자리로 남긴다.
-/
theorem Comm.eval_while_least {b : BoolExp V} {c : Comm V} {w : State V → SigmaBot V}
    (hw : ∀ σ, w σ = if ⟦b⟧ᵇ σ then Option.bind (c.eval σ) w else some σ) :
    Comm.eval (.wh b c) ≤ w :=
  fix_least (whileF_monotone b c.eval) (le_of_eq (funext fun σ => (hw σ).symm))
-- ANCHOR_END: whileLeast

/-! ## 5. 여기서 어디로 가나

의미 함수가 섰다. 그러나 `Classical.choice` 때문에 실행할 수 없고, `while tt do skip` 을
`#eval` 로 돌려 볼 수 없다는 것은 이 장의 언어에서 꽤 아쉬운 일이다.

다음 파일이 연료(fuel) 해석기를 만든다. `Fⁿ(⊥)` 가 "본체를 최대 `n` 바퀴 도는 반복문"
이라는 `Fixpoint.lean` 의 읽기를 프로그램으로 옮긴 것이고, 연료가 충분하면 표시적 의미와
일치한다는 정리(적합성, adequacy)가 실행과 증명을 잇는다. -/

end Reynolds.Answers.Ch02
