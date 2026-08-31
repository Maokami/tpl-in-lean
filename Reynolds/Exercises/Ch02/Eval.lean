/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Exercises.Ch02.Fixpoint
public import Reynolds.Exercises.Ch02.Domain.FunctionSpace

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

namespace Reynolds.Exercises.Ch02

open Reynolds Reynolds.Exercises.Ch01

universe u

variable {V : Type u} [DecidableEq V]

/-! ## 1. `while`의 함수 연산자

풀기 방정식의 우변에서 `⟦while b do c⟧` 자리를 구멍 `w`로 뚫으면 이 함수가 남는다. -/

/--
`while` 한 바퀴. `w`가 "반복의 나머지"다.

조건이 거짓이면 그 자리에서 끝나고, 참이면 본체를 한 번 돈 뒤 나머지 `w`에 넘긴다.
`s`는 본체의 뜻 — `Comm.eval`에서 `⟦c⟧`가 들어올 자리다.
-/
def whileF (b : BoolExp V) (s : State V → SigmaBot V)
    (w : State V → SigmaBot V) : State V → SigmaBot V :=
  fun σ => if ⟦b⟧ᵇ σ then Option.bind (s σ) w else some σ

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
  -- 먼저 볼 것: `Continuous`, `IsLUB`, `whileF_monotone`, `Chain.lub_apply`의 정의와 정리.
  -- 이 연습은 앞의 다른 연습 결과를 사용하지 않고 `Continuous` 정의에서 직접 증명한다.
  -- 힌트 1: 상계는 `c.le_lub`; 최소성은 상태 `σ`를 고정한 뒤 조건과 `s σ`로 나눈다.
  -- 힌트 2: `s σ = some τ`이면 `Chain.lub_le`로 각 `c.seq n τ`가 상계 아래임을 보인다.
  -- 힌트 3: 조건이 거짓이면 함수상의 0번째 항을 상계 가정에 넣는다.
  sorry


/-! ## 2. 의미 함수

여섯 절 중 다섯은 §2.2의 방정식을 받아 적은 것이다. `wh` 절만 `fix`를 부른다. -/

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

@[inherit_doc Comm.eval]
scoped notation:max "⟦" c "⟧ᶜ" => Comm.eval c

/-! ## 3. 명세를 만족한다

§2.2의 `IsSemantics`는 여섯 방정식이었다. 다섯은 정의 그대로이고,
`wh` 방정식이 `fix_eq` — 극한이 고정점이라는 사실 — 로 나온다. -/

/--
**`Comm.eval`은 §2.2의 의미 방정식을 전부 만족한다.**

`while` 절을 풀어 쓰면 `fix`는 `whileF`의 고정점이므로

```
⟦while b do c⟧ σ = whileF b ⟦c⟧ ⟦while b do c⟧ σ
                 = if ⟦b⟧ σ then ⟦c⟧ σ >>= ⟦while b do c⟧ else some σ
```

§2.2에서 정의가 되지 못했던 풀기 방정식이 정의(`fix`)와 정리(`fix_eq`)로
갈라져서 돌아왔다.
-/
theorem Comm.eval_isSemantics : IsSemantics (V := V) Comm.eval := by
  refine ⟨fun v e σ => rfl, fun σ => rfl, fun c₀ c₁ σ => rfl, fun b c₀ c₁ σ => rfl,
    fun b c σ => ?_, fun v e c σ => rfl⟩
  -- `wh` 방정식. 고정점 등식을 상태 `σ`에서 읽는다.
  have h := fix_eq (whileF_continuous b c.eval)
  calc Comm.eval (.wh b c) σ
      = whileF b c.eval (fix (whileF b c.eval) (whileF_monotone b c.eval)) σ :=
        (congrFun h σ).symm
    _ = if ⟦b⟧ᵇ σ then Option.bind (c.eval σ) (Comm.eval (.wh b c)) else some σ := rfl

/-! ## 4. 어떤 해보다도 아래에 있다

§2.2의 `unwinding_not_unique`는 풀기 방정식에 해가 여럿임을 보였다. 여기서는 방정식을
만족하는 어떤 `w`를 가져와도 `⟦while b do c⟧ ⊑ w`임을 보여 어느 해를 택하는지 답한다. -/

/--
**`while`의 뜻은 풀기 방정식의 최소 해다.**

`w`가 방정식을 만족하면 `whileF`의 고정점이고, 고정점은 전고정점이므로
`fix_least`가 바로 준다.

채점 연습이 아니다. `fix_least`가 이미 연습이라, 이것까지 비우면 비운 것끼리
의존하게 된다 (연습 독립성 원칙, `AGENTS.md` §1-9). 완성본을 읽는 자리로 남긴다.
-/
theorem Comm.eval_while_least {b : BoolExp V} {c : Comm V} {w : State V → SigmaBot V}
    (hw : ∀ σ, w σ = if ⟦b⟧ᵇ σ then Option.bind (c.eval σ) w else some σ) :
    Comm.eval (.wh b c) ≤ w :=
  fix_least (whileF_monotone b c.eval) (le_of_eq (funext fun σ => (hw σ).symm))

/-! ## 5. 여기서 어디로 가나

`Comm.eval`은 `Classical.choice` 때문에 실행할 수 없다. `Interpreter.lean`은 유한한 연료로
계산하는 `Comm.run`을 정의하고 다음 적합성(adequacy) 정리로 실행과 표시적 의미를 잇는다.

```lean
c.eval σ = some τ ↔ ∃ n, c.run n σ = some τ
```

필요한 연료 `n`은 명령과 입력, 종료 실행에 따라 달라진다. -/

end Reynolds.Exercises.Ch02
