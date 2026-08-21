/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Answers.Ch02.Syntax
public import Reynolds.Answers.Ch01.Semantics
public import Reynolds.Meta.Exercise
-- `#guard` 는 컴파일 시점에 계산한다 (AGENTS.md §10).
public meta import Reynolds.Answers.Ch02.Syntax
public meta import Reynolds.Answers.Ch01.Semantics

/-!
# §2.2 표시적 의미론 — 그리고 `while` 이라는 벽

Reynolds §2.2 에 대응한다.

## 이 파일에서 다루는 것
- 불 식의 뜻. 1장과 달리 `Bool` 이고, 그래서 실제로 돌아간다
- `Σ⊥` — 상태 또는 비종료. Reynolds 가 `⊥` 를 도입하는 자리
- 명령의 의미 방정식 다섯 개
- **여섯 번째 방정식이 뜻을 유일하게 정하지 못한다는 것.** 이 절의 결론이다

## 1장과 무엇이 다른가

1장의 의미 함수는 구문에 대한 구조적 재귀였다. 각 절이 자기보다 작은 부분식의 뜻으로
자기 뜻을 정했고, 그래서 정의가 곧 함수를 유일하게 결정했다
(`Depth/Algebra.lean` 이 그 유일성을 초기 대수로 설명한다).

`while b do c` 는 그렇지 않다. 뜻을 쓰려고 하면 이렇게 된다.

```
⟦while b do c⟧ σ = if ⟦b⟧ σ then (⟦while b do c⟧)⊥⊥ (⟦c⟧ σ) else σ
```

우변에 `while b do c` **자신**이 나온다. 부분식이 아니라 자기 자신이므로 구조적 재귀가
아니고, 따라서 이것은 정의가 아니라 **방정식**이다. 방정식은 해가 없을 수도, 여럿일 수도
있다. 이 파일의 마지막 절에서 실제로 여럿임을 증명한다.

## 왜 그게 중요한가

Reynolds 는 여기서 도메인 이론으로 넘어간다. 해가 여럿이면 그중 하나를 **고르는 원리**가
있어야 하고, 그 원리가 "가장 적게 정의된 해" 즉 최소 고정점이다. §2.3 에서 그 순서를 만들고
§2.4 에서 최소 고정점 정리를 증명한다.

이 파일을 읽고 나면 §2.3 이 왜 필요한지가 분명해진다. 순서를 뒤집어서 도메인 이론을 먼저
배우면 그 동기가 사라진다.

## 읽는 순서
`Syntax.lean` → 이 파일 → `Domain.lean`
-/

-- 이 파일은 `#guard` 로 계산을 확인한다.
set_option linter.hashCommand false

@[expose] public section

/-! ## 불 값으로 가는 확장은 1장 이름공간에 둔다

`Cmp` 와 `LogOp` 는 1장 타입이다. 확장을 2장 이름공간에 두면 `c.denoteBool` 같은 점 표기가
안 되므로, 타입이 사는 곳에 맞춰 1장 이름공간에 넣는다. 파일과 이름공간이 갈리지만
같은 타입에 대한 연산을 한 이름 아래 모으는 쪽이 읽기에 낫다. -/

namespace Reynolds.Answers.Ch01

/-- 비교 기호의 뜻, `Bool` 판. 1장 `Cmp.denote` 의 계산되는 짝이다. -/
def Cmp.denoteBool : Cmp → Int → Int → Bool
  | .eq, a, b => a == b
  | .ne, a, b => a != b
  | .lt, a, b => a < b
  | .le, a, b => a ≤ b
  | .gt, a, b => a > b
  | .ge, a, b => a ≥ b

/-- 논리 기호의 뜻, `Bool` 판. -/
def LogOp.denoteBool : LogOp → Bool → Bool → Bool
  | .and, a, b => a && b
  | .or,  a, b => a || b
  | .imp, a, b => !a || b
  | .iff, a, b => a == b

/-- 비교의 두 뜻이 맞물린다. -/
theorem Cmp.denoteBool_iff (c : Cmp) (a b : Int) :
    c.denoteBool a b = true ↔ c.denote a b := by
  cases c <;> simp [Cmp.denote, Cmp.denoteBool]

/-- 논리 연산의 두 뜻이 맞물린다. 전제는 부분식에 대한 귀납 가설로 들어온다. -/
theorem LogOp.denoteBool_iff (op : LogOp) {a b : Bool} {p q : Prop}
    (hp : a = true ↔ p) (hq : b = true ↔ q) :
    op.denoteBool a b = true ↔ op.denote p q := by
  cases op <;> cases a <;> cases b <;> simp_all [LogOp.denote, LogOp.denoteBool]

end Reynolds.Answers.Ch01

namespace Reynolds.Answers.Ch02

open Reynolds Reynolds.Answers.Ch01

universe u

/-! ## 1. 불 식의 뜻 — `Bool` 로 돌아간다

1장에서 단언의 뜻을 `Prop` 으로 준 이유는 양화사였다. `⟦∀v. p⟧ σ = ∀ n : ℤ, …` 는
정수 전체를 훑으므로 `Bool` 로 정의가 서지 않는다.

불 식에는 양화사가 없다. 그 이유가 사라지므로 `Bool` 로 갈 수 있고, 결과가 실제로 계산된다.
비교와 논리 연산의 뜻만 `Bool` 판으로 다시 쓰면 된다. -/

-- ANCHOR: boolEval
/--
`⟦b⟧ᵇ σ` — 불 식의 뜻. Reynolds §2.2 의 `⟦-⟧boolexp ∈ ⟨boolexp⟩ → Σ → 𝔹`.

1장의 `Assert.eval` 과 절이 하나씩 대응하고, 결과 타입만 `Prop` 에서 `Bool` 로 바뀌었다.
그 차이가 `#eval` 로 돌릴 수 있느냐를 가른다.
-/
def BoolExp.eval {V : Type u} : BoolExp V → State V → Bool
  | .tru,         _ => true
  | .fls,         _ => false
  | .cmp c e₀ e₁, σ => c.denoteBool (⟦e₀⟧ₑ σ) (⟦e₁⟧ₑ σ)
  | .not b,       σ => !b.eval σ
  | .bin op b₀ b₁, σ => op.denoteBool (b₀.eval σ) (b₁.eval σ)
-- ANCHOR_END: boolEval

@[inherit_doc BoolExp.eval]
scoped notation:max "⟦" b "⟧ᵇ" => BoolExp.eval b

-- 1장의 `⟦e⟧ₑ` 와 달리 결과가 눈에 보인다.
#guard ⟦(.cmp .lt (.var "x") (.num 10) : BoolExp String)⟧ᵇ (State.const 3) == true
#guard ⟦(.cmp .lt (.var "x") (.num 10) : BoolExp String)⟧ᵇ (State.const 42) == false

/-! ### 1장의 뜻과 어긋나지 않는가

Reynolds 는 불 식을 "양화사 없는 단언" 이라고 부른다. 그 말이 맞다면 두 의미 함수가
양화사 없는 조각에서 같은 답을 내야 한다. 그것을 정리로 확인한다. -/

/-- 불 식을 단언으로 읽는다. 양화사가 없으므로 절이 그대로 옮겨진다. -/
def BoolExp.toAssert {V : Type u} : BoolExp V → Assert V
  | .tru          => .tru
  | .fls          => .fls
  | .cmp c e₀ e₁  => .cmp c e₀ e₁
  | .not b        => .not b.toAssert
  | .bin op b₀ b₁ => .bin op b₀.toAssert b₁.toAssert

-- ANCHOR: boolAgree
/--
**불 식은 양화사 없는 단언이다** — 두 의미 함수가 일치한다.

Reynolds 가 §2.1 에서 한 문장으로 넘어가는 말을 정리로 확인한 것이다.
`Prop` 과 `Bool` 의 갈림이 표현력 차이가 아니라 **결정 가능성** 차이라는 것이 요점이다.
양화사가 빠지면 결정 가능해지고, 그러면 두 표현이 같은 것을 말한다.
-/
@[exercise "§2.2 boolexp-assert" 2]
theorem boolExp_eval_iff {V : Type u} [DecidableEq V] (b : BoolExp V) (σ : State V) :
    ⟦b.toAssert⟧ₐ σ ↔ ⟦b⟧ᵇ σ = true := by
  induction b with
  | tru => simp [BoolExp.toAssert, Assert.eval, BoolExp.eval]
  | fls => simp [BoolExp.toAssert, Assert.eval, BoolExp.eval]
  | cmp c e₀ e₁ => simp [BoolExp.toAssert, Assert.eval, BoolExp.eval, Cmp.denoteBool_iff]
  | not b ih => simp [BoolExp.toAssert, Assert.eval, BoolExp.eval, ih]
  | bin op b₀ b₁ ih₀ ih₁ =>
      simp only [BoolExp.toAssert, Assert.eval, BoolExp.eval]
      exact (LogOp.denoteBool_iff op ih₀.symm ih₁.symm).symm
-- ANCHOR_END: boolAgree

/-! ## 2. `Σ⊥` — 상태 또는 비종료

명령은 상태를 바꾸지만, 끝나지 않을 수도 있다. 그래서 결과 타입이 상태가 아니다.

> *"we introduce the symbol ⊥, usually called 'bottom', to denote nontermination"*

Reynolds 는 부분 함수 대신 `Σ → Σ⊥` 를 쓰는 쪽을 고른다. 뒤에 나올 더 풍부한 언어로의
일반화가 그쪽에서 명확해지기 때문이다. -/

-- ANCHOR: sigmaBot
/--
`Σ⊥` — 상태 하나 또는 비종료. `none` 이 `⊥` 다.

`Option` 을 쓰는 것이 편의만은 아니다. Reynolds 가 §2.2 에서 손으로 도입하는 확장

```
f⊥⊥ x = if x = ⊥ then ⊥ else f x
```

이 정확히 `Option.bind` 다. 아래 `liftBot_eq_bind` 가 그것을 확인한다.
-/
abbrev SigmaBot (V : Type u) := Option (State V)
-- ANCHOR_END: sigmaBot

/--
Reynolds 의 `f⊥⊥` — 상태를 받는 함수를 `Σ⊥` 를 받도록 늘린 것.

정의를 그대로 옮겼다. `⊥` 가 들어오면 `⊥` 를 내고, 상태가 들어오면 원래 함수를 쓴다.
-/
def liftBot {V : Type u} (f : State V → SigmaBot V) : SigmaBot V → SigmaBot V
  | none   => none
  | some σ => f σ

/--
**Reynolds 의 `f⊥⊥` 는 `Option` 모나드의 bind 다.**

이 등식 하나로 §2.2 의 순차 합성 방정식이 `⟦c₀ ; c₁⟧ σ = ⟦c₀⟧ σ >>= ⟦c₁⟧` 가 된다.
"앞 명령이 끝나지 않으면 뒤 명령은 시작하지 않는다" 가 bind 의 정의와 같은 말이다.

5장에서 연속체(continuation)를 다룰 때 이 관점이 다시 쓰인다.
-/
@[exercise "§2.2 lift-bind" 1]
theorem liftBot_eq_bind {V : Type u} (f : State V → SigmaBot V) (x : SigmaBot V) :
    liftBot f x = Option.bind x f := by
  cases x <;> rfl

/-- `Option.bind` 가 곧 `>>=` 다. 타입을 적어 주면 Lean 도 같은 것으로 본다. -/
example {V : Type u} (f : State V → SigmaBot V) (x : Option (State V)) :
    Option.bind x f = x >>= f := rfl

/-! ## 3. 의미 방정식

Reynolds §2.2 의 방정식들이다. `while` 을 뺀 다섯 개는 구문 지향적이다 — 우변에 좌변보다
작은 구만 나온다.

```
⟦v := e⟧ σ               = σ[v := ⟦e⟧ σ]
⟦skip⟧ σ                 = σ
⟦c₀ ; c₁⟧ σ              = ⟦c₀⟧ σ >>= ⟦c₁⟧   (= Option.bind)
⟦if b then c₀ else c₁⟧ σ = if ⟦b⟧ σ then ⟦c₀⟧ σ else ⟦c₁⟧ σ
⟦newvar v := e in c⟧ σ   = (⟦c⟧ σ[v := ⟦e⟧ σ]).map (fun σ' => σ'[v := σ v])
```

여섯 번째만 다르다.

```
⟦while b do c⟧ σ         = if ⟦b⟧ σ then ⟦c⟧ σ >>= ⟦while b do c⟧ else σ
```

우변의 `⟦while b do c⟧` 가 좌변과 같은 구다.

## 그래서 아직 `Comm.eval` 을 정의하지 않는다

Lean 의 `def` 는 전함수를 요구하고, 구조적 재귀가 아닌 재귀는 받아 주지 않는다.
여기서 억지로 정의하려 들면 `partial def` 나 `unsafe` 로 도망가게 되는데, 그러면
§2.2 의 논점이 사라진다. 문제는 Lean 의 제약이 아니라 **방정식 자체가 뜻을 정하지 못한다**는
것이기 때문이다.

대신 "의미 함수라면 만족해야 할 조건" 을 술어로 적어 둔다. §2.4 에서 이 조건을 만족하는
함수를 실제로 만들고, 그것이 **최소** 해임을 증명한다. -/

/-- `newvar` 절이 하는 일. 본체를 새 값으로 실행한 뒤 그 변수만 원래 값으로 되돌린다. -/
def restore {V : Type u} [DecidableEq V] (v : V) (σ : State V) : SigmaBot V → SigmaBot V :=
  Option.map fun σ' => σ'[v := σ v]

-- ANCHOR: isSemantics
/--
명령의 의미 함수가 만족해야 할 조건. Reynolds §2.2 의 의미 방정식 여섯 개를 그대로 적었다.

**정의가 아니라 명세(specification)다.** 이런 `m` 이 있는지, 있다면 하나뿐인지는
이 술어가 답하지 않는다. 앞의 다섯 방정식은 `m` 을 구문에 대한 재귀로 결정하지만,
`wh` 방정식은 양변에 같은 구가 나와서 그렇게 하지 못한다.

§2.4 에서 이 조건을 만족하는 `Comm.eval` 을 만들고 `Comm.eval_isSemantics` 를 증명한다.
-/
def IsSemantics {V : Type u} [DecidableEq V] (m : Comm V → State V → SigmaBot V) : Prop :=
  (∀ v e σ, m (.assign v e) σ = some (σ[v := ⟦e⟧ₑ σ]))
  ∧ (∀ σ, m .skip σ = some σ)
  ∧ (∀ c₀ c₁ σ, m (.seq c₀ c₁) σ = Option.bind (m c₀ σ) (m c₁))
  ∧ (∀ b c₀ c₁ σ, m (.ite b c₀ c₁) σ = if ⟦b⟧ᵇ σ then m c₀ σ else m c₁ σ)
  ∧ (∀ b c σ, m (.wh b c) σ = if ⟦b⟧ᵇ σ then Option.bind (m c σ) (m (.wh b c)) else some σ)
  ∧ (∀ v e c σ, m (.newvar v e c) σ = restore v σ (m c (σ[v := ⟦e⟧ₑ σ])))
-- ANCHOR_END: isSemantics

/-! ## 4. 풀기 방정식은 뜻을 유일하게 정하지 못한다

이 절이 §2.2 의 결론이다.

Reynolds 는 구체적인 반복문 하나를 놓고 따진다.

```
while x ≠ 0 do x := x - 2
```

본체 `x := x - 2` 에는 반복이 없으므로 그 뜻은 문제없이 정해진다. 그래서 이 반복문 하나에
대한 방정식만 떼어 놓고 볼 수 있다.

`σx` 가 0 이상의 짝수면 반복은 끝나고 `x` 가 0 이 된다. 그 밖의 경우 — `σx` 가 홀수거나
음수인 짝수 — 에는 끝나지 않는다. 진짜 뜻은 그 경우에 `⊥` 를 내는 함수다.

문제는 **방정식이 그 경우를 전혀 제약하지 않는다**는 것이다. -/

/-- 예제 반복문의 본체 `x := x - 2` 의 뜻. 반복이 없어서 그냥 정해진다. -/
def decrBody (σ : State String) : SigmaBot String := some (σ["x" := σ "x" - 2])

/--
`while x ≠ 0 do x := x - 2` 의 풀기(unwinding) 방정식.

`IsSemantics` 의 `wh` 절에서 이 반복문 하나만 떼어 낸 것이다.
`⟦b⟧ᵇ σ` 는 `σ "x" ≠ 0` 이고 `⟦c⟧ σ` 는 `decrBody σ` 다.
-/
def UnwindsDecr (f : State String → SigmaBot String) : Prop :=
  ∀ σ : State String, f σ = if σ "x" ≠ 0 then Option.bind (decrBody σ) f else some σ

/-- 반복이 끝나는 상태들. `x` 가 0 이상의 짝수일 때. -/
def decrHalts (σ : State String) : Prop := 0 ≤ σ "x" ∧ σ "x" % 2 = 0

instance : DecidablePred decrHalts := fun σ => by
  unfold decrHalts; infer_instance

/-- 진짜 뜻. 끝나는 상태에서는 `x` 를 0 으로, 나머지에서는 `⊥`. -/
def decrTrue (σ : State String) : SigmaBot String :=
  if decrHalts σ then some (σ["x" := (0 : Int)]) else none

/--
가짜 뜻. 끝나는 상태에서는 진짜와 같고, **끝나지 않는 상태에서 아무 답이나 낸다.**

여기서는 `x` 를 999 로 만든 상태를 골랐다. 999 라는 값에 의미는 없다.
방정식이 그 자리를 제약하지 않는다는 것이 요점이므로 아무 값이나 된다.
-/
def decrFake (σ : State String) : SigmaBot String :=
  if decrHalts σ then some (σ["x" := (0 : Int)]) else some (σ["x" := (999 : Int)])

/-! ### 두 함수가 모두 방정식을 만족한다

증명은 `σ "x"` 를 네 갈래로 나누는 것이 전부다.

| `σ "x"` | 방정식의 양변 |
|---|---|
| 0 | 좌변 `σ[x := 0] = σ`, 우변 `σ`. 조건이 거짓이라 한 걸음도 안 간다 |
| 0 보다 큰 짝수 | 한 걸음 가면 여전히 0 이상 짝수. 둘 다 `σ[x := 0]` |
| 홀수 | 한 걸음 가도 홀수. 끝나지 않는 쪽에 머문다 |
| 음수 짝수 | 한 걸음 가도 음수 짝수. 마찬가지 |

마지막 두 갈래에서 방정식이 **아무것도 요구하지 않는다.** `f` 가 그 상태들에서 무엇을 내든,
한 걸음 간 상태에서도 같은 것을 내기만 하면 방정식이 성립한다.
`σ[x := k][x := k] = σ[x := k]` 라서 상수 답은 언제나 그 조건을 만족한다. -/

/-- 상태 갱신을 두 번 하면 뒤엣것만 남는다. 네 갈래 계산에서 계속 쓴다. -/
theorem State.subst_subst {V : Type u} [DecidableEq V] (σ : State V) (v : V) (m n : Int) :
    σ[v := m][v := n] = σ[v := n] := by
  simp [State.subst_def, Function.update_idem]

/-- 이미 그 값이면 갱신해도 그대로다. -/
theorem State.subst_eq_self {V : Type u} [DecidableEq V] (σ : State V) (v : V) {n : Int}
    (h : σ v = n) : σ[v := n] = σ := by
  subst h; simp [State.subst_def]

-- ANCHOR: unwindingNotUnique
/-- 한 걸음 간 상태. 네 갈래 계산에서 계속 쓴다. -/
theorem decr_step (f : State String → SigmaBot String) (σ : State String) :
    Option.bind (decrBody σ) f = f (σ["x" := σ "x" - 2]) := rfl

/-- 끝나는 상태에서 한 걸음 가도 여전히 끝나는 상태다. -/
theorem decrHalts_step {σ : State String} (hh : decrHalts σ) (h0 : σ "x" ≠ 0) :
    decrHalts (σ["x" := σ "x" - 2]) := by
  unfold decrHalts at hh ⊢
  simp only [State.subst_self]
  omega

/-- 끝나지 않는 상태에서 한 걸음 가도 여전히 끝나지 않는다. 홀수는 홀수로, 음수는 음수로. -/
theorem decrHalts_step_not {σ : State String} (hh : ¬ decrHalts σ) :
    ¬ decrHalts (σ["x" := σ "x" - 2]) := by
  unfold decrHalts at hh ⊢
  simp only [State.subst_self]
  omega

/-- 진짜 뜻은 풀기 방정식을 만족한다. -/
theorem unwindsDecr_true : UnwindsDecr decrTrue := by
  intro σ
  by_cases h0 : σ "x" = 0
  · -- 조건이 거짓이라 한 걸음도 가지 않는다.
    rw [if_neg (by simp [h0])]
    have hh : decrHalts σ := by unfold decrHalts; omega
    simp only [decrTrue, if_pos hh, State.subst_eq_self σ "x" h0]
  · rw [if_pos h0, decr_step]
    by_cases hh : decrHalts σ
    · simp only [decrTrue, if_pos hh, if_pos (decrHalts_step hh h0), State.subst_subst]
    · simp only [decrTrue, if_neg hh, if_neg (decrHalts_step_not hh)]

/--
**가짜 뜻도 풀기 방정식을 만족한다.**

`decrTrue` 와 `decrFake` 는 끝나지 않는 상태에서 다른 답을 낸다. 그런데 방정식은 둘을
구별하지 못한다. 증명이 `unwindsDecr_true` 와 글자까지 같다는 것이 그 사실이다 —
끝나지 않는 갈래에서 무엇을 내든 방정식은 상관하지 않는다.
-/
theorem unwindsDecr_fake : UnwindsDecr decrFake := by
  intro σ
  by_cases h0 : σ "x" = 0
  · rw [if_neg (by simp [h0])]
    have hh : decrHalts σ := by unfold decrHalts; omega
    simp only [decrFake, if_pos hh, State.subst_eq_self σ "x" h0]
  · rw [if_pos h0, decr_step]
    by_cases hh : decrHalts σ
    · simp only [decrFake, if_pos hh, if_pos (decrHalts_step hh h0), State.subst_subst]
    · simp only [decrFake, if_neg hh, if_neg (decrHalts_step_not hh), State.subst_subst]

/--
**풀기 방정식은 해를 유일하게 결정하지 않는다.**

Reynolds §2.2 의 논점을 그대로 옮긴 것이다. 이 정리가 §2.3~2.4 의 존재 이유다 —
해가 여럿이므로 그중 하나를 고르는 원리가 따로 있어야 하고, 그 원리가 최소 고정점이다.

증명은 두 해를 제시하고 다른 값을 내는 상태를 하나 짚으면 된다.
`x` 가 1 인 상태에서 하나는 `⊥` 를, 다른 하나는 상태를 낸다.
-/
@[exercise "§2.2 unwinding-not-unique" 3]
theorem unwinding_not_unique :
    ∃ f g : State String → SigmaBot String, UnwindsDecr f ∧ UnwindsDecr g ∧ f ≠ g := by
  refine ⟨decrTrue, decrFake, unwindsDecr_true, unwindsDecr_fake, ?_⟩
  intro h
  have hne : ¬ decrHalts (State.const 1 : State String) := by
    unfold decrHalts State.const; omega
  have := congrFun h (State.const 1)
  simp only [decrTrue, decrFake, if_neg hne] at this
  -- `⊥ = some …` 은 성립할 수 없다.
  simp at this
-- ANCHOR_END: unwindingNotUnique

/--
**더 나쁜 경우.** `while tt do skip` 의 풀기 방정식은 `f σ = f σ` 로 줄어든다.
`Σ → Σ⊥` 의 **모든** 함수가 해가 된다.

Reynolds 가 두 번째 예로 드는 것이고, 방정식이 뜻을 정하지 못한다는 사실을 가장 짧게
보여 준다. 조건이 언제나 참이고 본체가 상태를 바꾸지 않으므로 방정식이 동어 반복이 된다.
-/
@[exercise "§2.2 unwinding-trivial" 2]
theorem unwinding_trivial (f : State String → SigmaBot String) :
    ∀ σ, f σ = if ⟦(.tru : BoolExp String)⟧ᵇ σ then Option.bind (some σ : SigmaBot String) f
                else some σ := by
  intro σ
  simp [BoolExp.eval]

/-! ## 5. 여기서 어디로 가나

방정식의 해가 여럿이라는 것을 확인했다. 그러면 어느 것이 뜻인가.

`decrTrue` 와 `decrFake` 를 다시 보라. 둘의 차이는 **끝나지 않는 상태에서 무엇을
주장하는가** 다. `decrTrue` 는 아무 주장도 하지 않고(`⊥`), `decrFake` 는 없는 답을
지어낸다. 뜻으로 삼아야 할 것은 앞쪽이다 — 계산이 실제로 알려 주지 않는 것을 의미 함수가
알려 주면 안 된다.

"아무 주장도 하지 않는다" 를 **순서**로 만들면 `⊥` 가 가장 아래에 오고, 두 해 중 아래에
있는 것을 고르는 일이 된다. 그 순서가 §2.3 의 주제이고, 그런 최소 해가 언제나 존재한다는
것이 §2.4 의 최소 고정점 정리다.

Reynolds 가 도메인 이론을 이 자리에서 꺼내는 이유가 여기 있다. 먼저 배우고 나중에 쓰는
도구가 아니라, 이 문제를 풀려고 만들어진 도구다. -/

end Reynolds.Answers.Ch02
