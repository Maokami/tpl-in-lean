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
# §2.2 표시적 의미론 — `while`의 풀기 방정식

Reynolds §2.2 에 대응한다.

## 이 파일에서 다루는 것
- 불 식의 뜻. 1장과 달리 `Bool` 이고, 그래서 실제로 돌아간다
- `Σ⊥` — 상태 또는 비종료. Reynolds 가 `⊥` 를 도입하는 자리
- 명령의 의미 방정식 다섯 개
- `while`의 풀기 방정식과 해의 비유일성

## 1장과 무엇이 다른가

1장의 의미 함수는 구문에 대한 구조적 재귀였다. 각 절이 직접 부분식의 뜻만으로
자기 뜻을 정했고, 구문의 초기성 때문에 이 방정식을 만족하는 함수가 유일했다
(`Depth/Algebra.lean` 이 그 유일성을 초기 대수로 설명한다).

`while b do c` 는 그렇지 않다. 뜻을 쓰려고 하면 이렇게 된다.

```
⟦while b do c⟧ σ = if ⟦b⟧ σ then (⟦while b do c⟧)⊥⊥ (⟦c⟧ σ) else σ
```

우변의 재귀 호출은 `b`나 `c` 같은 부분구가 아니라 원래 `while` 명령을 다시 가리킨다.
따라서 이 식은 구문 지향 재귀 정의가 아니라, 의미 함수가 만족해야 할 방정식이다.
방정식만으로 함수를 정의하려면 해의 존재와 유일성을 따로 보여야 한다. 이 파일은 실제
명령 하나에 서로 다른 두 해를 구성해 유일성이 실패함을 확인한다.

## 다음 절과의 연결

Reynolds는 의미 함수들을 정보량 순서로 비교한다. 비종료를 나타내는 `⊥`는 어떤 결과 상태도
알려 주지 않으므로 가장 아래에 놓이고, 실제 계산이 뒷받침하지 않는 결과를 덧붙인 해는 그보다
위에 놓인다. §2.3은 이 근사 순서와 사슬의 극한을 정의하고, §2.4는 연속 자기함수의 여러
고정점 가운데 최소 고정점을 구성한다.

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

1장의 단언에는 정수 양화사가 있었다. 그 모든 단언의 참·거짓을 `Bool`로 계산하려면
언어 전체에 통하는 진리 판정 프로그램이 필요하지만, 그런 프로그램은 없다. 그래서
계산 절차를 요구하지 않는 `Prop`으로 뜻을 주었다.

불 식에는 양화사가 없고 모든 생성자 연산이 결정 가능하므로 구문을 유한하게 순회하는
`Bool` 평가기를 정의할 수 있다. 비교와 논리 연산의 뜻만 `Bool` 판으로 다시 쓰면 된다. -/

-- ANCHOR: BoolExp.eval
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
-- ANCHOR_END: BoolExp.eval

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

-- ANCHOR: boolExp_eval_iff
/--
**불 식은 양화사 없는 단언이다** — 두 의미 함수가 일치한다.

Reynolds 가 §2.1 에서 한 문장으로 넘어가는 말을 정리로 확인한 것이다.
같은 양화사 없는 조각을 `Prop`과 `Bool`로 각각 해석해도 표현력은 달라지지 않는다.
양화사가 빠진 식은 계산할 수 있고, 아래 정리는 그 계산 결과가 명제의 참·거짓과 일치함을 말한다.
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
-- ANCHOR_END: boolExp_eval_iff

/-! ## 2. `Σ⊥` — 상태 또는 비종료

명령은 상태를 바꾸지만, 끝나지 않을 수도 있다. 그래서 결과 타입이 상태가 아니다.

> *"we introduce the symbol ⊥, usually called 'bottom', to denote nontermination"*

Reynolds 는 부분 함수 대신 `Σ → Σ⊥` 를 쓰는 쪽을 고른다. 뒤에 나올 더 풍부한 언어로의
일반화가 그쪽에서 명확해지기 때문이다. -/

-- ANCHOR: SigmaBot
/--
`Σ⊥` — 상태 하나 또는 비종료. `none` 이 `⊥` 다.

이 타입은 결정적 언어의 정상 종료와 비종료만 구분한다. `none`을 실행 오류나 비결정적
결과로도 함께 읽지 않는다. Reynolds가 §2.7에서 산술 오류를 추가하면 의미 공간을 다시
매개변수화해야 하고, 비결정성은 7장에서 멱집합이나 멱영역과 같은 다른 구조를 요구한다.

`Option` 을 쓰는 것이 편의만은 아니다. Reynolds 가 §2.2 에서 손으로 도입하는 확장

```
f⊥⊥ x = if x = ⊥ then ⊥ else f x
```

이 정확히 `Option.bind` 다. 아래 `liftBot_eq_bind` 가 그것을 확인한다.
-/
abbrev SigmaBot (V : Type u) := Option (State V)
-- ANCHOR_END: SigmaBot

/--
Reynolds 의 `f⊥⊥` — 상태를 받는 함수를 `Σ⊥` 를 받도록 늘린 것.

정의를 그대로 옮겼다. `⊥` 가 들어오면 `⊥` 를 내고, 상태가 들어오면 원래 함수를 쓴다.
-/
def liftBot {V : Type u} (f : State V → SigmaBot V) : SigmaBot V → SigmaBot V
  | none   => none
  | some σ => f σ

/--
Reynolds 의 `f⊥⊥` 는 이 `Option` 표현에서 `bind`와 같다.

이 등식 하나로 §2.2 의 순차 합성 방정식이 `⟦c₀ ; c₁⟧ σ = ⟦c₀⟧ σ >>= ⟦c₁⟧` 가 된다.
`Option.bind`의 타입은
`SigmaBot V → (State V → SigmaBot V) → SigmaBot V`이고, 첫 계산이 `none`이면 두 번째
함수를 호출하지 않는다. 이 동작이 순차 합성의 비종료 전파와 일치한다.
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

## 이 단계에서는 `Comm.eval`을 정의하지 않는다

Lean의 구조적 재귀 검사에 맞지 않는다는 컴파일 오류만 피해서는 문제가 해결되지 않는다.
`partial def`나 `unsafe`로 어떤 실행 절차를 만들더라도, 그 절차가 왜 풀기 방정식의 의도한
해를 고르는지는 별도로 정당화해야 한다. 여기서 남은 문제는 방정식 자체의 해가 유일하지
않다는 점이다.

대신 "의미 함수라면 만족해야 할 조건" 을 술어로 적어 둔다. §2.4 에서 이 조건을 만족하는
함수를 실제로 만들고, 그것이 **최소** 해임을 증명한다. -/

/-- `newvar` 절이 하는 일. 본체를 새 값으로 실행한 뒤 그 변수만 원래 값으로 되돌린다. -/
def restore {V : Type u} [DecidableEq V] (v : V) (σ : State V) : SigmaBot V → SigmaBot V :=
  Option.map fun σ' => σ'[v := σ v]

-- ANCHOR: IsSemantics
/--
명령의 의미 함수가 만족해야 할 조건. Reynolds §2.2 의 의미 방정식 여섯 개를 그대로 적었다.

**정의가 아니라 명세(specification)다.** 이런 `m` 이 있는지, 있다면 하나뿐인지는
이 술어가 답하지 않는다. `while`을 제외한 다섯 방정식은 `m` 을 구문에 대한 재귀로
결정하지만, `wh` 방정식은 양변에 같은 구가 나와서 그렇게 하지 못한다.

§2.4 에서 이 조건을 만족하는 `Comm.eval` 을 만들고 `Comm.eval_isSemantics` 를 증명한다.
-/
def IsSemantics {V : Type u} [DecidableEq V] (m : Comm V → State V → SigmaBot V) : Prop :=
  (∀ v e σ, m (.assign v e) σ = some (σ[v := ⟦e⟧ₑ σ]))
  ∧ (∀ σ, m .skip σ = some σ)
  ∧ (∀ c₀ c₁ σ, m (.seq c₀ c₁) σ = Option.bind (m c₀ σ) (m c₁))
  ∧ (∀ b c₀ c₁ σ, m (.ite b c₀ c₁) σ = if ⟦b⟧ᵇ σ then m c₀ σ else m c₁ σ)
  ∧ (∀ b c σ, m (.wh b c) σ = if ⟦b⟧ᵇ σ then Option.bind (m c σ) (m (.wh b c)) else some σ)
  ∧ (∀ v e c σ, m (.newvar v e c) σ = restore v σ (m c (σ[v := ⟦e⟧ₑ σ])))
-- ANCHOR_END: IsSemantics

/-! ## 4. 풀기 방정식은 뜻을 유일하게 정하지 못한다

이 절은 §2.2의 비유일성 주장을 함수 두 개와 정리로 확인한다.

Reynolds 는 구체적인 반복문 하나를 놓고 따진다.

```
while x ≠ 0 do x := x - 2
```

본체 `x := x - 2` 에는 반복이 없으므로 그 뜻은 문제없이 정해진다. 그래서 이 반복문 하나에
대한 방정식만 떼어 놓고 볼 수 있다.

`σx` 가 0 이상의 짝수면 반복은 끝나고 `x` 가 0 이 된다. 그 밖의 경우, 곧 `σx`가
홀수이거나 음수인 짝수이면 2를 계속 빼도 0에 도달하지 않는다. 운용적 실행을 기준으로
의도한 의미는 이 입력들에서 `⊥`를 내는 함수다. 이 파일에는 별도의 운용 의미론이 없으므로
그 적합성을 정리로 증명하지 않고, Reynolds의 실행 직관을 명시적인 후보 함수로 옮긴다.

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

/-- 의도한 의미 후보. 끝나는 상태에서는 `x` 를 0 으로, 나머지에서는 `⊥`. -/
def decrTrue (σ : State String) : SigmaBot String :=
  if decrHalts σ then some (σ["x" := (0 : Int)]) else none

/--
다른 해. 끝나는 상태에서는 `decrTrue`와 같고, 끝나지 않는 상태에서 임의의 상태를 낸다.

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

-- ANCHOR: unwinding_not_unique
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

/-- 의도한 의미 후보 `decrTrue`는 풀기 방정식을 만족한다. -/
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
대안으로 만든 `decrFake`도 풀기 방정식을 만족한다.

`decrTrue` 와 `decrFake` 는 끝나지 않는 상태에서 다른 답을 내지만 둘 다 같은 방정식을
만족한다. 종료하지 않는 입력에서는 우변이 다시 미지 함수에 돌아가므로, 방정식만으로는
그 입력의 결과를 제한하지 못한다.
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
풀기 방정식은 해를 유일하게 결정하지 않는다.

`decrTrue`와 `decrFake`가 모두 해라는 두 보조정리와 둘이 다르다는 증거를 묶은 정리다.
§2.3~2.4에서는 이 해들을 근사 순서로 비교하고 최소인 해를 선택한다.

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
-- ANCHOR_END: unwinding_not_unique

/--
`while tt do skip` 의 풀기 방정식은 `f σ = f σ` 로 줄어든다.
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

/-! ## 5. 해를 비교할 순서가 필요하다

`decrTrue`는 비종료하는 입력에서 `⊥`를 내고, `decrFake`는 결과 상태를 하나 덧붙인다.
첫 함수는 실제 계산이 확인해 주는 정보만 담지만, 둘 다 같은 풀기 방정식을 만족한다.

이 차이를 수학적으로 사용하려면 `⊥`가 구체적인 결과보다 적은 정보를 준다는 관계를
부분 순서로 적어야 한다. 그러면 두 해 가운데 더 아래에 있는 해를 말할 수 있다. §2.3은
그 근사 순서에서 증가하는 계산 근사들의 극한을 정의하고, §2.4는 연속 자기함수의 최소
고정점을 그 극한으로 구성한다. -/

end Reynolds.Answers.Ch02
