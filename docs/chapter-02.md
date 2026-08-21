# 2장 «The Simple Imperative Language» — 형식화 상세 설계

> Reynolds, *Theories of Programming Languages*, Chapter 2 (pp. 24–53)
> §2.1 Syntax · §2.2 Denotational Semantics · §2.3 Domains and Continuous Functions
> §2.4 The Least Fixed-Point Theorem · §2.5 Variable Declarations and Substitution
> §2.6 Syntactic Sugar: The for Command · §2.7 Arithmetic Errors · §2.8 Soundness and Full Abstraction

## 이 장의 위치

1장에는 비종료가 없었다. 2장에서 `while`이 들어오는 순간 **의미 함수가 전함수(total function)로
정의되지 않는다**. 이걸 해결하려고 Scott이 만든 것이 도메인 이론(domain theory)이고,
Reynolds는 그 최소한만 §2.3–2.4에서 직접 만든다.

이 장은 이 프로젝트에서 **가장 어렵고 가장 보람 있는 장**이다. 이유:

- Lean에서 `while`의 의미는 **계산 불가능**하다. `def`로 그냥 쓸 수 없다. 왜 그런지가 곧 §2.2의 논점이다.
- 최소 고정점 정리는 Lean에서 정말로 증명해야 한다. Reynolds의 세 단계 증명(사슬 → 고정점 → 최소)이
  그대로 세 개의 보조 정리가 된다.
- §2.5의 별칭(aliasing) 반례는 Lean에서 **실행해서 확인**할 수 있다.

### 이 장의 설계 핵심 결정

| 문제 | 결정 |
|---|---|
| `while`이 계산 불가능 | 표시적 의미(비계산) + **연료(fuel) 기반 해석기**(계산 가능) 둘 다 제공하고, 일치 정리를 증명 |
| 도메인 이론을 Mathlib에서 가져올까 | **직접 만든다.** §2.3–2.4가 그것 자체이므로. Mathlib 대응물은 `MathlibBridge.lean`에 대조표로 |
| `newvar`를 언제 넣을까 | `Comm`에 **처음부터** 넣는다. §2.5까지는 쓰지 않는다 (docstring에 명시) |
| Σ⊥ 표현 | `Option (State V)`. `⊥ = none`. **`Option.bind`가 Reynolds의 `f⊥⊥`와 정확히 같다** |

---

## 파일 배치

| 파일 | 책 | 내용 |
|---|---|---|
| `Ch02/Syntax.lean` | §2.1 | `BoolExp`, `Comm` |
| `Ch02/Notation.lean` | §2.1 | 명령 DSL `⟪ x := x - 1; y := y + x ⟫` |
| `Ch02/Domain.lean` | §2.3 | `Chain`, `Predomain`, `Domain`, `Continuous`, 함수 공간, 리프팅 |
| `Ch02/Fixpoint.lean` | §2.4 | 최소 고정점 정리, `Y`, Scott 귀납법 |
| `Ch02/Semantics.lean` | §2.2, §2.4 | `BoolExp.eval`, `Comm.eval`, `while` |
| `Ch02/Interpreter.lean` | §2.4 | 연료 기반 해석기 `Comm.run` + 적합성(adequacy) |
| `Ch02/FreeVars.lean` | §2.5 | `FV_comm`, `FA`, 명제 2.6 |
| `Ch02/Substitution.lean` | §2.5 | 명령 치환, 별칭, 명제 2.7 · 2.8 |
| `Ch02/Sugar.lean` | §2.6 | `for` 명령 세 판본과 각 결함의 증명 |
| `Ch02/ArithErrors.lean` | §2.7 | 산술 연산을 매개변수화한 축소판 |
| `Ch02/FullAbstraction.lean` | §2.8 | 문맥(context), 건전성, 완전 추상성 |
| `Ch02/MathlibBridge.lean` | — | Mathlib ωCPO / CSlib 대응표 (심화) |
| `Ch02/Ex.lean` | 연습 | 2.1 ~ 2.10 |

---

## §2.1 구문

```lean
-- ANCHOR: BoolExp
/--
불 식(boolean expression). Reynolds §2.1의 ⟨boolexp⟩.

1장의 `Assert`에서 **양화사만 뺀 것**이다. Reynolds:

> *"boolean expressions are the same as assertions except for the omission of quantifiers
> (for the obvious reason that they are noncomputable)"*

정수 산술과 양화를 포함한 단언 언어 전체에는 실행 가능한 공통 판정기가 없다. 양화사를
뺀 불 식은 구문을 따라 계산할 수 있으므로 `Bool` 평가기를 줄 수 있고, **`#eval`로 실제로
돌릴 수 있다.**
-/
inductive BoolExp (V : Type u) where
  | tru | fls
  | cmp : Cmp → IntExp V → IntExp V → BoolExp V
  | not : BoolExp V → BoolExp V
  | bin : LogOp → BoolExp V → BoolExp V → BoolExp V
  deriving DecidableEq, Repr
-- ANCHOR_END: BoolExp

-- ANCHOR: Comm
/--
명령(command). Reynolds §2.1의 ⟨comm⟩ + §2.5의 `newvar`.

**책과의 차이**: Reynolds는 `newvar`를 §2.5에서 추가한다. 여기서는 처음부터 넣었다.
같은 타입을 두 번 정의하면 §2.2–2.4의 모든 정의·정리를 복제해야 하기 때문이다.
§2.5 이전 절에서는 `newvar`를 쓰지 않는다.

`Comm.newvar v e c` — `newvar v := e in c`. `v`는 **결합 발생**이고 그 유효 범위(scope)는
`c`다(`e`는 아니다). 이것이 이 장에서 결합이 등장하는 유일한 자리다.
-/
inductive Comm (V : Type u) where
  | assign : V → IntExp V → Comm V
  | skip   : Comm V
  | seq    : Comm V → Comm V → Comm V
  | ite    : BoolExp V → Comm V → Comm V → Comm V
  | wh     : BoolExp V → Comm V → Comm V
  | newvar : V → IntExp V → Comm V → Comm V
  deriving DecidableEq, Repr
-- ANCHOR_END: Comm
```

**모든 변수가 정수형이다** — Reynolds가 "다소 단순하게(somewhat simplistically)"라고 인정하는
설계 결정. 타입 체계는 15장에서 다룬다. docstring에 밝힌다.

DSL은 1장의 것을 확장한다:
```lean
#eval ⟪ x := 1; while x ≤ 10 do (y := y + x; x := x + 1) ⟫
```

---

## §2.2 표시적 의미론 — 그리고 `while`이라는 벽

### `Bool`로 돌아가는 즐거움

```lean
/-- `⟦b⟧ σ` — 불 식의 의미. **계산 가능하다.** -/
def BoolExp.eval : BoolExp V → State V → Bool

/-- 양화사 없는 조각에서 1장의 `Assert.eval`과 일치한다. -/
@[exercise "§2.2 boolexp-assert" 2]
theorem boolExp_eval_iff (b : BoolExp V) (σ : State V) :
    b.toAssert.eval σ ↔ b.eval σ = true
```

### Σ⊥ 와 리프팅

```lean
-- ANCHOR: SigmaBot
/--
`Σ⊥` — 상태 또는 비종료. Reynolds §2.2.

> *"we introduce the symbol ⊥, usually called 'bottom', to denote nontermination"*

`none`이 ⊥다. Reynolds는 "부분 함수를 쓰는 사람도 많지만 Σ → Σ⊥ 를 쓰면
더 풍부한 언어로의 일반화가 명확해진다"고 한다.

**Lean에서의 보너스**: Reynolds가 §2.2에서 도입하는 "함수를 ⊥를 포함하도록 확장"
    `f⊥⊥ x = if x = ⊥ then ⊥ else f x`
는 정확히 `Option.bind`다. 즉

    ⟦c₀ ; c₁⟧ σ = (⟦c₁⟧)⊥⊥ (⟦c₀⟧ σ)  =  (⟦c₀⟧ σ) >>= ⟦c₁⟧

순차 합성(sequential composition)이 **Option 모나드의 bind**로 드러난다.
5장에서 연속체(continuation)와 재개(resumption)로 이어질 때 이 관점이 계속 쓰인다.
-/
abbrev SigmaBot (V : Type u) := Option (State V)
-- ANCHOR_END: SigmaBot
```

### 의미 방정식

```lean
⟦v := e⟧ σ            = some (σ[v := ⟦e⟧ σ])
⟦skip⟧ σ              = some σ
⟦c₀ ; c₁⟧ σ           = (⟦c₀⟧ σ) >>= ⟦c₁⟧
⟦if b then c₀ else c₁⟧ σ = if ⟦b⟧ σ then ⟦c₀⟧ σ else ⟦c₁⟧ σ
⟦newvar v := e in c⟧ σ = (⟦c⟧ σ[v := ⟦e⟧ σ]).map (fun σ' => σ'[v := σ v])
⟦while b do c⟧        = ???        ← 여기서 막힌다
```

### ★ `while`이 왜 방정식으로 정의되지 않는가

Reynolds가 §2.2 전체를 들여 설명하는 논점. 반드시 Lean으로 재현한다.

**풀기(unwinding) 방정식**은 성립한다:
```
⟦while b do c⟧ σ = if ⟦b⟧ σ then (⟦while b do c⟧)⊥⊥(⟦c⟧ σ) else σ
```
그러나 이건 **의미 방정식이 아니다** — 우변에 `while b do c` 자신이 나오므로
구문 지향적(syntax-directed)이 아니다. 따라서 **유일성이 보장되지 않는다.**

Reynolds의 두 반례를 Lean 정리로 만든다:

```lean
-- ANCHOR: unwindingNotUnique
/--
**풀기 방정식은 해를 유일하게 결정하지 않는다** — 반례 1.

`while x ≠ 0 do x := x - 2` 의 풀기 방정식은
`σx`가 짝수이고 음수일 때, 그리고 `σx`가 홀수일 때
**아무 상태나 ⊥를 넣어도** 만족된다. Reynolds가 `σ'`, `σ''`라고 부른 것들이다.

실제 뜻은 `σ' = σ'' = ⊥`인 해지만, **풀기 방정식만으로는 그걸 골라낼 수 없다.**
-/
theorem unwinding_not_unique :
    ∃ f g : State V → SigmaBot V, f ≠ g ∧ Unwinds f ∧ Unwinds g

/--
**반례 2 (더 극단적)** — `while true do skip` 의 풀기 방정식은
`⟦while true do skip⟧ σ = ⟦while true do skip⟧ σ` 로 줄어들어
**Σ → Σ⊥ 의 모든 함수**가 해가 된다.
-/
theorem unwinding_trivial (f : State V → SigmaBot V) : Unwinds_true_skip f
-- ANCHOR_END: unwindingNotUnique
```

> **교육적으로 매우 중요**: 이 두 정리를 학습자가 직접 증명하면
> "왜 도메인 이론이 필요한가"가 몸으로 이해된다. 별점 ★★ 로 배정한다.

---

## §2.3 도메인과 연속 함수 — 직접 만든다

Mathlib에 `OmegaCompletePartialOrder`가 있지만 **쓰지 않는다.** 이 절이 그것을 만드는 절이기 때문이다.
대신 `MathlibBridge.lean`에서 대조한다.

```lean
-- ANCHOR: domain
/--
사슬(chain) — 가산 증가 열. Reynolds §2.3.

> *"A chain is a countably infinite increasing sequence x₀ ⊑ x₁ ⊑ x₂ ⊑ ⋯"*

Reynolds는 "엄밀히는 가산 사슬이지만 다른 종류는 안 다루므로 그냥 사슬이라 부른다"고 한다.
(더 일반적인 유향 집합(directed set)을 쓰는 정의도 있다 — §2.3의 논의 참고.)
-/
structure Chain (α : Type u) [Preorder α] where
  seq : ℕ → α
  mono : Monotone seq

/-- **프리도메인(predomain)** — 모든 사슬이 극한을 갖는 부분 순서 집합. -/
class Predomain (α : Type u) [PartialOrder α] where
  lub : Chain α → α
  lub_isLUB (c : Chain α) : IsLUB (Set.range c.seq) (lub c)

/-- **도메인(domain)** — 최소원 ⊥ 를 가진 프리도메인. -/
@[nolint unusedArguments]
abbrev Domain (α : Type u) [PartialOrder α] [OrderBot α] := Predomain α

/-- `c.lub`로 쓸 수 있게 한다. -/
def Chain.lub [PartialOrder α] [Predomain α] (c : Chain α) : α := Predomain.lub c

/-- **연속(continuous)** — 사슬의 극한을 보존한다. -/
def Continuous [PartialOrder α] [PartialOrder β] [Predomain α] (f : α → β) : Prop :=
  ∀ c : Chain α, IsLUB (f '' Set.range c.seq) (f c.lub)
-- ANCHOR_END: domain
```

`Predomain`과 `Domain`이 순서 클래스를 `extends`하지 않는 것은 Mathlib이 이미 주는 순서와
별도 상속 경로가 생기는 것을 피하기 위해서다. 연속성의 공역에는 `PartialOrder`만 요구한다.
상의 최소 상계가 `f c.lub`라는 진술 자체로 극한 보존을 표현할 수 있기 때문이다.

### 만들 도메인들 (Reynolds가 드는 예를 전부)

| Reynolds의 예 | Lean |
|---|---|
| 이산 순서로 본 집합 | `Discrete α` (타입 동의어 + `x ≤ y ↔ x = y`) |
| 리프팅 `P⊥` | `Option (Discrete α)`, `none = ⊥` |
| **평평한 도메인(flat domain)** | 위와 같음. `Σ⊥`가 그 예 |
| 유한·무한 정수 열 | `Stream'`/`List ⊕ Stream'` — 5.2절 예고. **선택** |
| 멱집합 도메인 `𝒫 S` | `Set S`, `⊆` |
| **수직 자연수 `ℕ⊤`** | Mathlib `ENat` — 연속하지 않은 단조 함수의 반례에 필요 |

> **타입 동의어 주의**: `State V = V → Int`에는 Mathlib의 Pi 순서 인스턴스가 이미 붙는다.
> 평평한 도메인을 만들려면 `def Discrete (α) := α` 로 감싸야 한다. (`DESIGN.md` §10-4)

### 명제 2.1 ~ 2.4

```lean
/-- **명제 2.1** — 단조 함수가 연속일 필요충분조건은
    흥미로운 사슬에 대해 `f(⨆ xᵢ) ⊑ ⨆ f xᵢ` 가 성립하는 것이다.
    (반대 방향은 단조성에서 공짜. 흥미롭지 않은 사슬에서는 자명.) -/
@[exercise "Prop 2.1" 2]
theorem continuous_iff_le …

/-- **연속하지 않은 단조 함수의 반례** — Reynolds §2.3.
    `ℕ⊤ → {⊥', ⊤'}`, `f x = if x = ∞ then ⊤' else ⊥'`.
    `⨆{0,1,2,…} = ∞` 이고 `f ∞ = ⊤'` 이지만 `⨆{f 0, f 1, …} = ⊥'`. -/
@[exercise "§2.3 반례" 2]
theorem exists_monotone_not_continuous …

/-- **명제 2.2** — 연속 함수 공간 `P → P'` 는 점별 순서로 프리도메인이고,
    `P'`가 도메인이면 도메인이다. 사슬의 극한은 점별 극한이다. -/
@[exercise "Prop 2.2" 3]

/-- **명제 2.3 (a)~(e)** — 상수·항등 함수는 연속, 합성은 연속성을 보존한다. -/
@[exercise "Prop 2.3" 2]

/-- **명제 2.4 (a)~(e)** — 리프팅 `f⊥`, 원천 리프팅 `f⊥⊥`, 주입 `ι` 의 성질.
    (a)(b)는 "유일한 순 확장(strict extension)"이라는 주장이다.
    Lean에서 `f⊥ = Option.map f`, `g⊥⊥ = Option.elim ⊥ g` 임을 확인한다. -/
@[exercise "Prop 2.4" 2]
```

**`Σ → Σ⊥` 의 순서를 직관으로 설명하는 docstring** (Reynolds가 §2.3 끝에서 하는 말):

> `f ⊑ g` ⟺ 모든 σ에 대해 `f σ = ⊥` 이거나 `f σ = g σ`.
> "정보가 늘어나는" 순서다. g는 f와 같은 결과를 주되 **더 많은 초기 상태에서 종료**할 수 있다.

---

## §2.4 최소 고정점 정리

### Reynolds의 세 단계를 그대로 세 보조 정리로

```lean
-- ANCHOR: lfp
/-- 근사 열 `⊥, f⊥, f²⊥, …`. Reynolds §2.4의 `fⁿ⊥`. -/
def approx [Domain D] (f : D → D) : ℕ → D
  | 0     => ⊥
  | n + 1 => f (approx f n)

/-- **1단계** — `⊥ ⊑ f⊥ ⊑ f²⊥ ⊑ ⋯` 는 사슬이다.
    `⊥ ⊑ f⊥` 는 자명하고, 나머지는 `f`의 단조성과 `n`에 대한 귀납법. -/
@[exercise "Prop 2.5-1" 1]
theorem approx_mono [Domain D] {f : D → D} (hf : Continuous f) : Monotone (approx f)

/-- **2단계** — `x = ⨆ₙ fⁿ⊥` 는 `f`의 고정점이다.
    `f`의 연속성으로 `f(⨆ fⁿ⊥) = ⨆ fⁿ⁺¹⊥` 이고, 사슬 앞에 ⊥를 붙여도 상한이 안 변한다. -/
@[exercise "Prop 2.5-2" 2]
theorem lfp_isFixed …

/-- **3단계** — `x`는 **최소** 고정점이다.
    `f y = y` 라 하자. `⊥ ⊑ y` 이고 `fⁿ⊥ ⊑ y → fⁿ⁺¹⊥ ⊑ f y = y`. 귀납법으로 `y`는 상계.

    Reynolds의 주석: 사실 `f y ⊑ y` 만으로 충분하다. 즉 `x`는
    **최소 전(pre)고정점**이기도 하다. 이 강한 형태를 증명해 둔다 —
    §2.5·§2.8의 증명에서 쓰인다. -/
@[exercise "Prop 2.5-3" 2]
theorem lfp_le_of_le …

/-- **명제 2.5 (최소 고정점 정리)** — 위 셋을 합친 것. -/
theorem lfp_isLeast [Domain D] {f : D → D} (hf : Continuous f) :
    IsLeast {x | f x = x} (Predomain.lub ⟨approx f, approx_mono hf⟩)

/-- `Y_D` — 연속 함수를 그 최소 고정점으로 보내는 함수. -/
noncomputable def Y [Domain D] (f : D →𝒸 D) : D := …

/-- `Y_D` 자체가 연속이다. Reynolds: *"It can also be shown that Y_D itself is a
    continuous function."* — 책은 증명하지 않는다. 우리는 한다. -/
@[exercise "§2.4 Y-연속" 3]
theorem Y_continuous …
-- ANCHOR_END: lfp
```

### Scott 귀납법 (핵심 인프라 — 학습자에게 제공)

Reynolds는 명시하지 않지만, §2.5의 명제 2.6·2.7과 §2.8의 완전 추상성을 Lean에서 증명하려면
**고정점에 대한 귀납 원리**가 반드시 필요하다. 이걸 완전 증명된 채로 제공한다.

```lean
/--
**Scott 귀납법(fixed-point induction)**.

`P`가 **허용 가능(admissible)** 하면 — 즉 `P ⊥` 이고 `P`가 사슬 극한에서 닫혀 있으면 —
`(∀x, P x → P (f x))` 로부터 `P (Y f)` 를 얻는다.

책에는 없다. 하지만 Reynolds가 §2.5에서 `while`이 든 명령에 대해 하는
비형식적 논증("근사 명령 wₙ에 대해 성립하므로 극한에서도 성립한다")은 정확히 이 원리다.
Lean에서는 그 논증을 이렇게 명시적으로 만들어야 한다.
-/
theorem scott_induction [Domain D] {f : D → D} (hf : Continuous f)
    {P : D → Prop} (hbot : P ⊥)
    (hlub : ∀ c : Chain D, (∀ n, P (c.seq n)) → P (Predomain.lub c))
    (hstep : ∀ x, P x → P (f x)) : P (Y ⟨f, hf⟩)
```

### `while`의 의미

```lean
-- ANCHOR: whileSem
/--
`⟦while b do c⟧` — Reynolds §2.4의 의미 방정식 (2.4).

    ⟦while b do c⟧ = Y (F)   where  F f σ = if ⟦b⟧ σ then f⊥⊥(⟦c⟧ σ) else σ

**"믿음의 도약(leap of faith)"**: 왜 하필 **최소** 해인가?
Reynolds는 증명할 수 없다고 인정한다 — `while`의 다른 엄밀한 정의가 없기 때문이다.
대신 비형식적 논증을 준다:

    w₀     = while true do skip          (절대 종료하지 않음, 즉 ⊥)
    wₙ₊₁   = if b then (c ; wₙ) else skip

이면 `⟦wₙ⟧ = Fⁿ⊥` 이고, `while b do c`가 `b`를 정확히 n번 검사한 뒤 종료한다면
`i > n`인 모든 `wᵢ`가 같은 결과를 낸다. 따라서 `⟦while b do c⟧ = ⨆ₙ ⟦wₙ⟧ = ⨆ₙ Fⁿ⊥ = Y F`.

**이 프로젝트의 핵심 설계**: `wₙ`은 우리의 **연료 기반 해석기**(`Interpreter.lean`)와
정확히 같은 것이다. 즉 연료 해석기는 편법이 아니라 Reynolds의 논증 그 자체다.
-/
noncomputable def Comm.eval : Comm V → State V → SigmaBot V
  | .wh b c, σ => Y ⟨whileF b (Comm.eval c), whileF_continuous …⟩ σ
  | …
-- ANCHOR_END: whileSem

/-- Reynolds 연습문제 2.4 — `F`가 연속임을 증명하라. **의미 정의가 성립하려면 필수**이므로
    Answers에서는 제공하고, Exercises에서 다시 풀게 한다. -/
@[exercise "Ex 2.4" 3]
theorem whileF_continuous …
```

### 실행 가능한 해석기 — 이 프로젝트를 "돌아가는 것"으로 만드는 부분

```lean
-- ANCHOR: run
/--
연료(fuel) 기반 해석기. Reynolds §2.4의 근사 명령 `wₙ` 을 그대로 구현한 것이다.

`c.run n σ = none` 은 두 가지를 뜻할 수 있다: 정말 발산하거나, 연료가 모자라거나.
그 둘은 `Comm.run_mono` 와 `Comm.eval_eq_run` 으로 구분된다.

**이게 있어야 `#eval`이 된다.** 표시적 의미는 계산 불가능하지만,
학습자는 프로그램을 실제로 돌려보고 싶다.

    #eval (⟪ y := 1; while x > 0 do (y := y × x; x := x - 1) ⟫).run 100 (fun _ => 5)
    -- some (…)   x ↦ 0, y ↦ 120
-/
def Comm.run : Comm V → ℕ → State V → Option (State V)
  | _,       0,     _ => none                     -- w₀ = while true do skip
  | .wh b c, n + 1, σ => if b.eval σ then (c.run n σ) >>= (Comm.wh b c).run n else some σ
  | …
-- ANCHOR_END: run

/-- 연료를 늘리면 결과가 나빠지지 않는다. `Σ → Σ⊥` 의 순서로 말하면 `run n ⊑ run (n+1)`. -/
theorem Comm.run_mono : Monotone (fun n => c.run n)

/--
**적합성(adequacy)** — 표시적 의미와 해석기가 일치한다.

    ⟦c⟧ σ = some σ'  ↔  ∃ n, c.run n σ = some σ'

이 정리가 이 장의 **가장 중요한 다리**다. 왼쪽은 증명용, 오른쪽은 실행용이고,
둘이 같다는 것을 커널이 보증한다. 증명은 `while` 케이스에서 Scott 귀납법을 쓴다.
-/
@[exercise "§2.4 적합성" 3]
theorem Comm.eval_eq_run : c.eval σ = some σ' ↔ ∃ n, c.run n σ = some σ'
```

### 계산 예 — Reynolds가 손으로 하는 것을 Lean으로

```lean
/--
Reynolds §2.4의 비자명한 예:

    Fⁿ⊥ σ = if 0 ≤ σx ≤ n then σ[x := 0][y := σy + σx×(σx-1)÷2] else ⊥

`n`에 대한 귀납법. 책의 계산을 그대로 옮기면 되고, 산술은 `omega`가 처리한다.
그 다음 극한을 취해 `⟦while x ≠ 0 do (x := x-1; y := y+x)⟧` 를 닫힌 꼴로 얻는다.
-/
@[exercise "§2.4 예제" 3]
theorem approx_example …
```

### 추상 구문의 최소 고정점 구성과 초기 대수

§2.4 끝에서 Reynolds는 §1.1의 추상 문법 반송자를 `𝒫(P)ⁿ`에서 최소 고정점으로 구성한다.
Lean의 `inductive`는 같은 구문을 초기 대수로 준다. `MathlibBridge.lean` 또는 Verso 문서에서
둘의 연결과 차이를 **심화 노트**로 설명한다:

> Reynolds의 `sᵢ⁽ʲ⁺¹⁾ = fᵢ(s⁽ʲ⁾)`, `sᵢ = ⋃ⱼ sᵢ⁽ʲ⁾` 는
> 생성자가 유한 인자를 가지므로 `f`가 유한 생성(finitely generated) → 연속 → 최소 고정점 존재.
> 다항 시그니처의 초기 대수는 초기 사슬의 여극한으로 구성할 수 있고, Lambek 보조정리는
> 그 구조 사상이 동형임을 말한다. 이는 구문 반송자의 최소 고정점 구성과 연결되지만,
> 명령 의미의 함수 도메인에서 `Y`가 고르는 최소 고정점과 같은 대상은 아니다.

---

## §2.5 변수 선언과 치환

### 자유 변수 두 종류

```lean
/-- `FV_comm(c)` — 명령의 자유 변수. `newvar v := e in c` 에서 `v`는 `c`에서만 묶인다(`e`에서는 아님). -/
def Comm.fv [DecidableEq V] : Comm V → Finset V
  | .newvar v e c => (c.fv.erase v) ∪ e.fv
  | …

/-- `FA(c)` — **대입되는** 자유 변수. `FA(c) ⊆ FV(c)`. Reynolds §2.5.
    명제 2.6(b)와 §2.6의 `for` 제약(`v ∉ FA(c)`)에 쓰인다. -/
def Comm.fa [DecidableEq V] : Comm V → Finset V
  | .assign v _   => {v}
  | .newvar v _ c => c.fa.erase v
  | …
```

### 명제 2.6 — 명령에 대한 일치 정리

1장의 명제 1.1과 달리 **진술이 복잡하다.** 비종료 때문이다.

```lean
/--
**명제 2.6 (명령에 대한 일치 정리)**

(a) `σ`와 `σ'`가 `FV(c)` 위에서 일치하면,
    `⟦c⟧σ`와 `⟦c⟧σ'`가 **둘 다 ⊥** 이거나, **둘 다 상태이고 `FV(c)` 위에서 일치**한다.
(b) `⟦c⟧σ ≠ ⊥` 이면 `w ∉ FA(c)` 인 모든 `w`에 대해 `(⟦c⟧σ) w = σ w`.

**Lean에서의 진술 설계**: `Option`의 두 경우를 다 다뤄야 하므로 그냥
`⟦c⟧σ = ⟦c⟧σ'` 라고 쓸 수 없다. 관계로 정의하는 편이 낫다:

    def AgreeOn (S : Finset V) : SigmaBot V → SigmaBot V → Prop
      | none,    none    => True
      | some τ,  some τ' => ∀ w ∈ S, τ w = τ' w
      | _,       _       => False

이렇게 두면 진술이 `AgreeOn c.fv (⟦c⟧σ) (⟦c⟧σ')` 로 깔끔해지고, 귀납도 쉬워진다.

**`while` 케이스**: Scott 귀납법을 쓴다. `AgreeOn`이 허용 가능(admissible)함을
먼저 보여야 한다 (평평한 도메인이라 사슬이 결국 상수가 되므로 어렵지 않다).
-/
@[exercise "Prop 2.6" 3]
theorem coincidence_comm …
```

### 명령 치환 — 타입이 제약을 강제한다

```lean
/--
명령에 대한 치환. **치환 사상이 `V → V` 다** (`V → IntExp V` 가 아니다).

Reynolds §2.5:
> *"substitution into commands is much more constrained, since the substitution of an
> expression that is not a variable for the occurrence of a variable on the left side of
> an assignment command would produce a syntactically illegal phrase, such as
> `(x := x+1)/x → 10`, which is `10 := 10+1`."*

**Lean의 장점**: 이 제약을 주석으로 적을 필요가 없다. `δ : V → V` 라는 타입이
문법적으로 불가능한 치환을 애초에 표현할 수 없게 만든다. Reynolds가
"엄밀히 말하면 변수가 정수 식이라고 문법이 말하진 않지만 c_var를 명시하면
정의가 끔찍해진다"며 반칙(cheating)이라 자백하는 부분을, 타입이 정직하게 처리한다.
-/
def Comm.subst [DecidableEq V] [HasFresh V] : Comm V → (V → V) → Comm V
```

### ★ 별칭(aliasing) — 치환 정리가 깨진다

이 절의 하이라이트. **Lean에서 실행해서 확인할 수 있다.**

```lean
-- ANCHOR: aliasing
/--
**치환 정리는 명령에 대해 성립하지 않는다.** Reynolds §2.5.

`x := x+1 ; y := y×2` 와 `y := y×2 ; x := x+1` 은 같은 뜻이다.
그런데 `x`와 `y`를 **둘 다 `z`로** 치환하면
`z := z+1 ; z := z×2` 와 `z := z×2 ; z := z+1` 이 되어 뜻이 달라진다.

서로 다른 변수가 같은 변수로 가는 것을 **별칭(aliasing)** 이라 한다.
Reynolds: *"an inherent subtlety of imperative programming that is a rich source of
programming errors."* 13장에서 이름 호출·참조 호출 프로시저가 이 문제를 악화시킨다.
-/
theorem swap_ok : ⟦⟪ x := x+1; y := y×2 ⟫⟧ = ⟦⟪ y := y×2; x := x+1 ⟫⟧

theorem swap_broken_by_alias : ⟦⟪ z := z+1; z := z×2 ⟫⟧ ≠ ⟦⟪ z := z×2; z := z+1 ⟫⟧

/-- 덜 사소한 예: 계승(factorial) 프로그램이 `x`와 `y`를 별칭으로 만들면 망가진다.
    `#eval`로 직접 확인할 수 있다. -/
example : (⟪ y := 1; while x > 0 do (y := y×x; x := x-1) ⟫).run 100 σ₅ = … -- y ↦ 120
example : (⟪ z := 1; while z > 0 do (z := z×z; z := z-1) ⟫).run 100 σ₅ = … -- ≠ 120
-- ANCHOR_END: aliasing
```

### 명제 2.7 · 2.8

```lean
/--
**명제 2.7 (명령에 대한 치환 정리)** — 별칭을 만들지 않는 치환에 한해 성립한다.

`FV(c) ⊆ V₀` 이고 `δ`가 `V₀` 위에서 단사이면 …

Reynolds가 §2.5 끝에서 하는 방법론적 언급이 중요하다:
> 두 특수 경우(`V₀` = 전체 변수 / `V₀` = FV(c))는 **구조적 귀납법으로 직접 증명되지 않는다.**
> 귀납 가설을 쓰려면 더 일반적인 진술로 강화해야 한다.

Lean에서 증명하다 보면 이걸 몸으로 겪게 된다. **일반화가 왜 필요한지 배우는
최고의 예제**다. Answers에 "약한 진술로 시도했을 때 어디서 막히는지"를 주석으로 남길 것.
-/
@[exercise "Prop 2.7" 3]

/-- **명제 2.8 (명령에 대한 이름 바꾸기 정리)** — 별칭이 있어도 α-변환은 뜻을 보존한다. -/
@[exercise "Prop 2.8" 2]
```

---

## §2.6 구문 설탕: `for` 명령

**가장 재미있고 가장 실행하기 좋은 절.** Reynolds가 `for`의 설계를 네 번 고쳐 쓴다.

```lean
-- ANCHOR: forV1
/-- 판본 1 — 가장 순진한 정의. -/
def forV1 (v) (e₀ e₁) (c) : Comm V := ⟪ %v := %e₀; while %v ≤ %e₁ do (%c; %v := %v + 1) ⟫

/-- **결함 1**: 제어 변수 `v`가 밖으로 샌다. Reynolds: *"the 'side effect' of resetting
    the control variable v"*. `v`는 보통 지역 변수여야 한다.
    `#eval`로 확인 후 정리로 증명한다. -/
theorem forV1_leaks : ∃ σ, (⟦forV1 …⟧ σ).map (· "i") ≠ some (σ "i")
-- ANCHOR_END: forV1

/-- 판본 2 — `newvar`로 감싼다. -/
def forV2 … := ⟪ newvar %v := %e₀ in while %v ≤ %e₁ do (%c; %v := %v + 1) ⟫

/-- **결함 2**: 상한 `e₁`이 매 반복마다 **재평가**된다.
    Reynolds의 극단적 예: `for x := 1 to x do skip` 은 **절대 종료하지 않는다.**
    Lean 정리: `⟦forV2 "x" 1 (var "x") skip⟧ σ = ⊥` (단, `σ x ≥ 1`).
    `run`으로 먼저 감을 잡고(`run 1000 = none`), Scott 귀납법으로 증명한다. -/
theorem forV2_diverges …

/-- 판본 3 — 상한을 미리 고정한다. Reynolds의 최종안. -/
def forV3 … := ⟪ newvar %w := %e₁ in newvar %v := %e₀ in while %v ≤ %w do (%c; %v := %v+1) ⟫

/-- **남은 결함 3**: 본문 `c`가 `v`를 바꾸면 연속된 값으로 돌지 않는다.
    `for x := 1 to 10 do (c'; x := 2×x)` 는 `c'`를 x = 1, 3, 7 에서 실행한다.
    → `v ∉ FA(c)` 제약을 부과한다. 이 제약 하에서 **반복 횟수가 구간 크기와 같음**을 증명한다. -/
theorem forV3_iterates_exactly (h : v ∉ c.fa) …
```

> **왜 이 절이 중요한가**: "구문 설탕은 표현력을 늘리지 않지만 어떤 계산을
> 더 간결하고 이해하기 쉽게 만든다"는 Landin의 통찰과, **잘못 설계된 설탕이
> 어떻게 버그를 부르는지**를 동시에 보여준다. 실무 개발자에게 가장 와닿는 절이다.

연습 2.9 (제어 변수가 구간 밖 값을 갖지 않는 `for`), 2.10 (`dotwice`의 디슈가링 종료성)도 여기.

**2.10이 특히 좋다**: "`c` 안에 `dotwice`가 둘 이상 있으면 치환이 `dotwice` 개수를 늘리는데
왜 이 정의가 유효한가?" → Lean에서는 디슈가링 함수의 **종료 증명**이 그 답이다.
구조적 재귀로 쓰면 자동, 아니면 `termination_by`로 척도를 밝혀야 한다.

---

## §2.7 산술 오류

대부분 산문이지만, **한 가지는 반드시 형식화한다.**

Reynolds의 논점은 오류를 검사하지 않기로 한 연산도 입력마다 결과 하나를 주는 전함수여야
한다는 것이다. 0으로 나눈 구체적인 결과를 사용하지 않는 등식만 그 선택과 무관하다.

```lean
-- ANCHOR: arithParam
/--
0으로 나눌 때의 결과를 **매개변수화**한 축소판 의미론.

Reynolds §2.7:
> *"The only restriction is that these operations must actually be functional.
> For example, x ÷ 0 must be some integer function of x."*

0인 제수에서 `div`와 `rem`이 돌려줄 값만 인자로 받는 `eval`을 만든다. 그러면 아래 등식들이
그 선택을 실제로 관찰하는지 구분할 수 있다.
-/
structure ZeroDivision where
  divZero remZero : Int → Int

variable (A : ZeroDivision)

theorem arith_indep_1 : ⟦⟪ (x + y) × 0 ⟫⟧A σ = 0
theorem arith_indep_2 : ⟦⟪ x ÷ 0 = x ÷ 0 ⟫⟧A σ = true
theorem arith_indep_3 (h : "y" ∉ e.fv) : ⟦⟪ y := x ÷ 0; y := %e ⟫⟧A = ⟦⟪ y := %e ⟫⟧A
theorem arith_indep_4 : ⟦⟪ if x + y = z then %c else %c ⟫⟧A = ⟦%c⟧A
-- ANCHOR_END: arithParam
```

> 이 절의 매개변수화는 **`Ch02/ArithErrors.lean` 안에서만** 한다.
> 본 의미론 전체를 매개변수화하면 나머지 모든 정리가 지저분해진다.
> docstring에 그 이유를 밝힌다.

또한 Lean의 `Int` 나눗셈 규약(`Int.div`, `Int.emod`, `Int.tmod`)을 정리해 적는다 —
스터디에서 반드시 질문이 나온다.

---

## §2.8 건전성과 완전 추상성

```lean
-- ANCHOR: fullAbstraction
/-- 문맥(context) — 구멍(`-`)이 하나 있는 명령. Reynolds §2.8. -/
inductive Ctx (V : Type u) where
  | hole
  | seqL : Ctx V → Comm V → Ctx V
  | seqR : Comm V → Ctx V → Ctx V
  | …
  | newvar : V → IntExp V → Ctx V → Ctx V

/-- `C[c]` — 구멍에 `c`를 **끼워 넣는다**. 치환이 아니다 (이름 바꾸기가 없다). -/
def Ctx.fill : Ctx V → Comm V → Comm V

/-- 관찰(observation) — 초기 상태에서 시작해 종료 여부와 어떤 변수의 값을 본다. -/
def observe (σ : State V) (v : V) (c : Comm V) : Option Int := (c.eval σ).map (· v)

/-- **건전(sound)** — 뜻이 같다고 한 것이 어떤 문맥에서도 다르게 관찰되지 않는다. -/
def Sound (den : Comm V → α) : Prop :=
  ∀ c c', den c = den c' → ∀ C σ v, observe σ v (C.fill c) = observe σ v (C.fill c')

/-- **완전 추상(fully abstract)** — 건전하고, 관찰로 구별되지 않는 것은 뜻도 같다. -/
def FullyAbstract (den : Comm V → α) : Prop := …
-- ANCHOR_END: fullAbstraction

/-- **§2.8의 정리** — 우리 표시적 의미는 완전 추상이다. -/
@[exercise "§2.8 완전추상" 3]
theorem eval_fullyAbstract : FullyAbstract (Comm.eval (V := V))

/--
**더 놀라운 판본** — 관찰을 **닫힌 명령의 종료 여부**로만 제한해도 완전 추상이다.

Reynolds의 증명이 아름답다. `⟦c⟧σ ≠ ⟦c'⟧σ` 인 σ가 있다면,
`c`, `c'`의 자유 변수 `v₀,…,vₙ₋₁`을 `σ`의 값 상수 `κᵢ`로 초기화하는 문맥
    C = newvar v₀ := κ₀ in ⋯ in −
를 잡는다. 일치 정리(명제 2.6)로 `⟦C[c]⟧σ₀ = ⟦c⟧σ` 이다.
한쪽만 발산하면 끝. 둘 다 종료하면 어떤 변수 v와 상수 κ에서 값이 다르므로
    D = C[ − ; if v = κ then skip else while true do skip ]
로 종료 여부만 보고도 구별한다.

**§2.5의 명제 2.6이 여기서 쓰인다.** 장 전체가 이 정리로 수렴하는 구조다.
-/
@[exercise "§2.8 닫힌관찰" 3]
theorem eval_fullyAbstract_closed …
```

**그리고 반드시 짚을 것** (Reynolds가 §2.8 끝에서 경고하는 바):

```lean
/--
완전 추상성은 **무엇을 관찰하기로 했는가**에 달려 있다.

우리 의미론은 다음 쌍들을 같다고 본다:
    x := x+1; x := x+1        ≡  x := x+2
    x := 0; while x<100 do x := x+1  ≡  x := 100
    x := x+1; y := y×2        ≡  y := y×2; x := x+1

실행 시간이나 실행 중 변수 값을 관찰에 넣으면 **건전하지 않게 된다.**
또한 8장에서 병행 합성 `c₀ ∥ c₁` 을 추가하면 문맥이 늘어나 위 셋을 모두 구별할 수 있고,
13장에서 프로시저가 별칭을 만들면 마지막 쌍이 구별된다.
**그때는 다른 의미론으로 갈아타야 한다.**

→ 8장·13장으로 가는 다리. 이 세 등식을 Lean 정리로 증명해 두면
   나중에 "이게 왜 깨지는지"를 대조할 수 있다.
-/
theorem obs_eq_1 : ⟦⟪ x := x+1; x := x+1 ⟫⟧ = ⟦⟪ x := x+2 ⟫⟧
theorem obs_eq_2 : ⟦⟪ x := 0; while x < 100 do x := x+1 ⟫⟧ = ⟦⟪ x := 100 ⟫⟧
```

`obs_eq_2`는 `while`의 최소 고정점을 실제로 계산해야 하는 좋은 연습이다 (★★★).

---

## `MathlibBridge.lean` — 직접 만든 것 ↔ Mathlib

심화 파일. **필수 아님.** 하지만 "실무에서는 뭘 쓰나"에 답한다.

| 우리 (`Ch02/Domain.lean`) | Mathlib |
|---|---|
| `Chain α` | `OmegaCompletePartialOrder.Chain α` |
| `Predomain` | `OmegaCompletePartialOrder` |
| `Predomain.lub c` | `OmegaCompletePartialOrder.ωSup c` |
| `Continuous f` | `OmegaCompletePartialOrder.ωScottContinuous f` |
| `D →𝒸 D` | `α →𝒄 β` (`ContinuousHom`) |
| `Y f` (최소 고정점) | `Part.fix` (부분 함수판), `OrderHom.lfp` (완비 격자판) |
| `Option (State V)` | `Part (State V)` 또는 `WithBot` |
| `scott_induction` | `Part.fix_le`, `Part.fix_eq_ωSup_of_ωScottContinuous` |

**CSlib 쪽 대응** (6장 예고): Reynolds가 §2.8에서 "관찰(observation)에 따라 완전 추상성이
달라진다"고 말하는 논점은, 6장 이후 CSlib의 `Foundations/Semantics/LTS/TraceEq.lean`(트레이스 동치)과
`LTS/Bisimulation.lean`(이중시뮬레이션)에서 **서로 다른 프로그램 동치**로 다시 나타난다.
`Ch02/FullAbstraction.lean` docstring에서 이 예고를 남겨 둘 것.

주의할 점을 docstring으로 남긴다:
- `OrderHom.lfp`는 **완비 격자(complete lattice)** 를 요구한다. `Σ → Σ⊥` 는 완비 격자가 아니다
  (두 서로 다른 상태의 상한이 없다). 그래서 Kleene 방식(`⨆ fⁿ⊥`)이 맞는 도구다.
- Mathlib의 `Part.fix`는 `(∀ a, Part (β a))` 꼴에 특화되어 있다. 우리 `Σ → Σ⊥` 를
  그 꼴로 맞추면 `Part.fix_eq_ωSup` 등을 그대로 쓸 수 있다 — 재작성 연습으로 좋다.

---

## 연습문제 매핑

| 책 | 형태 | 별점 | 비고 |
|---|---|---|---|
| **2.1** | 이중 대입 `v₀, v₁ := e₀, e₁` 문법 + 의미 방정식 | ★ | `v₀ = v₁` 일 때를 어떻게 할지 논의거리 |
| **2.2** (a) | `repeat c until b` 문법 + **최소 고정점으로** 의미 | ★★ | |
| **2.2** (b) | 같은 것을 구문 설탕으로 | ★ | |
| **2.2** (c) | (a)와 (b)가 동치임을 **증명** | ★★★ | 고정점 유일성 논증. 이 장 최고의 연습 |
| **2.3** | `while x ≠ 0 do x := x-2` 의 닫힌 꼴 증명 | ★★★ | 짝/홀·양/음 4분할. `omega`와 Scott 귀납법 |
| **2.4** | `F`가 연속임 | ★★★ | 의미 정의의 전제. Answers에 이미 있으므로 Exercises에서 재현 |
| **2.5** | `⟦while b do c⟧ = ⟦while b do (c; if b then c else skip)⟧` | ★★★ | 양방향 `⊑`. 매우 어렵다. 힌트 필수 |
| **2.6** | `FV(c₀) ∩ FA(c₁) = FA(c₀) ∩ FV(c₁) = ∅` 이면 순서 교환 가능 | ★★ | 명제 2.6 활용. 책의 진술에 `= ∅` 이 빠져 있으니 주석으로 밝힐 것 |
| **2.7** | 별칭에 안전한 계승 프로그램 작성 | ★★ | `#eval`로 두 경우 다 확인 → **가장 재밌는 문제** |
| **2.8** | 명제 2.7의 조건 약화 | ★★★ | |
| **2.9** | 제어 변수가 구간 밖으로 나가지 않는 `for` | ★★ | 오버플로 회피 동기 |
| **2.10** | `dotwice`의 디슈가링이 유효한 이유 | ★★ | Lean에서는 종료 증명이 곧 답 |

---

## 이 장에서 학습자가 얻는 것

1. **왜 비종료가 의미론을 어렵게 만드는가** — 풀기 방정식의 해가 여럿이라는 것을 직접 증명
2. **도메인·연속성·최소 고정점**을 직접 만들어 본 경험 (Mathlib에서 꺼내 쓴 것이 아니라)
3. **`Option` 모나드 = 리프팅** — 순차 합성이 bind라는 관점
4. **연료 해석기 ↔ 표시적 의미**의 다리. 실행과 증명이 같은 것을 말한다는 확인
5. **별칭이 실제 버그다** — 실행해서 눈으로 확인
6. **좋은 구문 설탕 설계**가 왜 어려운지 (`for`의 네 판본)
7. **완전 추상성** — "의미론이 충분히 추상적인가"를 묻는 정확한 방법, 그리고 그 답이
   *무엇을 관찰하기로 했는가*에 달렸다는 것
8. **일반화하지 않으면 귀납이 안 된다** (명제 2.7) — 증명 실무의 핵심 기술
