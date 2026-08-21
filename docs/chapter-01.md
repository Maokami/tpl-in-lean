# 1장 «Predicate Logic» — 형식화 상세 설계

> Reynolds, *Theories of Programming Languages*, Chapter 1 (pp. 1–23)
> §1.1 Abstract Syntax · §1.2 Denotational Semantics · §1.3 Validity and Inference · §1.4 Binding and Substitution

## 이 장의 위치

Reynolds가 프로그래밍 언어 책을 **논리학**으로 시작하는 이유를 그가 직접 밝힌다:

1. 술어 논리는 수학 표기에 가까워 독자의 직관이 정확하다 → **낯선 개념을 익숙한 무대에서 배운다**
2. 술어 논리에는 **비종료(nontermination)가 없다** → 의미를 보통 집합으로 줄 수 있고, 도메인은 2장으로 미룬다
3. 3장에서 명령형 프로그램 명세에 그대로 쓰인다

즉 1장은 **추상 구문 · 표시적 의미론 · 추론 규칙 · 결합** 네 개념의 예행연습이다.
이 넷은 책 전체를 관통한다.

Reynolds가 §1.1에서 추상 구문에 부과하는 조건은 Lean의 `inductive`가 제공하는
생성자 단사성, 생성자 치역의 서로소성, 구조적 재귀에 각각 대응한다.

---

## 파일 배치

| 파일 | 책 | 내용 |
|---|---|---|
| `Prelude.lean` | — | `Var` 요구조건(CSlib `HasFresh`), `State`, CSlib `σ[v := n]` |
| `Ch01/Syntax.lean` | §1.1 | `IntExp`, `Assert`, 추상 구문 조건이 왜 공짜인가 |
| `Ch01/Notation.lean` | §1.1 | 구체 구문 → 추상 구문 (Lean 매크로 DSL) |
| `Ch01/Realizations.lean` | §1.1, 연습 1.3 | 괄호 없는 접두 표기와 구문 트리의 일대일 대응 |
| `Ch01/Depth/Algebra.lean` | §1.1 각주 | 초기 대수(initial algebra) — 선택 심화 |
| `Ch01/Semantics.lean` | §1.2 | `IntExp.eval`, `Assert.eval` |
| `Ch01/Validity.lean` | §1.3 | 타당성, 강함/약함, 추론 규칙, 건전성 |
| `Ch01/FreeVars.lean` | §1.4 | `FV`, 명제 1.1 일치 정리 |
| `Ch01/Substitution.lean` | §1.4 | 치환, 명제 1.2~1.5 (α-변환은 CSlib `HasAlphaEquiv` 표기) |
| `Ch01/Ex.lean` | 연습 | 1.1 ~ 1.4, 1.7 |
| `Ch01/Ex/Summation.lean` | 연습 | 1.5, 1.6 (합 식). 축소판 언어를 따로 세운다 |

---

## Prelude — 변수를 어떻게 다룰 것인가

Reynolds 원문:

> *"Certain predefined nonterminals do not occur on the left side of productions.
> In the above case, ⟨var⟩ is a predefined nonterminal denoting a countably infinite
> set of variables (with unspecified representations)."*

Reynolds의 가산 무한 조건에서 이 형식화에 필요한 부분은, 유한한 금지 집합 밖에서 언제나
새 변수를 고를 수 있다는 성질이다. CSlib의 `HasFresh`가 바로 그 성질을 제공한다.
`HasFresh` 자체가 가산성을 뜻하지는 않는다.

```lean
-- Cslib/Foundations/Data/HasFresh.lean (CSlib 원문)
class HasFresh (α : Type u) where
  fresh : Finset α → α
  fresh_notMem (s : Finset α) : fresh s ∉ s
```

우리 쪽 docstring에서 대응을 짚어 준다:

```lean
/--
변수 타입에 요구하는 것. Reynolds §1.1의
"표현이 지정되지 않은(with unspecified representations) 가산 무한 변수 집합 ⟨var⟩".

- `DecidableEq` — 두 변수가 같은지 판정할 수 있어야 치환과 자유 변수를 계산할 수 있다.
- `HasFresh`    — 어떤 유한 집합이 주어져도 그 안에 없는 변수를 하나 만들 수 있다.
                  §1.4에서 변수 포획(capture)을 피할 때 반드시 필요하다.

Reynolds는 §1.4에서 새 변수를 "어떤 표준 순서(some standard ordering)에서 첫 번째"로
정한다. 그런데 **그 표준 순서가 실제로 무엇인지는 어떤 명제에도 영향을 주지 않는다.**
필요한 성질은 "항상 새 이름을 얻는다"뿐이고, 그것이 `HasFresh.fresh_notMem`이다.
CSlib가 이 추상화를 이미 갖고 있다는 사실 자체가, 이것이 언어를 형식화할 때
**반복해서 나타나는 패턴**이라는 증거다.
-/
```

인스턴스는 `String`과 `ℕ`에 준다. 예제는 `String`, 증명 실험은 `ℕ`이 편하다.
(CSlib는 `HasFresh.ofNatEmbed`로 `ℕ ↪ α` 로부터 인스턴스를 만드는 길을 준다.)

`State`:
```lean
/-- 상태(state). Reynolds의 Σ = ⟨var⟩ → ℤ. §1.2에서 "논리학자가 assignment라 부르는 것". -/
abbrev State (V : Type u) := V → Int
```

상태 갱신 `[σ | v: n]` 표기는 **새로 만들지 않는다.** CSlib에 이미 있다:

```lean
-- Cslib/Foundations/Syntax/HasSubstitution.lean
instance [DecidableEq α] : HasSubstitution (α → β) α β where
  subst := Function.update
```
→ `σ["x" := 3]` 이 곧 Reynolds의 `[σ | x: 3]` 이다. **프로브에서 동작 확인 완료.**

CSlib는 `Function.update`를 **치환(substitution)** 타입클래스의 인스턴스로 등록한다.
> Reynolds는 §1.2에서 상태 갱신 `[σ | v: n]`을, §1.4에서 치환 `p / v → e`를 따로 도입하는데,
> **둘은 같은 모양**이다. 상태는 `⟨var⟩ → ℤ`이고 치환 사상은 `⟨var⟩ → ⟨intexp⟩`이며,
> 둘 다 "한 변수에서만 바꾸기"를 한다. 이 대응을 여기서 짚어두면
> §1.4의 `Subst V := V → IntExp V`와 명제 1.3(치환 정리)이 훨씬 자연스럽게 들어온다.

---

## §1.1 추상 구문

### 데이터 타입

```lean
-- ANCHOR: IntOp
/-- 이항 정수 연산자. Reynolds §1.1의 `+  -  ×  ÷  rem`. -/
inductive IntOp where
  | add | sub | mul | div | rem
  deriving DecidableEq, Repr
-- ANCHOR_END: IntOp

-- ANCHOR: IntExp
/--
정수 식(integer expression). Reynolds §1.1의 ⟨intexp⟩.

**책과의 차이 1**: Reynolds는 이항 연산마다 별도 생성자(`c₊`, `c₋`, `c×`, …)를 둔다.
여기서는 연산자를 `IntOp` 태그로 묶었다. 이유는 구조적 귀납법(structural induction)의
케이스가 5배로 늘어나는 것을 막기 위해서다. Reynolds 본인도 의미 방정식을 쓸 때
"(and similarly for -, ×, ÷, rem)"이라고 적는다. 태그는 그 "and similarly"를
코드로 만든 것이다.

**책과의 차이 2**: Reynolds의 상수 생성자는 `c₀, c₁, c₂, …` 즉 자연수뿐이고,
음수는 단항 마이너스로 만든다. 여기서는 `Int`를 직접 넣었다. 자유 변수·치환·의미
어느 명제도 이 선택에 영향받지 않는다 (연습문제 1.0에서 확인한다).
-/
inductive IntExp (V : Type u) where
  | num : Int → IntExp V
  | var : V → IntExp V
  | neg : IntExp V → IntExp V
  | bin : IntOp → IntExp V → IntExp V → IntExp V
  deriving DecidableEq, Repr
-- ANCHOR_END: IntExp
```

```lean
/-- 비교 연산자. Reynolds의 `=  ≠  <  ≤  >  ≥`. -/
inductive Cmp where | eq | ne | lt | le | gt | ge

/-- 이항 논리 연산자. Reynolds의 `∧  ∨  ⇒  ⇔`. -/
inductive LogOp where | and | or | imp | iff

/-- 양화사. Reynolds의 `∀  ∃`. -/
inductive Quant where | all | ex

/--
단언(assertion). Reynolds §1.1의 ⟨assert⟩ — 논리학자가 "정형식(well-formed formula)"이라
부르는 것.

`Assert`는 `IntExp`를 참조하지만 그 역은 없다. 그래서 상호 귀납(mutual induction)이
아니라 별도 `inductive` 두 개다. Reynolds의 문법도 정확히 그렇게 되어 있다.
-/
inductive Assert (V : Type u) where
  | tru | fls
  | cmp   : Cmp → IntExp V → IntExp V → Assert V
  | not   : Assert V → Assert V
  | bin   : LogOp → Assert V → Assert V → Assert V
  | quant : Quant → V → Assert V → Assert V
  deriving DecidableEq, Repr
```

### 추상 구문 조건과 `inductive`

Reynolds가 §1.1에서 부과하는 세 조건과 Lean의 대응:

| Reynolds의 조건 | Lean이 주는 것 |
|---|---|
| 각 생성자는 **단사(injective)** | `IntExp.bin.injEq`, `injection` 태틱 |
| 같은 반송자(carrier)로 가는 두 생성자의 **치역이 서로소** | `IntExp.noConfusion`, `simp`/`nofun` |
| 모든 원소가 **유한 번의 생성자 적용**으로 만들어짐 | 재귀자 `IntExp.rec` = 구조적 귀납법 |
| (각주) 이들이 **다중 정렬 초기 대수(many-sorted initial algebra)**를 이룬다 | `IntExp.rec`의 유일성 |

이걸 코드로 직접 보여준다:

```lean
-- ANCHOR: freeConditions
section 추상구문조건
variable {V : Type u} (e₀ e₁ : IntExp V) (op : IntOp) (n : Int) (v : V)

/-- 조건 1 — 생성자는 단사다. Reynolds가 손으로 요구하는 것을 `inductive`가 준다. -/
example (h : IntExp.bin op e₀ e₁ = IntExp.bin op e₀ e₁) : True := trivial
example : Function.Injective (IntExp.var (V := V)) := fun _ _ h => by injection h

/-- 조건 2 — 서로 다른 생성자의 치역은 서로소다. -/
example : IntExp.num n ≠ IntExp.var v := by nofun

/-- 조건 3 — 모든 정수 식은 유한 번의 생성자 적용으로 만들어진다.
    이것이 구조적 귀납법이 가능한 이유이며, `IntExp.rec`가 바로 그 원리다. -/
#check @IntExp.rec
end 추상구문조건
-- ANCHOR_END: freeConditions
```

> **스터디 토론거리**: Reynolds는 §2.4 끝에서 "추상 문법의 정의는 사실
> `𝒫(P)ⁿ`에서의 최소 고정점(least fixed point)"이라고 말한다.
> Lean의 `inductive`는 구문을 초기 대수로 준다. 다항 시그니처에서는 초기 사슬을 통한
> 최소 고정점 구성과 연결되지만, 이것은 명령 의미의 함수 도메인에서 고르는 최소 고정점과
> 같은 대상이 아니다. `Depth/SignatureFunctor.lean`에서 이 구분을 짚는다.

### 구체 구문 — Lean 매크로 DSL

Reynolds는 "추상 구문을 위해서도 표기는 필요하다"며 **추상 문법(abstract grammar)** 이라는
타협안을 쓴다. Lean에서는 이걸 진짜로 구현할 수 있다:

```lean
-- ANCHOR: dsl
/--
객체 언어(object language)를 Lean 안에서 직접 쓰기 위한 표기.
`⟪ … ⟫`  안에서는 Reynolds의 구체 구문을 쓰고, 결과는 `IntExp`/`Assert` 값이다.

    #eval ⟪ x + 1 × 2 ⟫              -- IntExp.bin .add (.var "x") (…)
    #eval ⟪ ∀ y, y ≤ x ⇒ y < x + 1 ⟫ -- Assert.quant .all "y" (…)

이것이 Reynolds가 §1.1에서 "구체 표현과 추상 본질의 분리"라고 말한 바로 그것이다.
매크로가 구체 구문을, `inductive`가 추상 본질을 맡는다.
-/
syntax "⟪" reyExp "⟫" : term
-- (elaborator 구현)
-- ANCHOR_END: dsl
```

우선순위(precedence)는 Reynolds의 우선순위 목록을 그대로 옮긴다:
```
(× ÷ rem) (-단항 + -이항) (= ≠ < ≤ > ≥) ¬ ∧ ∨ ⇒ ⇔
```
모두 좌결합. 양화사 본문은 "첫 정지 기호(stopping symbol) 또는 둘러싼 구의 끝까지".

DSL은 `IntExp.bin .add (.var "x") (IntExp.bin .mul (.num 1) (.num 2))`처럼 중첩된
생성자 표현을 줄여, 예제의 구문 구조를 표기에서 바로 읽게 한다.

### 여러 실현(realization)

Reynolds는 같은 추상 구문의 세 가지 실현을 든다: 괄호 중위 문자열, 접두 문자열, 구문 트리.
이 저장소는 그중 연습 1.3의 괄호 없는 접두 표기를 형식화한다. 문자열의 토큰화 문제를
섞지 않으려고 결과를 `String`이 아니라 `List Tok`으로 둔다.

```lean
/-- 괄호 없는 접두 표기를 이루는 토큰 열. -/
def IntExp.toPrefix : IntExp String → List Tok

/-- 실제 식을 나타내는 토큰 열만 모은 구문 세계. -/
def PrefixPhrase := {xs : List Tok // ∃ e : IntExp String, e.toPrefix = xs}

/-- 구문 트리와 접두 표기 구문 세계의 일대일 대응. -/
noncomputable def IntExp.equivPrefixPhrase : IntExp String ≃ PrefixPhrase
```

`toPrefix_prefixFree`와 `toPrefix_injective`는 괄호가 없어도 식의 경계가 모호해지지 않음을
증명한다. `equivPrefixPhrase`는 여기에 모든 접두 구가 실제 식에서 왔다는 조건까지 더한다.
이런 구문 재귀가 왜 유일한지는 `Depth/Algebra.lean`에서 초기성으로 설명한다.

### `Depth/Algebra.lean` (선택 심화)

범주론을 아는 사람을 위한 보너스이자, Reynolds의 각주
*"the reader who is familiar with universal algebra will recognize that these conditions
insure that abstract phrases form a many-sorted initial algebra"* 의 형식화다.

```lean
/-- `IntExp V`에 대한 대수(algebra) — Reynolds의 "반송자 + 생성자". -/
structure IntExpAlg (V : Type u) where
  carrier : Type v
  num : Int → carrier
  var : V → carrier
  neg : carrier → carrier
  bin : IntOp → carrier → carrier → carrier

/-- 초기성(initiality): 임의의 대수로 가는 준동형(homomorphism)이 **유일하게** 존재한다. -/
theorem IntExp.initial (A : IntExpAlg V) :
    ∃! f : IntExp V → A.carrier, IsHom f A
```
현재 파일은 `eval`과 `fv`가 이 유일 준동형으로 얻는 fold와 같음을 증명한다.
`toPrefix`도 같은 재귀 구조를 따르지만, 그 일치 정리는 아직 따로 두지 않았다.

---

## §1.2 표시적 의미론

```lean
-- ANCHOR: eval
/-- `⟦e⟧ σ` — 정수 식의 의미. Reynolds §1.2의 `⟦-⟧intexp ∈ ⟨intexp⟩ → Σ → ℤ`. -/
def IntExp.eval : IntExp V → State V → Int
  | .num n,        _ => n
  | .var v,        σ => σ v
  | .neg e,        σ => -(e.eval σ)
  | .bin op e₀ e₁, σ => op.denote (e₀.eval σ) (e₁.eval σ)
-- ANCHOR_END: eval
```

`IntOp.denote`의 docstring은 0으로 나누는 경우를 다음처럼 설명한다.

```lean
/--
연산자 기호의 의미. `÷`와 `rem`은 0으로 나누는 경우가 있다.

Reynolds §1.2: *"expressions always terminate without an error stop.
In particular, division by zero must produce some integer result."*
그가 여기서 요구하는 것은 0으로 나누는 경우에도 정수 하나를 돌려주는 전함수라는 점까지다.

이 형식화는 Lean의 규약인 `x / 0 = 0`, `x % 0 = x`를 쓴다. 0인 제수의 구체적인 결과를
사용하는 명제는 이 선택에 의존하고, 그 경우를 사용하지 않는 명제만 선택과 무관하다.
-/
def IntOp.denote : IntOp → Int → Int → Int
```

단언의 의미:

```lean
-- ANCHOR: assertEval
/--
`⟦p⟧ σ` — 단언의 의미. Reynolds의 `⟦-⟧assert ∈ ⟨assert⟩ → Σ → 𝔹`.

**책과의 차이**: Reynolds는 𝔹 = {true, false}로 간다. 여기서는 `Prop`이다.
정수 산술과 양화를 포함한 단언 언어 전체에는 실행 가능한 공통 진리 판정기가 없다.
계산 가능한 `Bool` 평가기는 그런 판정기를 요구하지만, `Prop`은 판정 절차 없이 뜻을
표현할 수 있다.

이 경계는 우연이 아니다. Reynolds가 §2.1에서 명령형 언어의 ⟨boolexp⟩를 만들 때
*"the same as assertions except for the omission of quantifiers
(for the obvious reason that they are noncomputable)"* 라고 쓴다.
이 형식화에서는 그 계산 가능성의 경계를 `Prop`과 `Bool`의 차이로 드러낸다.

2장에서 `BoolExp.eval : BoolExp V → State V → Bool` 을 만들고, 양화사 없는 조각에서
두 의미가 일치함을 증명한다(`Ch02/Semantics.lean`의 `boolExp_eval_iff`).
-/
def Assert.eval [DecidableEq V] : Assert V → State V → Prop
  | .tru,            _ => True
  | .fls,            _ => False
  | .cmp c e₀ e₁,    σ => c.denote (e₀.eval σ) (e₁.eval σ)
  | .not p,          σ => ¬ p.eval σ
  | .bin op p q,     σ => op.denote (p.eval σ) (q.eval σ)
  | .quant .all v p, σ => ∀ n : Int, p.eval (σ[v := n])
  | .quant .ex  v p, σ => ∃ n : Int, p.eval (σ[v := n])
-- ANCHOR_END: assertEval
```

**메타언어/객체언어 구분** — Reynolds가 강조하는 논점이다.
그는 메타변수를 이탤릭·그리스 문자로, 객체 변수를 산세리프로 쓴다. Lean에서는:
- 메타변수 = Lean 변수 (`v : V`, `e : IntExp V`)
- 객체 변수 = `V`의 원소 (`"x" : String`)

DSL이 이 구분을 눈에 보이게 만든다: `⟪ x ⟫`의 `x`는 문자열이고,
`⟪ %v ⟫` 같은 안티쿼트(antiquote)로 메타변수를 삽입한다. DSL은 이 구분을 설계에 반영한다.

---

## §1.3 타당성과 추론

```lean
/-- **타당(valid)** — 모든 상태에서 참. -/
def Valid (p : Assert V) : Prop := ∀ σ : State V, ⟦p⟧ₐ σ

/-- **충족 불가능(unsatisfiable)** — 모든 상태에서 거짓. -/
def Unsat (p : Assert V) : Prop := ∀ σ : State V, ¬ ⟦p⟧ₐ σ

/-- `p`가 `q`보다 **강하다(stronger)**. `Valid (p ⇒ q)`와 같다. -/
def Stronger (p q : Assert V) : Prop := ∀ σ : State V, ⟦p⟧ₐ σ → ⟦q⟧ₐ σ

/-- **동치(equivalent)** — 같은 의미. -/
def Equivalent (p q : Assert V) : Prop := ∀ σ : State V, (⟦p⟧ₐ σ ↔ ⟦q⟧ₐ σ)
```

증명할 것:
- `Stronger`의 반사성과 추이성 — Reynolds가 "dual preorders라 영어 어감과는 안 맞는다"고
  적는 대목. `Stronger.refl`과 `Stronger.trans`로 증명한다.
- `Valid .tru`, `Unsat .fls`, `Stronger .fls p`, `Stronger p .tru`
- `Equivalent p q ↔ Stronger p q ∧ Stronger q p`

### 추론 규칙

Reynolds는 완전한 체계를 주지 않는다(*"consult any elementary text on logic"*).
그의 목적은 **개념의 예시**다. 그래서 우리도 작은 체계를 주고 **건전성(soundness)** 을 증명한다.

```lean
-- ANCHOR: proofSystem
/--
술어 논리의 작은 추론 체계. Reynolds §1.3이 예시로 드는 규칙들이다.

각 생성자가 하나의 추론 규칙이다. 전제가 위, 결론이 아래 — Lean의 화살표 방향이
Reynolds의 가로선과 정확히 대응한다.
-/
inductive Proof : Assert V → Prop where
  /-- 공리꼴: `e = e`. -/
  | eqRefl (e : IntExp V) : Proof (.cmp .eq e e)
  /-- 한 전제 규칙: `e₀ = e₁`로부터 `e₁ = e₀`. -/
  | eqSymm {e₀ e₁ : IntExp V} : Proof (.cmp .eq e₀ e₁) → Proof (.cmp .eq e₁ e₀)
  /-- 두 전제 규칙 — 전건 긍정(modus ponens). -/
  | mp {p q : Assert V} : Proof p → Proof (.bin .imp p q) → Proof q
  /-- 두 전제 규칙 — 연언 도입. -/
  | andIntro {p q : Assert V} : Proof p → Proof q → Proof (.bin .and p q)
  /-- 보편 일반화(∀-도입). -/
  | genAll (v : V) {p : Assert V} : Proof p → Proof (.quant .all v p)
-- ANCHOR_END: proofSystem

/-- **건전성(soundness)** — 증명된 것은 타당하다. -/
theorem Proof.sound {p : Assert V} : Proof p → Valid p
```

### `∀`-도입은 규칙이지 함의가 아니다

Reynolds가 한 페이지를 할애하는 논점을 두 정리로 비교한다.

```lean
-- ANCHOR: genVsImp
/-- 건전한 규칙: `p`가 **타당**하면 `∀v. p`도 타당하다. -/
@[exercise "§1.3 gen-sound" 1]
theorem valid_forall_of_valid {p : Assert V} (v : V) (h : Valid p) :
    Valid (.quant .all v p) := by sorry

/--
건전하지 **않은** 규칙: `p ⇒ ∀v. p` 는 타당하지 않다.

Reynolds의 반례를 그대로 쓴다: `v`가 `x`, `p`가 `x > 0`일 때
`x > 0 ⇒ ∀x. x > 0` 은 `x = 3`인 상태에서 거짓이다.

이것이 "추론(inference)"과 "함의(⇒)"를 헷갈리면 안 되는 이유다.
-/
@[exercise "§1.3 gen-not-imp" 2]
theorem not_valid_imp_forall :
    ¬ Valid (⟪ x > 0 ⇒ ∀ x, x > 0 ⟫ : Assert String) := by sorry
-- ANCHOR_END: genVsImp
```

이 두 정리가 나란히 서 있는 것만으로 §1.3의 요점이 전달된다.
`decide`로 반례를 확인할 수 있게 상태를 구체적으로 잡아준다.

> Reynolds가 언급하는 논리적 타당성(logical validity)·완전성(completeness)·괴델
> 불완전성 정리는 **Verso 문서에만** 산문으로 쓴다. Lean 코드로 만들지 않는다.
> (Reynolds 본인이 "이 책에서는 거의 다루지 않는다"고 한다.)
>
> → `manual/Manual/Ch01.lean` 의 "곁가지 — 완전성과 괴델" 절에 있다.

---

## §1.4 결합과 치환 — 이 장의 본론

### 자유 변수

```lean
-- ANCHOR: fv
/-- `FV_intexp(e)` — 정수 식에 자유롭게 나타나는 변수. Reynolds §1.4. -/
def IntExp.fv [DecidableEq V] : IntExp V → Finset V
  | .num _        => ∅
  | .var v        => {v}
  | .neg e        => e.fv
  | .bin _ e₀ e₁  => e₀.fv ∪ e₁.fv

/--
`FV_assert(p)` — 단언의 자유 변수.

양화사 케이스가 전부다: `FV(∀v. p) = FV(p) \ {v}`.
`v`의 결합 발생(binding occurrence)이 `p` 안의 모든 `v`를 잡아먹는다.
-/
def Assert.fv [DecidableEq V] : Assert V → Finset V
  | .quant _ v p => p.fv.erase v
  | …
-- ANCHOR_END: fv
```

### 명제 1.1 — 일치 정리 (Coincidence Theorem)

> *"If p is a phrase of type θ, and σ and σ' are states such that σw = σ'w
> for all w ∈ FV_θ(p), then ⟦p⟧σ = ⟦p⟧σ'."*

```lean
-- ANCHOR: coincidence
/--
**명제 1.1 (일치 정리, coincidence theorem)** — 정수 식 판.

구의 값은 **자유 변수 위에서의 상태에만** 의존한다.
이것이 "자유 변수"라는 개념이 의미론적으로 옳다는 증거다.

증명은 구조적 귀납법(structural induction)이다. Reynolds는 이 증명을
"형식 언어의 성질을 증명하는 중요한 방법"의 첫 예로 든다.
-/
@[exercise "Prop 1.1a" 2]
theorem coincidence_intExp [DecidableEq V] {e : IntExp V} {σ σ' : State V}
    (h : ∀ w ∈ e.fv, σ w = σ' w) : e.eval σ = e.eval σ' := by sorry

/--
**명제 1.1 (일치 정리)** — 단언 판.

양화사 케이스가 새롭다. Reynolds는 `∀v. q`를 다룰 때 귀납 가설을 `σ`, `σ'`가 아니라
`σ[v := n]`, `σ'[v := n]`에 적용하라고 설명한다. `FV(∀v.q) = FV(q) \ {v}` 이므로
`v`만 빼고 일치하던 두 상태를 `v`에 같은 값으로 덮으면 `FV(q)` 전체에서 일치하게 된다.

Lean에서는 이게 "귀납 가설이 `∀ σ σ'`로 일반화되어 있어야 한다"는 뜻이다.
`induction p generalizing σ σ'` 를 쓰거나, 애초에 `σ σ'`를 `theorem` 인자에서
빼고 `∀`로 둔다.
-/
@[exercise "Prop 1.1b" 3]
theorem coincidence_assert [DecidableEq V] {p : Assert V} {σ σ' : State V}
    (h : ∀ w ∈ p.fv, σ w = σ' w) : (p.eval σ ↔ p.eval σ') := by sorry
-- ANCHOR_END: coincidence
```

> **왜 `=`가 아니라 `↔`인가**: `Assert.eval`이 `Prop`을 돌려주므로,
> `propext` 없이는 `=`가 아니라 `↔`가 자연스럽다. docstring에 밝힌다.

### 치환

Reynolds가 변수 포획의 문제를 보이는 반례를 따라간다.

> 공리꼴 `(∀v. p) ⇒ (p / v → e)` 에서 `p := ∃y. y > x`, `v := x`, `e := y + 1` 을 넣으면
> `(∀x. ∃y. y > x) ⇒ ((∃y. y > x) / x → y+1)`.
> 왼쪽은 항상 참. 그런데 순진하게 밀어 넣으면 오른쪽은 `∃y. y > y + 1` — 항상 거짓.
> → `y + 1`의 자유 변수 `y`가 `∃y`에 **포획(capture)** 되었다.

```lean
-- ANCHOR: subst
/-- 치환 사상(substitution map). Reynolds의 Θ = ⟨var⟩ → ⟨intexp⟩. -/
abbrev Subst (V : Type u) := V → IntExp V

/-- `e /ₛ δ` — 정수 식에 대한 동시 치환(simultaneous substitution). -/
def IntExp.subst [DecidableEq V] : IntExp V → Subst V → IntExp V
  | .var v, δ => δ v
  | …

/--
`p /ₛ δ` — 단언에 대한 동시 치환. **변수 포획을 피한다.**

양화사 케이스:
```
(∀v. p) /ₛ δ = ∀ vnew. (p /ₛ δ[v := .var vnew])
  where vnew ∉ ⋃ { FV(δ w) | w ∈ FV(p) \ {v} }
```

`vnew`를 고르는 규칙 (Reynolds §1.4):
- `v` 자체가 조건을 만족하면 `vnew := v` (불필요한 이름 바꾸기를 피한다)
- 아니면 "어떤 표준 순서에서 첫 번째" → 우리는 `Cslib.HasFresh.fresh`

**종료성**: 재귀 호출이 `p`(진부분항)에 대해 일어나므로 구조적 재귀다.
"이름을 바꾼 뒤 다시 치환한다"는 순진한 정의로 쓰면 종료 증명이 필요해진다.
Reynolds의 정의를 그대로 따르면 그 문제가 없다.
-/
def Assert.subst [DecidableEq V] [HasFresh V] : Assert V → Subst V → Assert V
  | .quant q v p, δ =>
      let S := (p.fv.erase v).biUnion fun w => (δ w).fv
      let vnew := if v ∈ S then HasFresh.fresh S else v
      .quant q vnew (p.subst (Function.update δ v (.var vnew)))
  | …

/-- `p /[v := e]` — 한 변수 치환. Reynolds의 `p / v → e`. -/
scoped notation:80 p:80 " /[" v ":=" e "] " =>
  Assert.subst p (Function.update IntExp.var v e)
-- ANCHOR_END: subst
```

### 명제 1.2 — 치환의 구문적 성질

```lean
/-- **명제 1.2(a)** — 자유 변수 위에서 같은 치환은 같은 결과를 낸다. -/
@[exercise "Prop 1.2a" 2]
theorem subst_congr_intExp
    (h : ∀ w ∈ e.fv, δ w = δ' w) : e /ₑ δ = e /ₑ δ'

/-- **명제 1.2(b)** — 항등 치환. Reynolds: `p / c_var = p`.
    "변수를 대응하는 정수 식으로 보내는 생성자 `c_var`가 항등 치환으로 작동한다." -/
theorem subst_var_intExp (e : IntExp V) : e /ₑ IntExp.var = e

/-- **명제 1.2(c)** — 치환 후의 자유 변수. -/
@[exercise "Prop 1.2c" 2]
theorem fv_subst_intExp (e : IntExp V) (δ : Subst V) :
    (e /ₑ δ).fv = e.fv.biUnion fun w => (δ w).fv

@[exercise "Prop 1.2b-assert" 3]
theorem subst_var_assert [HasFresh V] (p : Assert V) : p /ₛ IntExp.var = p
```

### 명제 1.3 — 치환 정리 (Substitution Theorem)

```lean
/--
**명제 1.3 (치환 정리, substitution theorem)**

`FV(p)`의 모든 `w`에서 `σ w = ⟦δ w⟧ σ'`이면,
`σ'`에서 `p /ₛ δ`를 평가한 결과와 `σ`에서 `p`를 평가한 결과가 같다.

**구문적 치환과 의미적 상태 변경이 대응한다**는 것이 요점이다.
"δ로 치환한 뒤 σ'에서 평가"하는 것과 "δ를 σ'에서 평가해 만든 상태 σ에서 평가"하는 것이 같다.

증명의 까다로운 부분은 양화사 케이스다. Reynolds의 논증을 따라가면:
`σ[v := n] w = ⟦δ[v := .var vnew] w⟧ (σ'[vnew := n])` 이 `FV(q)` 전체에서 성립함을 먼저 보이고
(w = v 일 때와 w ∈ FV(q)\{v} 일 때를 나눈다. 후자에서 `vnew ∉ FV(δw)`가 결정적이다),
그 다음 귀납 가설을 쓴다.
-/
@[exercise "Prop 1.3-assert" 3]
theorem substitution_assert [DecidableEq V] [HasFresh V]
    {p : Assert V} {δ : Subst V} {σ σ' : State V}
    (h : ∀ w ∈ p.fv, σ w = (δ w).eval σ') :
    ((p /ₛ δ).eval σ' ↔ p.eval σ)
```

### 명제 1.4 — 한 변수 치환 따름정리

```lean
/-- **명제 1.4** — 명제 1.3에서 얻는 한 변수 치환 정리. -/
theorem substitution_single [HasFresh V]
    (p : Assert V) (v : V) (e : IntExp V) (σ : State V) :
    (⟦p /[v := e] ⟧ₐ σ ↔ ⟦p⟧ₐ (σ[v := ⟦e⟧ₑ σ]))
```

### 명제 1.5 — 이름 바꾸기 정리 (α-변환)

```lean
/--
**명제 1.5 (이름 바꾸기 정리, renaming theorem)**

`vnew ∉ FV(q) \ {v}` 이면 `⟦∀vnew. (q /[v := var vnew])⟧ = ⟦∀v. q⟧`.

**결합 변수의 이름은 뜻에 영향을 주지 않는다.** λ-계산법에서 α-변환(alpha conversion)이라
부르는 것이다.

Reynolds는 이 성질이 잘 작동하는 결합을 가진 언어에 적용되지만 예외도 있다고 덧붙인다.
§11.7의 동적 결합(dynamic binding)이 그 예외다.
-/
theorem renaming_assert …
```

### 마무리: 공리꼴 (1.13)의 타당성

```lean
/-- Reynolds §1.4가 명제 1.4의 응용으로 드는 공리꼴 `(∀v. p) ⇒ p /[v := e]`는 타당하다. -/
theorem valid_instAll : Valid (.bin .imp (.quant .all v p) (p /[v := e]))
```

### 고차 추상 구문에 대한 각주

Reynolds는 §1.4 끝에서 결합 변수 이름을 구체 구문에만 남기고 α-동치인 표기들을 같은
추상 구의 표현으로 보는 관점을 고차 추상 구문(higher-order abstract syntax)이라고 부른다.
현대 용례의 HOAS는 메타언어의 함수와 결합자로 객체언어의 결합을 나타내는 더 구체적인
기법을 가리킨다. Verso 문서는 이 차이를 설명하고, de Bruijn 색인과 locally nameless
접근은 CSlib의 `Cslib/Languages/LambdaCalculus/LocallyNameless/*`를 가리킨다.
이 장에서는 어느 방식도 새로 구현하지 않는다.

→ `manual/Manual/Ch01.lean` 의 "곁가지 — 이름을 어떻게 다룰 것인가" 절에 있다.
§11.7 동적 결합 예고는 "곁가지 — 이름 바꾸기가 깨지는 언어" 절에 있다.

CSlib 의존성 소스의
`.lake/packages/cslib/Cslib/Languages/LambdaCalculus/LocallyNameless/Untyped/Basic.lean`에
locally nameless 구현이 있다. 우리의 이름 있는(named) 치환과 나란히 비교할 수 있다.

---

## 연습문제 매핑

| 책 | 형태 | 별점 | 비고 |
|---|---|---|---|
| **1.0** (자체 추가) | `num : Int` → `num : Nat` + `neg` 로 바꿔도 명제들이 그대로인지 | ★ | §1.1 "책과의 차이 2" 확인 |
| **1.1** (a)~(d) | DSL로 단언을 작성하고, **그 뜻이 의도와 같음을 정리로 증명** | ★★ | 예: `⟦p⟧ σ ↔ ∃! n, 0 < n ∧ n < 2`. 정답 검증이 기계화된다 |
| **1.2** (a)~(d) | 약수·공약수·최대공약수·소수를 `÷`, `rem` 없이 작성 + 뜻 증명 | ★★ | 자연수 범위 가정 |
| **1.3** | 괄호 없는 접두 구문 세계와 생성자, 표기 단사성 | ★★★ | `toPrefix_prefixFree`를 일반화해 `toPrefix_injective`를 증명 |
| **1.4** (a)~(c) | 동시 치환 계산 | ★ | `#guard (p /ₛ δ) = 기대값` — `DecidableEq`로 **자동 채점** |
| **1.5** (a)~(d) | 합 식 `Σ v : e₀ to e₁. e₂` 추가. (a) 문법 (b) 의미 (c) FV·치환 (d) **추론 규칙** | ★★★ | 자족 파일 `Ex/Summation.lean` 에 축소판 언어 `SExp` 로. 채점은 일치 정리와 규칙 넷 |
| **1.6** | 부정 합 `Σv. e` 의 문제점 논의. `v` 가 묶이면서 동시에 상계로 자유롭다 | ★★★ | 같은 파일. 이름 바꾸기 정리가 깨지는 반례를 증명한다 |
| **1.7** (a)(b) | 치환 합성 법칙 | ★★★ | `vo = vl` 특수 케이스 주의 (책 힌트) |

1.1과 1.2의 “술어 논리로 표현하라”는 문제는 식만으로 자동 채점하기 어렵다.
Lean에서는 작성한 단언의 의미가 의도한 메타 수준 명제와 동치임을 함께 증명해,
식의 의미까지 기계적으로 검사한다.

---

## 이 장에서 학습자가 얻는 것

1. `inductive`가 곧 추상 구문이고, Reynolds의 조건들이 공짜라는 것
2. 합성적(compositional) 의미 함수 = 구조적 재귀 = 초기 대수의 유일 준동형
3. 구조적 귀납법의 감각, 특히 **결합 케이스에서 귀납 가설을 일반화해야 한다**는 것
4. 단언과 불 식에서 `Prop`/`Bool` 선택이 계산 가능성의 경계를 어떻게 드러내는지
5. 변수 포획이 왜 실제 문제인지 (Reynolds의 반례를 Lean에서 직접 재현)
6. 추론(inference)과 함의(⇒)의 차이 — 형식 체계를 다룰 때 가장 흔한 오해
