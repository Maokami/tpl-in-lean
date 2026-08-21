# 심화 트랙 (Depth Track) — 설계

> 1·2장에 **보편 대수(universal algebra) · 초기 대수 의미론 · 모나드 · 범주론**을 얹는다.
> 목표는 "범주론도 배우기"가 아니라, **Reynolds가 이미 말하고 있는 것을 이름 붙여 주기**다.

작성일: 2026-08-21 · 상태: 설계안

---

## 0. 왜 이게 억지가 아닌가

Reynolds는 세 곳에서 **직접 손가락으로 가리킨다.**

| 책 | 그가 쓴 문장 | 그가 말하지 않은 이름 |
|---|---|---|
| §1.1 | *"the reader who is familiar with universal algebra will recognize that these conditions insure that abstract phrases form a many-sorted **initial algebra** whose operators are the constructors"* | 초기 대수 의미론 |
| §1.4 Prop 1.2(b) | *"the constructor `c_var` … **acts as an identity substitution**"* | 모나드 우단위 법칙 |
| §2.4 끝 | *"such a definition gives a family of carriers that is the **least solution** of the equations"* (추상 문법 = `𝒫(P)ⁿ`의 최소 고정점) | 구문 반송자의 최소 고정점 구성과 초기 대수의 연결 |

그리고 §1.4에서 `FV`를 정의한 뒤 이렇게 쓴다:

> *"they are (as the reader may verify) syntax-directed, and thus they **define the functions
> FV uniquely**."*

**왜 유일한가?** Reynolds는 답하지 않는다. 심화 트랙이 답하는 첫 질문이 이것이다.

---

## 1. 세 가지 설계 원칙

### 원칙 1 — Reynolds가 가리킨 곳에만 붙인다

심화 파일은 반드시 **책의 특정 문장에 앵커**된다. 파일 상단 배너에 그 문장을 인용한다.
그러면 "범주론을 갖다 붙였다"가 아니라 **"그가 가리킨 방향으로 한 걸음 더 갔다"** 가 된다.

임의로 좋아 보이는 수학은 넣지 않는다. 가리키는 문장이 없으면 그 주제는 심화 트랙에 없다.

### 원칙 2 — 추상은 집세를 내야 한다

각 심화 파일은 **본문에서 이미 신경 쓰던 것**을 되돌려줘야 한다. 추상 자체가 목적이면 뺀다.

| 심화 | 집세 |
|---|---|
| 대수와 초기성 | Reynolds의 *"define the functions uniquely"* 주장을 **증명**한다 |
| 항 모나드 | Prop 1.2(b) + 연습 1.7이 모나드 법칙과 같은 모양임을 보인다 |
| 시그니처 함자 | 구문의 초기 대수, Lambek 동형, 최소 고정점 구성을 구분하고 연결한다 |
| 리프팅 모나드 | 명제 2.4 (a)~(e) 전부 + `;`의 결합성이 **공짜로** 따라온다 |
| CPO 범주 | 명제 2.2·2.3이 "이 범주에 곱과 지수가 있다"의 사례임을 보인다 |

### 원칙 3 — 구체 → 패턴 → 이름

추상 이름을 먼저 던지지 않는다. **항상** 이미 쓴 코드 두셋을 나란히 놓고,
"같은 모양이다" → "이 모양에 이름이 있다" 순서로 간다.

```
❌ "Σ-대수란 반송자와 연산의 족이며 …"
✅ "eval, fv, toPrefix 를 나란히 놓아 보자. 셋 다 생성자마다 규칙 하나,
    재귀는 부분구에만. …이 모양에 이름이 있다."
```

---

## 2. 두 개의 층

심화 트랙 안에서도 진입 장벽이 다르다. **A / B로 나눈다.**

| 층 | 대상 | 사전 지식 | 어휘 |
|---|---|---|---|
| **심화 A** | 스터디 전원에게 권함 | 해당 절 본문만 | 범주론 어휘 **없이** 씀. "대수", "접기(fold)", "유일함" |
| **심화 B** | 범주론에 관심 있는 사람 | A + 범주 개념 | `Category`, `IsInitial`, 함자, 자연 변환, CCC |

**A는 B 없이 완결된다.** B는 A에서 한 말을 범주 어휘로 다시 말하고, Mathlib·CSlib의
기성 추상과 연결한다.

---

## 3. 파일 배치와 배너 규약

```
Reynolds/Answers/Ch01/Depth/
├── Algebra.lean            # A — 대수, fold, 초기성(∃!)
├── TermMonad.lean          # A — 치환 = bind, 모나드 법칙, α 문제
├── SignatureFunctor.lean   # B — 시그니처 함자, Lambek, CSlib FreeM 과의 동형
└── AlgebraCategory.lean    # B — Mathlib Category 인스턴스, IsInitial

Reynolds/Answers/Ch02/Depth/
├── LiftingMonad.lean       # A — (-)⊥ = Option 모나드, 명제 2.4, ; 의 결합성
├── CpoCategory.lean        # B — ωCPO 의 곱·지수, 명제 2.2·2.3
└── FixpointAlgebraically.lean # B — 구문의 초기 사슬과 도메인 최소 고정점 비교
```

`Depth/` 하위에 두는 이유: 본문 파일 목록이 책의 절과 1:1로 깨끗하게 유지된다.
이름만 봐도 선택 사항임이 드러난다.

**모든 심화 파일은 이 배너로 시작한다** (AGENTS.md 규약으로 넣는다):

```lean
/-!
# 심화 A · 대수와 초기성 — 의미론이 왜 유일한가

> **선택 파일이다.** 책을 따라가는 데 필요하지 않다. 본문만 읽어도 1장은 완결된다.

## 책의 어디서 시작하나
Reynolds §1.1, 추상 구문 조건을 나열한 직후:
> *"…abstract phrases form a many-sorted initial algebra whose operators are the constructors."*

## 무엇이 되돌아오나
§1.4에서 Reynolds는 FV 방정식이 *"define the functions FV uniquely"* 라고 쓰지만
왜 유일한지는 말하지 않는다. 이 파일이 그 답이다.

## 사전 지식
없음. §1.1–1.2 만 읽었으면 된다.

## 읽는 순서
`Ch01/Syntax.lean` → `Ch01/Semantics.lean` → 이 파일 → `Depth/TermMonad.lean`
-/
```

**연습 id 규약**: `@[exercise "심화 A1.2" 3]`, `@[exercise "심화 B2.1" 3]`.
`grade` 표에서 바로 구분되고, `check-anchors.sh`의 중복 검사도 그대로 걸린다.

---

## 4. 1장 심화 — 상세

### 4.1 `Depth/Algebra.lean` (A) — 대수와 초기성

**흐름**

1. **관찰.** `IntExp.eval`, `IntExp.fv`, `IntExp.toPrefix` 를 나란히 놓는다.
   생성자마다 절 하나, 재귀는 부분구에만. **셋 다 같은 모양이다.**

2. **이름 붙이기.** 그 "모양"을 데이터로 만든다.
   ```lean
   /-- `IntExp` 의 **대수(algebra)** — 생성자마다 연산 하나를 가진 타입. -/
   structure IntExpAlg (V : Type u) where
     Carrier : Type v
     num : Int → Carrier
     var : V → Carrier
     neg : Carrier → Carrier
     bin : IntOp → Carrier → Carrier → Carrier
   ```
   `IntExp V` 자신이 대수다 (생성자를 연산으로 삼으면 된다). 그것이 **항 대수(term algebra)**.

3. **접기(fold).**
   ```lean
   def IntExpAlg.fold (A : IntExpAlg V) : IntExp V → A.Carrier
     | .num n        => A.num n
     | .var v        => A.var v
     | .neg e        => A.neg (A.fold e)
     | .bin op e₀ e₁ => A.bin op (A.fold e₀) (A.fold e₁)
   ```

4. **준동형(homomorphism).** "구조를 보존하는 함수".
   ```lean
   structure IsHom (A : IntExpAlg V) (h : IntExp V → A.Carrier) : Prop where
     num : ∀ n, h (.num n) = A.num n
     var : ∀ v, h (.var v) = A.var v
     neg : ∀ e, h (.neg e) = A.neg (h e)
     bin : ∀ op e₀ e₁, h (.bin op e₀ e₁) = A.bin op (h e₀) (h e₁)
   ```
   **`IsHom` 의 각 절이 곧 "의미 방정식" 한 줄이다.** 이 대응이 이 파일의 핵심.

5. **★ 초기성(initiality).**
   ```lean
   theorem IntExp.initial (A : IntExpAlg V) : ∃! h : IntExp V → A.Carrier, IsHom A h
   ```
   존재 = `fold`. **유일성 = 구조적 귀납법.**
   이것이 "항 대수는 모든 대수로 가는 유일한 준동형을 갖는다" = **초기 대수**다.

6. **집세 1 — 셋이 전부 fold다.**
   ```lean
   theorem eval_eq_fold : ∀ e : IntExp V, ⟦e⟧ₑ = evalAlg.fold e
   theorem fv_eq_fold   : ∀ e : IntExp V, e.fv = fvAlg.fold e
   ```
   `eval` 의 반송자가 `State V → Int` 라는 점이 중요하다 — **뜻은 값이 아니라 함수**라는
   §1.2의 논점이 여기서 "어떤 대수를 골랐는가"로 다시 나타난다.

7. **★ 집세 2 — Reynolds의 "uniquely"를 증명한다.**
   ```lean
   /-- 의미 방정식을 만족하는 함수는 `eval` 하나뿐이다. -/
   theorem eval_unique (f : IntExp V → State V → Int)
       (hnum : ∀ n σ, f (.num n) σ = n)
       (hvar : ∀ v σ, f (.var v) σ = σ v)
       (hneg : ∀ e σ, f (.neg e) σ = -(f e σ))
       (hbin : ∀ op e₀ e₁ σ, f (.bin op e₀ e₁) σ = op.denote (f e₀ σ) (f e₁ σ)) :
       f = IntExp.eval
   ```
   **이것이 "표시적 의미론이 잘 정의된다"의 정확한 내용이다.**
   2장에서 `while` 의 풀기 방정식이 **유일한 해를 갖지 않는** 것과 정면으로 대조된다.
   → 2장을 여는 가장 좋은 다리.

8. **두 정렬(two-sorted).** `Assert` 는 `IntExp` 를 참조하므로 반송자가 둘이다.
   `LogicAlg` 를 같은 방식으로 만들어 보이고, Reynolds의 "many-sorted"가 무슨 뜻인지 확인.
   (일반적인 다중 정렬 시그니처 프레임워크는 만들지 않는다 — 비용 대비 효용이 낮다.
   구체적으로 두 번 보이면 패턴은 전달된다.)

**연습**
| id | 내용 | ★ |
|---|---|---|
| 심화 A1.1 | `fold` 를 정의하고 `IsHom A (A.fold)` 를 증명하라 | ★ |
| 심화 A1.2 | 초기성의 **유일성** 부분을 증명하라 | ★★ |
| 심화 A1.3 | `toPrefix` 를 대수로 만들고 fold 임을 보여라 | ★★ |
| 심화 A1.4 | `eval_unique` 를 초기성만 써서 증명하라 (귀납법을 다시 쓰지 말 것) | ★★★ |

---

### 4.2 `Depth/TermMonad.lean` (A) — 치환과 bind

**이 파일이 심화 트랙 전체의 하이라이트다.**

**관찰.** Reynolds는 Prop 1.2(b)를 이렇게 주석한다:

> *"Note that part (b) of this proposition asserts that the constructor `c_var`, which injects
> variables into the corresponding integer expressions, **acts as an identity substitution**."*

고정된 변수 타입에서 이 진술은 모나드의 우단위 법칙과 같은 모양이다.

**대응표** — 다형적 치환 `IntExp V → (V → IntExp W) → IntExp W`까지 일반화하면
`V ↦ IntExp V`가 모나드를 이룬다. 현재 파일은 `V = W`인 경우의 법칙을 증명한다.

| Reynolds | 모나드 |
|---|---|
| `c_var : ⟨var⟩ → ⟨intexp⟩` | `pure` |
| `p / δ` (치환) | `p >>= δ` |
| **Prop 1.2(b)** `p / c_var = p` | **우단위** `m >>= pure = m` |
| `(c_var v) / δ = δ v` (정의로 성립) | **좌단위** `pure v >>= f = f v` |
| **연습 1.7(a)** `δ''w = (δw)/δ'` ⟹ `p/δ''` 는 `(p/δ)/δ'` 의 이름 바꾸기 | **결합법칙** `(m >>= f) >>= g = m >>= (f >=> g)` |
| Prop 1.3 (치환 정리) | 단언의 치환과 평가 뒤 상태 재색인이 호환됨 |

가군(module) 비유를 쓰려면 작용의 주체를 구분해야 한다. 작용을 받는 것은 `Assert` 구문이고,
`eval`은 그 치환 작용을 상태 재색인으로 보내는 호환 사상으로 읽는다. 현재 파일은 이 호환성을
명제 1.3으로 증명할 뿐, 가군 구조 자체를 Lean 클래스로 만들지는 않는다.

**★ 여기서 진짜 깊은 것이 나온다 — 연습 1.7은 "같다"가 아니라 "이름 바꾸기다"**

Reynolds의 진술을 다시 보라: *"`p/δ''` **is a renaming of** `(p/δ)/δ'`"*. **등호가 아니다.**

- `IntExp` 에는 결합자가 없다 → 모나드 법칙이 **그대로(on the nose)** 성립한다.
- `Assert` 에는 `∀v` 가 있다 → 포획 회피를 위해 새 이름을 뽑으므로 **α-동치까지만** 성립한다.

현재의 이름 있는 표현에서는 결합 변수 이름의 차이 때문에 보통 등식으로 모나드 법칙을
말하기 어렵다. α-동치로 나눈 몫, de Bruijn 색인, locally nameless, 준층 위 구문처럼
이름 차이를 표현에서 처리하는 방법이 여기서 필요해진다.

Reynolds가 §1.4 끝에서 **고차 추상 구문(higher-order abstract syntax)**을 언급하는 것도
결합 변수의 이름을 추상 구문의 본질로 보지 않는 이 문제와 이어진다.

**구성**
1. 고정된 `V`에서 `pure := .var`, `bind := subst` 역할을 하는 치환 법칙 세 개를 증명한다.
2. `Monad IntExp` 인스턴스는 만들지 않는다. 실제 인스턴스에는 변수 타입을 바꾸는 다형적
   `bind`와 universe 정리가 필요하다. 현재 학습 목표에는 명시적 정리가 더 읽기 쉽다.
3. `Assert V → Subst V → Assert V`는 현재의 이름 있는 표현에서는 **가군 작용의 후보**다.
   법칙이 등호가 아니라 `=α`까지만 성립함을 반례와 함께 보인다.
4. CSlib `HasAlphaEquiv` 로 `=α` 를 정의하고, 몫에서 법칙이 그대로 성립함을 ★★★ 연습으로.
5. 참고문헌: Fiore–Plotkin–Turi, *Abstract Syntax with Variable Binding* (LICS 1999) —
   원시 이름 구문은 `Type` 위 초기 대수로 둘 수 있다. 문맥 확장, α-동치, 포획 회피
   치환까지 구조에 담을 때는 **준층(presheaf)**이 표준적인 방법 중 하나다.

**연습**
| id | 내용 | ★ |
|---|---|---|
| 심화 A2.1 | `IntExp` 의 좌단위·우단위 법칙 | ★★ |
| 심화 A2.2 | `IntExp` 의 결합법칙 (= 연습 1.7(a)의 결합자 없는 판) | ★★★ |
| 심화 A2.3 | `Assert` 에서 결합법칙이 등호로는 깨지는 **반례**를 만들어라 | ★★ |
| 심화 A2.4 | `Assert` 판을 `=α` 로 진술하고 증명하라 | ★★★ |

---

### 4.3 `Depth/SignatureFunctor.lean` (B) — 함자와 Lambek

**시그니처를 함자로.**
```lean
/-- 시그니처 함자. `F X` = "생성자 한 겹, 자식 자리는 X". -/
inductive Sig (V : Type u) (X : Type v) where
  | num : Int → Sig V X
  | var : V → Sig V X
  | neg : X → Sig V X
  | bin : IntOp → X → X → Sig V X
```

**Lambek 보조정리** — 초기 대수의 구조 사상은 **동형**이다.
```lean
def IntExp.unfold : IntExp V → Sig V (IntExp V)
def IntExp.roll   : Sig V (IntExp V) → IntExp V
theorem IntExp.lambek : Function.Bijective (IntExp.roll (V := V))
-- 또는 `IntExp V ≃ Sig V (IntExp V)`
```

**이것이 2장으로 가는 다리다.** Lambek 보조정리는 초기 대수의 구조 사상이 동형임을 말한다.
Reynolds가 §2.4 끝에서 주는 `𝒫(P)ⁿ` 위 최소 고정점 구성은 같은 구문 반송자를 만드는 다른
설명이다. 명령 의미의 함수 도메인에서 `Y`가 고르는 최소 고정점과는 구분해야 한다.

**CSlib 자유 모나드와의 동형.**
CSlib `Cslib/Foundations/Data/PFunctor/Free.lean` 의 `PFunctor.FreeM P α` 는
"다항 함자 `P` 위의 자유 모나드"다. 적절한 다항 시그니처를 고르면 `IntExp V`와의 동형을
기대할 수 있고, 실제 동형을 세우는 일은 연습으로 남긴다:

```lean
/-- 우리 시그니처를 다항 함자로. -/
def sigP : PFunctor := ⟨Op, arity⟩   -- Op = num n | neg | bin op,  arity = Empty | Unit | Bool

/-- `IntExp V ≃ sigP.FreeM V`. 이 동형 아래에서
    `pure = .var` 이고 `bind = 치환` 이다. -/
def IntExp.equivFreeM : IntExp V ≃ sigP.FreeM V
```

CSlib의 `Interprets.iff`는 효과 handler를 확장하는 모나드 interpreter의 유일성을 말한다.
`Depth/Algebra.lean`의 초기성은 고정된 `V`에서 임의의 `IntExpAlg V`로 가는 대수 준동형의
유일성을 말하므로, 그대로 같은 정리는 아니다. CSlib 문서는 전자의 보편 성질을 이렇게 부른다:

> *"The universal property of the free monad. That is, `liftM handler` is the **unique**
> interpreter that extends the effect handler."*

둘을 연결하려면 모든 변수 타입에 자연적인 동형을 세우고, 그 동형이 `pure`, `bind`, 생성자를
보존함을 증명해야 한다. 고정된 `V` 하나의 타입 동형만으로 `LawfulMonad` 구조를 옮길 수는 없다.
아래 연습은 타입 동형에서 시작해 이 호환성 증명으로 나아가는 순서다.

**연습**
| id | 내용 | ★ |
|---|---|---|
| 심화 B1.1 | Lambek 동형을 구성하고 양쪽 합성이 항등임을 보여라 | ★★ |
| 심화 B1.2 | `IntExp V ≃ sigP.FreeM V` 를 세워라 | ★★★ |
| 심화 B1.3 | 그 동형 아래 `bind` 가 우리 `subst` 와 일치함을 보여라 | ★★★ |

---

### 4.4 `Depth/AlgebraCategory.lean` (B) — 범주 어휘로 다시 말하기

`∃!` 로 쓴 초기성을 Mathlib 어휘로 옮긴다.

```lean
/-- `IntExp` 의 대수와 준동형이 이루는 범주. -/
instance : Category (IntExpAlg V) where
  Hom A B := { f : A.Carrier → B.Carrier // IsAlgHom A B f }
  id A := ⟨id, …⟩
  comp f g := ⟨g.1 ∘ f.1, …⟩

/-- 항 대수가 초기 대상이다. -/
def termAlgIsInitial : Limits.IsInitial (termAlg V)
```

**왜 굳이 하나**: `∃!` 는 "이 대수 하나에 대해" 유일하다는 말이다.
`IsInitial` 은 그것이 **범주 전체의 구조적 성질**임을 말한다.
그리고 이 어휘가 있어야 2장 `FixpointAlgebraically.lean` 과 5장 재귀 영역 방정식이 이어진다.

산문(Verso)으로만 다룰 것:
- 범주·함자·자연 변환이 무엇인가 (그림 포함)
- 왜 **초기 대수 의미론**이라 부르는가 — 구문은 초기 대상, 의미는 유일 사상
- 왜 **합성적(compositional)** 이 준동형과 같은 말인가

---

## 5. 2장 심화 — 상세

### 5.1 `Depth/LiftingMonad.lean` (A) — `f⊥⊥` 는 bind다

**관찰.** Reynolds가 §2.2에서 도입하는 것:
```
f⊥⊥ x = if x = ⊥ then ⊥ else f x
⟦c₀ ; c₁⟧ σ = (⟦c₁⟧)⊥⊥ (⟦c₀⟧ σ)
```
`Σ⊥ = Option (State V)` 로 두면 `f⊥⊥ = fun x => x >>= f` 다. **순차 합성이 Kleisli 합성이다.**

**대응표**

| Reynolds §2.2–2.3 | 모나드 |
|---|---|
| 리프팅 `(-)⊥` | 모나드 `Option` |
| `ι : P → P⊥` (항등 주입) | `pure` |
| `f⊥ : P⊥ → P'⊥` | `Functor.map` |
| `g⊥⊥ : P⊥ → D` (원천 리프팅) | `bind` (`Option.elim ⊥ g`) |
| **명제 2.4(a)(b)** 유일한 순 확장 | 리프팅의 **보편 성질** |
| **명제 2.4(c)** `(f ∘ e)⊥ = f⊥ ∘ e⊥` | **함자성** |
| **명제 2.4(d)** `(g ∘ f)⊥⊥ = g⊥⊥ ∘ f⊥` | Kleisli 합성 법칙 |
| **명제 2.4(e)** `(h ∘ g)⊥⊥ = h ∘ g⊥⊥` (h가 순) | 순 사상은 bind를 통과 |

**★ 집세가 즉각적이다.** Reynolds는 §2.1에서 이렇게만 말한다:

> *"we will always give this operator an associative semantics where `(c₀ ; c₁) ; c₂` and
> `c₀ ; (c₁ ; c₂)` have the same meaning."*

말만 하고 증명하지 않는다. 우리는 **한 줄로 증명한다** — `Option` 의 `bind_assoc` 이다.

```lean
theorem seq_assoc (c₀ c₁ c₂ : Comm V) :
    ⟦(c₀ ;; c₁) ;; c₂⟧꜀ = ⟦c₀ ;; (c₁ ;; c₂)⟧꜀ := by
  funext σ; simp [Comm.eval, bind_assoc]
```

**Moggi 예고 (산문).** Reynolds의 책(1998)은 각 계산 효과를 따로 구성한다.
Moggi(1991)는 그것들이 전부 모나드임을 보였다. 이 책의 나머지가 그 목록이다:

| 장 | 효과 | 모나드 |
|---|---|---|
| 2 | 비종료 | 리프팅 `(-)⊥` |
| 5 | 출력 | 작가(writer) / 열(sequence) |
| 5 | 입력 | 재개(resumption) |
| 5·12 | 연속체 | 연속체 모나드 `(- → R) → R` |
| 7 | 비결정성 | 멱영역(powerdomain) |
| 13 | 상태 | 상태 모나드 |

**이 표가 스터디 내내 지도가 된다.**

**연습**
| id | 내용 | ★ |
|---|---|---|
| 심화 A3.1 | 명제 2.4 (c)(d)(e)를 `Option` 모나드 법칙으로 증명하라 | ★★ |
| 심화 A3.2 | `;` 의 결합성을 `bind_assoc` 로 증명하라 | ★ |
| 심화 A3.3 | `skip` 이 `;` 의 양쪽 항등원임을 단위 법칙으로 증명하라 | ★ |

---

### 5.2 `Depth/CpoCategory.lean` (B) — 곱과 지수

**Mathlib에 `ωCPO` 범주가 이미 있다** (`Mathlib/Order/Category/OmegaCompletePartialOrder.lean`):
`LargeCategory`, `ConcreteCategory`, `HasProducts`, `HasEqualizers`, `HasLimits`.

**그런데 지수(exponential)는 없다.** 그리고 그게 정확히 **명제 2.2**다.

```lean
/-- 명제 2.2 = 지수 대상. 연속 함수 공간 `P →𝒄 P'` 가 다시 ωCPO 이고,
    이것이 곱에 대한 오른쪽 수반이다. -/
example : (P →𝒄 P') 이 ωCPO 임   -- Mathlib 에 있다
-- 우리가 할 것: 커링 동형
def curry   : (X × Y →𝒄 Z) ≃ (X →𝒄 (Y →𝒄 Z))
```

**왜 CCC가 중요한가 (산문).**
데카르트 닫힌 범주(cartesian closed category)는 **단순 타입 λ-계산법의 모델**이다
(Lambek–Scott). 즉 §2.3에서 Reynolds가 "연속 함수 공간도 프리도메인(predomain)이다"를
증명하는 것은,
**10장 λ-계산법과 15장 타입 체계의 의미론을 미리 준비하는 것**이다.
그는 그렇게 말하지 않지만 사실이 그렇다.

명제 2.3 (상수·항등 연속, 합성이 연속)도 여기서 제자리를 찾는다 —
"이것들이 범주를 이룬다"는 말의 성분들이다.

**정직한 범위 표시**: `CartesianClosed ωCPO` 인스턴스를 완성하는 것은 이 프로젝트의 범위를
넘는다. 커링 동형까지 만들고, 남은 것은 **열린 과제**로 명시한다.

**연습**
| id | 내용 | ★ |
|---|---|---|
| 심화 B3.1 | `X × Y →𝒄 Z` 와 `X →𝒄 (Y →𝒄 Z)` 사이 동형 | ★★★ |
| 심화 B3.2 | 명제 2.3을 "합성이 범주의 사상 합성"으로 다시 읽어라 | ★ |

---

### 5.3 `Depth/FixpointAlgebraically.lean` (B) — 세 고정점 구성을 비교한다

여기서는 구문의 초기 대수, Reynolds의 구문 반송자 최소 고정점 구성, 명령 의미의 최소
고정점을 한 표에 놓되 같은 대상으로 합치지 않는다.

| | 구문의 초기 대수 | 구문 반송자의 최소 고정점 | 명령 의미의 최소 고정점 |
|---|---|---|---|
| 대상 | `IntExp V`와 생성자 | 구를 모은 부분집합들의 튜플 | `State → State⊥` 같은 의미 함수 |
| 무대 | 집합과 함수 | 멱집합 격자와 포함 관계 | 도메인과 근사 순서 |
| 방정식 | `X ≃ F X` | `S = Φ S` | `g = Ψ g` |
| 선택 원리 | 초기성이라는 보편 성질 | 생성자로 닫힌 최소 반송자 | 연속 자기함수의 최소 고정점 |
| 구성 | 초기 사슬의 여극한 | `∅, Φ∅, Φ²∅, …`의 합집합 | `⊥, Ψ⊥, Ψ²⊥, …`의 최소 상계 |
| Lean | `inductive`, Lambek 동형 | 아직 형식화하지 않음 | `lfp`를 직접 정의 |

**Reynolds가 직접 잇는다** (§2.4 끝):

> *"By the least fixed-point theorem, `s` is the least solution of `s = f s`. …
> Of course, this depends on the function `f` being continuous. In fact, the continuity of `f`
> stems from the fact that each `fᵢ` is **finitely generated** …, which in turn stems from the fact
> that **the constructors of the abstract syntax have a finite number of arguments**."*

생성자가 유한 개의 인자를 갖는다는 조건은 Reynolds의 반송자 생성 함수가 필요한 사슬의
합을 보존하게 한다. 범주론에서는 이 연결을 finitary polynomial functor의 초기 사슬로
설명할 수 있다. Lean의 `inductive`는 커널이 별도로 제공하는 기능이다.

**Lean 코드로 확인할 것**: 아주 작은 문법(예: `S ::= ε | a S`)을 두 가지로 만든다.
① `inductive` ② `𝒫(String)` 위의 최소 고정점 `⨆ₙ Fⁿ ∅`.
**둘이 같은 집합임을 증명한다.** 구체적이고, 놀랍고, 두 장을 한 문장으로 잇는다.

**5장 예고 (산문).** 재귀적 영역 방정식 `D ≅ [D → D]` (§5.5)도 재귀적 대상을 구성한다.
다만 `X ↦ [X → X]` 는 **공변이 아니다** — 초기 대수로 다룰 수 없다.
Scott의 해법은 사영 쌍(embedding–projection pair)의 사슬을 따라 **쌍극한(bilimit)** 을 취하는 것.
1장 초기 대수, 2장 최소 고정점, 5장 쌍극한은 모두 재귀적 대상을 구성하지만 사용하는
범주와 보편 성질은 서로 다르다.

**연습**
| id | 내용 | ★ |
|---|---|---|
| 심화 B4.1 | 작은 문법을 `𝒫` 위의 최소 고정점으로 만들고 `inductive` 판과 같음을 보여라 | ★★★ |
| 심화 B4.2 | 생성자가 무한 인자를 가지면 연속성이 깨지는 예를 만들어라 | ★★★ |

---

## 6. 본문에 심는 훅

심화 파일이 존재해도 **본문에서 손짓하지 않으면 아무도 안 읽는다.**
본문에는 **딱 한 줄씩만** 넣는다. 설명하지 않고 가리키기만 한다.

| 위치 | 훅 |
|---|---|
| `Ch01/Syntax.lean` 의 `추상구문조건` 절 끝 | `> Reynolds는 이 조건들이 "다중 정렬 초기 대수"를 이룬다고 각주에 적는다.`<br>`> 그게 무슨 말이고 왜 중요한지는 `Depth/Algebra.lean`. (선택)` |
| `Ch01/Semantics.lean` `eval` docstring 끝 | `> 이 의미 방정식들이 함수를 **유일하게** 정한다는 사실의 증명: `Depth/Algebra.lean`.` |
| `Ch01/Substitution.lean` Prop 1.2(b) 근처 | `> Reynolds는 `c_var` 가 "항등 치환으로 작동한다"고 쓴다.`<br>`> 이것이 모나드 단위 법칙이다: `Depth/TermMonad.lean`.` |
| `Ch02/Semantics.lean` `;` 의미 방정식 | `> `f⊥⊥` 는 `Option` 모나드의 bind 다. `;` 의 결합성이 공짜로 나온다: `Depth/LiftingMonad.lean`.` |
| `Ch02/Domain.lean` 명제 2.2 | `> 이것은 ωCPO 범주의 **지수 대상**이다. 그래서 λ-계산법의 모델이 된다: `Depth/CpoCategory.lean`.` |
| `Ch02/Fixpoint.lean` 끝 | `> 1장의 구문 구성과 이 최소 고정점의 공통점과 차이는 `Depth/FixpointAlgebraically.lean`에서 비교한다.` |

---

## 7. Verso 문서 구성

심화 트랙은 **산문이 특히 중요하다** — 코드만으로는 "왜"가 전달되지 않는다.

```
manual/Manual/
├── Depth.lean            # 심화 트랙 안내 — 무엇을, 왜, 어떤 순서로
├── Depth/Algebra.lean    # 대수 · 준동형 · 초기성 (그림 포함)
├── Depth/Monads.lean     # 치환 = bind, 리프팅 = Option, Moggi 표
├── Depth/Category.lean   # 범주 · 함자 · CCC · 초기 대상
└── ThroughLines.lean     # ★ 관통 주제 — 스터디 내내 참조하는 지도
```

### `ThroughLines.lean` — 책 전체를 꿰는 네 줄기

| 줄기 | 1장 | 2장 | 이후 |
|---|---|---|---|
| **재귀적 구성** | 초기 대수로 보는 추상 구문 | 도메인의 최소 고정점 | 5장 재귀 영역 방정식 |
| **모나드** | 치환 | 리프팅·순차 합성 | 5장 연속체, 7장 멱영역, 13장 상태 |
| **결합(binding)** | 양화사 | `newvar` | 10장 λ, **11.7장 동적 결합의 실패** |
| **관찰과 추상성** | (없음) | 완전 추상성 | 8장 병행성이 깨는 것, 13장 별칭 |

**이 표 하나가 스터디의 뼈대가 된다.** 매 장 시작할 때 "지금 어느 줄기의 어디인가"를 짚는다.

---

## 8. 비용과 단계

| 단계 | 내용 | 선행 |
|---|---|---|
| **D0** | AGENTS 배너 규약 · 훅 삽입 · `ThroughLines` 초안 | 없음 |
| **D1** | `Ch01/Depth/Algebra.lean` (A) | 1장 §1.1–1.2 ✅ |
| **D2** | `Ch01/Depth/TermMonad.lean` (A) | §1.4 치환 (M1 예정) |
| **D3** | `Ch01/Depth/SignatureFunctor.lean` · `AlgebraCategory.lean` (B) | D1 |
| **D4** | `Ch02/Depth/LiftingMonad.lean` (A) | 2장 §2.2 (M2) |
| **D5** | `Ch02/Depth/CpoCategory.lean` · `FixpointAlgebraically.lean` (B) | 2장 §2.3–2.4 (M2) |

**D1은 지금 바로 가능하다.** D2는 §1.4 치환이 들어온 뒤. D4·D5는 2장 본문과 함께.

### 위험과 완화

| 위험 | 완화 |
|---|---|
| 초보자가 심화를 보고 위축된다 | 배너에 "선택이다"를 첫 줄에 못박고, 본문 훅은 한 줄로만. A/B 층 분리 |
| 추상이 본문을 잠식한다 | 원칙 2 (집세). 되돌려주는 것이 없으면 뺀다 |
| 범주론이 목적이 된다 | 원칙 1 (Reynolds가 가리킨 곳에만). 가리키는 문장이 없으면 주제 자체를 뺀다 |
| Lean 비용 폭발 (CCC 인스턴스 등) | 완성 못 하는 것은 **열린 과제로 명시**. 반쯤 한 것을 숨기지 않는다 |
| 스터디 진도가 늦어진다 | 심화는 별도 PR. 본문 PR을 막지 않는다 |

---

## 부록 · 참고문헌 (Verso `citep` 대상)

- Goguen, Thatcher, Wagner, Wright, *Initial Algebra Semantics and Continuous Algebras* (1977)
  — Reynolds가 §1.1·§2.4 참고문헌에서 직접 인용하는 논문이다.
- Burstall, Landin, *Programs and their Proofs: an Algebraic Approach* (1969) — Reynolds가
  "대수와의 연결을 처음 알아챈" 것으로 언급.
- Moggi, *Notions of Computation and Monads* (1991)
- Fiore, Plotkin, Turi, *Abstract Syntax with Variable Binding* (1999)
- Lambek, Scott, *Introduction to Higher Order Categorical Logic* (1986) — CCC와 λ-계산법
- Pfenning, Elliott, *Higher-Order Abstract Syntax* (1988) — Reynolds §1.4 참고문헌
- Scott, *Continuous Lattices* (1972), *Data Types as Lattices* (1976)
