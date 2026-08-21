# AGENTS.md — `tpl-in-lean` 작업 규약

이 문서는 이 저장소에서 코드를 쓰는 **모든 주체**(사람 기여자, AI 코딩 에이전트)에게 적용된다.
`CLAUDE.md`, `.cursorrules` 등이 따로 있어도 이 파일이 우선이다.

---

## 0. 이 프로젝트가 무엇인가

John C. Reynolds, *Theories of Programming Languages* (Cambridge University Press, 1998)를
Lean 4로 따라 읽는 **스터디용 실습 저장소**다.

독자는 **프로그래밍 언어 이론과 Lean을 처음 접하는 실무 개발자**다.
범주론·도메인 이론·형식 의미론에 대한 사전 지식을 가정하지 않는다.

따라서 이 저장소의 성공 기준은 "정리가 증명됐다"가 아니라
**"동료가 파일만 읽고 그 절을 이해했다"** 이다. 모든 규칙이 여기서 나온다.

전체 설계는 [`DESIGN.md`](./DESIGN.md)를 먼저 읽어라.

---

## 1. 절대 규칙 (위반 시 PR 반려)

1. **`Reynolds/Answers/**` 에 `sorry`가 있으면 안 된다.** CI가 막는다.
2. **`Reynolds/Exercises/**` 의 연습 지점은 `sorry`여야 한다.** 정답을 흘리지 마라.
3. **`native_decide` 금지.** 커널 밖에서 참을 만들어낸다. `decide`, `omega`, `grind`를 써라.
4. **새 `axiom` 선언 금지.** 허용 공리는 `Classical.choice`, `Quot.sound`, `propext`, `funext` 뿐이다.
5. **모든 공개 선언에 docstring을 단다.** `linter.missingDocs`가 빌드를 실패시킨다.
6. **책 본문을 옮겨 적지 마라.** 저작권 문제다. 요약·해설·코드만 쓴다.
   책의 문장이 필요하면 짧게 인용하고 절·페이지를 밝힌다.
7. **Mathlib 정리 이름을 추측하지 마라.** 반드시 `exact?` / `apply?` / `loogle` / 실제 소스로
   확인하고 쓴다. 존재하지 않는 이름을 적은 채 "아마 이럴 것"이라고 넘기지 않는다.
8. **`Exercises/ChNN`은 `Answers/Ch(NN-1)`을 import한다.** `Exercises/Ch(NN-1)`이 아니다.
   (이유: 장별 독립 학습 + `sorry` 전파로 인한 채점 오염 방지. `DESIGN.md` §3.1)
9. **연습 독립성 원칙** — 모든 `@[exercise]` 선언은 **주어진 완성 자료만으로 풀 수 있어야 한다.**
   한 연습이 다른 연습의 결과를 필요로 하면, 그 결과를 `ChNN/Given.lean`에 완성본으로 주거나
   진술의 가설로 넣어라. (이유: Lean은 다른 모듈의 증명 항을 볼 수 없어서 "본인 sorry"와
   "선행 미완성"을 구분할 수 없다. `DESIGN.md` §5.2)
10. **코드 패키지의 모든 `.lean` 파일은 모듈 시스템을 쓴다.** `module`로 시작한다.
    대상은 `Reynolds/**`, `ReynoldsTests/**`, `Grade.lean`, `Reynolds.lean`, `ReynoldsTests.lean`.
    **혼용은 불가능하다** — 모듈 파일은 비-모듈 파일을 import할 수 없어서 루트 모듈에서 터진다.

    **예외: `manual/` 패키지.** 별도 Lake 패키지이고 Verso 관례를 따른다
    (Verso 템플릿의 문서 파일에는 `module` 이 없다). 모듈 시스템을 강제한 이유는
    Mathlib·CSlib 와의 상호운용인데 `manual/` 은 그 둘에 의존하지 않는다.

---

## 1.5 모듈 시스템 — 5분 요약

이 프로젝트의 모든 파일은 이렇게 시작한다.

```lean
/-
Copyright (c) 2026 <이름>. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: <이름>
-/
module

public import Reynolds.Init
public import Mathlib.Data.Finset.Union

/-! # §1.4 결합과 치환 … (모듈 docstring) -/

@[expose] public section

-- 여기부터 내용

end
```

| 키워드 | 뜻 | 언제 |
|---|---|---|
| `module` | 이 파일을 모듈 시스템으로 다룬다 | **모든 파일 첫 줄** |
| `import X` | X를 이 파일 안에서만 쓴다 (downstream에 전파 안 됨) | 구현 세부에만 필요할 때 |
| `public import X` | X를 downstream에도 전파한다 | **기본값으로 이걸 쓴다** |
| `meta import X` | 엘라보레이션 시점에만 필요 (매크로·태틱) | `Lean.Elab` 등 |
| `public meta import X` | 위 둘 다 | `meta` 선언을 downstream에서 쓸 때 |
| `public section … end` | 이 구간의 선언을 downstream에 공개 | 거의 항상 |
| `@[expose] public section` | 공개 + **정의의 본문**까지 공개 | `#guard`/`decide`가 환원되어야 하는 파일 (구문·의미 파일 전부) |
| `meta section … end` | 메타프로그래밍 구간 | 애트리뷰트·매크로 선언 |

**실전 규칙 3가지** (전부 실측으로 확인된 함정이다)

1. `decide`·`#guard`가 downstream에서 동작해야 하면 **`@[expose] public section`** 을 쓴다.
   그냥 `public section`이면 정의가 불투명(opaque)해져 환원되지 않는다.
2. `initialize`로 만든 환경 확장은 **같은 모듈에서 쓸 수 없다.** 선언 모듈과 사용 모듈을 나눠라.
   그리고 `public initialize`로 명시해야 downstream에서 보인다.
3. 막히면 **Lean의 오류 메시지를 읽어라.** 모듈 시스템 오류는 대개 고치는 법을 직접 알려준다:
   `consider adding 'public meta import Foo'`

---

## 2. 주석과 문서 — 이 프로젝트의 본체

> 코드는 **무엇**을 하는지 말한다. 주석은 **왜** 그렇게 했는지, 그리고 **책의 어디**인지 말한다.

### 2.1 언어

- **한국어로 쓴다.**
- 기술 용어는 **첫 등장 시에만** `한글(English)` 형태로 병기한다.
  - ✅ `표시적 의미론(denotational semantics)`, `최소 고정점(least fixed point)`, `자유 변수(free variable)`
  - ✅ 두 번째 등장부터는 `표시적 의미론`
  - ❌ 매번 병기 (읽는 흐름이 끊긴다)
- 관용적으로 원어가 더 통하는 것은 원어를 쓴다: `람다 계산법`보다 `λ-calculus`가 나으면 그쪽으로.
  판단 기준은 **스터디 참가자가 검색할 때 쓸 단어**다.
- Lean 식별자·태틱·타입 이름은 번역하지 않는다: `Finset`, `induction`, `omega`.
- 맞춤법과 띄어쓰기를 지킨다. 문장은 `~다`로 끝낸다 (`~습니다` 아님).

### 2.1.1 피해야 할 문체 (실제로 지적받은 것들)

주석이 "AI가 쓴 것처럼" 읽히는 데는 몇 가지 반복 패턴이 있다.
금지어 목록이 아니라 **글 전체에서 같은 장치가 자동으로 반복되는지**를 본다.

| 패턴 | 증상 | 고치는 법 |
|---|---|---|
| 거대한 도입 | "이 파일이 그 답이다", "1장에서 가장 중요한 교훈이다" | 중요성을 선언하지 말고 그냥 내용을 쓴다 |
| 자동 대조문 | "A가 아니다. B다." 가 절마다 등장 | 버려야 할 오해가 실제로 있을 때만 대조한다 |
| 장식적 형용사 | 근거 없는 "핵심", "결정적", "우아한", "강력한" | 무엇이 무엇을 계산·보존·구분하는지 쓴다 |
| 수사 질문 후 즉답 | "왜 유일한가?" 하고 바로 답함 | 서술로 바꾼다. 진짜 열린 질문만 남긴다 |
| 절 끝 요약 | "## 정리", "기억할 것은 하나다" | 이미 말한 것을 다시 말하지 않는다 |
| 균일한 리듬 | 모든 절이 같은 순서·같은 길이 | 절의 기능에 따라 길이와 구조를 바꾼다 |
| 복선 회수 남발 | 같은 예고를 여러 파일에서 반복 | 가장 결정적인 한 곳에서만 연결한다 |
| 볼드·기호 남용 | `**...**` 와 `★` 가 문단마다 | 대비가 정말 필요한 곳만. `★` 는 별점에만 쓴다 |
| 명령조 남발 | "~보라", "~주목할 것", "~눈여겨보라" | 서술로 바꾼다 |

**목표 목소리**: 한 단계 먼저 헤매 본 동료가 옆에서 설명하는 톤.
가르치려 들지 않고, 판단의 근거와 범위와 한계를 솔직하게 밝힌다.
자신감은 형용사가 아니라 정확한 범위와 검증 가능한 서술에서 나온다.

**고쳐 쓴 예**

```
✗  **왜 유일한가?** 그는 답하지 않는다. 이 파일이 그 답이다.
   그리고 그 답이 `eval`, `fv` 가 **하나의 구성**임을 보여 준다.

✓  구문 지향이면 왜 유일해지는지는 설명하지 않는다. 여기서 그 이유를 따라간다.
   따라가다 보면 `eval` 과 `fv` 가 같은 구성의 두 사례라는 것도 같이 나온다.
```

### 2.2 3층 구조

#### (a) 모듈 docstring — 파일 최상단 `/-! … -/`

**반드시** 다음을 포함한다:

```lean
/-!
# §1.4 결합과 치환 (Binding and Substitution)

Reynolds §1.4에 대응한다.

## 이 파일에서 다루는 것
- 자유 변수(free variable) 함수 `FV`
- 치환(substitution) `p / δ` 와 변수 포획(capture) 회피
- 명제 1.1 일치 정리, 1.3 치환 정리, 1.5 이름 바꾸기 정리

## 핵심 아이디어
∀v. p 에서 v 는 결합 발생(binding occurrence)이다. p 안에서 e 를 v 자리에
그냥 밀어 넣으면, e 의 자유 변수가 v 의 결합자에 **포획**되어 뜻이 바뀐다.
    (∀x. ∃y. y > x)  ⇒  (∃y. y > x) / x ↦ y+1
왼쪽은 항상 참인데, 순진하게 치환하면 오른쪽은 `∃y. y > y+1` — 항상 거짓.
그래서 치환은 결합 변수를 먼저 **새 이름으로 바꾼 뒤** 밀어 넣어야 한다.

## 읽는 순서
`FreeVars.lean` → 이 파일 → `Ex.lean`

## 책과의 차이
- Reynolds는 vnew 를 "어떤 표준 순서에서 첫 번째"로 정한다. 여기서는
  `HasFresh` 타입클래스로 추상화했다 (§1.1의 "표현이 지정되지 않은 변수 집합"과 같은 정신).
-/
```

분량 기준: **15~40줄**. 이보다 짧으면 정보가 없고, 길면 Verso 문서로 옮겨라.

#### (b) 선언 docstring — `/-- … -/`

모든 `def`, `theorem`, `inductive`, `structure`, `class`, `instance`, `abbrev`에 단다.

포함할 것:
- **책의 어느 기호인가** — `Reynolds의 FV_assert(p)` 처럼 명시
- **직관** — 한두 문장
- **왜 이 형식화인가** — 다른 선택지가 있었다면 왜 이걸 골랐는지
- 비자명한 인자·가정의 의미

```lean
/--
`⟦p⟧assert σ` — 단언(assertion)의 표시적 의미. Reynolds §1.2의 `⟦-⟧assert`.

**왜 `Bool`이 아니라 `Prop`인가**: `∀v. p` 의 의미는 `∀ n : ℤ, …` 이고 ℤ는 무한하므로
결정 가능하지 않다. Reynolds도 2장에서 boolexp를 만들 때 "양화사는 계산 불가능하므로
뺀다"고 말한다. 그 계산 가능성의 경계가 여기서 `Prop`/`Bool`의 차이로 드러난다.

2장의 `BoolExp.eval`은 `Bool`을 돌려주고, 실제로 `#eval`로 돌릴 수 있다.
두 의미가 양화사 없는 조각에서 일치한다는 것은 `Ch02/Semantics.lean`에서 증명한다.
-/
def Assert.eval : Assert V → State V → Prop
  | …
```

분량 기준: **3~15줄**. 자명한 보조 정의는 1줄로 끝내도 된다.

#### (c) 인라인 주석 — `--`

증명 안에서 **케이스 구분**과 **비자명한 한 수**에만 쓴다.

```lean
theorem coincidence_assert … := by
  induction p with
  | tru | fls => rfl
  | cmp op e₀ e₁ =>
      -- 비교식은 두 정수 식의 의미만으로 정해진다. 각각에 명제 1.1(intexp 판)을 쓴다.
      simp [Assert.eval, coincidence_intExp (h.mono …), …]
  | quant q v p ih =>
      -- 결합 케이스. 여기가 핵심: 귀납 가설을 **원래 σ, σ' 가 아니라**
      -- σ[v ↦ n], σ'[v ↦ n] 에 적용한다. FV(∀v.p) = FV(p) \ {v} 이므로
      -- v 에서만 다르던 두 상태가 v 를 같은 값으로 덮으면 FV(p) 전체에서 일치한다.
      …
```

**하지 말 것**
- 코드를 한국어로 번역하는 주석: `-- e의 자유변수를 구한다` 옆에 `e.fv` — 무가치하다.
- 낡을 주석: `-- 아래 3줄은 …` (줄 수가 바뀌면 거짓말이 된다)
- `-- TODO`, `-- FIXME` 를 남긴 채 PR — 미완성은 `sorry` + `@[exercise]`로 표현하거나 이슈로 뺀다.

### 2.3 표기(notation)

책 기호를 Lean 표기로 살린다. **책을 옆에 두고 코드를 읽을 수 있어야 한다.**

| 책 | Lean 표기 | 정의 위치 |
|---|---|---|
| `⟦e⟧intexp σ` | `⟦e⟧ σ` (스코프된 표기) | `Ch01/Semantics.lean` |
| `[σ \| v: n]` | `σ[v := n]` | **CSlib `HasSubstitution`** — `Function.update` 인스턴스 |
| `p / δ` | `p /ₛ δ` | `Ch01/Substitution.lean` |
| `p / v → e` | `p[v := e]` | **CSlib `HasSubstitution`** 인스턴스로 등록 |
| α-변환 (명제 1.5) | `p =α q` | **CSlib `HasAlphaEquiv`** |
| `⊑` | `⊑` | `Ch02/Domain.lean` |
| `⊔ᵢ xᵢ` | `⨆ᶜ c` | `Ch02/Domain.lean` |

> **CSlib 표기를 먼저 찾아라.** 같은 개념에 우리만의 표기를 새로 만들지 마라.
> `NOTATION.md`(CSlib)에 이미 정해진 관례가 있으면 그것을 따른다.
> Reynolds의 `[σ | v: n]`이 CSlib의 `σ[v := s]`와 같은 것이라는 사실 자체가
> 좋은 교육 포인트다 — docstring에 짚어라.

규칙:
- 표기는 **`scoped notation`** 으로 선언하고 `open Reynolds.Ch01` 시에만 보이게 한다.
  전역 오염은 Mathlib과 충돌한다.
- 표기를 정의한 곳 바로 아래에 `/-- … -/`로 **책의 어느 기호인지** 적는다.
- 새 유니코드를 도입하면 `AGENTS.md`의 위 표에 추가한다.

### 2.4 증명 스타일

**읽히는 것이 최우선.** 짧은 것이 아니라.

- ✅ `induction e with | num n => … | var v => …` — 케이스 이름을 드러낸다
- ✅ `calc` 로 등식 사슬을 보여준다 (Reynolds가 책에서 하는 그대로)
- ✅ 긴 증명은 `have` 로 중간 사실에 이름을 붙인다
- ❌ `by simp_all [*]` 한 줄로 끝내기 — 통과해도 아무도 못 배운다
- ❌ `<;>` 를 3단 이상 겹치기
- ❌ 100자 넘는 줄

**타협**: 완전히 기계적인 케이스(예: 이항 연산 5종)는 `all_goals simp [...]`로 묶어도 된다.
단, 바로 위에 `-- 나머지 이항 연산은 전부 같은 모양이다. Reynolds도 "and similarly for …"라고 쓴다.`
같은 주석을 단다.

**golfing 규칙**: Answers에서 증명을 줄였다면, 줄이기 전의 구조를 주석으로 남긴다.

---

## 3. Verso 연동 규약

`manual/` 패키지가 이 저장소의 코드를 **직접 인용**한다. 복사가 아니라 인용이라
소스가 바뀌면 문서 빌드가 깨진다. 그게 목적이다.

### 3.1 ANCHOR 마커

Verso 문서에 실릴 코드는 앵커로 감싼다.

```lean
-- ANCHOR: IntExp
/-- 정수 식의 추상 구문. Reynolds §1.1의 ⟨intexp⟩. -/
inductive IntExp (V : Type u) where
  | num  : Int → IntExp V
  | var  : V → IntExp V
  | neg  : IntExp V → IntExp V
  | bin  : IntOp → IntExp V → IntExp V → IntExp V
  deriving DecidableEq, Repr
-- ANCHOR_END: IntExp
```

규칙:
- 앵커 이름은 **선언 이름과 같게** 한다 (`IntExp`, `IntExp.eval`, `coincidence_assert`).
- 앵커는 **`Answers/` 트리에만** 단다. Verso는 Answers를 참조한다.
- 앵커는 중첩되어도 되고 겹쳐도 된다. 짝만 맞으면 된다 (`scripts/check-anchors.sh`가 검사).
- `#eval` 출력을 문서에 실을 거면 앵커 안에 `#eval`을 넣고, 문서에서 `anchorInfo`로 받는다.
  → 출력이 바뀌면 문서 빌드가 깨진다.

### 3.2 어디에 무엇을 쓰는가

| 내용 | 위치 |
|---|---|
| 정의의 정확한 뜻, 인자 의미, 책 기호 대응 | 선언 docstring (`/-- -/`) |
| 절 전체의 흐름, 왜 이 순서인가 | 모듈 docstring (`/-! -/`) |
| **서사** — 이야기로 풀어낸 설명, 비유, 그림, 오해하기 쉬운 지점 | `manual/Manual/ChNN.lean` (Verso) |
| 연습문제 힌트 | `manual/Manual/ChNN.lean` |
| 참고문헌 | `manual/Manual/Refs.lean` |

**같은 내용을 두 곳에 쓰지 마라.** Verso는 `{docstring Foo}`로 docstring을 그대로 끌어올 수 있다.
설명이 길어지면 docstring에서 덜어내 Verso로 옮기고, docstring에는 요점만 남긴다.

---

## 4. 파일·이름 규약

### 4.1 배치

```
Reynolds/Answers/ChNN/<주제>.lean     # 완성본
Reynolds/Exercises/ChNN/<주제>.lean   # 같은 이름, 같은 선언, 연습 부분만 sorry
```
두 트리는 **파일 이름·선언 이름·선언 순서가 같아야 한다.** 비교가 목적이기 때문이다.

한 파일은 책의 **한 절(section)** 에 대응시킨다. 절이 크면 쪼개고, 모듈 docstring에
`§2.5 (1/2)` 처럼 밝힌다.

### 4.2 선언 이름

| 대상 | 규칙 | 예 |
|---|---|---|
| 책의 명제/정리 | `<내용>` + docstring에 번호 | `coincidence_intExp`, `substitution_assert`, `renaming_comm` |
| 책의 연습문제 | `ex_<장>_<번호>` | `ex_2_5`, `ex_1_7a` |
| 의미 함수 | `<타입>.eval` | `IntExp.eval`, `Comm.eval` |
| 구문 함수 | `<타입>.<동사>` | `Assert.fv`, `Comm.subst` |
| 보조 정리 | Mathlib 관례(스네이크, 결론을 이름에) | `fv_subst_eq_biUnion`, `eval_update_of_notMem` |

**번호를 이름에 넣지 않는다** (`prop_1_1` ✗). 책 개정판에서 번호가 바뀌면 전부 깨진다.
번호는 `@[exercise "Prop 1.1"]`과 docstring에만 둔다.

### 4.3 `@[exercise]` 태그

```lean
@[exercise "Prop 1.3" 3]
theorem substitution_assert … := by
  sorry
```

문법은 `@[exercise "<id>" <stars>?]` 다. 별점을 생략하면 1이다.

- `id` — 책의 문제/명제 번호. `"Prop 1.1a"`, `"Ex 2.5"`, `"§1.3 gen-sound"`
- `stars` — 1 = 정의를 따라 쓰면 됨 / 2 = 구조적 귀납법 + 약간의 궁리 /
  3 = 결합 케이스가 까다롭거나 진술의 일반화가 필요
- **책의 절 참조는 애트리뷰트가 아니라 docstring에 쓴다.** 애트리뷰트에 `ref` 필드를 두지
  않은 이유다 — 같은 정보를 두 곳에 두면 반드시 어긋난다.
- **Answers와 Exercises의 태그 집합이 정확히 같아야 하고, 한 트리 안에서 id가 중복되면
  안 된다.** `scripts/check-anchors.sh` 가 검사한다.

### 4.4 문서에 연습 개수를 적을 때

산문에 적은 숫자는 `@[exercise]` 가 늘거나 줄어도 그대로 남는다. 1장 문서가 28 이라고
적어 둔 동안 실제는 31 이었고, 표를 더해 본 사람이 나올 때까지 CI는 전부 초록이었다.
그래서 개수는 아래 틀로만 적고 `scripts/check-doc-counts.py` 가 실제 태그와 대조한다.

```markdown
3장에는 채점되는 연습이 10 개 있다.

| 갈래 | 개수 | 어디에 |
|---|---|---|
| 본문 명제 | 6 | `Semantics.lean`, `FixedPoint.lean` |
| 심화 트랙 | 4 | `Depth/` |
```

실제로 쓰인 것은 `manual/Manual/Ch01.lean` 의 "연습문제" 절에 있다.

- 문장의 두 숫자는 장 번호와 그 장의 총 개수다. 장 번호가 문장 안에 있으므로 Markdown이든
  Verso Lean 소스든 같은 틀을 그대로 쓴다.
- `어디에` 칸은 `Reynolds/Answers/ChNN/` 기준 상대 경로를 백틱으로 적는다.
  `Depth/` 처럼 슬래시로 끝내면 그 디렉터리 아래 전부를 가리킨다.
- 행은 그 장의 연습 파일을 빠짐없이, 겹치지 않게 나눈다. 연습이 든 파일이 어느 행에도
  없으면 검사가 실패한다 — 파일을 새로 만들고 표를 안 고친 경우가 여기서 걸린다.
- **연습이 있는 장에 `manual/Manual/ChNN.lean` 이 있으면 그 파일에 이 블록이 있어야 한다.**
  틀을 안 쓰면 검사할 것도 없기 때문이다.
- 숫자가 어긋나면 검사기가 고쳐 쓸 블록의 뼈대를 찍어 준다. 갈래 이름만 채우면 된다.
- 이 규약 자체를 예시로 보일 때는 코드 울타리 안에 넣는다. 울타리 안은 검사하지 않는다.

---

## 5. 형식화 결정 지침

새 정의를 만들 때 다음 순서로 판단한다.

1. **책에 충실한가?** 기본은 Reynolds를 그대로 옮기는 것이다.
2. **충실함이 증명을 망치는가?** 예: 이항 연산 6개를 각각 생성자로 두면 모든 구조적
   귀납이 6배로 늘어난다. Reynolds 본인이 "and similarly for -, ×, ÷, rem"이라고 쓰므로,
   연산 태그(`IntOp`)로 묶는 것이 **오히려 책의 정신에 맞다.** → 묶는다. docstring에 이유를 쓴다.
3. **Lean이 공짜로 주는 것을 다시 만들지 마라.** Reynolds의 "추상 구문 조건"
   (생성자 단사, 치역 서로소, 유한 생성)은 `inductive`가 `injEq`/`noConfusion`/`rec`로
   전부 준다. **이걸 예제로 보여주는 것**이 형식화의 하이라이트다.
4. **차이가 생기면 docstring에 `**책과의 차이**:` 절을 만든다.** 예외 없다.

### CSlib / Mathlib 과의 경계선

| 층 | 누가 | 예 |
|---|---|---|
| **인프라** | CSlib에 있으면 **쓴다** | `HasFresh`, `HasSubstitution`, `HasAlphaEquiv`, `InferenceSystem`, (6장~) `LTS`, `Bisimulation`, `Confluence` |
| **수학 기반** | Mathlib에 있으면 **쓴다** | `Finset`, `Function.update`, 순서론, `omega`/`grind` |
| **책의 내용** | **전부 우리가 쓴다** | 구문 정의, 의미 함수, 명제와 증명 |

- ❌ CSlib에 STLC 안전성 증명이 있다고 15장을 `import`로 때우지 마라. 그러면 스터디가 아니다.
- ✅ 대신 **교차 참조**하라. docstring에 이렇게 적는다:
  > 이에 대응하는 것이 `Cslib.Languages.LambdaCalculus.LocallyNameless.Stlc.Safety`에 있다.
  > Reynolds는 표시적(denotational)으로, CSlib는 연산적(operational)으로 접근한다. 비교해 보라.

  **비교가 곧 학습 재료다.**
- ✅ **교육 목적의 재정의는 권장**한다. 2장의 도메인 이론은 Mathlib의 `OmegaCompletePartialOrder`가
  있어도 **직접 만든다** — 그게 §2.3–2.4다. 단 `MathlibBridge.lean`에 대조표를 남긴다.

### 계산 가능성

- 구문 조작(치환, 자유 변수, 디슈가링)은 **반드시 계산 가능**하게. `#guard`로 테스트 가능해야 한다.
- 의미론은 계산 불가능해도 된다 (`while`의 최소 고정점). 대신 **연료(fuel) 기반 해석기를
  같이 제공**하고, 둘이 일치한다는 정리를 증명한다.
- `deriving DecidableEq, Repr`을 모든 구문 타입에 붙인다. `#eval`과 `decide`가 학습에 필수다.

---

## 6. 반드시 돌려야 하는 명령

작업을 "끝났다"고 말하기 전에 **전부** 통과해야 한다.

```bash
python3 scripts/gen-exercises.py            # Answers → Exercises 재생성 (손으로 고치지 마라)
lake build --wfail ReynoldsTests            # 엄격 모드 — Answers + 테스트, 경고 0
lake build                                  # 전체 (Exercises 의 sorry 경고 허용)
lake test                                   # #guard 단위 테스트
lake lint                                   # 환경 린터 (docBlame 등)
lake exe grade --answers                    # Answers sorry-free · 불법 공리 없음
lake exe grade --chapter N                  # 손댄 장의 Exercises 상태 확인
python3 scripts/gen-exercises.py --check    # 두 트리가 어긋나지 않는지
./scripts/check-anchors.sh                  # ANCHOR 짝 + 두 트리 @[exercise] 태그 일치
python3 scripts/check-doc-counts.py --grade # 문서에 적은 연습 개수가 실제와 맞는지 (§4.4)
```

> `check-doc-counts.py` 는 `--grade` 없이 돌리면 빌드 없이 소스만 세므로 즉시 끝난다.
> `--grade` 는 `lake exe grade` 의 레지스트리와 총계를 대조하는 것이라 빌드가 있어야 한다.

> **`Reynolds/Exercises/**` 를 직접 고치지 마라.** `scripts/gen-exercises.py` 가 Answers 에서
> 생성한다. 연습을 추가하거나 힌트를 바꾸려면 그 스크립트의 `BLANKS` 표를 고친다.
> 어떤 정리를 비울지 고르는 규칙(반사슬 조건)도 그 파일 docstring 에 적혀 있다.

> **엄격 모드에 왜 `ReynoldsTests` 를 넣나**: `Exercises` 트리는 **의도적으로** `sorry` 를
> 갖고 있어서 `--wfail` 을 전체에 걸면 항상 실패한다. `ReynoldsTests` 는 `Answers` 만
> import 하므로, 이 타겟을 엄격 빌드하면 **Answers 전체 + 테스트**가 경고 0 인지 검사된다.
>
> **`--iofail` 은 쓰지 않는다.** 그 플래그는 빌드 중 **모든 IO 출력**을 실패로 본다.
> 그런데 교육용 파일(`Background.lean` 등)은 `#eval` 로 값을 보여 주는 것이 목적이다.
> 둘은 근본적으로 충돌한다. 잡고 싶은 것(경고·`sorry`·deprecation)은 `--wfail` 이 다 잡는다.

새 파일을 추가하면 루트 모듈 `Reynolds.lean` 에 `public import` 를 한 줄 더한다.
`emit_exercise_registry` 호출은 **반드시 파일 맨 아래**여야 한다.

문서를 건드렸으면 추가로:
```bash
cd manual && lake exe build-manual
python3 ../scripts/serve.py 8000 -d _out/html-multi   # 눈으로 확인
```

**에이전트에게**: 위 명령의 실제 출력을 보지 않고 "통과했습니다"라고 쓰지 마라.
실패했으면 실패했다고 출력과 함께 보고하라.

---

## 7. 커밋과 PR — **히스토리가 교재다**

이 프로젝트는 [j2kun/mlir-tutorial](https://github.com/j2kun/mlir-tutorial) 방식을 따른다.
**완성된 코드만큼이나 "어떻게 쌓아 올렸는가"가 산출물이다.** 자세한 근거는 `DESIGN.md` §12.

### 7.1 단위: 1 PR = 책의 1개 절

```
feat(ch01): §1.4 결합과 치환
feat(ch02): §2.4 최소 고정점 정리
```
절이 너무 크면 쪼갠다: `feat(ch02): §2.5 변수 선언과 치환 (1/2) 자유 변수`

### 7.2 PR 안의 커밋 — 의미 단위로, 각각 컴파일되게

```
1. feat(ch01): FV 정의 추가
2. feat(ch01): 명제 1.1 진술 (sorry)      ← 진술만. 경고는 나지만 컴파일 통과
3. feat(ch01): 명제 1.1 증명
4. feat(ch01): 명제 1.1 Exercises 스텁
5. docs(ch01): §1.4 Verso 문서
```
**이 순서 자체가 교재다.** "진술 먼저, 증명 나중"이 정리 증명의 실제 작업 순서이고,
커밋 2와 3의 diff가 그것을 보여준다.

- 커밋 메시지는 한국어. 한 줄 요약 + 필요하면 본문.
- 접두사: `feat(chNN):` `fix:` `docs:` `chore:` `refactor:` `test:` `study(chNN-sMM):`
- **Answers와 대응 Exercises는 같은 커밋에 넣는다.** 어긋난 상태를 main에 남기지 않는다.
- 커밋 하나가 빌드를 깨뜨리면 안 된다. `sorry` 경고는 괜찮지만 **에러는 안 된다.**

### 7.3 PR 본문 = 그 절의 학습 노트

`.github/PULL_REQUEST_TEMPLATE.md`를 반드시 채운다. 빈 채로 열지 마라.

```markdown
## 책의 위치        Reynolds §N.M (pp. ..–..)
## 추가한 것        정의·정리 목록
## 형식화 결정      왜 이렇게 옮겼는가. 다른 선택지가 있었다면 왜 안 골랐는가
## 막혔던 곳        어디서 헤맸고 무엇이 답이었나  ← 가장 가치 있는 칸이다
## 책과 다른 점     없으면 "없음"
## 스터디 토론 질문  2~3개
```

> **"막혔던 곳"을 비워 두지 마라.** 이 프로젝트에서 가장 재사용성 높은 정보다.
> 같은 곳에서 다음 사람도 막힌다.

### 7.4 머지와 태그

- **squash merge** (제목에 PR 번호). `main`의 `git log --oneline`이 목차가 된다.
- 머지 후 **교재 PR에만** 태그를 찍는다: `git tag ch01-s04 -m "§1.4 결합과 치환"`
- `fix`/`chore`/`refactor`/`docs` PR은 **태그를 찍지 않는다.** 태그 목록이 곧 목차이므로.
- README 목차 표에 **문서 링크 · PR 번호 · 태그**를 추가한다. (교재 PR과 같은 PR에서)

### 7.5 스터디 풀이 PR

각자의 풀이는 `study(ch01-s04): <이름> 풀이`로 올린다.
**main에 머지하지 않는다.** 리뷰 후 닫는다. 리뷰 코멘트가 토론 아카이브가 된다.

### 7.6 AI 도구 사용 고지

AI 도구로 작성했으면 PR 설명에 **어떤 도구를 어떻게 썼는지** 적는다.
(Mathlib/CSlib 정책과 동일. 리뷰어가 다른 종류의 실수를 찾아야 하기 때문이다.)

---

## 8. 한 절(section)을 추가할 때 체크리스트

**1 PR = 1 절**이므로 이 체크리스트가 곧 PR 하나의 정의다.

**코드**
- [ ] `Reynolds/Answers/ChNN/<주제>.lean` — 파일 첫 줄 `module`, 저작권 헤더, 모듈 docstring
- [ ] 모든 공개 선언에 docstring (`linter.missingDocs`가 강제)
- [ ] 책의 명제를 전부 `theorem`으로 (증명 포함, `sorry` 없음)
- [ ] 책의 연습문제를 전부 `ex_N_M`으로
- [ ] Verso 인용 대상에 `ANCHOR` 마커
- [ ] `Reynolds/Exercises/ChNN/<주제>.lean` — 1:1 대응, 연습 지점만 `sorry`
- [ ] `@[exercise]` 태그를 두 트리에 동일하게, **연습 독립성 원칙**(§1-9) 준수
- [ ] `ReynoldsTests/ChNN.lean`에 `#guard` 단위 테스트 (계산 가능한 부분 전부)
- [ ] `lake exe mk_all`로 루트 모듈 갱신

**문서**
- [ ] `manual/Manual/ChNN.lean`에 해당 절 추가
- [ ] 연습이 늘거나 줄었으면 `manual/Manual/ChNN.lean`의 개수 블록을 갱신 (§4.4)
- [ ] `STUDY.md`에 주차 배정 추가

**검증**
- [ ] §6의 명령 전부 통과

**히스토리 (§7)**
- [ ] PR 안의 커밋이 의미 단위로 쪼개져 있고 각각 컴파일된다
- [ ] PR 템플릿을 다 채웠다 — 특히 **"막혔던 곳"**
- [ ] PR 열기 전 로컬 1차 리뷰를 받았다 (`codex review --base main`)
- [ ] Codex GitHub 리뷰 지적을 처리했다 (반박했으면 근거를 코멘트로 남겼다)
- [ ] 머지 후 태그 `chNN-sMM` 을 찍었다
- [ ] README 목차 표에 문서 링크 · PR 번호 · 태그를 추가했다
      (**저장소 상대 경로로** — `[#12](../../pull/12)`. §12.3 참고)

---

## 9. 하지 말 것 모음

- ❌ 책에 없는 내용을 "더 좋아 보여서" 추가하기 — 스터디는 책을 따라간다. 확장은 별도 파일 `Extra/`에.
- ❌ 증명을 못 하겠다고 정리 진술을 약화시키기 — 약화했으면 docstring에 크게 밝힌다.
- ❌ `sorry` 대신 `admit`, `stop`, `trivial`로 눈속임하기
- ❌ Mathlib에 있는 것을 이름을 몰라서 다시 정의하기 (단, **교육 목적의 재정의는 권장**한다.
      그 경우 docstring에 `Mathlib의 `X`에 대응한다`를 반드시 쓴다)
- ❌ 한 파일이 500줄을 넘기기 — 절 단위로 쪼개라
- ❌ `set_option maxHeartbeats 999999` 로 느린 증명 덮기 — 증명을 고쳐라
- ❌ 툴체인/의존성 버전을 혼자 올리기 — `DESIGN.md` §8의 업그레이드 정책을 따른다

---

## 10. 이미 밟아 본 지뢰 (실측 확인됨)

새로 밟지 마라. 전부 프로브에서 실제로 터진 것들이다. (`DESIGN.md` §10.2)

| 증상 | 원인 | 해결 |
|---|---|---|
| `cannot import non-\`module\` X from \`module\`` | 모듈/비-모듈 혼용 | **전 파일을 `module`로.** 반대 방향은 되지만 루트 모듈에서 반드시 터진다 |
| `cannot evaluate \`[init]\` declaration … in the same module` | `initialize` 환경 확장을 같은 모듈에서 사용 | 선언 모듈과 사용 모듈을 분리 |
| `unknown declaration '_private.….exerciseExt'` | 모듈 시스템 기본 가시성이 private | `public initialize …` |
| `Invalid \`meta\` definition …; consider adding \`public meta import X\`` | meta 선언의 전파 부족 | 오류가 시키는 대로 `public meta import` |
| `decide` 가 downstream에서 안 풀림 | 정의 본문이 불투명 | `@[expose] public section` |
| `The environment does not contain \`Finset.biUnion\`` | import 경로 오해 | `Mathlib.Data.Finset.Union` (`Lattice.Fold`가 아니다) |
| `unexpected token '#eval'; expected …` | `/-- … -/` 를 `#eval`/`#check` 앞에 붙임 | 명령 앞에는 `--` 주석 |
| 정리의 `value?` 가 `none` | 정리 증명 항은 **다른 모듈에서 안 보인다** | 증명 항을 들여다보는 설계를 하지 마라 (§1-9) |
| `failed to compile definition … depends on 'Int.instConditionallyCompleteLinearOrder'` | Mathlib 과 CSlib 을 함께 열면 `Preorder ℤ` 가 계산 불가능한 경로로 잡힌다. `Finset.Icc` 를 쓰는 정의가 통째로 계산 불가능해진다 | 파일 안에서 `attribute [-instance] Int.instConditionallyCompleteLinearOrder`. 순서 자체는 같으므로 보조정리는 그대로 쓰인다 |
| 매크로가 뱉은 이름이 엉뚱한 이름공간으로 붙음 | Lean 매크로는 hygienic 이라 이름을 **정의 자리**에서 해석한다 | `Lean.mkIdent` 로 만들면 **쓰는 자리**에서 해석된다 (`Notation.lean`) |
| `environment already contains 'Lean.Parser.Category.…'` | `declare_syntax_cat` 은 전역이라 두 트리에 복제할 수 없다 | 생성기의 `SHARED` 에 넣어 Answers 쪽을 공유한다 |

---

## 11. 막혔을 때

1. Mathlib 이름 찾기: `exact?`, `apply?`, `rw?`, [Loogle](https://loogle.lean-lang.org),
   [Moogle](https://www.moogle.ai), [Mathlib 문서](https://leanprover-community.github.io/mathlib4_docs/)
2. 이 개념이 CSlib에 이미 있는지: `.lake/packages/cslib/` 트리를 직접 뒤져라.
   특히 `Foundations/Syntax`, `Foundations/Semantics/LTS`, `Languages/LambdaCalculus`.
   [`ORGANISATION.md`](https://github.com/leanprover/cslib/blob/main/ORGANISATION.md)와
   [`NOTATION.md`](https://github.com/leanprover/cslib/blob/main/NOTATION.md)를 먼저 읽어라.
3. Verso 문법: [verso-templates](https://github.com/leanprover/verso-templates)의
   `package-docs/manual/Docs/DocFeatures.lean` 이 사실상 치트시트다.
4. 모듈 시스템: **Lean의 오류 메시지가 대개 답을 알려준다.** 먼저 끝까지 읽어라.
5. 그래도 안 되면 `sorry` + `@[exercise … 3]` + 이슈. **막힌 채 커밋하지 말고
   막혔다고 표시하고 커밋한다.** 그리고 PR 본문 "막혔던 곳"에 적는다.

---

## 12. 리뷰 규약

### 12.1 리뷰 순서

```
lake build --wfail ReynoldsTests && lake test && lake exe grade --answers   ① 기계 검증
        ↓  (통과해야 다음으로)
codex review --base main                                              ② 로컬 1차 (푸시 전)
        ↓
PR 열기 → Codex GitHub 리뷰                                            ③ 기록에 남는 리뷰
        ↓
스터디 시간 사람 리뷰                                                    ④ 이해·토론
```

**①을 건너뛰지 마라.** 빌드도 안 되는 코드를 리뷰시키면 리뷰어가 빌드 오류 이야기만 한다.

### 12.2 ★ 무엇을 리뷰하는가 — Lean에서는 기본값이 틀렸다

**"이 증명이 맞나요?"는 이미 커널이 답했다.** `lake build`가 통과했으면 정리는 참이다.
그러므로 정확성을 리뷰 대상으로 삼으면 리뷰가 무의미해진다.

이 저장소에서 리뷰의 가치는 **교육적 품질**에 있다.

| ❌ 리뷰하지 말 것 | ✅ 리뷰할 것 |
|---|---|
| 증명이 참인가 | **docstring만 읽고 이 정의를 이해할 수 있는가** |
| 타입이 맞는가 | 형식화 결정이 정당한가. 책과 다르게 했다면 `**책과의 차이**:`로 밝혔는가 |
| 빌드가 되는가 | 책의 절·명제 번호 참조가 **정확한가** |
| | 증명이 읽히는가 — `simp_all` 한 줄로 뭉갠 곳이 있는가 (§2.4) |
| | 표기가 CSlib `NOTATION.md` 관례를 따르는가. 중복 표기를 새로 만들지 않았는가 |
| | **연습 독립성 원칙**(§1-9)을 지키는가 |
| | Answers / Exercises 두 트리가 파일·선언·순서까지 1:1인가 |
| | `@[exercise]` 태그 집합이 두 트리에서 같은가 |
| | 한국어 용어 규약 — 첫 등장 시에만 `한글(English)` (§2.1) |
| | ANCHOR 짝이 맞고 앵커 이름이 선언 이름과 같은가 (§3.1) |
| | 모듈 시스템 규약 — `module` 시작, `@[expose] public section` 필요 여부 (§1.5) |

**이 표가 곧 Codex의 리뷰 기준이다.** Codex는 저장소 루트의 `AGENTS.md`를 읽으므로
별도 설정 파일이 필요 없다. 리뷰 품질이 낮다고 느껴지면 **이 표를 고쳐라.**

### 12.3 링크는 상대 경로로

이 저장소는 개인 계정에서 시작해 나중에 조직으로 이전한다(`DESIGN.md` §13).
소유자·저장소 이름이 바뀌어도 안 깨지게 쓴다.

```markdown
✅ [DESIGN.md](./DESIGN.md)
✅ [1장 설계](./docs/chapter-01.md)
✅ [#12](../../pull/12)              ← PR 링크
✅ [ch01-s04](../../tree/ch01-s04)   ← 태그 링크
❌ https://github.com/<user>/tpl-in-lean/pull/12
```
GitHub Pages 절대 URL은 **README 한 곳에만** 둔다. 이전 후 한 줄만 고치면 되게.

### 12.4 리뷰 코멘트에 동의하지 않을 때

**반박하고 닫는다.** 근거를 코멘트로 남겨라.
그 반박도 PR에 남아 교재의 일부가 된다 — "왜 저렇게 안 했는가"는 종종
"왜 이렇게 했는가"보다 유익하다.
