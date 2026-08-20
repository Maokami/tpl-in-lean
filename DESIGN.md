# `tpl-in-lean` — 설계 문서

> John C. Reynolds, *Theories of Programming Languages* (Cambridge, 1998 / 2009 페이퍼백)를
> Lean 4로 따라가며 실습하는 스터디 프로젝트.
> 모델: [fpinscala/fpinscala](https://github.com/fpinscala/fpinscala)

작성일: 2026-08-20 · 상태: 설계안 (코드 미작성)

---

## -1. 이름

| 대상 | 이름 |
|---|---|
| 저장소 / 디렉터리 | `tpl-in-lean` |
| Lake 패키지 | `tpl-in-lean` |
| Lean 라이브러리 · 루트 네임스페이스 | `Reynolds` |
| 테스트 라이브러리 | `ReynoldsTests` |
| 실행 파일 | `grade` |
| 문서 패키지 | `tpl-in-lean-manual` (lib `Manual`, exe `build-manual`) |

**왜 `tpl-in-lean`인가**

Lean 생태계의 학습 자료는 **"X in Lean"** 이라는 강한 관례를 갖는다 —
*Mathematics in Lean*, *Functional Programming in Lean*, *Theorem Proving in Lean*.
이름만 보고 "이건 Lean으로 배우는 자료구나"를 알게 하는 것이 이 관례의 값어치다.
`tpl`은 책 제목 *Theories of Programming Languages*의 약자다.

**왜 네임스페이스는 `Reynolds`인가**

저장소 이름과 Lean 네임스페이스가 달라도 된다 — *Mathematics in Lean*도
저장소는 `mathematics_in_lean`, 네임스페이스는 `MIL`이다.

코드 안에서는 **매 줄에 등장하는 이름**이 중요하다.
`Reynolds.Answers.Ch01.Syntax`는 읽히지만 `Tpl.Answers.Ch01.Syntax`의 `Tpl`은
소음이고 "template"으로 읽힌다. 저자 이름은 PL 분야에서 이 책을 가리키는 가장 확실한 단어다.

**검토했으나 고르지 않은 이름**

| 후보 | 이유 |
|---|---|
| `tpl-exercise` | "exercise"는 형태만 가리킨다. 이 프로젝트는 연습 + 정리 증명 + Verso 책이다 |
| `reynolds-in-lean` | 모호성은 0이지만 책 제목이 이름에 안 남는다 |
| `reynolds-tpl` | `tpl`이 접미사로 붙어 "Reynolds 템플릿"으로 읽힌다 |
| `theories-of-programming-languages-lean` | 정확하지만 길어서 아무도 안 친다 |

README 첫 줄에 책의 정식 제목·저자·출판사를 적어 `tpl` 약자의 모호성을 즉시 해소한다.

---

## 0. 요약 (TL;DR)

| 항목 | 결정 |
|---|---|
| 툴체인 | Lean `v4.33.0` (2026-08-10 안정판) |
| 의존성 | **CSlib `v4.33.0`**, Mathlib `v4.33.0`, SubVerso `verso-v4.33.0` |
| 모듈 시스템 | **채택** — `module` / `public import` / `meta import` / `@[expose] public section` |
| 문서 | 별도 Lake 패키지 `manual/` + Verso `v4.33.0` (Manual 장르) |
| 실습 구조 | `Reynolds/Exercises/ChNN/*` (빈칸) ↔ `Reynolds/Answers/ChNN/*` (정답) — fpinscala 2트리 방식 |
| 채점 | `lake exe grade` — `@[exercise]` 애트리뷰트 + `Lean.collectAxioms`로 `sorryAx` 검사 |
| 테스트 | `lake test` + CSlib식 위생 도구 (`lake lint`, `lint-style`, `shake`, `mk_all`) |
| 언어 | 주석·문서 전부 한국어, 기술 용어는 `한글(English)` 병기 |
| 핵심 차별점 | 정의(코드) · 설명(주석) · 증명(정리)이 **한 파일 안에서 기계 검증**된다 |

> **버전이 한 줄로 정렬된다**: Lean · Mathlib · CSlib · Verso · SubVerso가 모두
> `v4.33.0` 태그를 갖는다 (2026-08-10 동시 릴리스). 정합성 고민이 필요 없다.

### 부목표: Lean 4 자체에 익숙해지기

이 프로젝트에는 "Reynolds 책 이해"와 별개로 **현재의 Lean 4에 익숙해진다**는 목표가 있다.
따라서 **최신 기능을 의도적으로, 적극적으로 쓴다.** 무엇을 어디서 쓰는지는 §11에 표로 정리했다.

---

## 1. 조사 결과

### 1.1 fpinscala에서 가져올 것 / 버릴 것

[fpinscala](https://github.com/fpinscala/fpinscala)의 구조:

```
src/main/scala/fpinscala/exercises/<chapter>/   # ??? 스텁
src/main/scala/fpinscala/answers/<chapter>/     # 완성본 + 해설
answerkey/<chapter>/04.hint.md, 04.answer.md    # 힌트/해설 마크다운
```
- 빌드: Scala CLI (`scala-cli compile . / test .`), SBT 대체 빌드 병행
- 테스트: 패키지별로 정리, 와일드카드로 특정 연습만 실행

**가져올 것**
- `exercises` / `answers` **두 트리 병행**. 정답을 숨기지 않는다 (fpinscala도 같은 저장소에 넣는다). 목적은 은닉이 아니라 "채울 자리"와 "비교 대상"을 주는 것.
- 장(chapter)별 디렉터리 · 장별 실행/테스트
- README에 설치·실행이 한 번에 되도록 적기

**버릴 것 / 바꿀 것**
- `???` 스텁 → Lean에서는 `sorry`. 단, Scala의 `???`는 **런타임** 실패지만 Lean의 `sorry`는 **컴파일 타임 경고**다. 즉 "타입은 맞는데 증명이 없음"을 정적으로 구분할 수 있다 → 채점기가 훨씬 정확해진다.
- 단위 테스트(assert) 중심 → Lean에서는 **정리(theorem)** 자체가 스펙이다. 단위 테스트는 계산 가능한 부분(평가기, 치환, 디슈가링)에만 `#guard`로 붙인다.
- `answerkey/*.md` 힌트 파일 → Lean에서는 **docstring + Verso 문서**로 흡수. 별도 마크다운 트리를 두면 코드와 어긋난다.

### 1.2 CSlib — 채택한다

[leanprover/cslib](https://github.com/leanprover/cslib) (Lean 공식 CS 라이브러리, Mathlib의 CS판). 실제 트리를 확인한 결과:

```
Cslib/Foundations/Data/HasFresh.lean          # 유한집합에서 fresh 변수 생성
Cslib/Foundations/Syntax/HasSubstitution.lean # t[x := s] 표기 타입클래스
Cslib/Foundations/Syntax/HasAlphaEquiv.lean   # m =α n
Cslib/Foundations/Logic/InferenceSystem.lean  # 추론 규칙 시스템
Cslib/Foundations/Semantics/LTS/*             # 라벨 전이 시스템, 이중시뮬레이션
Cslib/Languages/LambdaCalculus/LocallyNameless/*
Cslib/Languages/LambdaCalculus/Named/Untyped/*
```

이 프로젝트와 겹치는 부분이 **매우 많다**. 특히
- `HasFresh` = Reynolds가 §1.1에서 말한 "표현이 지정되지 않은 가산 무한 변수 집합 ⟨var⟩"의 정확한 형식화
- `HasSubstitution`의 `t[x := s]` 표기 = Reynolds의 `p/v → e`
- `LTS` = 6장 전이 의미론(transition semantics), `Bisimulation` = 9장 CSP

빌드 설정도 참고할 만하다:
```toml
testDriver = "CslibTests"
lintDriver = "batteries/runLinter"
[leanOptions]
weak.linter.mathlibStandardSet = true
```

#### 채택 근거

**(1) 버전이 안 맞을 거라는 우려는 사실이 아니었다.**
CSlib는 **모든 Lean 릴리스마다 태그를 찍는다** — rc뿐 아니라 안정판도.

```
cslib v4.33.0  (commit 3951377e5a3f, 2026-08-10)
  lean-toolchain: leanprover/lean4:v4.33.0     ← 안정판
  require mathlib rev = "v4.33.0"              ← 태그 → 캐시 존재
```
즉 CSlib를 쓴다고 rc에 끌려가지 않는다. **오히려 버전 정렬이 강제되어 좋다.**

**(2) 책의 후반부와 CSlib의 대응이 놀랍도록 정확하다.**

| Reynolds 장 | CSlib 모듈 |
|---|---|
| §1.1 ⟨var⟩ (표현 미지정 가산 무한 집합) | `Foundations/Data/HasFresh.lean` |
| §1.4 치환 `p/δ` 표기 | `Foundations/Syntax/HasSubstitution.lean` (`t[x := s]`) |
| §1.4 명제 1.5 이름 바꾸기 = α-변환 | `Foundations/Syntax/HasAlphaEquiv.lean` (`m =α n`) |
| §1.3 추론 규칙 / 3장 Hoare 논리 | `Foundations/Logic/InferenceSystem.lean` |
| **6장** 전이 의미론 | `Foundations/Semantics/LTS/*` |
| **7장** 비결정성 | `Foundations/Semantics/LTS/*`, `Relation/*` |
| **8·9장** 병행성 · CSP | `Languages/CCS/*`, `LTS/Bisimulation.lean`, `TraceEq.lean` |
| **10장** λ-계산법, 축약, 합류성 | `Languages/LambdaCalculus/*`, `Relation/Confluence.lean` |
| **15장** 단순 타입 체계 | `LambdaCalculus/LocallyNameless/Stlc/{Basic,Safety,StrongNorm}.lean` |
| **16·17장** 부분타입 · 다형성 | `LambdaCalculus/LocallyNameless/Fsub/{Subtype,Typing,Safety}.lean` |

1~5장만 보면 CSlib의 이득은 표기 타입클래스 정도로 크지 않다.
**6장부터 이득이 폭발한다.** 나중에 붙이려면 그때 전체 구조를 갈아엎어야 한다.

**(3) 부목표에 정확히 부합한다.**
"현재의 Lean 4에 익숙해지기"의 가장 좋은 방법은 **현재 잘 관리되는 Lean 4 코드베이스의
관습을 따르는 것**이다. CSlib는 Mathlib 스타일 + 모듈 시스템 + `grind` + 최신 Lake 위생 도구를
전부 쓰는 살아 있는 예다. CSlib의 `AGENTS.md`·`CONTRIBUTING.md`·`ORGANISATION.md`·`NOTATION.md`가
그대로 우리 규약의 본이 된다.

**(4) 도입할 도구 세트** — CSlib에서 그대로 가져온다.
```bash
lake build --wfail --iofail   # 경고도 실패로 (CI 엄격도)
lake test                      # testDriver
lake lint                      # 환경 린터 (batteries/runLinter)
lake exe lint-style            # 텍스트 스타일 린터
lake exe mk_all --check        # 루트 모듈이 모든 파일을 import하는지
lake exe shake Reynolds        # 불필요한 import 검출
```
이것들을 쓰는 것만으로 "Lean 프로젝트 위생"을 배운다.

#### 인정해야 할 실제 비용

| 비용 | 실태 | 완화 |
|---|---|---|
| CSlib는 **prebuilt olean을 배포하지 않는다** (릴리스 자산 0개) | 소스 빌드 필요 | `lake build Reynolds`는 **실제로 의존하는 모듈만** 빌드한다. 1~5장에서는 `HasFresh`, `HasSubstitution`, `InferenceSystem` 등 극소수만 필요 → 전체 266파일을 빌드하지 않는다 (§10에서 실측) |
| CSlib는 **아직 젊고 API가 바뀐다** (`ORGANISATION.md`: *"still under active discussion and is subject to change"*) | 업그레이드 때 깨질 수 있다 | ① `main`이 아니라 **태그로 핀**한다 ② `Reynolds/Compat.lean` 얇은 재수출 층을 두어, 이름이 바뀌면 **한 파일만** 고친다 |
| 의존성 하나가 더 늘어난다 | 셋업 설명이 길어진다 | Devcontainer / Codespaces 프리빌드 제공 |

#### 어디까지 CSlib에 맡기는가 (경계선)

- ✅ **인프라** — `HasFresh`, 표기 타입클래스(`HasSubstitution`, `HasAlphaEquiv`), `InferenceSystem`,
  6장 이후의 `LTS`/`Bisimulation`/`Confluence`
- ❌ **내용** — 구문 정의, 의미 함수, 책의 명제와 증명은 **전부 우리가 쓴다.**
  CSlib에 STLC 안전성 증명이 있다고 해서 15장을 `import`로 때우지 않는다. 그러면 스터디가 아니다.
- 📝 **교차 참조 규율** — CSlib에 대응물이 있으면 docstring에 반드시 적는다.
  예: *"Reynolds의 진행(progress)·보존(preservation)에 해당하는 것이
  `Cslib.LambdaCalculus.LocallyNameless.Stlc.Safety`에 있다. 접근 방식이 어떻게 다른지 비교해 보라."*
  → **비교가 곧 학습 재료**가 된다.

#### 교육적 절충 하나

`HasFresh`는 20줄이면 직접 쓸 수 있고, 직접 써 보는 것이 §1.1의 이해에 도움이 된다.
그래서 **본 코드는 `Cslib.HasFresh`를 쓰되**, `Exercises/Ch01`에 ★ 연습으로
*"`Cslib.HasFresh`를 보지 말고 직접 정의하고 `ℕ`·`String` 인스턴스를 만들어 보라"* 를 둔다.
같은 논리를 `HasSubstitution` 표기 클래스에도 적용한다.

### 1.3 Verso — 문서화 전략

[leanprover/verso](https://github.com/leanprover/verso)는 Lean 공식 문서 저작 도구다. Lean 언어 레퍼런스 매뉴얼이 이걸로 작성된다.

[verso-templates](https://github.com/leanprover/verso-templates)의 `package-docs` 템플릿이 우리가 원하는 바로 그 형태다:

```
package-docs/
├── zippers/        # 라이브러리 패키지 (subverso 의존)
│   └── Zippers.lean
└── manual/         # 문서 패키지 (verso 의존)
    ├── Docs.lean
    └── Main.lean
```

`manual/Docs.lean`:
```lean
set_option verso.exampleProject "../zippers"
set_option verso.exampleModule "Zippers"
```
`zippers/Zippers.lean`:
```lean
-- ANCHOR: Zipper
class Zipper (α : outParam (Type u)) … where …
-- ANCHOR_END: Zipper
```
문서 쪽에서:
````
```anchor Zipper
class Zipper (α : outParam (Type u)) … where …
```
````
→ 코드 블록의 내용이 **실제 소스와 다르면 빌드가 실패한다.** 문서와 코드가 절대 어긋나지 않는다.

추가로 쓸 수 있는 것: `{anchorTerm}`, `{anchorName}`, `{anchorInfo}`(`#eval` 출력 검증), `{docstring Foo}`, `{index}`, `{citep}`, `{margin}`, `{ref}`, `{theIndex}`.

**두 패키지로 쪼개는 이유** (템플릿이 명시하는 이유이기도 하다):
- 문서용 Lean 버전과 라이브러리용 Lean 버전을 분리할 수 있다.
- **실질적 이유**: Verso는 `plausible`에 의존하고 Mathlib도 `plausible`에 의존한다. 한 Lake 워크스페이스에 Mathlib + Verso를 같이 넣으면 전이 의존성 리비전 충돌 위험이 있다. 형제 패키지로 두면 각자 `lake-manifest.json`을 갖는다.
- 제약 하나: *"예제 프로젝트는 문서의 Verso가 쓰는 것과 같은 버전의 subverso에 의존해야 한다."* → 코드 패키지가 `subverso @ verso-v4.33.0`을 직접 require한다.

### 1.4 버전 선택

2026-08-20 기준 실제 릴리스 상황:

| 패키지 | 최신 안정 | 비고 |
|---|---|---|
| Lean 4 | `v4.33.0` (2026-08-10) | `v4.34.0-rc1`은 rc |
| Mathlib | 태그 `v4.33.0` | `lake exe cache get` 캐시 존재 |
| Verso | 태그 `v4.33.0` | Lean 릴리스마다 대응 태그 생성 |
| SubVerso | 태그 `verso-v4.33.0` | 의존성 없음(cross-version 호환 설계) → Mathlib과 충돌 없음 |

→ **전부 `v4.33.0` 계열로 핀한다.** 세 저장소가 같은 날 같은 번호로 릴리스되므로 정합성이 보장된다.

> 업그레이드 정책: Lean 새 안정판이 나오고 **Mathlib·Verso 대응 태그가 모두 나온 뒤**에만 올린다. rc는 쓰지 않는다. (§8 참고)

### 1.5 채점 메커니즘 조사

[robertylewis/lean4-autograder-main](https://github.com/robertylewis/lean4-autograder-main)이 검증된 레퍼런스다. 핵심:
- `ParametricAttribute`로 `@[autogradedProof 5]` 같은 애트리뷰트를 선언
- `Lean.collectAxioms`로 선언이 쓴 공리를 모으고, `sorryAx`가 있으면 실패
- 허용 공리: `Classical.choice`, `Quot.sound`, `propext`, `funext`

Lean 코어의 실제 API (`src/Lean/Util/CollectAxioms.lean`, v4.33.0):
```lean
public def collectAxioms [Monad m] [MonadEnv m] (constName : Name) : m (Array Name)
```
→ `CoreM`에서 바로 쓸 수 있고, import된 선언에 대해서도 동작한다 (olean에 사전 계산되어 저장됨).

우리는 Gradescope 연동이 필요 없으므로 훨씬 단순한 로컬 리포터를 만든다. 다만 **한 가지를 더 한다**: `sorry`가 그 선언 자체에서 왔는지, 선행 문제에서 전파된 것인지 구분한다.

```
Expr.hasSorry (해당 선언의 value)  →  본인이 비워둠           ⛔
그렇지 않은데 collectAxioms에 sorryAx →  선행 문제 미완성      ⚠️
sorryAx 없음                        →  통과                    ✅
```
이게 있어야 "1.1을 안 풀었더니 1.5도 실패로 뜬다"는 좌절을 막는다.

---

## 2. 프로젝트 목표와 비목표

### 목표
1. **읽으면서 실행할 수 있다.** 각 절의 정의를 `#eval`·`#guard`로 즉시 돌려본다.
2. **빈칸을 채우고 확인할 수 있다.** `sorry`를 지우고 `lake exe grade`로 확인한다.
3. **책의 명제가 Lean 정리다.** Reynolds의 Proposition 1.1~1.5, 2.1~2.8이 그대로 `theorem`이다. 증명을 "믿는" 게 아니라 커널이 검사한다.
4. **주석이 교재를 대신한다.** 책을 옆에 두지 않아도 파일만 읽고 흐름을 따라갈 수 있다.
5. **문서가 자동으로 나온다.** Verso로 HTML 책이 나오고, 그 안의 코드는 실제 소스와 동기화된다.

### 비목표
- Reynolds 책의 완역/전재 (저작권). 코드와 **요약·해설**만 쓴다.
- 19개 장 전부를 한 번에. **1~5장을 1차 목표**로 하고 이후는 스터디 진행 상황에 따른다.
- 성능. 평가기는 연료(fuel) 기반 참조 구현으로 충분하다.
- Mathlib 수준의 일반성. 필요하면 자체 정의하고 Mathlib 대응물을 주석으로 가리킨다.

---

## 3. 저장소 구조

```
tpl-in-lean/
├── README.md                     # 설치·실행·스터디 진행 (한국어)
├── AGENTS.md                     # 에이전트/기여자 규약 ← 별도 파일
├── STUDY.md                      # 주차별 진행표와 토론 질문
├── LICENSE                       # Apache-2.0
├── lean-toolchain                # leanprover/lean4:v4.33.0
├── lakefile.toml
├── lake-manifest.json
├── .gitignore                    # .lake/, _out/, *.olean
├── .devcontainer/devcontainer.json
├── .vscode/settings.json
├── .github/workflows/
│   ├── ci.yml                    # build + test + grade(answers) + lint
│   └── manual.yml                # Verso 빌드 → GitHub Pages 배포
├── scripts/
│   ├── serve.py                  # Verso HTML 로컬 서빙 (CSP/캐시 헤더 처리)
│   └── check-anchors.sh          # ANCHOR 마커 짝 검사
│
├── Reynolds.lean                 # 루트 모듈 (`lake exe mk_all`로 자동 생성)
├── Reynolds/
│   ├── Init.lean                 # 공통 진입점 — 모든 파일이 전이적으로 import (CSlib 방식)
│   ├── Compat.lean               # CSlib API 재수출 층 (churn 방어벽)
│   ├── Prelude.lean              # State, σ[v ↦ n], 공통 표기, 스타일 옵션
│   ├── Meta/
│   │   ├── Exercise.lean         # @[exercise "1.4a" (stars := 2)] 애트리뷰트
│   │   └── Report.lean           # 채점 리포트 자료구조·포매팅
│   │
│   ├── Answers/                  # ★ 진리의 원천. sorry 금지. Verso가 참조.
│   │   ├── Ch01.lean             # 장 루트 (하위 전체 import)
│   │   ├── Ch01/
│   │   │   ├── Syntax.lean       # §1.1 추상 구문
│   │   │   ├── Notation.lean     # §1.1 구체 구문 (Lean 매크로 DSL)
│   │   │   ├── Semantics.lean    # §1.2 표시적 의미론
│   │   │   ├── Validity.lean     # §1.3 타당성과 추론
│   │   │   ├── FreeVars.lean     # §1.4 자유변수 · 일치 정리
│   │   │   ├── Substitution.lean # §1.4 치환 · 치환 정리 · 이름 바꾸기 정리
│   │   │   ├── Initiality.lean   # §1.1 보론: 시작 대수(initial algebra)
│   │   │   └── Ex.lean           # 책 연습문제 1.1~1.7
│   │   ├── Ch02.lean
│   │   └── Ch02/
│   │       ├── Syntax.lean       # §2.1
│   │       ├── Notation.lean
│   │       ├── Domain.lean       # §2.3 도메인·연속함수 (자체 구축)
│   │       ├── Fixpoint.lean     # §2.4 최소 고정점 정리 · Scott 귀납법
│   │       ├── Semantics.lean    # §2.2 + §2.4 while
│   │       ├── Interpreter.lean  # 실행 가능한 연료 기반 해석기 + 적합성
│   │       ├── FreeVars.lean     # §2.5 FV, FA, 일치 정리
│   │       ├── Substitution.lean # §2.5 치환·별칭(aliasing)·이름 바꾸기
│   │       ├── Sugar.lean        # §2.6 for 명령
│   │       ├── ArithErrors.lean  # §2.7 산술 오류 (연산 매개변수화)
│   │       ├── FullAbstraction.lean # §2.8 건전성·완전 추상성
│   │       ├── MathlibBridge.lean   # Mathlib ωCPO 대응표
│   │       └── Ex.lean           # 책 연습문제 2.1~2.10
│   │
│   └── Exercises/                # ★ 학습자용. 구조 동일, 채울 곳만 sorry.
│       ├── Ch01.lean
│       ├── Ch01/…                # Answers와 1:1 대응
│       ├── Ch02.lean
│       └── Ch02/…
│
├── ReynoldsTests.lean            # lake test 진입점
├── ReynoldsTests/
│   ├── Ch01.lean                 # #guard / #guard_msgs 골든 테스트
│   ├── Ch02.lean
│   └── AnswersAreComplete.lean   # Answers에 sorry 없음을 CI에서 강제
├── Grade.lean                    # lake exe grade 진입점
│
└── manual/                       # ★ 별도 Lake 패키지 (Verso)
    ├── lean-toolchain            # v4.33.0 (코드 패키지와 동일하게 유지)
    ├── lakefile.toml
    ├── lake-manifest.json
    ├── Main.lean
    ├── Manual.lean               # 책 루트 문서
    └── Manual/
        ├── Intro.lean            # 이 프로젝트 사용법
        ├── Ch01.lean
        ├── Ch02.lean
        └── Refs.lean             # 참고문헌 (citep 대상)
```

### 3.1 왜 `Exercises`/`Answers` 두 트리인가

세 가지 안을 검토했다.

| 안 | 장점 | 단점 | 판정 |
|---|---|---|---|
| A. 단일 트리 + `sorry` | 중복 없음 | 정답 비교 불가, Verso가 참조할 완성 코드 없음 | ✗ |
| B. 단일 소스 + 생성 스크립트 (Mathematics in Lean 방식) | 중복 없음, 항상 동기화 | 빌드 단계 추가, 마커 문법 학습 필요, 생성물 커밋 여부 논쟁 | △ |
| C. **2트리 (fpinscala 방식)** | 단순, 익숙, Verso 참조 대상 명확, 정답 비교 쉬움 | 파일 중복 | **✓ 채택** |

C의 중복 비용은 CI가 흡수한다: `ReynoldsTests/AnswersAreComplete.lean`이 Answers의 sorry-free를 강제하고, `scripts/check-anchors.sh`가 두 트리의 `@[exercise]` 태그 집합이 일치하는지 검사한다.

**의존 방향 규칙**
- `Answers/ChNN` → `Answers/Ch(NN-1)` (정상적인 누적)
- `Exercises/ChNN` → **`Answers/Ch(NN-1)`** ← 중요
  - 즉 **각 장은 독립적으로 풀 수 있다.** 1장을 건너뛰고 2장을 풀어도 된다.
  - 이전 장의 `sorry`가 다음 장으로 전파되어 채점을 오염시키는 문제를 원천 차단한다.
- 장 **내부**에서는 `Exercises/ChNN/A` → `Exercises/ChNN/B` 의존이 생긴다. 이건 채점기의 ⚠️(선행 미완성) 판정으로 처리한다.

---

## 4. 빌드 설정

### 4.1 `lean-toolchain`
```
leanprover/lean4:v4.33.0
```

### 4.2 `lakefile.toml` (루트 = 코드 패키지)

CSlib의 `lakefile.toml`을 본으로 삼는다.

```toml
name = "tpl-in-lean"
version = "0.1.0"
defaultTargets = ["Reynolds"]
testDriver = "ReynoldsTests"
lintDriver = "batteries/runLinter"     # CSlib와 동일

[leanOptions]
autoImplicit = false
relaxedAutoImplicit = false
linter.missingDocs = true              # 모든 공개 선언에 docstring 강제
weak.linter.mathlibStandardSet = true  # Mathlib 표준 린터 세트
weak.linter.flexible = true

# CSlib v4.33.0 은 Lean v4.33.0 + Mathlib v4.33.0 위에서 돈다.
# mathlib 은 cslib 을 통해 전이적으로도 들어오지만, 버전을 눈에 보이게 하려고 명시한다.
# 두 require 의 rev 가 같으므로 Lake 가 충돌 없이 해결한다.
[[require]]
name = "cslib"
git = "https://github.com/leanprover/cslib"
rev = "v4.33.0"

[[require]]
name = "mathlib"
scope = "leanprover-community"
rev = "v4.33.0"

[[require]]
name = "subverso"
git = "https://github.com/leanprover/subverso"
rev = "verso-v4.33.0"

[[lean_lib]]
name = "Reynolds"

[[lean_lib]]
name = "ReynoldsTests"
leanOptions = { weak.linter.style.header = false }

[[lean_exe]]
name = "grade"
root = "Grade"
```

> `linter.missingDocs = true`는 강제 규율이다. "주석을 쉽고 자세하게"라는 목표를
> 사람의 선의가 아니라 **빌드 실패**로 보장한다.

### 4.2.1 `Reynolds/Init.lean` — CSlib 방식의 공통 진입점

CSlib는 *"모든 `Cslib/` 파일은 `Cslib.Init`을 전이적으로 import해야 한다"* 는 규칙을 두고
테스트로 강제한다. 기본 린터·태틱 설정을 한 곳에 모으기 위해서다. 그대로 따른다.

```lean
module

public import Cslib.Init          -- CSlib 기본 린터/태틱 (Mathlib.Init 포함)
public import Reynolds.Compat     -- CSlib API 재수출 층 (§1.2 참고)

/-! # Reynolds 프로젝트 공통 진입점
모든 `Reynolds/` 파일이 (전이적으로) 이 파일을 import한다. -/
```

### 4.2.2 `Reynolds/Compat.lean` — CSlib 재수출 층

CSlib API 변경의 충격을 한 파일에 가둔다.

```lean
module
public import Cslib.Foundations.Data.HasFresh
public import Cslib.Foundations.Syntax.HasSubstitution
public import Cslib.Foundations.Syntax.HasAlphaEquiv
public import Cslib.Foundations.Logic.InferenceSystem

/-! CSlib에서 쓰는 것만 골라 우리 이름공간으로 재수출한다.
    CSlib가 이름을 바꾸면 **이 파일만** 고치면 된다. -/

namespace Reynolds
public export Cslib (HasFresh HasSubstitution HasAlphaEquiv)
end Reynolds
```

### 4.3 `manual/lakefile.toml`

```toml
name = "tpl-in-lean-manual"
defaultTargets = ["Manual", "build-manual"]

[[require]]
name = "verso"
git = "https://github.com/leanprover/verso"
rev = "v4.33.0"

[[lean_lib]]
name = "Manual"

[[lean_exe]]
name = "build-manual"
root = "Main"
```

`manual/Manual.lean` 상단:
```lean
set_option verso.exampleProject ".."
set_option verso.exampleModule "Reynolds.Answers.Ch01.Syntax"
```

### 4.4 Mathlib — 논쟁의 여지가 없다

CSlib가 Mathlib을 요구하므로 선택지가 아니다. 다만 **어차피 쓸 것이었다.**

**쓰는 이유**
- `Finset` — `FV(p)`를 자연스럽게 표현. (Lean 코어에는 `Finset`이 없다.)
- `Function.update` — Reynolds의 `[σ | v: n]` 그 자체.
- 순서론 API — `Preorder`, `PartialOrder`, `IsLUB`, `WithBot`, `ENat`.
- `OmegaCompletePartialOrder`, `ωSup`, `ωScottContinuous`, `Part.fix` — 2장 도메인 이론의 산업용 대응물. **직접 구축한 것과 비교하는 부록**의 재료.
- 태틱 — `omega`, `grind`, `decide`, `simp` 세트, `fun_prop`.

**대가 — 실측했다** (§10 프로브 참고)
- 빈 프로젝트 + Mathlib `v4.33.0` 기준: `lake update` → `lake exe cache get`(8690 파일) → `lake build`
  전 과정이 **약 3분 45초** (M시리즈 Mac, 유선 기준). 태그 릴리스라 캐시가 존재하므로 **Mathlib을 컴파일하지 않는다.**
  → README에 "첫 셋업 5분 내외"로 안내 가능. 네트워크에 따라 달라지므로 범위로 적는다.
- Mathlib `v4.33.0`은 새 모듈 시스템을 쓴다. **비-모듈 파일에서 import해도 정상 동작함을 프로브로 확인했다.**
  즉 모듈 시스템 채택은 강제가 아니라 **우리의 선택**이다 — 그리고 채택한다(§11).

---

## 5. 학습 루프 (핵심 UX)

```
┌─ 1. 읽는다 ────────────────────────────────────────────┐
│  Reynolds 책 §N.M  +  Reynolds/Exercises/ChNN/X.lean   │
│  (파일 상단 모듈 docstring이 그 절의 요약)              │
└────────────────────────────────────────────────────────┘
                    ↓
┌─ 2. 돌려본다 ──────────────────────────────────────────┐
│  #eval / #guard 로 정의가 뭘 하는지 즉시 확인          │
│  예: #eval (⟪x := x - 1; y := y + x⟫).run 100 σ₀       │
└────────────────────────────────────────────────────────┘
                    ↓
┌─ 3. 채운다 ────────────────────────────────────────────┐
│  @[exercise "1.4a" ★★] 가 붙은 sorry 를 지운다          │
│  VS Code 에서 목표(goal)를 보며 대화형으로 증명         │
└────────────────────────────────────────────────────────┘
                    ↓
┌─ 4. 확인한다 ──────────────────────────────────────────┐
│  $ lake exe grade --chapter 1                          │
│    ✅ 1.1  자유변수 정의                                │
│    ✅ 1.4a 일치 정리(coincidence theorem)               │
│    ⛔ 1.4b 치환 정리 — 본인 sorry                       │
│    ⚠️ 1.4c 유한 치환 따름정리 — 선행(1.4b) 미완성       │
│    12/17 (70%)                                          │
└────────────────────────────────────────────────────────┘
                    ↓
┌─ 5. 비교한다 ──────────────────────────────────────────┐
│  Reynolds/Answers/ChNN/X.lean 의 같은 이름 선언과 비교  │
│  (Answers에는 "왜 이렇게 증명했는가" 주석이 더 있다)     │
└────────────────────────────────────────────────────────┘
```

### 5.1 `@[exercise]` 애트리뷰트

```lean
/-- 연습문제 메타데이터. -/
structure ExerciseInfo where
  /-- 책의 번호 또는 명제 번호. 예: `"1.4"`, `"Prop 2.6"` -/
  id : String
  /-- 난이도. 1~3. -/
  stars : Nat := 1
  /-- 책의 참조 위치. 예: `"§1.4, Proposition 1.3"` -/
  ref : String := ""
```

사용:
```lean
@[exercise "Prop 1.1" (stars := 2) (ref := "§1.4, 일치 정리")]
theorem coincidence_intExp {e : IntExp V} {σ σ' : State V}
    (h : ∀ w ∈ e.fv, σ w = σ' w) : e.eval σ = e.eval σ' := by
  sorry
```

구현은 `ParametricAttribute ExerciseInfo` (autograder와 동일 패턴). `grade` 실행 파일이
`importModules`로 `Reynolds.Exercises`를 읽고, 애트리뷰트가 붙은 모든 상수를 순회한다.

### 5.2 판정 규칙 — 프로브로 설계가 한 번 바뀌었다

처음엔 `⛔ 본인 sorry` / `⚠️ 선행 미완성`을 구분하려 했다. **불가능하다는 것을 실측으로 확인했다.**

> **발견**: Lean v4.33.0에서 **정리(theorem)의 증명 항은 다른 모듈에서 볼 수 없다.**
> `env.find? n |>.value?` 가 `none`을 준다. 커널 환경(`env.checked.get`)을 강제해도,
> 애트리뷰트 적용 시점(`applicationTime := .afterCompilation`)에 잡아도 마찬가지다.
> 증명은 비동기로 엘라보레이트되며 애트리뷰트는 그 전에 실행된다.
> → `Expr.hasSorry` 기반 구분은 **원리적으로 안 된다.**

**설계 변경**: 구분하려 하지 말고, **구분할 필요가 없게 만든다.**

> **연습 독립성 원칙** — 모든 `@[exercise]` 선언은 **주어진 완성 자료만으로 풀 수 있어야 한다.**
> 한 연습이 다른 연습의 결과를 필요로 하면, 그 결과를 `ChNN/Given.lean`에 완성본으로 제공하거나
> 진술의 가설로 넣는다.

이러면 `sorry` 전파가 애초에 일어나지 않고, 판정이 2값으로 단순·정확해진다.

```lean
def verdict (env : Environment) (n : Name) : Verdict :=
  let axs := collectAxioms n
  if axs.contains ``sorryAx then .unfinished              -- ⛔ 미완성
  else if axs.all (· ∈ allowedAxioms) then .ok            -- ✅ 통과
  else .illegalAxiom (axs.filter (· ∉ allowedAxioms))     -- ❌ 불법 공리
```
허용 공리: `Classical.choice`, `Quot.sound`, `propext`, `funext`.
금지: `sorryAx`, `Lean.ofReduceBool` (= `native_decide` 사용 흔적).

**부수 효과**: 이 원칙은 그 자체로 좋은 교육 설계다. fpinscala의 연습도 서로 독립적이고,
"앞 문제를 못 풀면 뒤가 전부 막힌다"는 최악의 학습 경험을 구조적으로 없앤다.

### 5.2.1 `@[exercise]` 애트리뷰트 구현 제약 (프로브로 확인)

모듈 시스템에서 애트리뷰트를 만들 때 **세 가지 함정**이 있다. 전부 실측했다.

1. **`initialize`로 만든 환경 확장은 같은 모듈에서 쓸 수 없다.**
   → `Meta/Exercise.lean`(선언) / `Exercises/**`(사용) / `Grade.lean`(채점)을 **모듈로 분리**한다.
   ```
   error: cannot evaluate `[init]` declaration '…exerciseExt' in the same module
   ```
2. **모듈 시스템 기본 가시성은 private다.** `public initialize exerciseExt : … ← …` 로 명시해야 한다.
   ```
   error: (interpreter) unknown declaration '_private.…exerciseExt'
   ```
3. **`meta` 선언을 쓰는 곳에서는 `public meta import`가 필요하다.** Lean이 직접 알려준다.
   ```
   error: Invalid `meta` definition `_eval`, `instReprExerciseInfo` is not accessible here;
          consider adding `public meta import Probe.Ex.Attr`
   ```

**동작 확인된 최종 형태** (프로브 실행 결과):
```
[1.1] probe_done     stars=1  PASS ✅
[1.2] probe_todo     stars=2  ⛔ 미완성
[1.3] probe_blocked  stars=2  ⛔ 미완성
```

### 5.3 CLI

```
lake exe grade                     # Exercises 전체
lake exe grade --chapter 2         # 2장만
lake exe grade --answers           # Answers 검증 (CI용, 하나라도 실패 시 exit 1)
lake exe grade --json              # 기계 판독용
```

### 5.4 Gradescope — 검토했고, **쓰지 않는다**

[robertylewis/lean4-autograder-main](https://github.com/robertylewis/lean4-autograder-main)이
검증된 Lean용 Gradescope 오토그레이더다. 실제 운영 요건을 확인했다.

**비용**
- Gradescope의 **코드 오토그레이더는 무료 티어에 포함되지 않는다.** `Gradescope Complete`가 필요하고,
  이는 기관 라이선스 또는 학생당 유료 업그레이드다. 가격은 공개되어 있지 않고 문의해야 한다.
- 무료 `Basic for Teams`(기관당 첫 5명 강사)는 **종이/디지털 과제 채점**용이고 코드 채점이 빠져 있다.

**운영 부담** (autograder README가 명시하는 것)
- Docker 기반 채점 zip을 만들어 업로드해야 한다. Mathlib이 들어가므로
  컨테이너에 **최소 2 CPU / 3GB RAM**이 필요하고, 부족하면 "알아보기 어려운 OOM 오류"가 난다.
- 채점 판정을 [Comparator](https://github.com/leanprover/comparator) + `landrun` 샌드박스 +
  `lean4export`로 **커널에서 재검증**한다.
- **툴체인을 올릴 때마다 컨테이너를 다시 빌드해서 다시 업로드**해야 한다.

**결정적인 이유 — Gradescope가 푸는 문제를 우리는 갖고 있지 않다**

| Gradescope의 핵심 가치 | 우리 상황 |
|---|---|
| 100명+ 규모 제출물 수집·명단 관리·기한 | 회사 스터디. 인원이 한 자릿수 |
| **신뢰할 수 없는 제출물**을 안전하게 채점 (그래서 landrun 샌드박스와 Comparator가 있다) | 서로 신뢰하는 동료. 부정행위 방지 대상이 없다 |
| 학생 로컬 환경과 무관한 표준 채점 환경 | Devcontainer / Codespaces로 대체 가능 |
| 점수와 성적 산출 | 성적이 없다 |

즉 **Gradescope 아키텍처 복잡도의 대부분이 우리에게 불필요한 문제를 푸는 데 쓰인다.**

#### 대신: GitHub Actions 진행판 (비용 0, 유지보수 1파일)

Gradescope에서 우리가 실제로 원했던 것은 *"다 올바르게 풀었는지 중앙에서 확인"* 하나다.
그건 이미 만든 `lake exe grade --json`으로 충분하다.

```
각자 study/<이름> 브랜치에 push
        ↓
CI: lake exe grade --json --chapter N
        ↓
① $GITHUB_STEP_SUMMARY 에 마크다운 표로 렌더  ← 개인 채점 결과 페이지
② PR 체크 상태 pass/fail
③ (선택) progress/<이름>.json 스냅샷 → GitHub Pages 진행판
   → Verso 매뉴얼과 같은 사이트에 붙인다
```

GitHub Actions의 **Job Summary**는 마크다운 표를 그대로 렌더한다. 이것이 곧 채점 결과 화면이다.

| | Gradescope | GitHub Actions 진행판 |
|---|---|---|
| 비용 | 유료 (기관 라이선스) | 0 |
| 초기 셋업 | Docker 이미지 빌드 + 업로드 | workflow 파일 1개 |
| 툴체인 업그레이드 | 컨테이너 재빌드·재업로드 | `lean-toolchain` 한 줄 |
| 로컬/원격 동일성 | 다름 (컨테이너) | **동일** (`lake exe grade` 그대로) |
| 중앙 대시보드 | ✅ | ✅ (Job Summary + Pages) |
| 제출 이력 | ✅ | ✅ (git 히스토리 · PR) |
| 부정행위 방지 | ✅ | ❌ (필요 없음) |

**언제 Gradescope를 재검토하나**: 스터디가 사내 정식 교육 과정이 되어 수십 명 규모가 되고,
수료 판정이 필요해질 때. 그전까지는 과잉이다.

---

## 6. 주석·문서 규약 (요약)

> 전체 규약은 [`AGENTS.md`](./AGENTS.md)에 있다. 여기서는 설계 의도만.

### 3층 구조

| 층 | 위치 | 담당 | 분량 |
|---|---|---|---|
| **모듈 docstring** `/-! … -/` | 파일 최상단 | 이 파일이 책의 어느 절인가, 무엇을 다루는가, 읽는 순서, 핵심 아이디어 | 15~40줄 |
| **선언 docstring** `/-- … -/` | 모든 `def`/`theorem` | 책 기호 ↔ Lean 이름 대응, 직관, **왜 이렇게 형식화했는가** | 3~15줄 |
| **인라인 주석** `--` | 증명 안 | 케이스 구분, 까다로운 단계의 이유 | 짧게 |

### 원칙

1. **한국어로 쓴다.** 기술 용어는 첫 등장 시 `한글(English)` 병기: `표시적 의미론(denotational semantics)`. 이후로는 한글만.
2. **쉽고 자세하되 간결하게.** "왜"를 쓰고 "무엇"은 코드가 말하게 둔다. 코드를 한국어로 번역하지 않는다.
3. **책과 다르면 반드시 밝힌다.** docstring에 `**책과의 차이**:` 항목을 둔다.
4. **책 기호를 표기(notation)로 살린다.** `⟦e⟧ σ`, `σ[v ↦ n]`, `p / v ↦ e` — 책을 보며 코드를 읽을 수 있게.
5. **증명은 읽히게 쓴다.** 골프 금지. `induction … with` 구조를 드러내고 각 케이스에 한 줄 주석. `calc`를 적극 쓴다.
6. **Verso 인용 구간은 `ANCHOR`로 감싼다.**

```lean
-- ANCHOR: IntExp
/-- 정수 식(integer expression)의 추상 구문. … -/
inductive IntExp (V : Type u) where
  | num  : Int → IntExp V
  …
-- ANCHOR_END: IntExp
```

---

## 7. Verso 문서 설계

`manual/`은 **책의 대체물이 아니라 코드의 안내서**다. 저작권상 Reynolds 본문을 옮기지 않는다.

각 장 문서의 구성:
1. **이 장에서 배우는 것** — 3~5줄
2. **책의 절 ↔ Lean 파일 대응표**
3. **핵심 정의** — `anchor` 블록으로 실제 소스 인용 + 해설
4. **직접 해보기** — `#eval` 예시와 기대 출력 (`anchorInfo`로 검증)
5. **연습문제 목록** — 번호, 별점, 힌트
6. **더 읽을거리** — Mathlib/CSlib 대응물, 참고문헌(`citep`)

```
lake build && cd manual && lake exe build-manual
python3 ../scripts/serve.py 8000 -d _out/html-multi
```

> Verso HTML은 브라우저에서 파일로 직접 열면 코드 호버가 깨진다(JSON을 fetch하므로).
> 반드시 서버로 서빙한다. `scripts/serve.py`가 적절한 헤더를 붙인다.

---

## 8. CI

`.github/workflows/ci.yml`
1. `leanprover/lean-action` 사용 (elan + 캐시 자동)
2. `lake exe cache get`
3. `lake build` — **Answers는 경고 없이 통과해야 한다** (`sorry` 경고 포함)
4. `lake test` — `#guard` 단위 테스트
5. `lake exe grade --answers` — Answers 전체 sorry-free · 불법 공리 없음
6. `lake build Reynolds.Exercises` — Exercises는 `sorry` 경고는 허용, **에러는 불가**
7. `scripts/check-anchors.sh` — ANCHOR 짝 맞음 + 두 트리 `@[exercise]` id 집합 일치

`.github/workflows/manual.yml` — `main` 푸시 시 Verso 빌드 → GitHub Pages 배포.

**업그레이드 정책**: Lean 안정판 + Mathlib 태그 + Verso 태그가 **모두** 나온 뒤 한 PR에서
`lean-toolchain`, 두 `lakefile.toml`, 두 `lake-manifest.json`을 함께 올린다.

---

## 9. 로드맵

| 단계 | 범위 | 산출물 |
|---|---|---|
| **M0** | 스캐폴딩 | lakefile, toolchain, Prelude, Meta/Exercise, grade exe, CI, README, manual 뼈대 |
| **M1** | 1장 | §1.1~1.4 + 연습 1.1~1.7 + Verso Ch01 |
| **M2** | 2장 | §2.1~2.8 + 연습 2.1~2.10 + 실행 가능 해석기 + Verso Ch02 |
| **M3** | 3장 | Hoare 논리, 부분/전체 정확성, 피보나치·빠른 거듭제곱 검증 |
| **M4** | 4~5장 | 배열, 실패·입출력·연속체(continuation) |
| **M5** | 6~9장 | 전이 의미론 · 비결정성 · 병행성 · CSP — **CSlib `LTS`/`Bisimulation` 본격 활용** |

> 6장부터 CSlib의 `Foundations/Semantics/LTS/*`, `Languages/CCS/*`가 거의 그대로 쓰인다.
> 처음부터 CSlib에 올려 두는 이유가 여기 있다 — 나중에 붙이려면 전체 구조를 갈아엎어야 한다.

---

## 10. 검증 현황

### 10.1 프로브로 확인한 것 (2026-08-20 실측, Lean v4.33.0 + Mathlib v4.33.0)

| 항목 | 결과 |
|---|---|
| 비-모듈 파일에서 Mathlib(모듈 시스템) import | ✅ 정상 |
| `inductive` + `deriving DecidableEq, Repr` | ✅ |
| Reynolds 추상 구문 조건 — 생성자 단사성(`injection`) · 치역 서로소(`nofun`) | ✅ **공짜로 얻어짐** |
| **명제 1.1 일치 정리** 실제 증명 | ✅ 구조적 재귀로 성립 |
| `Function.update` + `σ[v ↦ n]` 커스텀 표기 | ✅ |
| `(5 : Int) / 0 = 0` (§2.7 나눗셈 규약) | ✅ `by decide` |
| `#eval` · `#guard` | ✅ |
| Mathlib ωCPO API — `Chain`·`ωSup`·`ωScottContinuous`·`ContinuousHom` | ✅ 4개 모두 존재, 시그니처 확인 |
| **전체 셋업 시간** (`lake update` + `cache get` 8690파일 + `build`) | ✅ **3분 45초** |
| **모듈 시스템** `module` / `public import` / `meta import` / `public meta import` / `@[expose] public section` | ✅ 정상 |
| **CSlib 통합** — `HasFresh`, `HasSubstitution`(`σ["x" := 3]`), `HasAlphaEquiv`(`e =α e`) | ✅ 전부 동작 |
| **CSlib 부분 빌드** | ✅ **266개 중 5개만 빌드** (`Lint.Basic`, `Init`, `HasFresh`, `HasSubstitution`, `HasAlphaEquiv`) — **37초** |
| `Finset.biUnion` + `HasFresh.fresh` 로 §1.4 fresh 변수 선택 | ✅ |
| `@[expose]` 덕에 downstream `decide` 환원 (`e.fv = {"x"}` by decide) | ✅ |
| `grind [IntExp.fv]` 자동화 | ✅ |
| `@[exercise]` `ParametricAttribute` + `collectAxioms` 채점 | ✅ (§5.2.1 제약 준수 시) |

### 10.2 프로브가 잡아낸 함정 (전부 설계에 반영)

1. **`Finset.biUnion`의 import 경로** — `Mathlib.Data.Finset.Lattice.Fold`에 **없다.**
   올바른 위치는 `Mathlib.Data.Finset.Union`. → AGENTS.md §1-7 "이름 추측 금지" 규칙이
   실제로 필요하다는 증거.
2. **`/-- … -/` docstring은 `#eval`/`#check` 앞에 붙일 수 없다** — 파서 오류가 난다.
   명령(command) 앞에는 `--` 주석을 쓴다. Verso 예제를 쓸 때 자주 걸린다.
3. **★ 모듈 파일은 비-모듈 파일을 import할 수 없다.** 반대는 된다.
   ```
   error: cannot import non-`module` Probe.Basic from `module`
   ```
   → **혼용 불가. 프로젝트 전체를 모듈 시스템으로 통일한다.** (루트 모듈에서 반드시 터진다)
4. **★ 정리의 증명 항은 다른 모듈에서 안 보인다** (`value? = none`).
   → 채점기 설계 변경. §5.2 참고.
5. **애트리뷰트 3중 제약** — `initialize` 모듈 분리 · `public initialize` · `public meta import`.
   → §5.2.1에 정리.

### 10.3 M0 스캐폴딩에서 추가로 검증한 것

| 항목 | 결과 |
|---|---|
| `lake lint` (`lintDriver = "batteries/runLinter"`) | ✅ 동작. `docBlame` 이 자동 생성 선언의 docstring 누락까지 잡는다 |
| **Verso `verso.exampleProject ".."`** — 루트를 상위로 가리키기 | ✅ 동작. 형제 디렉터리로 옮길 필요 없다 |
| **모듈 시스템 파일에서 SubVerso ANCHOR 추출** | ✅ 동작 |
| SubVerso 리비전 일치 (루트 `verso-v4.33.0` ↔ manual 전이 의존) | ✅ 둘 다 `3a75ede0…` |
| **문서-코드 동기화 강제** | ✅ 앵커 블록이 소스와 다르면 **문서 빌드가 실패**하고, 올바른 내용을 오류 메시지로 알려 준다 |
| `lake exe grade` 전 모드 (`--chapter` / `--answers` / `--json`) | ✅ |
| CI 게이트 구성 | ✅ (§10.4) |

### 10.4 M0 에서 드러난 함정 (전부 실측)

1. **★ 런타임 실행 파일은 `meta` 선언을 참조할 수 없다.**
   ```
   error: Invalid definition `collect`, may not access declaration `exerciseExt` marked as `meta`
   ```
   그런데 애트리뷰트(환경 확장)는 컴파일 시점에 동작해야 하므로 **반드시 `meta`** 여야 한다.
   → **해법**: `emit_exercise_registry` 커맨드가 컴파일 시점에 애트리뷰트를 읽어
   평범한 `def` 로 굳힌다. `Grade` 는 그 `def` 를 읽는다.
   이름은 `Name` 이 아니라 `String` 으로 담는다(인용이 안전하다). 읽는 쪽에서 `String.toName`.

2. **`meta` 코드는 `meta` 인스턴스만 본다.**
   `deriving Inhabited` 로 만든 인스턴스는 `meta` 문맥에서 안 보인다 →
   `meta instance : Inhabited ExerciseInfo := …` 를 따로 준다.

3. **`--wfail` 을 전체에 걸면 안 된다.** `Exercises` 는 의도적으로 `sorry` 를 갖는다.
   → 엄격 게이트는 **`lake build --wfail --iofail ReynoldsTests`**.
   `ReynoldsTests` 가 `Answers` 만 import 하므로 이 한 줄로 Answers 전체 + 테스트가 검사된다.

4. **`#guard` 는 컴파일 시점에 계산한다** → 테스트 모듈에 `public meta import` 가 필요하다.
   그리고 Mathlib 의 `hashCommand` 린터가 `#`-커맨드를 막으므로 테스트 lib 에서만 끈다.

5. **Verso 마크업은 `*굵게*`, `_강조_`** 다. `**굵게**` 는 오류다.

6. **`{docstring Foo}` 는 매뉴얼 패키지 환경의 상수만 가리킨다.**
   우리 라이브러리는 별도 패키지라 import 되지 않으므로 쓸 수 없다 → `anchor` 로만 인용한다.

7. **한국어 절 제목은 URL 슬러그가 `____________` 로 뭉개진다.** (기능에는 영향 없음)
   절마다 `%%% tag := "why-lean" %%%` 를 달아 두면 `find/?tag=…` 로 안정적인 상호 참조가 된다.
   슬러그 자체는 화장품이므로 감수한다.

8. **`Lean.addDocString` 은 `Syntax` 를 받는다.** 문자열로 붙이려면 `addDocStringCore`.

9. **`/-- … -/` docstring 은 선언에만 붙는다.** `#eval`·`#guard`·커스텀 커맨드 앞에서는
   파서 오류가 난다. `--` 를 쓴다. (M0 동안 세 번 밟았다.)

10. **한글은 Lean 식별자로 쓸 수 없다.** `section 추상구문조건` → 파서 오류.
    이름은 ASCII, 설명은 한국어.

### 10.5 아직 미검증

1. **`Part.fix` vs 자체 `lfp`** — 2장을 자체 구축으로 갈 때 Mathlib 의 Pi 순서 인스턴스와
   우리 평평한 순서 인스턴스가 충돌하지 않는지 (`State V = V → Int` 에 이미
   Pi 순서 인스턴스가 있다 → 타입 동의어로 감싸야 한다). **M2 에서 확인.**
2. **`lake exe mk_all` / `lint-style` / `shake`** — Mathlib 이 제공하는 실행 파일을
   우리 패키지에서 그대로 부를 수 있는지. 현재는 루트 모듈을 손으로 관리한다.
3. **Codex GitHub 리뷰** — 저장소를 GitHub 에 올린 뒤 플랜에서 실제로 붙는지.

---

## 11. Lean 4 최신 기능 활용 지도

> 부목표 "현재의 Lean 4에 익숙해지기"를 **추상적 다짐이 아니라 체크리스트**로 만든다.
> 각 기능을 **어디서 실제로 쓰는지** 지정해 두면, 진도가 나가면서 자연히 익힌다.

| 기능 | 쓰는 곳 | 학습 포인트 |
|---|---|---|
| **모듈 시스템** `module` / `public import` / `meta import` / `@[expose] public section` | 전 파일 | 현대 Lean 프로젝트의 기본. Mathlib·CSlib가 쓴다 |
| **`@[expose]`** | 구문·의미 파일 전부 | 정의의 **본문**이 downstream에서 환원되어야 `decide`·`#guard`가 동작 |
| **`grind` + `@[grind]`/`@[grind =]`/`@[grind ←]`** | 반복적인 케이스 증명 | 새 자동화. CSlib가 `attribute [grind <=] HasFresh.fresh_notMem` 식으로 쓴다 |
| **`omega`** | 2장 산술 (`Fⁿ⊥` 계산, `for` 반복 횟수) | 선형 정수 산술 자동화 |
| **`fun_prop`** | 2장 연속성 곁조건 | Mathlib이 `ωScottContinuous`에 `@[fun_prop]`을 달아 둠 |
| **매크로/엘라보레이터** `syntax` / `macro_rules` / `elab` / `app_unexpander` | `ChNN/Notation.lean` 객체 언어 DSL | **1장 최대의 재미.** "구체 구문 ↔ 추상 구문"을 직접 구현 |
| **환경 확장 + `ParametricAttribute`** | `Meta/Exercise.lean` 채점기 | 메타프로그래밍 심화. autograder와 동일 패턴 |
| **`Lean.collectAxioms` / `Expr.hasSorry`** | `Grade.lean` | 커널이 무엇을 믿는지 들여다보기 |
| **`termination_by` / `decreasing_by`** | 연습 2.10 디슈가링 종료성 | 정지성 증명이 곧 문제의 답 |
| **`deriving DecidableEq, Repr`** | 모든 구문 타입 | `#eval`·`decide` 없이는 학습 프로젝트가 성립하지 않음 |
| **`#guard` / `#guard_msgs`** | `ReynoldsTests/*` | 골든 테스트. 출력이 바뀌면 CI가 잡는다 |
| **`calc` / `conv` / `show`** | 책의 계산을 그대로 옮길 때 | Reynolds의 등식 사슬을 그대로 표현 |
| **`simp?` → 최소 `simp` 집합** | 전 증명 | `simp_all`로 뭉개지 않고 무엇이 쓰였는지 드러내기 |
| **Lake 위생 도구** `--wfail --iofail`, `lake lint`, `lint-style`, `shake`, `mk_all` | CI + 로컬 | 프로젝트 운영을 배우는 부분 |
| **Verso** `anchor` / `docstring` / `anchorInfo` | `manual/` | 문서-코드 동기화 |
| **CSlib 타입클래스** `HasFresh` / `HasSubstitution` / `HasAlphaEquiv` / `InferenceSystem` | 1·3장 | 생태계 라이브러리 사용법 |

**의도적으로 쓰지 않는 것**
- `native_decide` — 커널 밖 신뢰. 금지 (AGENTS.md §1-3).
- 새 `axiom` — 금지.
- `partial def` (해석기에) — 추론이 불가능해진다. 연료 방식을 쓴다.
- 자체 `Finset` 재구현 등 — Mathlib이 있는데 다시 만들지 않는다(교육 목적 예외는 명시).

---

## 12. 커밋·PR을 교재로 쓴다 (j2kun 방식)

[j2kun/mlir-tutorial](https://github.com/j2kun/mlir-tutorial)의 방식을 도입한다.
그의 표현대로:

> *"the series as a whole will be built up along with a GitHub repository that
> breaks down each step into clean, communicative commits"*

실제 히스토리를 확인해 보면 **글 1편 = PR 1개**로 정확히 대응한다:
```
6c0b9ce7  Analysis Passes (#28)
7a94ad86  Lowering Through LLVM (#26)
fac42a30  Dialect Conversion (#20)
```
그리고 README가 **글 목록 = 목차** 역할을 한다.

### 12.1 왜 이게 우리에게 특히 잘 맞는가

완성된 저장소는 **결과**만 보여준다. 그런데 학습에 필요한 것은 **과정**이다:

- "§1.4를 추가하려면 어떤 파일이 어떻게 바뀌는가"
- "이 정의를 바꾸니 어느 증명이 깨지는가" ← **Lean에서는 이게 특히 교육적이다**
- "이 형식화 결정을 왜 이렇게 했는가" (커밋 시점의 판단 기록)

fpinscala에는 없는 축이고, Lean처럼 **모든 것이 서로 얽혀 있는 언어**에서
"한 단계씩 쌓아 올리는 diff"의 가치는 훨씬 크다.

### 12.2 규칙

**단위: 1 PR = 책의 1개 절**

```
feat(ch01): §1.4 결합과 치환                     → PR #12
feat(ch02): §2.3 도메인과 연속 함수               → PR #18
feat(ch02): §2.4 최소 고정점 정리                 → PR #19
```

**PR 안의 커밋은 의미 단위로 쪼갠다.** 각 커밋은 **컴파일이 되어야 한다.**

```
1. feat(ch01): FV 정의 추가                     ← 정의만
2. feat(ch01): 명제 1.1 진술 (sorry)            ← 진술만. 컴파일 통과(경고)
3. feat(ch01): 명제 1.1 증명                    ← 증명 채움
4. feat(ch01): 명제 1.1 Exercises 스텁          ← 학습자용 빈칸
5. docs(ch01): §1.4 Verso 문서                  ← 서사
```

이 순서 자체가 교재다. **"진술 먼저, 증명 나중"** 이 커밋 2·3으로 드러나고,
이것이 정리 증명의 실제 작업 순서다.

**PR 본문 = 그 절의 학습 노트.** 템플릿(`.github/PULL_REQUEST_TEMPLATE.md`):

```markdown
## 책의 위치
Reynolds §1.4 (pp. 15–21)

## 추가한 것
- `IntExp.fv`, `Assert.fv`
- 명제 1.1 (일치 정리), 1.2, 1.3 (치환 정리), 1.5 (이름 바꾸기 정리)

## 형식화 결정
- `vnew` 선택을 `Cslib.HasFresh`로 추상화했다. Reynolds의 "표준 순서에서 첫 번째"는
  구현 세부이고, 필요한 성질은 "항상 새 이름을 얻는다"뿐이기 때문이다.
- `Assert.eval`이 `Prop`이라 일치 정리의 결론이 `=`가 아니라 `↔`다.

## 막혔던 곳
양화사 케이스에서 귀납 가설을 `σ σ'`에 대해 일반화하지 않아 3시간 헤맸다.
`induction p generalizing σ σ'`가 답이다. → Answers에 주석으로 남겼다.

## 책과 다른 점
없음 / (있으면 여기에)

## 스터디 토론 질문
1. Reynolds의 "추상 구문 조건"을 Lean이 공짜로 주는 이유는? 시작 대수와 어떻게 연결되나?
2. `Prop` vs `Bool` 경계가 §2.1의 ⟨assert⟩ vs ⟨boolexp⟩ 구분과 같은 이유는?
```

**머지 후 태그를 찍는다** — j2kun에게 없는 개선점.

```bash
git tag ch01-s04 -m "§1.4 결합과 치환"
```
그러면 이런 것이 가능해진다:
```bash
git checkout ch01-s04                 # 그 절 시점의 저장소 전체
git diff ch01-s03..ch01-s04           # 그 절이 추가한 전부
git log --oneline ch01-s03..ch01-s04  # 그 절을 만든 사고 과정
```

**머지 전략**: j2kun과 동일하게 **squash merge**(제목에 PR 번호). `main`의 `git log --oneline`이
그대로 목차가 된다. 세부 커밋은 PR 페이지에 영구 보존된다.

**PR 종류를 구분한다.**

| 접두사 | 성격 | 태그 | 목차 등재 |
|---|---|---|---|
| `feat(chNN):` | **교재가 되는 PR** — 책의 한 절 | ✅ | ✅ |
| `fix:` / `chore:` / `refactor:` / `docs:` | 정비 PR | ❌ | ❌ |

정비 PR은 태그를 찍지 않는다. 그래야 태그 목록이 목차로 남는다.

### 12.3 스터디 운영과의 결합

이게 진짜 이득이다. **PR이 스터디 세션의 형식이 된다.**

```
주중  각자 자기 브랜치에서 그 주 절의 Exercises 를 푼다
       ↓
발표 전  그 주 발표자가 자기 풀이를 PR 로 올린다
        (`study(ch01-s04): 지호 풀이` — 태그 없음, main 에 머지하지 않음)
       ↓
스터디  PR diff 를 화면에 띄우고 리뷰한다.
        "여기서 왜 generalizing 이 필요했나?" ← 코드 리뷰가 곧 토론
       ↓
정리   합의된 정답을 `feat(chNN): §N.M` PR 로 main 에 머지 + 태그
```

- 리뷰 코멘트가 **토론 아카이브**가 된다. 나중에 온 사람이 그 절의 PR을 읽으면
  당시 무엇이 헷갈렸는지까지 알 수 있다.
- GitHub Discussions를 절별로 열어 두면 PR과 상호 링크된다.

### 12.4 README = 목차

j2kun의 README를 그대로 본뜬다.

```markdown
## 목차

### 1장 술어 논리 (Predicate Logic)
| 절 | 문서 | PR | 태그 |
|---|---|---|---|
| §1.1 추상 구문 | [문서](https://…/ch01.html#abstract-syntax) | [#8](…/pull/8) | `ch01-s01` |
| §1.2 표시적 의미론 | [문서](…) | [#9](…) | `ch01-s02` |
| §1.3 타당성과 추론 | [문서](…) | [#11](…) | `ch01-s03` |
| §1.4 결합과 치환 | [문서](…) | [#12](…) | `ch01-s04` |
```

그리고 README 맨 위에 **"이 저장소를 읽는 법"**:

> 완성본을 위에서 아래로 읽지 마라. 위 표의 PR을 순서대로 따라가라.
> 각 PR은 책의 한 절이고, PR 본문이 그 절의 학습 노트이며,
> PR 안의 커밋이 그 절을 만든 사고 과정이다.

### 12.5 비용과 완화

| 비용 | 완화 |
|---|---|
| PR 규율 유지가 번거롭다 | PR 템플릿 + AGENTS.md 체크리스트로 기계화. 스터디가 끝나도 남는 자산이다 |
| 나중에 리팩터링하면 옛 태그의 코드가 현재와 달라진다 | 태그는 **그 시점의 스냅샷**임을 README에 명시. 리팩터링은 `chore` PR로 분리하고 태그를 다시 찍지 않는다 |
| 한 절이 너무 커서 PR이 비대해진다 | 절을 쪼갠다 (`§2.5 (1/2)`, `§2.5 (2/2)`). 실제로 §2.5·§2.8은 쪼개는 게 낫다 |
| 혼자 작업할 때 PR이 형식적이다 | 그래도 PR을 만든다. **PR 본문이 산출물**이지 리뷰가 산출물이 아니다 |

---

## 13. 저장소 운영 — 개인 → 조직 이전, 그리고 리뷰

### 13.1 이전 전략: **GitHub 네이티브 Transfer. Copybara 아님.**

계획: 개인 저장소로 시작 → 정리되면 HyperAccel 조직으로 이전.

**Copybara는 이 문제에 맞는 도구가 아니다.**
Copybara는 내부/외부 두 저장소를 **계속 동기화**하면서 **변환**(내부 전용 파일 제거, 경로 재작성)을
가하는 도구다. 우리는 **한 번 옮기면 끝**이고 걸러낼 내부 전용 콘텐츠도 없다.
Copybara를 도입하면 워크플로 하나를 영구히 떠안게 되는데 얻는 것이 없다.

> Copybara가 필요해지는 조건은 명확하다: ① 두 저장소를 **동시에 살려 두어야 하고**,
> ② 한쪽에만 있어야 할 파일이 있을 때. 둘 중 하나라도 아니면 쓰지 않는다.
> 만약 회사 정책상 공개 저장소가 불가하다면, 애초에 조직 private 저장소로 시작하면 된다.

**`git push --mirror`도 안 된다.** ← 이게 이 프로젝트에서 특히 중요하다.

우리 설계(§12)에서 **PR과 리뷰 코멘트가 교재다.** 미러 푸시는 커밋과 태그만 옮기고
**PR·이슈·리뷰 코멘트를 전부 버린다.** 문서의 PR 링크도 전부 깨진다.
즉 미러 푸시는 이 저장소의 핵심 산출물을 파괴한다.

**GitHub Transfer**(Settings → Danger Zone → Transfer ownership)는 이걸 보존한다:

| 항목 | Transfer | mirror push |
|---|---|---|
| 커밋 · 브랜치 · 태그 | ✅ | ✅ |
| **PR (번호 포함)** | ✅ | ❌ |
| **리뷰 코멘트** | ✅ | ❌ |
| 이슈 | ✅ | ❌ |
| 옛 URL 리다이렉트 | ✅ | ❌ |
| Actions secrets | ❌ 재등록 | ❌ |
| GitHub Pages URL | ❌ 바뀜 | ❌ |

### 13.2 이전 체크리스트

**사전 조건**
- [ ] HyperAccel 조직에서 **저장소 이전을 받을 권한**이 있는지 확인 (조직 설정에서 막아둘 수 있다)
- [ ] 개인 계정이 해당 조직의 멤버여야 한다

**지금부터 해 둘 준비** (이전 충격을 줄이는 실질적 조치)
- [ ] 문서 간 링크는 **상대 경로**로만 쓴다 — `./DESIGN.md`, `../docs/chapter-01.md`
- [ ] PR·태그 링크도 **저장소 상대 경로**로 쓴다 — `[#12](../../pull/12)`, `[ch01-s04](../../tree/ch01-s04)`
      → 소유자/저장소 이름이 바뀌어도 그대로 동작한다. **README 목차 표가 이 방식이어야 한다.**
- [ ] Pages 절대 URL은 **README 한 곳에만** 둔다 (이전 후 한 줄만 고치면 되게)
- [ ] 저장소는 **private으로 시작**한다. 공개 여부는 이전 후에 결정한다

**이전 당일**
- [ ] Transfer 실행
- [ ] Actions secrets / variables 재등록
- [ ] 브랜치 보호 규칙 재설정 (`main` 직접 푸시 금지 등)
- [ ] GitHub Pages 재활성화 + README의 Pages URL 갱신
- [ ] Codex GitHub App을 새 저장소에 다시 설치/승인
- [ ] 각자 로컬에서 `git remote set-url origin <새 URL>`
      (리다이렉트가 동작하지만 명시적으로 바꾸는 편이 낫다)
- [ ] 태그가 전부 따라왔는지 확인: `git ls-remote --tags origin`

### 13.3 PR 단위 Codex 리뷰

**두 층으로 나눈다. 역할이 다르다.**

| 층 | 도구 | 시점 | 목적 | 기록 |
|---|---|---|---|---|
| 1차 | **로컬 Codex** | 커밋/푸시 전 | 빠른 자기 점검 — 규약 위반, 오탈자, 명백한 문제 | 남지 않음 |
| 2차 | **Codex GitHub 리뷰** | PR 열릴 때 | 절 단위 품질 리뷰 | **PR에 영구 기록** ← 이게 핵심 |
| 3차 | 사람 (스터디) | 스터디 시간 | 이해·토론 | PR 코멘트 |

2차가 §12 설계와 정확히 맞물린다. **리뷰 코멘트가 PR에 남으므로,
나중에 그 절의 PR을 읽는 사람은 "무엇이 지적됐고 어떻게 고쳤는지"까지 읽게 된다.**
이건 완성된 코드만 봐서는 절대 알 수 없는 정보다.

#### ★ 핵심: 리뷰 지시를 제대로 줘야 유용하다

**Lean 프로젝트에서 AI 코드 리뷰의 기본값은 거의 쓸모없다.**
"이 증명이 맞나요?" 는 이미 **커널이 답했다.** `lake build`가 통과했으면 정리는 참이다.
그러므로 정확성을 리뷰하라고 시키면 리뷰어가 할 일이 없다.

이 프로젝트에서 리뷰의 가치는 **교육적 품질**에 있다:

```
❌ 리뷰하지 말 것          ✅ 리뷰할 것
─────────────────────     ─────────────────────────────────────────
증명이 참인가             docstring만 읽고 이 정의를 이해할 수 있는가
타입이 맞는가             형식화 결정이 정당한가 (책과 다르게 했다면 밝혔는가)
빌드가 되는가             책의 절·명제 번호 참조가 정확한가
                          증명이 읽히는가 (simp_all 한 줄로 뭉갠 곳)
                          표기가 CSlib NOTATION 관례를 따르는가
                          연습 독립성 원칙(§5.2)을 지키는가
                          Answers/Exercises 두 트리가 1:1로 대응하는가
                          한국어 용어 규약 (첫 등장 시에만 한글(English))
```

**AGENTS.md가 그대로 리뷰 기준이 된다.** Codex는 저장소 루트의 `AGENTS.md`를 규약으로 읽으므로,
우리가 이미 쓴 규약이 자동으로 리뷰 체크리스트가 된다. 별도 설정 파일을 만들 필요가 없다.
→ `AGENTS.md`에 **§12 리뷰 규약** 절을 두어 위 표를 명시한다.

#### 로컬 1차 리뷰

푸시 전에 diff를 리뷰받는다. 커밋 단위가 아니라 **PR 전체 diff** 기준이 낫다
(절 하나가 완결된 상태에서 봐야 판단이 선다).

```bash
lake build --wfail --iofail && lake test && lake exe grade --answers   # 먼저 기계 검증
codex review --base main                                              # 그 다음 사람/AI 리뷰
```
기계 검증을 먼저 통과시키는 순서가 중요하다. 빌드도 안 되는 코드를 리뷰시키면
리뷰어가 빌드 오류 이야기만 한다.

#### 리뷰가 스터디 리듬을 방해하지 않게

- Codex 리뷰는 **사람 리뷰 전 사전 통과 게이트**다. 여기서 걸리는 건 규약 위반이지 학문적 논점이 아니다.
- 학문적 토론은 **사람이** 스터디 시간에 한다. Codex 코멘트가 토론을 대체하지 않는다.
- Codex 코멘트에 동의하지 않으면 **반박하고 닫는다.** 근거를 코멘트로 남기면 그것도 기록이 된다.

> **주의**: Codex GitHub 코드 리뷰는 플랜에 따라 사용 가능 여부가 다르다.
> 저장소를 만들 때 실제로 붙는지 먼저 확인하고, 안 되면 로컬 1차 리뷰만으로도 충분하다.

---

## 부록 A. 참고 링크

- [fpinscala/fpinscala](https://github.com/fpinscala/fpinscala)
- [leanprover/cslib](https://github.com/leanprover/cslib) · [ORGANISATION.md](https://github.com/leanprover/cslib/blob/main/ORGANISATION.md) · [NOTATION.md](https://github.com/leanprover/cslib/blob/main/NOTATION.md)
- [leanprover/verso](https://github.com/leanprover/verso) · [verso-templates](https://github.com/leanprover/verso-templates)
- [Lake 문서](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/)
- [robertylewis/lean4-autograder-main](https://github.com/robertylewis/lean4-autograder-main)
- [Mathlib `Order.OmegaCompletePartialOrder`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/OmegaCompletePartialOrder.html)
- [Mathlib `Order.FixedPoints`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Order/FixedPoints.html)
