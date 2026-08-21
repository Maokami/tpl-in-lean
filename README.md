# tpl-in-lean

**John C. Reynolds, _Theories of Programming Languages_** (Cambridge University Press, 1998)를
**Lean 4** 로 따라 읽는 스터디 저장소.

책의 정의는 Lean 코드로, 설명은 한국어 주석으로, 명제는 **기계가 검사하는 정리**로 옮긴다.
연습문제는 빈칸을 채우고 `lake exe grade` 로 확인한다.

---

## 이 저장소를 읽는 법

> **완성본을 위에서 아래로 읽지 마라.** 아래 목차의 PR을 순서대로 따라가라.
> 각 PR은 책의 한 절이고, PR 본문이 그 절의 학습 노트이며,
> PR 안의 커밋이 그 절을 만든 사고 과정이다.

```bash
git log --oneline                 # main 의 히스토리가 곧 목차다
git diff ch01-s01..ch01-s02       # 그 절이 추가한 전부
git checkout ch01-s02             # 그 절 시점의 저장소 전체
```

---

## 시작하기

### 1. Lean 설치 (elan)

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```
Lean 버전은 `lean-toolchain`(`v4.33.0`)에 적혀 있고 elan이 알아서 맞춰 준다.

### 2. 의존성 받기 — **`lake build` 전에 반드시**

```bash
lake exe cache get     # Mathlib 미리 빌드된 파일 받기 (수천 개)
lake build
```

> `lake exe cache get` 을 건너뛰면 Mathlib을 **처음부터 컴파일**한다. 몇 시간 걸린다.
> 캐시를 쓰면 전체 셋업이 **5분 내외**다 (네트워크에 따라 다름).

### 3. 에디터

VS Code + [Lean 4 확장](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4).
파일을 열면 커서 위치의 증명 목표(goal)가 옆 패널에 뜬다. 이게 없으면 증명을 못 한다.

---

## 실습하는 법

1. `Reynolds/Exercises/ChNN/` 에서 `sorry` 를 찾는다
2. 지운다. 에디터에서 목표를 보며 채운다
3. 확인한다

```bash
lake exe grade                 # 전체
lake exe grade --chapter 1     # 1장만
```
```
| | 문제 | 난이도 | 선언 | 결과 |
|---|---|---|---|---|
| ⛔ | Prop 1.1a | ★★☆ | `Reynolds.Exercises.Ch01.coincidence_intExp` | 미완성 (sorry) |

**0 / 1 (0%)**
```
4. 막히거나 다 풀었으면 `Reynolds/Answers/ChNN/` 의 같은 이름 선언과 비교한다

막혔을 때 무엇부터 볼지는 [`docs/solving-guide.md`](./docs/solving-guide.md) 에 정리해 두었다.
이 저장소가 반복해 쓰는 증명 패턴 넷과 자주 만나는 오류 메시지가 들어 있다.

### 왜 `sorry` 만 보면 채점이 되는가

`lake build` 가 통과했다면 **커널이 이미 증명을 검사했다.**
남은 질문은 "그 증명이 `sorry` 같은 반칙에 기대는가" 뿐이고,
`lake exe grade` 는 `Lean.collectAxioms` 로 그것만 확인한다.
`native_decide` 처럼 커널 밖을 신뢰하는 것도 같이 걸러진다.

---

## 명령 모음

| 명령 | 용도 |
|---|---|
| `lake build` | 전체 빌드 (Exercises 의 `sorry` 경고 허용) |
| `lake build --wfail ReynoldsTests` | **엄격 모드** — Answers 와 테스트에 경고 0 |
| `lake test` | `#guard` 단위 테스트 |
| `lake exe grade` | 연습 채점 |
| `lake exe grade --answers` | Answers 검증 (CI용) |
| `lake exe grade --json` | 기계 판독용 |
| `lake lint` | 환경 린터 |

문서(Verso 책):
```bash
cd manual && lake exe build-manual
python3 ../scripts/serve.py 8000 -d _out/html-multi
```
> Verso HTML은 파일로 직접 열면 코드 호버가 깨진다. 반드시 서버로 띄운다.

---

## 목차

### 1장 술어 논리 (Predicate Logic)

| 절 | 파일 | PR | 태그 |
|---|---|---|---|
| 들어가기 전 | [`Background.lean`](./Reynolds/Answers/Ch01/Background.lean) | [#1](../../pull/1) | [`ch01-s01-s04`](../../tree/ch01-s01-s04) |
| §1.1 추상 구문 | [`Syntax.lean`](./Reynolds/Answers/Ch01/Syntax.lean) | [#1](../../pull/1) | 〃 |
| §1.2 표시적 의미론 | [`Semantics.lean`](./Reynolds/Answers/Ch01/Semantics.lean) | [#1](../../pull/1) | 〃 |
| §1.3 타당성과 추론 | [`Validity.lean`](./Reynolds/Answers/Ch01/Validity.lean) | [#1](../../pull/1) | 〃 |
| §1.4 자유 변수와 일치 정리 | [`FreeVars.lean`](./Reynolds/Answers/Ch01/FreeVars.lean) | [#1](../../pull/1) | 〃 |
| §1.4 치환 | [`Substitution.lean`](./Reynolds/Answers/Ch01/Substitution.lean) | [#1](../../pull/1) | 〃 |
| 심화 A · 대수와 초기성 | [`Depth/Algebra.lean`](./Reynolds/Answers/Ch01/Depth/Algebra.lean) | [#1](../../pull/1) | 〃 |
| 심화 B · 시그니처 함자와 Lambek | [`Depth/SignatureFunctor.lean`](./Reynolds/Answers/Ch01/Depth/SignatureFunctor.lean) | [#1](../../pull/1) | 〃 |
| 심화 A · 치환은 bind 다 | [`Depth/TermMonad.lean`](./Reynolds/Answers/Ch01/Depth/TermMonad.lean) | [#1](../../pull/1) | 〃 |
| §1.1 구체 구문 · DSL | [`Notation.lean`](./Reynolds/Answers/Ch01/Notation.lean) | [#2](../../pull/2) | [`ch01-ex01-ex04`](../../tree/ch01-ex01-ex04) |
| §1.1 실현 · 연습 1.3 | [`Realizations.lean`](./Reynolds/Answers/Ch01/Realizations.lean) | [#2](../../pull/2) | 〃 |
| 연습 1.1 · 1.2 · 1.4 | [`Ex.lean`](./Reynolds/Answers/Ch01/Ex.lean) | [#2](../../pull/2) | 〃 |
| 연습 1.5 · 1.6 합 식 | [`Ex/Summation.lean`](./Reynolds/Answers/Ch01/Ex/Summation.lean) | [#3](../../pull/3) | [`ch01-ex05-ex06`](../../tree/ch01-ex05-ex06) |

1장 본문은 절 단위로 PR 을 쪼개지 못하고 한 번에 올라왔다. 뼈대가 서로 얽혀 있었기 때문이다.
연습 PR 부터는 [`AGENTS.md` §7.1](./AGENTS.md) 대로 단위를 나눈다.

심화 트랙이 무엇이고 왜 그 자리에 있는지는 [`docs/depth-track.md`](./docs/depth-track.md).

### 2장 단순 명령형 언어 (The Simple Imperative Language)

| 절 | 파일 | PR | 태그 |
|---|---|---|---|
| §2.1 추상 구문 | [`Syntax.lean`](./Reynolds/Answers/Ch02/Syntax.lean) | [#4](../../pull/4) | [`ch02-s01`](../../tree/ch02-s01) |
| §2.1 구체 구문 · 명령 DSL | [`Notation.lean`](./Reynolds/Answers/Ch02/Notation.lean) | [#4](../../pull/4) | 〃 |

2장은 절 단위로 PR 을 나눈다. 전체 설계는 [`docs/chapter-02.md`](./docs/chapter-02.md).

> 링크는 저장소가 조직으로 이전되어도 안 깨지도록 **상대 경로**로 쓴다:
> `[#12](../../pull/12)`, `[ch01-s04](../../tree/ch01-s04)`

---

## 문서

| 파일 | 내용 |
|---|---|
| [`DESIGN.md`](./DESIGN.md) | 조사·설계 전체. 왜 이런 구조인가 |
| [`AGENTS.md`](./AGENTS.md) | 작업 규약 (사람·AI 공통). **기여 전 필독** |
| [`STUDY.md`](./STUDY.md) | 스터디 진행 방식 |
| [`docs/solving-guide.md`](./docs/solving-guide.md) | **연습 푸는 법** — 막혔을 때 먼저 볼 것 |
| [`docs/depth-track.md`](./docs/depth-track.md) | 심화 트랙 설계 |
| [`docs/chapter-01.md`](./docs/chapter-01.md) | 1장 형식화 상세 설계 |
| [`docs/chapter-02.md`](./docs/chapter-02.md) | 2장 형식화 상세 설계 |

## 의존성

| | 버전 | 역할 |
|---|---|---|
| [Lean 4](https://lean-lang.org) | `v4.33.0` | 언어 · 증명 보조기 |
| [Mathlib](https://github.com/leanprover-community/mathlib4) | `v4.33.0` | `Finset`, 순서론, 태틱 |
| [CSlib](https://github.com/leanprover/cslib) | `v4.33.0` | `HasFresh`, 치환·α-동치 표기, (6장~) LTS |
| [SubVerso](https://github.com/leanprover/subverso) | `verso-v4.33.0` | Verso 문서가 이 코드를 인용하기 위해 |

## 라이선스

코드와 문서는 Apache-2.0 ([`LICENSE`](./LICENSE)).
Reynolds의 책 본문은 포함하지 않는다 — 요약과 해설, 그리고 Lean 코드만 있다.
