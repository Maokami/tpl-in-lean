# 스터디 진행

## 한 주의 흐름

```
주중   각자 자기 브랜치에서 그 주 절의 Exercises 를 푼다
        ↓
발표 전  그 주 발표자가 자기 풀이를 PR 로 올린다
        `study(ch01-s04): <이름> 풀이`  — main 에 머지하지 않는다
        ↓
스터디   PR diff 를 띄우고 함께 읽는다.
        "여기서 왜 귀납 가설을 일반화해야 했나?"  ← 코드 리뷰가 곧 토론
        ↓
정리    합의된 정답을 `feat(chNN): §N.M` PR 로 main 에 머지 + 태그
```

리뷰 코멘트가 **토론 아카이브**가 된다. 나중에 합류한 사람이 그 절의 PR을 읽으면
당시 무엇이 헷갈렸는지까지 알 수 있다.

## 준비물

- Reynolds 책 (해당 절)
- 이 저장소 (`lake exe cache get && lake build` 가 끝나 있을 것)
- VS Code + Lean 4 확장

## 진행표

| 주 | 책 | 파일 | 상태 |
|---|---|---|---|
| 1 | 오리엔테이션 + §1.1 추상 구문 | `Ch01/Syntax.lean` | 완료 |
| 2 | §1.2 표시적 의미론 | `Ch01/Semantics.lean` | 완료 |
| 3 | §1.3 타당성과 추론 | `Ch01/Validity.lean` | 완료 |
| 4 | §1.4 결합과 치환 | `Ch01/FreeVars.lean`, `Substitution.lean` | 완료 |
| 5 | 1장 연습문제 | `Ch01/Ex.lean`, `Ex/Summation.lean` | 완료 |
| 6 | §2.1~§2.2 구문과 의미 방정식 | `Ch02/Syntax.lean`, `Semantics.lean` | 구현·문서 완료 |
| 7 | §2.3 도메인과 연속 함수 | `Ch02/Domain.lean`, `Domain/*` | 구현·문서 완료 |
| 8 | §2.4 최소 고정점과 연료 해석기 | `Ch02/Fixpoint.lean`, `Eval.lean`, `Interpreter.lean` | 구현·문서 완료 |
| 9 | §2.5 자유 변수와 치환 | `Ch02/FreeVars.lean`, `Substitution.lean` | 구현·문서 완료 |
| 10 | §2.6~§2.7 문법 설탕과 산술 오류 | `Ch02/Sugar.lean`, `Sugar2.lean`, `ArithErrors.lean` | 구현·문서 완료 |
| 11 | §2.8 완전 추상성 + 2장 연습문제 | `Ch02/FullAbstraction*.lean`, `Ex.lean`, `Ex/*` | 구현·문서 완료 |
| 12 | §3.1~§3.3 명세, 규칙, 건전성 | `Ch03/Spec.lean`, `Hoare.lean`, `Soundness.lean`, `Assign.lean` | 구현·문서 완료 |
| 13 | §3.4~§3.6 주석 명세, 전체 정확성, 변수 선언 | `Ch03/Annot.lean`, `Total.lean` | 구현·문서 완료 |
| 14 | §3.7~§3.9 더 많은 규칙과 예제 | `Ch03/Derived.lean`, `Semantic.lean`, `Examples/*` | 구현·문서 완료 |
| 15 | §3.10 최약 사전조건과 완전성 | `Ch03/Wlp.lean` | 구현·문서 완료 |
| 16 | 3장 연습문제 | 책 목록 대조 후 | 예정 |

> 1장은 5주, 2장은 6주, 3장은 5주 정도로 잡는다. 2장(도메인 이론·최소 고정점)이 가장 무겁고,
> 3장은 1·2장의 정리를 다시 쓰는 장이라 앞의 두 장을 잘 따라왔다면 가볍다.

## 첫 주에 다룰 것

Lean을 처음 보는 사람이 대부분이므로 1주차는 절반을 도구에 쓴다.

1. **설치 확인** — `lake exe cache get`, `lake build`, VS Code에서 goal 패널 보기
2. **`Reynolds/Answers/Ch01/Syntax.lean` 같이 읽기**
   - `inductive` 가 곧 Reynolds의 추상 구문이다
   - 그가 §1.1에서 손으로 부과하는 세 조건이 **공짜로** 딸려 온다
3. **`#eval` / `#guard` 로 놀아 보기** — 정의가 실제로 계산된다는 감각
4. **`sorry` 하나 채워 보기** — `lake exe grade` 로 확인

## 토론 질문 (누적)

### 1장
- Reynolds가 프로그래밍 언어 책을 술어 논리로 시작하는 이유 셋은 무엇인가?
- `inductive` 가 왜 "다중 정렬 시작 대수(many-sorted initial algebra)"인가?
- `Assert.eval` 은 `Prop` 인데 `BoolExp.eval` 은 `Bool` 이다. 이 경계가 §2.1의
  ⟨assert⟩ / ⟨boolexp⟩ 구분과 같은 이유는?
- 추론 규칙 `p / ∀v.p` 는 건전한데 `p ⇒ ∀v.p` 는 타당하지 않다. 왜인가?

### 2장
- 풀기(unwinding) 방정식의 해가 유일하지 않다는 것이 왜 도메인 이론을 부르는가?
- `Option.bind` 가 Reynolds의 `f⊥⊥` 와 같다는 것은 무슨 뜻인가?
- 완전 추상성(full abstraction)이 "무엇을 관찰하기로 했는가"에 달렸다는 말의 의미는?

### 3장
- `⊥` 가 모든 사후조건을 만족한다는 사실은 `while` 규칙의 건전성 증명 어디에 쓰이는가?
  전체 정확성에서는 왜 같은 증명이 안 되는가?
- 대입 공리가 거꾸로인 이유는? Floyd 의 앞으로 가는 판과 힘이 같은데도 뒤로 가는 판을 고른
  이유는?
- 결과 규칙의 전제가 "증명 가능" 이 아니라 "타당" 인 것이 완전성 논의에 어떤 차이를 만드는가?
- 상수 규칙이 `FV(r) ∩ FV(c) = ∅` 가 아니라 `FV(r) ∩ FA(c) = ∅` 를 요구하는 이유는?
- 2장에서 `while` 의 뜻은 최소 고정점이었는데 wlp 는 최대 고정점이다. 왜 뒤집히는가?
  그런데 왜 그 증명은 여전히 최소 고정점 위의 Scott 귀납법인가?
