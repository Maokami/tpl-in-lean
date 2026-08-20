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
| 1 | 오리엔테이션 + §1.1 추상 구문 | `Ch01/Syntax.lean` | 스캐폴딩 완료 |
| 2 | §1.2 표시적 의미론 | `Ch01/Semantics.lean` | 스캐폴딩 완료 |
| 3 | §1.3 타당성과 추론 | `Ch01/Validity.lean` | 예정 |
| 4 | §1.4 결합과 치환 | `Ch01/FreeVars.lean`, `Substitution.lean` | 일부 |
| 5 | 1장 연습문제 | `Ch01/Ex.lean` | 예정 |
| 6~ | 2장 | `Ch02/*` | 예정 |

> 1장은 5주, 2장은 6주 정도로 잡는다. 2장(도메인 이론·최소 고정점)이 훨씬 무겁다.

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
