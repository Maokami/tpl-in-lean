<!--
1 PR = 책의 1개 절.  자세한 규약은 AGENTS.md §7.
정비 PR(fix/chore/docs/refactor)이면 아래를 지우고 한 줄로 설명해도 된다.
-->

## 책의 위치
Reynolds §N.M (pp. ..–..)

## 추가한 것
-

## 형식화 결정
<!-- 왜 이렇게 옮겼는가. 다른 선택지가 있었다면 왜 안 골랐는가.
     책과 다르게 했다면 여기와 docstring 양쪽에 밝힌다. -->
-

## 막혔던 곳
<!-- ★ 이 칸을 비우지 마라. 이 저장소에서 가장 재사용성 높은 정보다.
     같은 곳에서 다음 사람도 막힌다. -->
-

## 책과 다른 점
없음

## 스터디 토론 질문
1.
2.

---

### 체크리스트
- [ ] `lake build --wfail --iofail ReynoldsTests` 통과 (Answers·테스트 경고 0)
- [ ] `lake test` 통과
- [ ] `lake exe grade --answers` 통과
- [ ] Answers ↔ Exercises 가 파일·선언·`@[exercise]` 태그까지 1:1
- [ ] 모든 공개 선언에 docstring
- [ ] Verso 인용 대상에 `ANCHOR` 마커
- [ ] 커밋이 의미 단위로 쪼개져 있고 각각 컴파일된다
- [ ] (교재 PR이면) 머지 후 태그 `chNN-sMM` + README 목차 갱신

<!-- AI 도구를 썼다면 어떤 도구를 어떻게 썼는지 여기에 적는다. -->
