/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open Verso.Code.External

set_option verso.exampleProject ".."
set_option verso.exampleModule "Reynolds.Answers.Ch03.Derived"

#doc (Manual) "§3.3·§3.5 유도 규칙과 보충 규칙" =>
%%%
tag := "ch03-derived"
file := "ch03-derived"
number := false
%%%

CA·DA·CSP·CST는 Reynolds §3.5 p.68의 규칙이다. CA와 DA는 부분·전체 정확성
체계의 생성자이고, `Semantic.lean`의 독립 연습에서 각 건전성을 증명한다.
DA는 두 사후조건이 서로 달라도 쓸 수 있다. 결론의 사후조건은 둘의 선언이다.

CSP는 `{p} c {p}`를 명세 전제 없이 준다. `c`가 `p`의 자유 변수에 대입하지 않으면
충분하다. 발산하는 명령에도 적용되므로 CSP만으로 종료를 주장할 수는 없다.
CST는 `[p] c [q]`를 전제로 받아 `[p ∧ r] c [q ∧ r]`를 준다.
부분 정확성의 같은 형태는 `Hoare.frame`에서 CSP와 CA로 유도한다(p.69).

이 페이지는 책이 이미 있는 규칙만으로 더 유도하는 ISK(§3.5 p.66)·MSQₙ(§3.3 pp.60–61)·
RASₙ(§3.3 pp.61–62)도 함께 둔다. 아래의 ∃·치환 규칙은 책에 없는 보충 자료다.

# 상수 규칙
%%%
tag := "ch03-constancy"
file := "ch03-constancy"
number := false
%%%

`c`가 _대입하지 않는_ 변수에 대한 주장은 `c`를 지나도 그대로다.

````anchor stmtConstancy (module := Reynolds.Answers.Ch03.Derived)
/--
**상수 규칙.** `c` 가 대입하지 않는 변수에 대한 주장은 `c` 를 지나도 그대로다.

```
{ p } c { q }
-----------------------   FA(c) ∩ FV(r) = ∅
{ p ∧ r } c { q ∧ r }
```

요구하는 것은 `FV(r)` 과 `FA(c)` 의 서로소다 — `c` 가 `r` 의 변수를 **읽는** 것은 괜찮다.
명제 2.6(b) 가 `r` 의 변수가 안 변했음을, 명제 1.1 이 `r` 의 진릿값이 안 변했음을 준다.
-/
@[exercise "§3.5 constancy" 2]
theorem constancy_sound {p q r : Assert V} {c : Comm V} (hr : Disjoint c.fa r.fv)
    (h : ｛p｝c｛q｝) : ｛p ⋀ r｝c｛q ⋀ r｝
````

§2.5에서 자유 변수를 _읽기_(`FV`)와 _쓰기_(`FA`)로 가른 이유가 여기서 드러난다. 요구하는
것은 `FV(r)`과 `FA(c)`가 겹치지 않는 것뿐이다. `c`가 `r`의 변수를 읽는 것은 괜찮다.

# 보충 — 유령 변수의 ∃ 규칙
%%%
tag := "ch03-ghost-exists"
file := "ch03-ghost-exists"
number := false
%%%

*책과의 관계*: 이 규칙은 Reynolds §3.5 본문에 없다. 책은 `newvar`로 들여온 지역
변수가 명세 밖으로 안 새게 하는 데 집중하고, 사전조건에서만 쓰인 변수를 양화로
감추는 규칙은 다루지 않는다. 보충(앞으로 가는 대입 규칙, `Rules.lean`)의 사후조건에
든 `∃ v₀`가 이 규칙의 거울상이라 여기 둔다.

명령도 사후조건도 보지 않는 변수는 사전조건에서 존재 양화로 감출 수 있다.

````anchor stmtGhostExists (module := Reynolds.Answers.Ch03.Derived)
/--
**∃ 규칙.** 명령도 사후조건도 보지 않는 변수는 사전조건에서 존재 양화로 감출 수 있다.

```
{ p } c { q }
--------------------------   v ∉ FV(c) ∪ FV(q)
{ ∃v. p } c { q }
```

증인 `n` 을 꺼내 `σ[v := n]` 에서 전제를 쓴다. `σ` 와 `σ[v := n]` 은 `v` 를 뺀 모든 곳에서
같으므로 `c` 의 결과도 `FV(c) ∪ FV(q)` 위에서 같고 (명제 2.6(a)), `q` 는 그 위만 본다.
보충(앞으로 가는 대입 규칙, `Assign.lean`)이 사후조건에 `∃ v₀` 를 들고 있는 이유가
이 규칙의 거울상이다.
-/
@[exercise "보충 ghost-exists" 2]
theorem exists_sound {p q : Assert V} {c : Comm V} {v : V} (hc : v ∉ c.fv) (hq : v ∉ q.fv)
    (h : ｛p｝c｛q｝) : ｛Assert.quant .ex v p｝c｛q｝
````

힌트: 증인 `n`을 꺼내 `σ[v := n]`에서 전제를 쓴다. `Comm.coincidence_general`(명제
2.6(a))로 `c`의 결과가 `FV(c) ∪ FV(q)` 위에서 같음을 얻고, `coincidence_assert`로
`q`의 진릿값까지 옮긴다.

# 보충 — 치환 규칙
%%%
tag := "ch03-subst-rule"
file := "ch03-subst-rule"
number := false
%%%

*책과의 관계*: 이 규칙도 Reynolds §3.5 본문에 없다. 책 연습 3.11(`Ex 3.11`,
`BookExercises.lean`)이 전체 정확성과 전체 자유 변수 집합 위의 단사 치환을 묻는데,
여기서는 그 결과를 부분·전체 정확성 모두에 대해 쓰기 변수만 단사이면 되도록
일반화한다. 건전성은 1장의 명제 1.3과 2장의 명제 2.7을 합친 것이다.

````anchor stmtSubstRule (module := Reynolds.Answers.Ch03.Derived)
/--
**치환 규칙.** 명세의 변수 이름을 통째로 바꿔도 된다.

```
{ p } c { q }
------------------------------   쓰는 변수와 명세의 다른 자유 변수를 합치지 않음
{ p/δ } c/δ { q/δ }
```

치환된 쪽의 시작 상태 `σ'` 에서 원래 쪽의 시작 상태를 `fun w => σ' (δ w)` 로 만든다. 그러면

- `p/δ` 가 `σ'` 에서 참 ↔ `p` 가 그 상태에서 참 (명제 1.3),
- 두 실행의 결과가 `δ` 를 사이에 두고 일치 (명제 2.7, 연습 2.8 의 약한 판),
- `q` 가 원래 결과에서 참 ↔ `q/δ` 가 치환된 결과에서 참 (명제 1.3).

각 `u ∈ FA(c)`는 `FV(c) ∪ FV(p) ∪ FV(q)`의 다른 변수와 합쳐지면 안 된다.
둘 다 쓰이지 않는 변수끼리는 합쳐도 된다. `FA(c)` 내부의 단사성만으로는 부족하다.
책 연습 3.11의 전체 정확성과 전체 자유 변수 집합 위 단사 조건은 `BookExercises.lean`에서 다룬다.
-/
@[exercise "보충 subst-rule" 3]
theorem subst_rule_sound [HasFresh V] {p q : Assert V} {c : Comm V} (δ : Ren V)
    (hinj : ∀ u ∈ c.fa, ∀ w ∈ c.fv ∪ p.fv ∪ q.fv, δ u = δ w → u = w)
    (h : ｛p｝c｛q｝) : ｛p /ₛ δ.toSubst｝(c /ᶜ δ)｛q /ₛ δ.toSubst｝
````

힌트: 치환된 쪽의 시작 상태 `σ'`에서 원래 쪽의 시작 상태를 `fun w => σ' (δ w)`로 만들면
`Ex.Comm.substitution_weak`(연습 2.8)와 `substitution_assert`(명제 1.3)의 가설이 모두
`rfl`이다. 원래 쪽 실행을 나누고, 사전조건은 명제 1.3으로 원래 쪽에, 사후조건은 명제
1.3으로 되돌린다.

명제 2.7의 원래 진술은 이름 바꾸기가 `FV(c)` _전체에서_ 단사일 것을 요구한다. 그 조건으로는
읽기만 하는 변수 둘을 하나로 합치는 흔한 사용법이 막힌다. 연습 2.8은 조건을 "쓰는 변수
`u ∈ FA(c)`는 다른 어떤 변수와도 합치지 않는다"로 약화했고, 그 약한 판이 이 규칙에 정확히
들어맞는다. 2장에서 조건을 약화하라고 한 연습이 3장의 규칙 하나를 위한 준비였던 셈이다.

`FA(c)` 안에서만 단사인 것으로는 부족하다. `x, y ↦ y`로 합치면 참인
`{y = 0} x := 1 {y = 0}`이 거짓인 `{y = 0} y := 1 {y = 0}`이 된다. 쓰는 변수 `x`를 읽기만 하는
`y`와 합쳤기 때문이다.
