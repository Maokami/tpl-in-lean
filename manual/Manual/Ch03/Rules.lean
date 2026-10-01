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
set_option verso.exampleModule "Reynolds.Answers.Ch03.Hoare"

#doc (Manual) "§3.2~3.5 추론 규칙과 건전성" =>
%%%
tag := "ch03-rules"
file := "ch03-rules"
number := false
%%%

§3.1은 명세가 _무엇을 뜻하는지_ 정했다. 이 절들은 명세를 _증명하는 규칙_을 세운다. 규칙은
구문 위의 조작이고, 뜻과는 따로 있다. 그래서 규칙이 뜻에 대해 옳다는 것, 곧
_건전성_(soundness)을 따로 증명해야 한다.

# 규칙 하나가 생성자 하나
%%%
tag := "ch03-hoare"
file := "ch03-hoare"
number := false
%%%

§1.3의 `Proof`와 같은 모양이다. 전제가 인자이고 결론이 결과 타입이다. Lean의 화살표가
Reynolds의 가로선 노릇을 한다.

```anchor hoare (module := Reynolds.Answers.Ch03.Hoare)
/--
부분 정확성의 추론 체계. Reynolds §3.2–§3.5의 규칙들이다.

`[HasFresh V]` 가 붙는 이유는 대입 공리의 치환 `q /[v := e]` 가 새 결합자를 뽑기
때문이다 (§1.4).
-/
inductive Hoare [HasFresh V] : Assert V → Comm V → Assert V → Prop where
  /-- `{p} skip {p}` -/
  | skip (p : Assert V) : Hoare p .skip p
  /-- 대입 공리 `{q/v→e} v := e {q}`. **거꾸로** 간다 — 사후조건에서 사전조건을 만든다. -/
  | assign (q : Assert V) (v : V) (e : IntExp V) :
      Hoare (q /[v := e]) (.assign v e) q
  /-- 순차 합성. 가운데 단언 `r` 이 이음매이고, 규칙은 그것을 주지 않는다 — 유도하는
  사람이 고른다 (§3.4). -/
  | seq {p r q : Assert V} {c₀ c₁ : Comm V} :
      Hoare p c₀ r → Hoare r c₁ q → Hoare p (.seq c₀ c₁) q
  /-- 조건. 각 가지가 조건의 참·거짓을 사전조건에 더해 받는다. -/
  | ite {p q : Assert V} {b : BoolExp V} {c₀ c₁ : Comm V} :
      Hoare (p ⋀ b.toAssert) c₀ q → Hoare (p ⋀ .not b.toAssert) c₁ q →
      Hoare p (.ite b c₀ c₁) q
  /-- 반복. `i` 가 **불변식**이다. 한 바퀴를 견디면 몇 바퀴를 돌아도 견디고, 끝난 자리에서는
  조건이 거짓이다. -/
  | wh {i : Assert V} {b : BoolExp V} {c : Comm V} :
      Hoare (i ⋀ b.toAssert) c i → Hoare i (.wh b c) (i ⋀ .not b.toAssert)
  /-- DC (§3.5 p.67). 사후조건에만 지역 변수가 나타나지 않아야 한다. -/
  | dc (s : List (Comm V)) {p q : Assert V} {v : V} {e : IntExp V} {c : Comm V}
      (hq : v ∉ q.fv) :
      Hoare p (Comm.seqs s (.seq (.assign v e) c)) q →
      Hoare p (Comm.seqs s (.newvar v e c)) q
  /-- RN: 앞부분 뒤의 지역 결합 이름을 어느 방향으로든 바꾼다. -/
  | rename {p q : Assert V} {c c' : Comm V} :
      Comm.PrefixRename c c' → Hoare p c q → Hoare p c' q
  /-- SP (§3.3 p.59). 사전조건을 강화한다. -/
  | strengthen {p p' q : Assert V} {c : Comm V} :
      Stronger p' p → Hoare p c q → Hoare p' c q
  /-- WC (§3.3 p.59). 사후조건을 약화한다. -/
  | weaken {p q q' : Assert V} {c : Comm V} :
      Hoare p c q → Stronger q q' → Hoare p c q'
  /-- CA (§3.5 p.68). 같은 명령의 두 명세를 연언으로 합친다. -/
  | conj {p₀ p₁ q₀ q₁ : Assert V} {c : Comm V} :
      Hoare p₀ c q₀ → Hoare p₁ c q₁ → Hoare (p₀ ⋀ p₁) c (q₀ ⋀ q₁)
  /-- DA (§3.5 p.68). 서로 다른 사후조건도 선언으로 합친다. -/
  | disj {p₀ p₁ q₀ q₁ : Assert V} {c : Comm V} :
      Hoare p₀ c q₀ → Hoare p₁ c q₁ →
      Hoare (.bin .or p₀ p₁) c (.bin .or q₀ q₁)
  /-- CSP (§3.5 p.68). 쓰이지 않는 변수의 단언은 종료한 실행에서 보존된다. -/
  | constancy {p : Assert V} {c : Comm V} (hp : Disjoint c.fa p.fv) : Hoare p c p
```

규칙 몇 개에 눈여겨볼 점이 있다.

: 대입

  사후조건에서 사전조건을 _만든다_. 방향이 거꾸로다. 아래에서 따로 본다.

: 순차 합성

  가운데 단언 `r`이 전제에만 나온다. 규칙이 `r`을 정해 주지 않으므로 유도하는 사람이
  골라야 한다. §3.4의 주석 명세가 이 선택을 적는 방법이다.

: 반복

  `i`가 _불변식_이다. 규칙은 불변식을 찾아 주지 않는다. 프로그램 검증에서 사람이 하는 일의
  대부분이 이 선택이다.

: 결과 규칙

  전제 `Stronger p' p`는 `∀ σ, ⟦p'⟧ σ → ⟦p⟧ σ`다. 단언 사이의 함의가 _타당하다_는 의미적
  사실이고, 1장의 `Proof`로 증명했다는 뜻이 아니다. Hoare 논리는 단언 논리를 _오라클_로
  쓴다. 완전성을 말할 때 "단언의 타당성에 상대적으로"라는 단서가 붙는 이유다(책은
  완전성을 §3.8 참고문헌에서 7장의 `wp`로 미루고 본문에서 다루지 않는다; 보충
  `Wlp.lean`에서 미리 본다).

SP와 WC는 각각 생성자이고, `conseq`는 두 규칙을 이어 만든 제공 정리다.
다음 여섯 연습은 서로의 풀이에 의존하지 않는다.

```anchor stmtSpSound (module := Reynolds.Answers.Ch03.Semantic)
/-- SP (§3.3 p.59). 더 강한 사전조건에서 원래 사전조건을 얻는다. -/
@[exercise "§3.3 sp-sound" 1]
theorem sp_sound {P P' Q : State V → Prop} {c : Comm V}
    (hp : ∀ σ, P' σ → P σ) :
    (PartialCorrectS P c Q → PartialCorrectS P' c Q) ∧
    (TotalCorrectS P c Q → TotalCorrectS P' c Q)
```

```anchor stmtWcSound (module := Reynolds.Answers.Ch03.Semantic)
/-- WC (§3.3 p.59). 종료 상태에서 사후조건의 함의를 적용한다. -/
@[exercise "§3.3 wc-sound" 1]
theorem wc_sound {P Q Q' : State V → Prop} {c : Comm V}
    (hq : ∀ σ, Q σ → Q' σ) :
    (PartialCorrectS P c Q → PartialCorrectS P c Q') ∧
    (TotalCorrectS P c Q → TotalCorrectS P c Q')
```

```anchor stmtCaSound (module := Reynolds.Answers.Ch03.Semantic)
/-- CA (§3.5 p.68). 두 전체 명세의 종료 상태는 같은 명령의 결과이므로 같다. -/
@[exercise "§3.5 ca-sound" 2]
theorem ca_sound {P₀ P₁ Q₀ Q₁ : State V → Prop} {c : Comm V} :
    (PartialCorrectS P₀ c Q₀ → PartialCorrectS P₁ c Q₁ →
      PartialCorrectS (fun σ => P₀ σ ∧ P₁ σ) c (fun σ => Q₀ σ ∧ Q₁ σ)) ∧
    (TotalCorrectS P₀ c Q₀ → TotalCorrectS P₁ c Q₁ →
      TotalCorrectS (fun σ => P₀ σ ∧ P₁ σ) c (fun σ => Q₀ σ ∧ Q₁ σ))
```

```anchor stmtDaSound (module := Reynolds.Answers.Ch03.Semantic)
/-- DA (§3.5 p.68). 사전조건의 어느 성분이 참인지에 따라 그 명세를 사용한다. -/
@[exercise "§3.5 da-sound" 1]
theorem da_sound {P₀ P₁ Q₀ Q₁ : State V → Prop} {c : Comm V} :
    (PartialCorrectS P₀ c Q₀ → PartialCorrectS P₁ c Q₁ →
      PartialCorrectS (fun σ => P₀ σ ∨ P₁ σ) c (fun σ => Q₀ σ ∨ Q₁ σ)) ∧
    (TotalCorrectS P₀ c Q₀ → TotalCorrectS P₁ c Q₁ →
      TotalCorrectS (fun σ => P₀ σ ∨ P₁ σ) c (fun σ => Q₀ σ ∨ Q₁ σ))
```

```anchor stmtCspSound (module := Reynolds.Answers.Ch03.Semantic)
/-- CSP (§3.5 p.68). 명령이 쓰지 않는 자유 변수의 단언은 종료 시 보존된다.
명세 전제는 없으며, 발산해도 부분 정확성에는 문제가 없다. -/
@[exercise "§3.5 csp-sound" 2]
theorem csp_sound {p : Assert V} {c : Comm V} (hp : Disjoint c.fa p.fv) :
    PartialCorrect p c p
```

```anchor stmtCstSound (module := Reynolds.Answers.Ch03.Semantic)
/-- CST (§3.5 p.68). 전체 명세 전제에서 종료 상태를 얻고, 쓰이지 않는 단언을 보존한다.
부분 판도 함께 증명한다. 두 성분 모두 다른 연습의 답 없이 풀 수 있다. -/
@[exercise "§3.5 cst-sound" 2]
theorem cst_sound {P Q : State V → Prop} {r : Assert V} {c : Comm V}
    (hr : Disjoint c.fa r.fv) :
    (PartialCorrectS P c Q →
      PartialCorrectS (fun σ => P σ ∧ r.eval σ) c (fun σ => Q σ ∧ r.eval σ)) ∧
    (TotalCorrectS P c Q →
      TotalCorrectS (fun σ => P σ ∧ r.eval σ) c (fun σ => Q σ ∧ r.eval σ))
```

CA의 전체 판에서는 두 전제가 내놓은 종료 상태가 같은 명령의 결과임을 쓴다.
DA는 사전조건의 선언을 나눈다. CSP와 CST는 `Comm.eval_agree_outside_fa`와
`coincidence_assert`로 쓰이지 않는 변수의 단언을 옮긴다. CST의 종료 상태는 전제가 준다.

첫 유도는 대입 공리 하나와 결과 규칙 하나다.

```anchor firstDeriv (module := Reynolds.Answers.Ch03.Hoare)
/-- `{x = 1} x := x + 1 {x = 2}`. 공리가 주는 사전조건은 `x + 1 = 2` 고, `x = 1` 이 그보다
강하다. -/
theorem incr_hoare : Hoare (⟪ x = 1 ⟫ₐ) ⟪ x := x + 1 ⟫ᶜ (⟪ x = 2 ⟫ₐ) := by
  refine Hoare.strengthen ?_ (Hoare.assign _ "x" _)
  intro σ h
  simp [Assert.subst, IntExp.subst, Assert.eval, IntExp.eval, IntOp.denote, Cmp.denote] at h ⊢
  omega
```

# 유도 규칙 — ISK · MSQₙ · RASₙ
%%%
tag := "ch03-derived-rules"
file := "ch03-derived-rules"
number := false
%%%

SK와 SP만으로도 한 줄짜리 파생 규칙이 나온다.

```anchor isk (module := Reynolds.Answers.Ch03.Derived)
/-- **ISK (§3.5 p.66).** SK `{q} skip {q}`에 SP를 적용한다 — `q`를 `p ⇒ q`로 강화한다. -/
theorem Hoare.isk [HasFresh V] {p q : Assert V} (h : Stronger p q) : Hoare p .skip q :=
  Hoare.strengthen h (Hoare.skip q)
```

MSQₙ(§3.3 pp.60–61)은 순차 합성 n개를 결과 규칙으로 잇는 가족이다. MSQ₁은 `p₀ ⇒ q₀`,
`{q₀} c₀ {p₁}`, `p₁ ⇒ q₁`에서 `{p₀} c₀ {q₁}`를 내는데, 이미 있는 `Hoare.conseq`와 글자
그대로 같다. 책은 MSQₙ을 MSQₙ₋₁에 SQ와 결과 규칙 한 겹을 더 둘러 유도한다(가정 있는
증명의 예) — 그 한 겹을 `n = 2`에서 직접 보인다.

```anchor stmtMsq2 (module := Reynolds.Answers.Ch03.Derived)
/-- MSQ₂ (§3.3 p.60). MSQ₁(`Hoare.conseq`) 둘을 SQ로 잇는다. -/
theorem Hoare.msq2 [HasFresh V] {p₀ q₀ p₁ q₁ p₂ q₂ : Assert V} {c₀ c₁ : Comm V}
    (h₀ : Stronger p₀ q₀) (hc₀ : Hoare q₀ c₀ p₁) (h₁ : Stronger p₁ q₁)
    (hc₁ : Hoare q₁ c₁ p₂) (h₂ : Stronger p₂ q₂) : Hoare p₀ (.seq c₀ c₁) q₂
```

힌트: MSQ₁(`Hoare.conseq h₀ hc₀ h₁`)로 왼쪽 명령을 `{p₀} c₀ {q₁}`까지 올리고, WC
(`Hoare.weaken hc₁ h₂`)로 오른쪽을 `{q₁} c₁ {q₂}`까지 내린 뒤 SQ로 잇는다. 일반 n은 같은
겹을 반복할 뿐이다.

RASₙ(§3.3 pp.61–62)은 대입만 늘어선 명령 `v₀ := e₀ ; ⋯ ; vₙ₋₁ := eₙ₋₁`의 전제를 반복
치환 하나로 압축한다. 대입 목록은 머리 `(v, e)`와 꼬리로 나눠 `rasComm`·`rasPre`로 적는다
— 꼬리부터 치환해 머리로 돌아오면 책의 `(⋯(q/vₙ₋₁→eₙ₋₁)⋯)/v₀→e₀`다.

```anchor rasComm (module := Reynolds.Answers.Ch03.Derived)
omit [DecidableEq V] in
/-- RASₙ이 대입하는 명령. `Comm.seqs`처럼 머리를 앞에 두고 꼬리로 재귀한다. -/
def rasComm (v : V) (e : IntExp V) : List (V × IntExp V) → Comm V
  | [] => .assign v e
  | (v', e') :: l => .seq (.assign v e) (rasComm v' e' l)
```

```anchor rasPre (module := Reynolds.Answers.Ch03.Derived)
/-- RASₙ의 전제가 반복하는 치환. -/
def rasPre [HasFresh V] (q : Assert V) (v : V) (e : IntExp V) :
    List (V × IntExp V) → Assert V
  | [] => q /[v := e]
  | (v', e') :: l => (rasPre q v' e' l) /[v := e]
```

```anchor stmtHoareRas (module := Reynolds.Answers.Ch03.Derived)
/-- **RASₙ의 건전성 (§3.3 p.61).** AS를 n번, SQ를 n−1번 쓴다. -/
theorem Hoare.ras [HasFresh V] (q : Assert V) (v : V) (e : IntExp V) :
    ∀ l : List (V × IntExp V), Hoare (rasPre q v e l) (rasComm v e l) q
```

힌트: 꼬리가 비면 AS 하나(`Hoare.assign`). 아니면 AS로 머리 대입을 올리고 — 사후조건은
바로 꼬리의 `rasPre` — SQ로 꼬리의 재귀 호출에 잇는다.

책은 RASₙ을 "건전할 뿐 아니라 완전하다"고 특별히 짚는다 — 결론이 타당하면 전제도
타당하다는 뜻이다. 그 완전성이 새 채점 연습 `§3.3 ras-complete`다(`Derived.lean`).
`ReynoldsTests/Ch03.lean`이 책 p.61의 예 `{y > 3} x := 2×y; x := x−y {x ≥ 4}`를
`Hoare.ras`로 회귀 검사한다.

# 규칙마다 앞 장의 정리 하나
%%%
tag := "ch03-soundness"
file := "ch03-soundness"
number := false
%%%

건전성은 `Hoare`에 대한 구조적 귀납이다. AS·SQ·CD·WHP의 의미 판을 독립된 연습으로
증명하고, 아래 구문 판은 그 결과를 구문 단언에 적용하는 따름정리로 둔다.

대입 공리의 건전성은 1장 명제 1.4 그대로다. §1.4에서 포획을 피하는 치환을 애써 만든 것이
이 한 줄을 위해서였다.

```anchor assignSound (module := Reynolds.Answers.Ch03.Soundness)
/--
**대입 공리의 건전성 — 명제 1.4 한 줄.**

대입 뒤의 상태는 `σ[v := ⟦e⟧ σ]` 이고, 거기서 `q` 가 참이라는 것은 `σ` 에서 `q/v→e` 가
참이라는 것과 같다. 그것이 `substitution_single` 이다.
-/
theorem assign_sound [HasFresh V] (q : Assert V) (v : V) (e : IntExp V) :
    ｛q /[v := e]｝(Comm.assign v e)｛q｝ := by
  intro σ hp
  exact (as_sound ⟦q⟧ₐ v e).1 σ ((substitution_single q v e σ).mp hp)
```

`while` 규칙의 건전성은 §2.4의 Scott 귀납법이다. §3.1에서 본 두 사실, 곧 `⊥`가 모든
사후조건을 만족한다는 것과 `Sat`이 극한을 통과한다는 것이 귀납의 두 의무를 채운다.

```anchor whSound (module := Reynolds.Answers.Ch03.Soundness)
/--
**`while` 규칙의 건전성.** 의미 판 WHP를 구문 단언으로 옮긴다.

`PartialCorrectS.wh`가 Scott 귀납법으로 반복의 부분 정확성을 준다.
여기서는 `boolExp_eval_iff`로 본체의 전제와 반복의 사후조건을 구문 단언에 맞춘다.
-/
theorem wh_sound {i : Assert V} {b : BoolExp V} {c : Comm V}
    (hbody : ｛i ⋀ b.toAssert｝c｛i｝) : ｛i｝(Comm.wh b c)｛i ⋀ .not b.toAssert｝ := by
  have hsem : PartialCorrectS (fun σ => ⟦i⟧ₐ σ ∧ ⟦b⟧ᵇ σ = true) c ⟦i⟧ₐ := by
    intro σ hp
    exact hbody σ ((Assert.eval_and _ _ _).mpr ⟨hp.1, (boolExp_eval_iff b σ).mpr hp.2⟩)
  intro σ hi τ hτ
  obtain ⟨hiτ, hb⟩ := PartialCorrectS.wh hsem σ hi τ hτ
  exact (Assert.eval_and _ _ _).mpr
    ⟨hiτ, (Assert.eval_not _ _).mpr fun h => by
      have := (boolExp_eval_iff b τ).mp h
      simp [hb] at this⟩
```

§2.5의 명제 2.6, 명제 2.7에 이어 Scott 귀납법을 세 번째로 쓰는 자리다. 앞의 둘은 두 상태
사이의 _관계_를 다뤘고 이번에는 한 상태의 _술어_라 더 단순하다.

Reynolds §3.5 pp.67–68의 DC는 `s; v := e; c`의 명세를
`s; newvar v := e in c`로 옮긴다. `s`는 비어 있을 수도 있는 앞부분이다.
두 명령은 같은 본체를 실행하며, 선언만 끝에서 지역 변수 값을 복원한다.
그래서 사후조건 `q`가 `v`를 보지 않으면 충분하다. 사전조건과 초기값 식에는 이 조건이 없다.

예를 들어 바깥 `x = 3`에서 `newvar x := x + 1 in y := x`는 `y = 4`를 남긴다.
초기값의 `x`는 바깥 값이다. 앞부분에서 `x := 7`을 실행했다면 본체는 `y = 8`을 만들고,
선언이 끝난 뒤의 `x`는 7이다. 앞부분을 실행하기 전의 3으로 복원하면 안 된다.

연습 3.9의 DC 건전성을 부분·전체 정확성 한 쌍으로 증명한다.
`hQ`는 지역 변수의 값만 바꾸어도 사후조건의 진릿값이 같다는 뜻이다.

```anchor stmtDcSound (module := Reynolds.Answers.Ch03.Semantic)
/-- DC (§3.5 p.67, 연습 3.9). 사후조건만 지역 변수를 무시하면 된다.
앞부분이 끝난 상태의 변수 값을 복원하므로 사전조건과 초기값에는 신선함을 요구하지 않는다. -/
@[exercise "Ex 3.9 dc-sound" 2]
theorem dc_sound (s : List (Comm V)) (P Q : State V → Prop)
    (v : V) (e : IntExp V) (c : Comm V)
    (hQ : ∀ (σ : State V) (n : Int), Q (σ[v := n]) ↔ Q σ) :
    (PartialCorrectS P (Comm.seqs s (.seq (.assign v e) c)) Q →
      PartialCorrectS P (Comm.seqs s (.newvar v e c)) Q) ∧
    (TotalCorrectS P (Comm.seqs s (.seq (.assign v e) c)) Q →
      TotalCorrectS P (Comm.seqs s (.newvar v e c)) Q)
```

힌트: `Comm.eval_seqs`로 앞부분을 분리한다. 부분 정확성에서는 선언의 종료 결과를,
전체 정확성에서는 대입 판의 종료 결과를 출발점으로 삼는다.
`Flat.bind_eq_some_iff`와 `Flat.map_eq_some_iff`로 중간 상태와 복원 전 상태를 찾는다.

RN은 결합 이름을 바꾸어도 뜻이 같다는 규칙이다. 여기서는 같은 앞부분 뒤의 지역 선언을
두 방향으로 바꾸는 `Comm.PrefixRename`을 사용한다. 초기값 `e`는 결합 범위 밖이므로
그대로 두며, 새 이름 `w`의 조건은 정확히 `w ∉ FV(c) \ {v}`다.

```anchor stmtRnSound (module := Reynolds.Answers.Ch03.Semantic)
/-- RN (§3.5 p.68)의 명령 앞부분 판. §2.5의 지역 이름 바꾸기는 전체 상태의 의미를 보존한다. -/
@[exercise "§3.5 rn-sound" 2]
theorem rn_sound [HasFresh V] (p q : Assert V) {c c' : Comm V}
    (h : Comm.PrefixRename c c') :
    (PartialCorrect p c q → PartialCorrect p c' q) ∧
    (TotalCorrect p c q → TotalCorrect p c' q)
```

힌트: §2.5의 `Comm.newvar_rename`과 `Comm.seqs_congr`를 연결한다.
이 연습은 DC의 답을 사용하지 않는다.

책 p.68의 `{x = 0} newvar x := 1 in x := x + 1 {x = 0}`에는 DC를 바로 쓸 수 없다.
사후조건에 `x`가 있기 때문이다. 먼저 지역 이름을 `y`로 두고 DC를 적용한다.
그 명령을 RN으로 `x`로 바꾸면 바깥 `x = 0`을 유지하는 원래 명세를 얻는다.
`ReynoldsTests/Ch03.lean`은 이 유도를 부분·전체 정확성에서 각각 검사한다.

*책과의 차이*: 책의 RN은 단언과 명령에서 여러 결합 이름을 바꾸는 일반 규칙이다.
여기서는 앞부분 뒤의 지역 선언에 한정한다. 여러 번의 명령 이름 바꾸기는 규칙을 반복
적용하고, 단언의 이름 바꾸기는 의미 함의인 결과 규칙으로 옮긴다.

기존 `Hoare.newvar`와 `HoareT.newvar`는 AS·SQ·DC로 유도한 제공 API다.
그 API의 세 신선함 조건은 검증 조건 생성기와 최약 사전조건 코드의 기존 사용을 보존한다.
직접 DC를 사용할 때는 사후조건의 조건만 필요하다.

절들을 모으면 건전성이다.

```anchor sound (module := Reynolds.Answers.Ch03.Soundness)
/--
**건전성.** 유도된 명세는 타당하다.

`Hoare` 에 대한 구조적 귀납이고 절마다 위의 정리 하나다. 채점 연습이 아니다 — 각 절이
이미 연습이라 비우면 비운 것끼리 의존한다 (연습 독립성 원칙, `AGENTS.md` §1-9).
-/
theorem Hoare.sound [HasFresh V] {p q : Assert V} {c : Comm V} :
    Hoare p c q → ｛p｝c｛q｝ := by
  intro h
  induction h with
  | skip p => exact skip_sound p
  | assign q v e => exact assign_sound q v e
  | seq _ _ ih₀ ih₁ => exact seq_sound ih₀ ih₁
  | ite _ _ ih₀ ih₁ => exact ite_sound ih₀ ih₁
  | wh _ ih => exact wh_sound ih
  | dc s hq _ ih =>
    exact (dc_sound s _ _ _ _ _ (Assert.eval_update_of_notMem hq)).1 ih
  | rename hr _ ih => exact (rn_sound _ _ hr).1 ih
  | strengthen hp _ ih => exact (sp_sound hp).1 ih
  | weaken _ hq ih => exact (wc_sound hq).1 ih
  | conj _ _ ih₀ ih₁ => exact ca_sound.1 ih₀ ih₁
  | disj _ _ ih₀ ih₁ => exact da_sound.1 ih₀ ih₁
  | constancy hp => exact csp_sound hp
```

# 대입 공리는 왜 거꾸로인가
%%%
tag := "ch03-assign"
file := "ch03-assign"
number := false
%%%

`{q/v→e} v := e {q}`는 사후조건에서 출발한다. 앞으로 가는 판도 있다. Floyd의 판은 대입 전
값을 새 변수 `v₀`로 기억해 둔다.

```anchor floydPost (module := Reynolds.Answers.Ch03.Assign)
/-- `v` 를 `v₀` 로 바꾼 정수 식. 단언의 `p /[v := .var v₀]` 에 대응하는 식 판이다. -/
def IntExp.renameTo (e : IntExp V) (v v₀ : V) : IntExp V :=
  e /ₑ Function.update IntExp.var v (.var v₀)

/-- Floyd 의 사후조건 `∃ v₀. p/v→v₀ ∧ v = e/v→v₀`. `v₀` 가 대입 전의 `v` 값을 붙든다. -/
def floydPost [HasFresh V] (p : Assert V) (v v₀ : V) (e : IntExp V) : Assert V :=
  .quant .ex v₀ ((p /[v := .var v₀]) ⋀ .cmp .eq (.var v) (IntExp.renameTo e v v₀))
```

이 판도 건전하다(보충). 신선함 조건이 셋 필요하다.

```anchor stmtAssignForward (module := Reynolds.Answers.Ch03.Assign)
/--
**앞으로 가는 대입 규칙의 건전성.** 대입 뒤 상태 `σ[v := ⟦e⟧ σ]` 에서 `v₀` 의 값으로
옛 `σ v` 를 잡으면 된다. 신선함 조건 셋이 각각 든다.

- `v₀ ∉ FV(p)` — `v₀` 를 새로 잡아도 `p` 가 그대로 (명제 1.1).
- `v₀ ∉ FV(e)` — `v₀` 를 새로 잡아도 `e` 가 그대로 (명제 1.1, 식 판).
- `v₀ ≠ v` — 두 갱신이 서로를 안 건드린다.

치환은 명제 1.4 (`substitution_single`) 와 그 식 판 `substitution_intExp` 로 뜻으로 옮긴다.
-/
@[exercise "보충 assign-forward" 2]
theorem assign_forward_sound [HasFresh V] (p : Assert V) (v v₀ : V) (e : IntExp V)
    (h₀ : v₀ ∉ p.fv) (h₁ : v₀ ∉ e.fv) (h₂ : v₀ ≠ v) :
    ｛p｝(Comm.assign v e)｛floydPost p v v₀ e｝
```

힌트: 증인은 대입 전의 옛 값 `σ v` 다. `p/v→v₀` 쪽은 명제 1.4 와 1.1 로, `v = e/v→v₀`
쪽은 식 판 치환 정리로 뜻을 옮긴 뒤 `w = v` 인지로 나눈다.

그리고 두 판은 결과 규칙으로 서로를 유도한다. 앞으로 가는 판은 뒤로 가는 판의 사례에
전제 강화를 붙인 것이다.

```anchor forwardOfBackward (module := Reynolds.Answers.Ch03.Assign)
/-- **앞으로 가는 판은 뒤로 가는 판에서 나온다.** 공리가 주는 사전조건
`(∃ v₀. …)/v→e` 가 `p` 보다 약하다는 것이 `assign_forward_sound` 의 내용 그대로다. -/
theorem Hoare.assign_forward [HasFresh V] (p : Assert V) (v v₀ : V) (e : IntExp V)
    (h₀ : v₀ ∉ p.fv) (h₁ : v₀ ∉ e.fv) (h₂ : v₀ ≠ v) :
    Hoare p (.assign v e) (floydPost p v v₀ e) :=
  Hoare.strengthen
    (fun σ hp => (substitution_single _ v e σ).mpr
      (assign_forward_sound p v v₀ e h₀ h₁ h₂ σ hp _ rfl))
    (Hoare.assign _ v e)
```

반대 방향도 된다(`Hoare.assign_of_forward`). 그러니 두 판은 _힘이 같다_. Hoare가 뒤로
가는 판을 고른 이유는 힘이 아니라 _모양_이다. `∃`도 새 변수도 없이 치환 하나로 끝나고,
그 치환은 1장에서 이미 만들어 두었다.
