/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Exercises.Ch03.Total

/-!
# §3.3·§3.5 유도 규칙, 그리고 보충 규칙

Reynolds가 SP·WC(§3.3)와 SK·AS·SQ(§3.2–§3.3)만으로 더 유도하는 규칙 셋 — ISK(§3.5
p.66), MSQₙ(§3.3 pp.60–61), RASₙ(§3.3 pp.61–62) — 을 먼저 두고, 그 뒤에 CA·DA·CSP·CST
(§3.5의 생성자)에서 유도되는 부분 CST, 마지막으로 책에 없는 보충 규칙(∃ 규칙, 치환
규칙)을 둔다.

## 두 상수 규칙
CSP는 명세 전제 없이 `{p} c {p}`를 준다. CST는 `[p] c [q]`라는 종료 전제를
받아 `[p ∧ r] c [q ∧ r]`를 준다. 부분 CST는 CSP와 CA를 조합하면 된다(p.69).

## 앞 장의 정리가 하나씩
- 상수 규칙은 명제 2.6(b)의 쓰기 집합과 명제 1.1의 단언 일치를 쓴다.
- RASₙ의 건전성은 AS·SQ만 쓴다. ∃ 규칙은 명제 2.6(a), 치환 규칙은 연습 2.8의 약한
  치환 정리를 쓴다.

## 읽는 순서
`Semantic.lean` → `Hoare.lean` → `Total.lean` → 이 파일.

## 책과의 차이
ISK·MSQₙ·RASₙ은 책의 유도 규칙 그대로다. 아래의 ∃·치환 규칙은 책에 없는 보충 자료다
(각 절 첫머리에 책과의 관계를 적는다).
-/

@[expose] public section

namespace Reynolds.Exercises.Ch03

open Reynolds Reynolds.Answers.Ch01 Reynolds.Answers.Ch02

universe u

variable {V : Type u} [DecidableEq V]

/-! ## 1. ISK · MSQₙ · RASₙ — SP·WC·AS·SQ에서 유도한다

이 절의 세 규칙은 책이 이미 있는 규칙만으로 더 유도하는 예다. ISK는 SK 하나에 SP를
얹고, MSQₙ은 결과 규칙을 n번 조립하며, RASₙ은 AS를 n번·SQ를 n−1번 쓴다. -/

/-- **ISK (§3.5 p.66).** SK `{q} skip {q}`에 SP를 적용한다 — `q`를 `p ⇒ q`로 강화한다. -/
theorem Hoare.isk [HasFresh V] {p q : Assert V} (h : Stronger p q) : Hoare p .skip q :=
  Hoare.strengthen h (Hoare.skip q)

/-- ISK의 전체 정확성 판. 같은 유도다. -/
theorem HoareT.isk [HasFresh V] {p q : Assert V} (h : Stronger p q) : HoareT p .skip q :=
  HoareT.strengthen h (HoareT.skip q)

/-!
### MSQₙ — 여러 번의 순차 합성 (§3.3 pp.60–61)

MSQ₁은 `p₀ ⇒ q₀`, `{q₀} c₀ {p₁}`, `p₁ ⇒ q₁`에서 `{p₀} c₀ {q₁}`를 얻는다 — SP 뒤 WC를
적용한 것과 글자 그대로 같으므로 이미 있는 `Hoare.conseq`(`HoareT.conseq`)가 그 이름이다.
책은 MSQₙ을 MSQₙ₋₁에 SQ와 결과 규칙 한 겹을 더 둘러 귀납적으로 유도한다(가정이 있는
증명의 예). 그 한 겹을 `n = 2`에서 직접 보인다 — 일반 n은 같은 겹을 반복할 뿐이다.
-/

/-- MSQ₂ (§3.3 p.60). MSQ₁(`Hoare.conseq`) 둘을 SQ로 잇는다. -/
theorem Hoare.msq2 [HasFresh V] {p₀ q₀ p₁ q₁ p₂ q₂ : Assert V} {c₀ c₁ : Comm V}
    (h₀ : Stronger p₀ q₀) (hc₀ : Hoare q₀ c₀ p₁) (h₁ : Stronger p₁ q₁)
    (hc₁ : Hoare q₁ c₁ p₂) (h₂ : Stronger p₂ q₂) : Hoare p₀ (.seq c₀ c₁) q₂
    :=
  Hoare.seq (Hoare.conseq h₀ hc₀ h₁) (Hoare.weaken hc₁ h₂)

/-- MSQ₂의 전체 정확성 판. -/
theorem HoareT.msq2 [HasFresh V] {p₀ q₀ p₁ q₁ p₂ q₂ : Assert V} {c₀ c₁ : Comm V}
    (h₀ : Stronger p₀ q₀) (hc₀ : HoareT q₀ c₀ p₁) (h₁ : Stronger p₁ q₁)
    (hc₁ : HoareT q₁ c₁ p₂) (h₂ : Stronger p₂ q₂) : HoareT p₀ (.seq c₀ c₁) q₂ :=
  HoareT.seq (HoareT.conseq h₀ hc₀ h₁) (HoareT.weaken hc₁ h₂)

/-!
### RASₙ — 대입열 (§3.3 pp.61–62)

대입 목록은 머리 `(v, e)`와 꼬리 `l : List (V × IntExp V)`로 나눠 `(v, e) :: l`로 표현한다
(책은 `n ≥ 1`을 요구하므로 머리를 따로 받는다). `rasComm`이 그 명령
`v := e ; v' := e' ; ⋯`, `rasPre`가 책의 반복 치환 `(⋯(q/vₙ₋₁→eₙ₋₁)⋯)/v→e`다 — 꼬리부터
치환해 머리로 돌아온다.
-/

omit [DecidableEq V] in
/-- RASₙ이 대입하는 명령. `Comm.seqs`처럼 머리를 앞에 두고 꼬리로 재귀한다. -/
def rasComm (v : V) (e : IntExp V) : List (V × IntExp V) → Comm V
  | [] => .assign v e
  | (v', e') :: l => .seq (.assign v e) (rasComm v' e' l)

/-- RASₙ의 전제가 반복하는 치환. -/
def rasPre [HasFresh V] (q : Assert V) (v : V) (e : IntExp V) :
    List (V × IntExp V) → Assert V
  | [] => q /[v := e]
  | (v', e') :: l => (rasPre q v' e' l) /[v := e]

/-- **RASₙ의 건전성 (§3.3 p.61).** AS를 n번, SQ를 n−1번 쓴다. -/
theorem Hoare.ras [HasFresh V] (q : Assert V) (v : V) (e : IntExp V) :
    ∀ l : List (V × IntExp V), Hoare (rasPre q v e l) (rasComm v e l) q
  | [] => Hoare.assign q v e
  | (v', e') :: l => Hoare.seq (Hoare.assign (rasPre q v' e' l) v e) (Hoare.ras q v' e' l)

/-- RASₙ의 전체 정확성 판. -/
theorem HoareT.ras [HasFresh V] (q : Assert V) (v : V) (e : IntExp V) :
    ∀ l : List (V × IntExp V), HoareT (rasPre q v e l) (rasComm v e l) q
  | [] => HoareT.assign q v e
  | (v', e') :: l => HoareT.seq (HoareT.assign (rasPre q v' e' l) v e) (HoareT.ras q v' e' l)

/-- RASₙ의 대입열이 상태에 하는 일. `rasComm`과 같은 모양으로 재귀한다. -/
def rasState (v : V) (e : IntExp V) : List (V × IntExp V) → State V → State V
  | [], σ => σ[v := ⟦e⟧ₑ σ]
  | (v', e') :: l, σ => rasState v' e' l (σ[v := ⟦e⟧ₑ σ])

/-- `rasComm`은 대입만 반복하므로 늘 끝나고, 끝난 상태가 `rasState`다. -/
theorem rasComm_eval (v : V) (e : IntExp V) :
    ∀ (l : List (V × IntExp V)) (σ : State V),
      (rasComm v e l).eval σ = Flat.some (rasState v e l σ)
  | [], _ => rfl
  | (v', e') :: l, σ => by
      simp only [rasComm, rasState, Comm.eval, Flat.bind_some]
      exact rasComm_eval v' e' l (σ[v := ⟦e⟧ₑ σ])

/-- RASₙ의 전제가 반복 치환과 같다는 것 — 명제 1.4(유한 치환)를 `l`을 따라 편 것. -/
theorem rasPre_iff [HasFresh V] (q : Assert V) (v : V) (e : IntExp V) :
    ∀ (l : List (V × IntExp V)) (σ : State V), ⟦rasPre q v e l⟧ₐ σ ↔ ⟦q⟧ₐ (rasState v e l σ)
  | [], σ => substitution_single q v e σ
  | (v', e') :: l, σ => by
      simp only [rasPre, rasState]
      rw [substitution_single]
      exact rasPre_iff q v' e' l (σ[v := ⟦e⟧ₑ σ])

/--
**RASₙ의 완전성 (§3.3 pp.61–62, ★★).** 책이 "건전할 뿐 아니라 완전하다"고 특별히 짚는
유일한 유도 규칙이다 — 결론이 타당하면 전제도 타당하다. 대입열은 늘 끝나므로
(`rasComm_eval`) `PartialCorrect`가 끝난 상태에서 사후조건을 주고, 그 상태에서 사후조건이
참인 것은 반복 치환이 시작 상태에서 참인 것과 같다(`rasPre_iff`, 명제 1.4). 같은 장의
채점 연습이나 `Hoare.sound`에는 기대지 않는다(연습 독립성 원칙).
-/
@[exercise "§3.3 ras-complete" 2]
theorem ras_complete [HasFresh V] {p q : Assert V} (v : V) (e : IntExp V)
    (l : List (V × IntExp V)) (h : PartialCorrect p (rasComm v e l) q) :
    Stronger p (rasPre q v e l) := by
  -- 먼저 볼 것: `rasComm_eval`, `rasPre_iff` (둘 다 완성 자료다).
  -- 힌트 1: `Stronger`를 펼쳐 σ, hp를 받는다.
  -- 힌트 2: `rasPre_iff`로 목표를 `⟦q⟧ₐ (rasState v e l σ)`로 바꾼다.
  -- 힌트 3: `rasComm_eval`이 주는 종료 증인 `rasComm v e l`의 결과를 `h`(PartialCorrect)에
  --         넣으면 끝난다.
  sorry


/-! ## 2. 상수 규칙 -/

/-- 부분 CST는 CA의 두 번째 전제로 CSP를 넣어 유도한다 (§3.5 p.69). -/
theorem Hoare.frame [HasFresh V] {p q r : Assert V} {c : Comm V}
    (hr : Disjoint c.fa r.fv) (h : Hoare p c q) : Hoare (p ⋀ r) c (q ⋀ r) :=
  Hoare.conj h (Hoare.constancy hr)

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
    (h : ｛p｝c｛q｝) : ｛p ⋀ r｝c｛q ⋀ r｝ := by
  -- 먼저 볼 것: §2.5 의 `Comm.eval_agree_outside_fa` (명제 2.6(b)), §1.4 의 `coincidence_assert`,
  --            Mathlib 의 `Finset.disjoint_right`.
  -- 힌트 1: `Assert.eval_and` 로 사전조건을 `⟦p⟧ₐ σ` 와 `⟦r⟧ₐ σ` 로 가른다.
  -- 힌트 2: `q` 쪽은 전제 그대로. `r` 쪽은 `r` 의 자유 변수가 `c.fa` 밖이라 `τ` 와 `σ` 에서
  --         같은 값이다 — 그러니 `r` 의 진릿값도 같다.
  sorry


/-! ## 3. 연언 · 선언 규칙

의미 수준에서는 정의를 펼치면 끝난다. 같은 명령 `c` 의 두 명세를 하나로 합친다. -/

/-- **연언 규칙.** 두 명세의 사전조건과 사후조건을 각각 연언으로 합친다. -/
theorem conj_sound {p₀ p₁ q₀ q₁ : Assert V} {c : Comm V}
    (h₀ : ｛p₀｝c｛q₀｝) (h₁ : ｛p₁｝c｛q₁｝) : ｛p₀ ⋀ p₁｝c｛q₀ ⋀ q₁｝ := by
  intro σ hp τ hτ
  obtain ⟨hp₀, hp₁⟩ := (Assert.eval_and _ _ _).mp hp
  exact (Assert.eval_and _ _ _).mpr ⟨h₀ σ hp₀ τ hτ, h₁ σ hp₁ τ hτ⟩

/-- DA. 사전조건과 서로 다른 사후조건을 각각 선언으로 합친다. -/
theorem disj_sound {p₀ p₁ q₀ q₁ : Assert V} {c : Comm V}
    (h₀ : ｛p₀｝c｛q₀｝) (h₁ : ｛p₁｝c｛q₁｝) :
    ｛Assert.bin .or p₀ p₁｝c｛Assert.bin .or q₀ q₁｝ := da_sound.1 h₀ h₁

/-- 사후조건이 같은 기존 선언 규칙은 DA 뒤 WC로 얻는다. -/
theorem disj_same_sound {p₀ p₁ q : Assert V} {c : Comm V}
    (h₀ : ｛p₀｝c｛q｝) (h₁ : ｛p₁｝c｛q｝) : ｛Assert.bin .or p₀ p₁｝c｛q｝ :=
  (wc_sound (fun _ h => h.elim id id)).1 (da_sound.1 h₀ h₁)

/-! ## 4. 보충 — 유령 변수의 ∃ 규칙

**책과의 관계**: 이 규칙은 Reynolds §3.5 본문에 없다. 책은 `newvar`로 들여온 지역 변수가
명세 밖으로 안 새게 하는 데 집중하고, 사전조건에서만 쓰인 변수를 양화로 감추는 규칙은
다루지 않는다. 앞으로 가는 대입 규칙(`Assign.lean`의 보충 규칙)의 사후조건에 든 `∃ v₀`가
이 규칙의 거울상이라 여기 둔다. -/

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
    (h : ｛p｝c｛q｝) : ｛Assert.quant .ex v p｝c｛q｝ := by
  -- 먼저 볼 것: §2.5 의 `Comm.coincidence_general` (명제 2.6(a)) 과 `AgreeOn`,
  --            `Assert.eval_ex`, `coincidence_assert`. `Total.lean`의 `whT_sound` 안에서
  --            본체 결과를 전달할 때도 같은 수법을 쓴다.
  -- 힌트 1: 증인 `n` 을 꺼낸다. 전제는 `σ[v := n]` 에서 쓸 수 있다.
  -- 힌트 2: `S := c.fv ∪ q.fv` 에 명제 2.6(a) 를 쓰면 `⟦c⟧ σ` 와 `⟦c⟧ (σ[v := n])` 가 `S` 에서
  --         일치한다. `rcases hτ' : c.eval (σ[v := n])` 로 나눠 `Flat.none` 쪽은 모순으로 닫는다.
  -- 힌트 3: `q` 는 `S` 만 보므로 두 결과에서 진릿값이 같다.
  sorry


/-! ## 5. 보충 — 치환 규칙

**책과의 관계**: 이 규칙도 Reynolds §3.5 본문에 없다. 책 연습 3.11(이 저장소의 `Ex 3.11`,
`BookExercises.lean`)이 전체 정확성과 전체 자유 변수 집합 위의 단사 치환을 묻는데,
여기서는 그 결과를 부분·전체 정확성 모두에 대해 쓰기 변수만 단사이면 되도록 일반화한다. -/

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
    (h : ｛p｝c｛q｝) : ｛p /ₛ δ.toSubst｝(c /ᶜ δ)｛q /ₛ δ.toSubst｝ := by
  -- 먼저 볼 것: 연습 2.8 의 `Ex.Comm.substitution_weak` 와 `AgreeVia` (`AgreeVia.some_some`,
  --            `AgreeVia.none_some`), §1.4 의 `substitution_assert` (명제 1.3).
  -- 힌트 1: 원래 쪽 시작 상태를 `fun w => σ' (δ w)` 로 잡는다. 그러면 `substitution_weak` 와
  --         `substitution_assert` 의 가설이 둘 다 `rfl` 이다.
  -- 힌트 2: `substitution_weak` 를 `S := c.fv ∪ p.fv ∪ q.fv` 로 부르고, 원래 쪽 실행을
  --         `rcases hc : c.eval (fun w => σ' (δ w))` 로 나눈다.
  -- 힌트 3: 사전조건은 명제 1.3 으로 원래 쪽에 옮기고, 사후조건은 명제 1.3 으로 되돌린다.
  sorry


/-! ## 6. 여기서 어디로 가나

CA·DA는 생성자이고 부분 CST는 위에서 유도했다. RASₙ은 유도 규칙 중 유일하게 완전성까지
증명된다(`ras_complete`). 나머지 모든 타당한 명세에 유도가 있는지는 별도의 완전성
문제다(`Wlp.lean`, `while` 없는 조각에서만). -/

end Reynolds.Exercises.Ch03
