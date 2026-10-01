/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Exercises.Ch03.Semantic

/-!
# §3.2–§3.5 추론 규칙

Reynolds §3.2(규칙의 모양)와 그 뒤 절들이 하나씩 내놓는 규칙 — §3.3 대입과 순차 합성,
§3.4 반복, §3.5 조건·변수 선언·이름 바꾸기 — 를 한 귀납 술어로 모은다. 건전성은
`Soundness.lean` 이다. 전체 정확성의 `while` 규칙은 `Total.lean` 이다.

## 규칙 하나가 생성자 하나

§1.3 의 `Proof` 와 같다. 전제가 인자, 결론이 결과 타입 — Lean 의 화살표가 Reynolds 의
가로선이다. `Hoare p c q` 는 "명세 `{p} c {q}` 의 **유도**가 있다" 이고, 그 유도가 실제로
타당한 명세만 만든다는 것은 따로 증명할 일이다 (`Hoare.sound`).

## 결과 규칙의 전제는 "타당하다" 다

`conseq` 의 전제 `Stronger p' p` 는 `∀ σ, ⟦p'⟧ σ → ⟦p⟧ σ` 다. 단언 사이 함의가 타당하다는
의미적 사실이지 1장의 `Proof` 로 증명했다는 것이 아니다. Hoare 논리는 단언 논리를
**오라클로** 쓴다 — 그래서 완전성을 말할 때 "단언의 타당성에 상대적으로" 라는 단서가
붙는다 (§3.10).

Reynolds의 SP와 WC를 각각 `strengthen`, `weaken` 생성자로 둔다.
기존 `conseq`는 두 생성자를 차례로 적용한 유도 정리다.

## 읽는 순서
`Spec.lean` → `Semantic.lean` → 이 파일 → `Soundness.lean` → `Assign.lean`.

## 책과의 차이
RN은 앞부분 뒤의 지역 선언만 바꾸는 `Comm.PrefixRename`으로 표현한다.
기존 합성형 `newvar`는 생성자 대신 AS·SQ·DC의 파생 정리로 제공한다.
-/

@[expose] public section

namespace Reynolds.Exercises.Ch03

open Reynolds Reynolds.Answers.Ch01 Reynolds.Answers.Ch02

universe u

variable {V : Type u} [DecidableEq V]

/-! ## 1. 단언 쪽 준비

규칙에 연언 · 부정 · 존재 양화 · 등식이 나온다. 정의 그대로인 네 동치를 이름 붙여 둔다.
`Assert.eval` 은 재귀 정의라 `⟨_, _⟩` 같은 익명 생성자가 바로 안 들어간다 — 이 보조정리로
한 겹 벗긴다. -/

/-- 단언의 연언. 규칙에서 자주 나와 표기를 둔다. 2장 DSL 의 `∧` 과 겹치지 않는다. -/
scoped infixl:35 " ⋀ " => Assert.bin LogOp.and

/-- 연언의 뜻은 `∧` 다. 정의 그대로. -/
theorem Assert.eval_and (p q : Assert V) (σ : State V) : ⟦p ⋀ q⟧ₐ σ ↔ ⟦p⟧ₐ σ ∧ ⟦q⟧ₐ σ :=
  Iff.rfl

/-- 부정의 뜻은 `¬` 다. 정의 그대로. -/
theorem Assert.eval_not (p : Assert V) (σ : State V) : ⟦Assert.not p⟧ₐ σ ↔ ¬ ⟦p⟧ₐ σ :=
  Iff.rfl

/-- 존재 양화의 뜻. 정의 그대로. -/
theorem Assert.eval_ex (v : V) (p : Assert V) (σ : State V) :
    ⟦Assert.quant .ex v p⟧ₐ σ ↔ ∃ n : Int, ⟦p⟧ₐ (σ[v := n]) :=
  Iff.rfl

/-- 등식의 뜻. 정의 그대로. -/
theorem Assert.eval_eq (e₀ e₁ : IntExp V) (σ : State V) :
    ⟦Assert.cmp .eq e₀ e₁⟧ₐ σ ↔ ⟦e₀⟧ₑ σ = ⟦e₁⟧ₑ σ :=
  Iff.rfl

/-! ## 2. 규칙 -/

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

/-! ## 3. 결과 규칙

전제 강화와 결론 약화를 이어 기존 `conseq`를 유도한다. -/

/-- SP와 WC를 차례로 적용한 결과 규칙. 기존 호출 형태를 보존한다. -/
theorem Hoare.conseq [HasFresh V] {p p' q q' : Assert V} {c : Comm V}
    (hp : Stronger p' p) (h : Hoare p c q) (hq : Stronger q q') : Hoare p' c q' :=
  Hoare.weaken (Hoare.strengthen hp h) hq

/-- 자유 변수가 아닌 이름의 갱신은 단언의 진릿값을 보존한다. -/
theorem Assert.eval_update_of_notMem {q : Assert V} {v : V} (hq : v ∉ q.fv)
    (σ : State V) (n : Int) : q.eval (σ[v := n]) ↔ q.eval σ := by
  exact (coincidence_assert q σ _ fun w hw =>
    (State.subst_of_ne σ v w n fun hwv => hq (hwv ▸ hw)).symm).symm

/-- 기존 합성형 선언 규칙의 안쪽 사전조건. `p`와 `e`의 신선함은 이 보조 규칙에 쓰인다. -/
theorem newvar_init {p : Assert V} {v : V} {e : IntExp V}
    (hp : v ∉ p.fv) (he : v ∉ e.fv) (σ : State V) (h : p.eval σ) :
    (p ⋀ .cmp .eq (.var v) e).eval (σ[v := e.eval σ]) := by
  refine ⟨(Assert.eval_update_of_notMem hp σ _).mpr h, ?_⟩
  change (σ[v := e.eval σ]) v = e.eval (σ[v := e.eval σ])
  rw [State.subst_self]
  exact coincidence_intExp e σ _ fun w hw =>
    (State.subst_of_ne σ v w _ fun hwv => he (hwv ▸ hw)).symm

/-- 대입 뒤 본체의 유도에서 빈 앞부분의 DC로 변수 선언을 얻는다. -/
theorem Hoare.newvar_comp [HasFresh V] {p r q : Assert V} {v : V}
    {e : IntExp V} {c : Comm V} (hq : v ∉ q.fv)
    (ha : Hoare p (.assign v e) r) (hc : Hoare r c q) :
    Hoare p (.newvar v e c) q :=
  Hoare.dc [] hq (Hoare.seq ha hc)

/-- 기존 합성형 선언 API. AS·SQ·DC로 유도되며 `p`, `e`의 신선함은 초기 단언에만 쓰인다. -/
theorem Hoare.newvar [HasFresh V] {p q : Assert V} {v : V}
    {e : IntExp V} {c : Comm V} (hp : v ∉ p.fv) (hq : v ∉ q.fv) (he : v ∉ e.fv)
    (h : Hoare (p ⋀ .cmp .eq (.var v) e) c q) : Hoare p (.newvar v e c) q := by
  refine Hoare.newvar_comp hq (Hoare.strengthen ?_ (Hoare.assign _ v e)) h
  intro σ hpσ
  exact (substitution_single _ v e σ).mpr (newvar_init hp he σ hpσ)

/-! ## 4. 첫 유도

대입 공리는 **뒤에서 앞으로** 쓴다. 사후조건에 치환을 걸어 사전조건을 얻고, 그것이 원래
사전조건과 다르면 결과 규칙으로 잇는다. -/

/-- `{x = 1} x := x + 1 {x = 2}`. 공리가 주는 사전조건은 `x + 1 = 2` 고, `x = 1` 이 그보다
강하다. -/
theorem incr_hoare : Hoare (⟪ x = 1 ⟫ₐ) ⟪ x := x + 1 ⟫ᶜ (⟪ x = 2 ⟫ₐ) := by
  refine Hoare.strengthen ?_ (Hoare.assign _ "x" _)
  intro σ h
  simp [Assert.subst, IntExp.subst, Assert.eval, IntExp.eval, IntOp.denote, Cmp.denote] at h ⊢
  omega

/-- §2.5 의 맞바꾸기 `t := x; x := y; y := t`. 유령 변수 `a`, `b` 가 원래 값을 붙든다.
이음매 단언 둘은 대입 공리가 뒤에서부터 만들어 준다 — 손으로 고를 것이 없다. -/
theorem swap_hoare :
    Hoare (⟪ x = a ∧ y = b ⟫ₐ) ⟪ t := x; x := y; y := t ⟫ᶜ (⟪ y = a ∧ x = b ⟫ₐ) := by
  refine Hoare.strengthen ?_ (Hoare.seq (Hoare.assign _ "t" _)
    (Hoare.seq (Hoare.assign _ "x" _) (Hoare.assign _ "y" _)))
  intro σ h
  simpa [Assert.subst, IntExp.subst, Assert.eval, IntExp.eval, Cmp.denote, LogOp.denote,
    Function.update] using h

/-! ## 5. 여기서 어디로 가나

유도가 있다고 명세가 참인 것은 아직 아니다. `Soundness.lean` 이 규칙마다 1·2장의 정리
하나로 그것을 증명한다. `Assign.lean` 은 대입 공리가 왜 거꾸로인지를 앞으로 가는 판과
비교해 답한다. -/

end Reynolds.Exercises.Ch03
