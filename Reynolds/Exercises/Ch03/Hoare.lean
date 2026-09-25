/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Exercises.Ch03.Spec

/-!
# §3.2 · §3.3 · §3.5 · §3.6 추론 규칙

Reynolds §3.2(규칙의 모양)와 그 뒤 절들이 하나씩 내놓는 규칙 — §3.3 대입과 순차 합성,
§3.5 조건과 `while`, §3.6 변수 선언 — 을 한 귀납 술어로 모은다. 건전성은
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

Reynolds 는 결과 규칙을 둘로 나눈다 — 전제 강화와 결론 약화. 여기서는 하나로 합치고
(`conseq`), 두 반쪽을 그것으로부터 유도한다 (`Hoare.strengthen`, `Hoare.weaken`).

## 읽는 순서
`Spec.lean` → 이 파일 → `Soundness.lean` → `Assign.lean`.
-/

@[expose] public section

namespace Reynolds.Exercises.Ch03

open Reynolds Reynolds.Exercises.Ch01 Reynolds.Exercises.Ch02

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
부분 정확성의 추론 체계. Reynolds §3.2~3.6 의 규칙들이다.

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
  /-- 변수 선언. 지역 변수는 밖의 단언과 초기값 식에 나오지 않아야 한다. 나오면 이름을
  바꾼다 (§2.5 `Comm.newvar_rename`). -/
  | newvar {p q : Assert V} {v : V} {e : IntExp V} {c : Comm V}
      (hp : v ∉ p.fv) (hq : v ∉ q.fv) (he : v ∉ e.fv) :
      Hoare (p ⋀ .cmp .eq (.var v) e) c q → Hoare p (.newvar v e c) q
  /-- 결과 규칙. 사전조건은 강하게, 사후조건은 약하게. 전제가 단언의 **타당성**이다. -/
  | conseq {p p' q q' : Assert V} {c : Comm V} :
      Stronger p' p → Hoare p c q → Stronger q q' → Hoare p' c q'

/-! ## 3. 결과 규칙의 두 반쪽

Reynolds 의 전제 강화·결론 약화는 `conseq` 의 한쪽을 항등으로 둔 것이다. -/

/-- 전제 강화. Reynolds 의 "strengthening precedent". -/
theorem Hoare.strengthen [HasFresh V] {p p' q : Assert V} {c : Comm V}
    (hp : Stronger p' p) (h : Hoare p c q) : Hoare p' c q :=
  Hoare.conseq hp h (Stronger.refl q)

/-- 결론 약화. Reynolds 의 "weakening consequent". -/
theorem Hoare.weaken [HasFresh V] {p q q' : Assert V} {c : Comm V}
    (h : Hoare p c q) (hq : Stronger q q') : Hoare p c q' :=
  Hoare.conseq (Stronger.refl p) h hq

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
