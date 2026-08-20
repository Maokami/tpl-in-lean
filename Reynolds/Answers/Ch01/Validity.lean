/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Answers.Ch01.Semantics
public import Reynolds.Meta.Exercise

/-!
# §1.3 타당성과 추론 (Validity and Inference)

Reynolds §1.3 (pp. 12–15) 에 대응한다.

## 이 파일에서 다루는 것
- 타당(valid) · 충족 불가능(unsatisfiable) · 강함/약함 · 동치
- 추론 규칙과 형식 증명
- **건전성(soundness)** — 증명된 것은 타당하다
- ★ 추론(inference)과 함의(⇒)를 헷갈리면 안 되는 이유

## 핵심 아이디어

단언 하나만으로는 참·거짓이 없다. **상태가 있어야** 정해진다 (`Background.lean` §4).
그래서 "참이다"에 단계가 생긴다:

* `σ` 에서 참 — `⟦p⟧ₐ σ`
* **타당(valid)** — 모든 `σ` 에서 참
* **충족 불가능** — 어떤 `σ` 에서도 거짓

**증명의 각 단계는 타당해야 한다.** `x > 0` 은 증명 단계가 될 수 없다 —
`x ↦ 0` 인 상태에서 거짓이기 때문이다. Reynolds 가 직접 경고하는 대목이고,
이 파일의 마지막 두 정리가 그것을 형식적으로 못박는다.

## 읽는 순서
`Semantics.lean` → 이 파일 → `Substitution.lean`

## 책과의 차이
Reynolds 는 완전한 추론 체계를 주지 않는다 (*"consult any elementary text on logic"*).
그의 목적은 개념의 예시다. 우리도 §1.3 에 나오는 규칙들만으로 **작은 체계**를 만들고
건전성을 증명한다. 완전성(completeness)은 다루지 않는다 — 그가 다루지 않기 때문이다.
-/

@[expose] public section

namespace Reynolds.Answers.Ch01

open Reynolds

universe u

variable {V : Type u} [DecidableEq V]

/-! ## 1. 타당 · 충족 불가능 · 강함 -/

-- ANCHOR: validity
/-- **타당(valid)** — 모든 상태에서 참. Reynolds §1.3. -/
def Valid (p : Assert V) : Prop := ∀ σ : State V, ⟦p⟧ₐ σ

/-- **충족 불가능(unsatisfiable)** — 어떤 상태에서도 거짓. -/
def Unsat (p : Assert V) : Prop := ∀ σ : State V, ¬ ⟦p⟧ₐ σ

/--
`p` 가 `q` 보다 **강하다(stronger)**. `q` 는 `p` 보다 **약하다(weaker)**.

Reynolds 가 곧바로 경고하듯 이 용어는 영어 어감과 잘 맞지 않는다:
*"'stronger' and 'weaker' are dual preorders, which does not quite jibe with normal
English usage. For example, any assertion is both stronger and weaker than itself."*

즉 **전순서(preorder)** 이지 순서(order)가 아니다 — 반대칭성이 없다.
-/
def Stronger (p q : Assert V) : Prop := ∀ σ : State V, ⟦p⟧ₐ σ → ⟦q⟧ₐ σ

/-- **동치(equivalent)** — 같은 뜻. -/
def Equivalent (p q : Assert V) : Prop := ∀ σ : State V, (⟦p⟧ₐ σ ↔ ⟦q⟧ₐ σ)
-- ANCHOR_END: validity

/-- `Stronger` 는 반사적이다. 그래서 "임의의 단언은 자기 자신보다 강하다". -/
theorem Stronger.refl (p : Assert V) : Stronger p p := fun _ h => h

/-- `Stronger` 는 추이적이다. -/
theorem Stronger.trans {p q r : Assert V} (h₀ : Stronger p q) (h₁ : Stronger q r) :
    Stronger p r := fun σ h => h₁ σ (h₀ σ h)

/-- 동치는 양방향으로 강한 것이다. Reynolds §1.3 의 관찰. -/
theorem equivalent_iff {p q : Assert V} :
    Equivalent p q ↔ (Stronger p q ∧ Stronger q p) := by
  constructor
  · intro h; exact ⟨fun σ => (h σ).mp, fun σ => (h σ).mpr⟩
  · intro ⟨h₀, h₁⟩ σ; exact ⟨h₀ σ, h₁ σ⟩

/-- `true` 는 어떤 단언보다도 약하다. -/
theorem stronger_tru (p : Assert V) : Stronger p .tru := fun _ _ => trivial

/-- `false` 는 어떤 단언보다도 강하다. -/
theorem fls_stronger (p : Assert V) : Stronger .fls p := fun _ h => h.elim

/-- `true` 는 타당하다. -/
theorem valid_tru : Valid (.tru : Assert V) := fun _ => trivial

/-- `false` 는 충족 불가능하다. -/
theorem unsat_fls : Unsat (.fls : Assert V) := fun _ h => h

/-! ## 2. 추론 규칙과 형식 증명

Reynolds §1.3 은 **추론 규칙(inference rule)** 을 이렇게 정의한다:
전제(premiss) 0개 이상과 결론(conclusion) 하나. 가로선으로 구분한다.
전제가 없으면 **공리꼴(axiom schema)**, 메타변수도 없으면 그냥 **공리(axiom)**.

Lean 에서는 이것이 `inductive` 다. **각 생성자가 규칙 하나**이고,
화살표의 왼쪽이 전제, 오른쪽이 결론이다 — Reynolds 의 가로선과 정확히 대응한다.

그리고 `Proof p` 의 값 하나가 곧 **증명 나무(proof tree)** 다.
Reynolds 가 *"proof trees are more perspicuous than sequences"* 라고 말하는 그 나무를
Lean 에서는 실제로 만들고 뜯어볼 수 있다. -/

-- ANCHOR: proofSystem
/--
술어 논리의 작은 추론 체계. Reynolds §1.3 이 예시로 드는 규칙들이다.

**완전하지 않다.** 그럴 의도도 없다 — Reynolds 본인이 완전한 체계는
논리학 교과서를 보라고 한다. 목적은 "추론 규칙"과 "건전성"이 무엇인지 보이는 것이다.
-/
inductive Proof : Assert V → Prop where
  /-- 공리꼴: `e = e`. -/
  | eqRefl (e : IntExp V) : Proof (.cmp .eq e e)
  /-- 한 전제 규칙: `e₀ = e₁` 로부터 `e₁ = e₀`. -/
  | eqSymm {e₀ e₁ : IntExp V} : Proof (.cmp .eq e₀ e₁) → Proof (.cmp .eq e₁ e₀)
  /-- 두 전제 규칙 — 전건 긍정(modus ponens). -/
  | mp {p q : Assert V} : Proof p → Proof (.bin .imp p q) → Proof q
  /-- 두 전제 규칙 — 연언 도입. -/
  | andIntro {p q : Assert V} : Proof p → Proof q → Proof (.bin .and p q)
  /--
  ★ **보편 일반화(∀-도입).**

  전제가 **타당**해야 결론이 타당하다는 점이 핵심이다. 아래 §3 에서 이 규칙과
  함의 `p ⇒ ∀v. p` 를 나란히 놓고 왜 다른지 본다.
  -/
  | genAll (v : V) {p : Assert V} : Proof p → Proof (.quant .all v p)
-- ANCHOR_END: proofSystem

/-! ## 3. ★ 건전성 (soundness) -/

/--
**건전성(soundness)** — 증명된 것은 타당하다.

Reynolds §1.3:
> *"the whole point of the concept of proof is its connection with semantics:
> If there is a proof of an assertion p, then p should be valid."*

증명은 `Proof` 에 대한 귀납법이다. **각 케이스가 "이 규칙이 건전하다"에 해당한다** —
즉 규칙 하나하나를 따로 검사하면 체계 전체의 건전성이 나온다.
이것이 형식 체계를 이런 식으로 짜는 이유다.
-/
@[exercise "§1.3 건전성" 2]
theorem Proof.sound {p : Assert V} : Proof p → Valid p := by
  intro hp
  induction hp with
  | eqRefl e => intro σ; simp [Assert.eval, Cmp.denote]
  | eqSymm _ ih => intro σ; simpa [Assert.eval, Cmp.denote] using (ih σ).symm
  | mp _ _ ihp ihimp => intro σ; exact ihimp σ (ihp σ)
  | andIntro _ _ ihp ihq => intro σ; exact ⟨ihp σ, ihq σ⟩
  | genAll v _ ih => intro σ n; exact ih _

/-! ## 4. ★ 추론과 함의는 다르다

Reynolds 가 §1.3 에서 한 페이지를 들여 경고하는 논점이다. 두 정리를 나란히 놓는다.

```
        p                                    ─────────────
     ───────  (건전한 규칙)                    p ⇒ ∀v. p     (타당하지 않다)
      ∀v. p
```

**가로선(추론)과 화살표(함의)는 다른 것이다.**
가로선은 "타당한 것으로부터 타당한 것을 얻는다"이고,
화살표는 "**한 상태 안에서** 앞이 참이면 뒤도 참"이다. -/

-- ANCHOR: genVsImp
/-- **건전한 규칙**: `p` 가 **타당하면** `∀v. p` 도 타당하다. -/
@[exercise "§1.3 gen-sound" 1]
theorem valid_forall_of_valid (v : V) {p : Assert V} (h : Valid p) :
    Valid (.quant .all v p) := fun _ _ => h _

/--
**타당하지 않은 함의**: `x > 0 ⇒ ∀x. x > 0`.

Reynolds 의 반례를 그대로 쓴다. `x ↦ 3` 인 상태에서
왼쪽 `x > 0` 은 참인데 오른쪽 `∀x. x > 0` 은 (`x ↦ 0` 을 넣으면) 거짓이다.

**같은 재료로 만든 규칙은 건전하고 함의는 타당하지 않다.** 이 대비가 §1.3 의 요점이다.
-/
@[exercise "§1.3 gen-not-imp" 2]
theorem not_valid_imp_forall :
    ¬ Valid (.bin .imp (.cmp .gt (.var "x") (.num 0))
                       (.quant .all "x" (.cmp .gt (.var "x") (.num 0))) : Assert String) := by
  intro h
  -- x ↦ 3 인 상태를 잡으면 왼쪽은 참이다.
  have h3 := h (State.const 3)
  simp only [Assert.eval, LogOp.denote, Cmp.denote, IntExp.eval, State.const] at h3
  -- 따라서 오른쪽이 성립해야 하는데, n = 0 을 넣으면 거짓이다.
  have := h3 (by decide) 0
  simp at this
-- ANCHOR_END: genVsImp

/-! ## 5. 이 책이 다루지 않는 것

Reynolds 는 §1.3 을 이렇게 닫는다.

**논리적 타당성(logical validity)** — 표현식 연산의 의미까지 임의로 바꿔도 성립하는 것.
**완전성(completeness)** — 건전성의 역. 타당한 것은 모두 증명된다.

우리처럼 타당성을 "정수에 대한 고정된 해석"으로 정의하면
**어떤 유한한 추론 규칙 집합도 완전하지 않다** — 괴델의 불완전성 정리다.
논리적 타당성으로 정의하면 완전한 유한 체계가 존재한다 (괴델의 완전성 정리).

그런데 Reynolds가 지적하듯, 프로그램 검증에서는 논리적 완전성이 별 쓸모가 없다.
우리는 `+` 가 정말 덧셈인 해석에만 관심이 있기 때문이다.
(예외는 §3.8 에서 다룬다.)

**이 주제는 코드로 만들지 않는다.** Reynolds 본인이 다루지 않고, 다루려면
증명론 전체가 따라와야 한다. Verso 문서에 산문으로만 남긴다. -/

end Reynolds.Answers.Ch01
