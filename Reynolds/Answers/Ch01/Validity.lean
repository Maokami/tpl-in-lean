/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Answers.Ch01.Semantics
public import Reynolds.Answers.Ch01.Notation
public import Reynolds.Meta.Exercise

/-!
# §1.3 타당성과 추론 (Validity and Inference)

Reynolds §1.3 (pp. 12–15) 에 대응한다.

## 이 파일에서 다루는 것
- 타당(valid) · 충족 불가능(unsatisfiable) · 강함/약함 · 동치
- 추론 규칙과 형식 증명
- 건전성(soundness) — 증명된 것은 타당하다
- 추론과 함의를 구분해야 하는 이유

## 배경

단언 하나만으로는 진리값이 없고 상태가 있어야 정해진다(`Background.lean` §4).
그래서 "참이다" 가 세 갈래로 나뉜다.

* `σ` 에서 참 — `⟦p⟧ₐ σ`
* 타당(valid) — 모든 `σ` 에서 참
* 충족 불가능(unsatisfiable) — 어떤 `σ` 에서도 거짓

증명의 각 단계는 이 중 타당이어야 한다. `x > 0` 은 `x ↦ 0` 인 상태에서 거짓이므로
증명 단계가 될 수 없다. 이 파일 §4 의 두 정리가 그 구분을 형식으로 옮긴 것이다.

## 읽는 순서
`Semantics.lean` → 이 파일 → `Substitution.lean`

## 책과의 차이
Reynolds 는 완전한 추론 체계를 주지 않고 논리학 교과서를 보라고 한다
(*"consult any elementary text on logic"*). 개념을 보이는 것이 목적이기 때문이다.
여기서도 §1.3 에 나오는 규칙만으로 작은 체계를 만들고 건전성까지만 증명한다.
완전성(completeness)은 범위 밖이다.
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
`p`가 `q`보다 **강하다(stronger)**. `q`는 `p`보다 **약하다(weaker)**.

Reynolds가 곧바로 붙이는 단서가 있다.

> *"'stronger' and 'weaker' are dual preorders, which does not quite jibe with normal
> English usage. For example, any assertion is both stronger and weaker than itself."*

`Stronger`는 반사적이고 추이적인 준순서(preorder)다. 어떤 단언이든 자기 자신보다 강하면서
동시에 약한 것은 반사성 때문이다. 의미가 같지만 구문이 다른 단언도 서로 강하므로, 구문
등식에 대한 반대칭성은 일반적으로 성립하지 않는다.
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

/-! ## 합성성의 귀결 — 같은 뜻이면 바꿔 넣어도 된다

Reynolds §1.2 p.11 은 의미 방정식이 구문 지향(syntax-directed)이라는 사실에서 바로
*합성성(compositionality)* 을 끌어낸다.

> *"A semantics is said to be compositional when the meaning of each phrase does not
> depend on any property of its immediate subphrases except the meanings of these
> subphrases. … It implies that, in any phrase, one can replace an occurrence of a
> subphrase by another phrase with the same meaning, without changing the meaning of
> the enclosing phrase."*

이 귀결을 문맥마다 따로 보이는 대신, 단언의 생성자 각각이 `Equivalent`를 보존한다는
합동(congruence) 보조정리로 한 번에 준다. `Assert.eval`이 구문을 조립하는 방식 그대로
값을 조립하는 구조적 재귀이므로, 부분구를 뜻이 같은 다른 구로 바꿔 끼워도 `eval`의
결과가 바뀌지 않는다 — 합성적 의미론이면 이 합동은 공짜로 따라온다.

§1.4 p.21에서 이름 바꾸기 정리(명제 1.5) 바로 뒤에 Reynolds가 다시 꺼내는 문장이
정확히 이 원리를 쓴다.

> *"From this proposition and the compositional nature of our semantics, it is clear
> that, in any context, one can replace an occurrence of a subphrase of the form
> ∀v. q by ∀vnew. (q/v → vnew), without changing the meaning of the context."*

`renaming_assert`(`Substitution.lean`)는 "그 양화 구 하나"의 뜻이 같다는 것만 보인다.
"어느 문맥에 넣어도" 쪽은 아래 생성자별 합동(`not_congr`, `bin_congr`, `quant_congr`)을
문맥의 모양에 대한 귀납으로 이어서 얻는다. 둘을 합치면 책이 산문으로 주장하는 "α-변환은
임의의 문맥에서 적용된다"가 된다. -/

/--
부정의 합동. 부분구를 뜻이 같은 다른 부분구로 바꿔도 부정의 뜻은 바뀌지 않는다.

넷 중 구조가 가장 간단해서 심화 A1.8 연습으로 남긴다. 나머지(`bin_congr`,
`quant_congr`, `cmp_congr`)는 같은 패턴(정의를 펼치고 가정을 꽂는다)의 완성본이다 —
먼저 풀어 보고 패턴이 반복됨을 확인하는 자료로 쓴다.
-/
-- ANCHOR: stmtNotCongr
@[exercise "심화 A1.8" 1]
theorem Equivalent.not_congr {p p' : Assert V} (h : Equivalent p p') :
    Equivalent (.not p) (.not p')
-- ANCHOR_END: stmtNotCongr
    := by
  intro σ; simp [Assert.eval, h σ]

/-- 이항 논리 연산의 합동. 양쪽 피연산자를 독립적으로 뜻이 같은 것으로 바꿀 수 있다. -/
theorem Equivalent.bin_congr {op : LogOp} {p p' q q' : Assert V}
    (hp : Equivalent p p') (hq : Equivalent q q') :
    Equivalent (.bin op p q) (.bin op p' q') := by
  intro σ; simp [Assert.eval, hp σ, hq σ]

/--
비교의 합동. `cmp`의 두 자리는 단언이 아니라 정수 식이므로, `Equivalent` 대신
"모든 상태에서 같은 값을 낸다"는 정수 식 쪽의 대응 조건을 가정으로 받는다.
합성성이 단언 생성자에만 있는 성질이 아니라 정수 식과 단언을 넘나드는 경계에서도
그대로 성립함을 보여 준다.
-/
-- ANCHOR: Equivalent.cmp_congr
theorem Equivalent.cmp_congr {c : Cmp} {e₀ e₀' e₁ e₁' : IntExp V}
    (h₀ : ∀ σ, e₀.eval σ = e₀'.eval σ) (h₁ : ∀ σ, e₁.eval σ = e₁'.eval σ) :
    Equivalent (.cmp c e₀ e₁) (.cmp c e₀' e₁') := by
  intro σ; simp [Assert.eval, h₀ σ, h₁ σ]
-- ANCHOR_END: Equivalent.cmp_congr

/--
양화의 합동. 결합 변수 `v`는 그대로 두고 본문만 뜻이 같은 것으로 바꾼다.

`forall_congr'`/`exists_congr`가 그대로 적용되는 것은 우연이 아니다 — 객체 언어의
`∀v. p`가 메타 수준에서는 `∀ n, p.eval (σ[v := n])`이고, 그 조건부 동치가 각 `n`에서
성립한다는 가정(`h`)이 정확히 `forall_congr'`가 요구하는 모양이다. `v` 자체를 다른
이름으로 바꾸는 쪽은 `renaming_assert`가 맡는다. 이 정리와 `renaming_assert`를 합치면
"임의의 문맥에서 α-변환이 가능하다"는 p.21의 주장이 완성된다.
-/
-- ANCHOR: Equivalent.quant_congr
theorem Equivalent.quant_congr {qt : Quant} (v : V) {p p' : Assert V}
    (h : Equivalent p p') : Equivalent (.quant qt v p) (.quant qt v p') := by
  intro σ
  have key : ∀ n : Int, (p.eval (σ[v := n]) ↔ p'.eval (σ[v := n])) := fun n => h _
  cases qt
  · simpa [Assert.eval] using forall_congr' key
  · simpa [Assert.eval] using exists_congr key
-- ANCHOR_END: Equivalent.quant_congr

/-! ## 2. 추론 규칙과 형식 증명

Reynolds §1.3 은 **추론 규칙(inference rule)** 을 이렇게 정의한다:
전제(premiss) 0개 이상과 결론(conclusion) 하나. 가로선으로 구분한다.
전제가 없으면 **공리꼴(axiom schema)**, 메타변수도 없으면 그냥 **공리(axiom)**.

Lean 에서는 `inductive` 가 그 역할을 한다. 생성자 하나가 규칙 하나이고,
화살표 왼쪽이 전제, 오른쪽이 결론이다. Reynolds 의 가로선과 자리가 같다.

`Proof p` 의 값 하나가 증명 나무(proof tree)에 해당한다.
Reynolds 는 *"proof trees are more perspicuous than sequences"* 라고 하면서도
조판 문제로 나무 대신 열(sequence)을 쓴다고 적는데, Lean 에서는 나무 쪽이 기본이다. -/

-- ANCHOR: proofSystem
/--
술어 논리의 작은 추론 체계. Reynolds §1.3 p.13이 공리·공리꼴·두 전제 규칙·한 전제
규칙의 예로 직접 드는 넷 그대로다: `x + 0 = x`, `e₁ = e₀ ⇒ e₀ = e₁`, 전건 긍정,
보편 일반화.

완전한 체계가 아니고 그럴 의도도 없다. 책도 이 넷을 "예시"라고만 하고 나머지는
논리학 교과서로 미룬다(모듈 docstring의 "책과의 차이" 참고).
-/
inductive Proof : Assert V → Prop where
  /--
  공리: `x + 0 = x`. 책은 메타변수가 없는 구체적인 객체 변수 x로 든다 — 바로 다음
  공리꼴과 대조하려는 것이다(p.13, "notice the special role of axiom schemas").

  **책과의 차이**: 여기서는 모든 객체 변수 x에 대해 한 번에 선언한다. Lean에서 변수마다
  따로 공리를 선언하면 쓸 수 없는 정의가 되기 때문이다. 책의 "메타변수 없음"은 이 x 하나를
  구체적으로 고정했을 때의 이야기이고, 다형화 자체는 책에 없는 저장소의 선택이다.
  -/
  | addZero (x : V) : Proof (.cmp .eq (.bin .add (.var x) (.num 0)) (.var x))
  /--
  공리꼴: `e₁ = e₀ ⇒ e₀ = e₁`. 전제 없이 바로 쓸 수 있지만 `e₀`, `e₁`이 메타변수라서
  임의의 정수 식 쌍에 대한 사례를 전부 대신한다 — 공리와 공리꼴의 차이가 바로 이
  메타변수 유무다(p.13, "their instances are assertions that can appear anywhere
  in a proof, regardless of what, if anything, precedes them").
  -/
  | eqSymmSchema (e₀ e₁ : IntExp V) :
      Proof (.bin .imp (.cmp .eq e₁ e₀) (.cmp .eq e₀ e₁))
  /-- 두 전제 규칙 — 전건 긍정(modus ponens). -/
  | mp {p q : Assert V} : Proof p → Proof (.bin .imp p q) → Proof q
  /--
  한 전제 규칙 — 보편 일반화(∀-도입).

  전제가 타당할 때만 결론이 타당해진다. 이 파일 §4에서 이 규칙과 함의 `p ⇒ ∀v. p`를
  나란히 놓고 비교한다.
  -/
  | genAll (v : V) {p : Assert V} : Proof p → Proof (.quant .all v p)
-- ANCHOR_END: proofSystem

/--
책 p.13의 네 줄짜리 증명 그대로: `∀x. x = x + 0`.

1. `x + 0 = x` — 공리(`addZero`)
2. `x + 0 = x ⇒ x = x + 0` — 공리꼴(`eqSymmSchema`)
3. `x = x + 0` — 전건 긍정, 1·2에서
4. `∀x. x = x + 0` — 일반화, 3에서

책의 증명 나무가 그대로 Lean 항이 된다: `genAll`이 맨 바깥, `mp`가 그 전제이고
`addZero`·`eqSymmSchema`가 나무의 잎이다.
-/
example : Proof (⟪ ∀ x, x = x + 0 ⟫ₐ : Assert String) :=
  .genAll "x" (.mp (.addZero "x")
    (.eqSymmSchema (.var "x") (.bin .add (.var "x") (.num 0))))

/-! ## 3. 건전성 -/

/--
건전성(soundness). 증명된 것은 타당하다.

> *"the whole point of the concept of proof is its connection with semantics:
> If there is a proof of an assertion p, then p should be valid."* (§1.3)

`Proof` 에 대한 귀납법으로 증명한다. 케이스 하나가 규칙 하나의 건전성에 대응하므로,
규칙을 따로따로 검사하면 체계 전체가 따라온다.
-/
@[exercise "§1.3 건전성" 2]
theorem Proof.sound {p : Assert V} : Proof p → Valid p := by
  intro hp
  induction hp with
  | addZero x => intro σ; simp [Assert.eval, Cmp.denote, IntExp.eval, IntOp.denote]
  | eqSymmSchema e₀ e₁ =>
      intro σ; simp only [Assert.eval, LogOp.denote, Cmp.denote]; exact Eq.symm
  | mp _ _ ihp ihimp => intro σ; exact ihimp σ (ihp σ)
  | genAll v _ ih => intro σ n; exact ih _

/-! ## 4. 추론과 함의

Reynolds 가 §1.3 에서 한 페이지를 들여 다루는 대목이다. 두 정리를 나란히 둔다.

```
        p                                    ─────────────
     ───────  (건전한 규칙)                    p ⇒ ∀v. p     (타당하지 않다)
      ∀v. p
```

가로선은 타당한 것에서 타당한 것을 얻는다는 뜻이고,
화살표는 한 상태 안에서 앞이 참이면 뒤도 참이라는 뜻이다. 범위가 다르다. -/

-- ANCHOR: stmtGenSound
/-- 규칙 쪽. `p`가 타당하면 `∀v. p`도 타당하다. -/
@[exercise "§1.3 gen-sound" 1]
theorem valid_forall_of_valid (v : V) {p : Assert V} (h : Valid p) :
    Valid (.quant .all v p)
-- ANCHOR_END: stmtGenSound
    := fun _ _ => h _

-- ANCHOR: stmtGenNotImp
/--
함의 쪽. `x > 0 ⇒ ∀x. x > 0`은 타당하지 않다.

Reynolds의 반례를 그대로 쓴다. `x ↦ 3` 인 상태에서 왼쪽은 참이고,
오른쪽은 `x`에 0 을 넣으면 거짓이다.

같은 재료로 만든 규칙(위)과 함의(여기)의 판정이 갈린다.
-/
@[exercise "§1.3 gen-not-imp" 2]
theorem not_valid_imp_forall :
    ¬ Valid (.bin .imp (.cmp .gt (.var "x") (.num 0))
                       (.quant .all "x" (.cmp .gt (.var "x") (.num 0))) : Assert String)
-- ANCHOR_END: stmtGenNotImp
    := by
  intro h
  -- x ↦ 3 인 상태를 잡으면 왼쪽은 참이다.
  have h3 := h (State.const 3)
  simp only [Assert.eval, LogOp.denote, Cmp.denote, IntExp.eval, State.const] at h3
  -- 따라서 오른쪽이 성립해야 하는데, n = 0 을 넣으면 거짓이다.
  have := h3 (by decide) 0
  simp at this

/-! ## 5. 이 책이 다루지 않는 것

Reynolds 는 §1.3 을 이렇게 닫는다.

**논리적 타당성(logical validity)** — 표현식 연산의 의미까지 임의로 바꿔도 성립하는 것.
**완전성(completeness)** — 건전성의 역. 타당한 것은 모두 증명된다.

정수의 표준 해석을 고정하면 닫힌 단언 가운데 참인 산술 문장도 모두 다뤄야 한다. 이때
산술을 충분히 표현하면서 공리와 증명을 기계적으로 열거·검사할 수 있는 일관된 체계는
모든 참인 문장을 증명할 수 없다. 괴델의 불완전성 정리에는 이런 표현력과 효과성 조건이
필요하다.

반면 모든 구조에서 참인 문장만 묻는 일차 논리에는 건전하고 완전한 효과적 증명 체계가
있다. 이것이 괴델의 완전성 정리다.

Reynolds 는 프로그램 검증에서 논리적 완전성이 별 쓸모가 없다고 덧붙인다.
`+` 가 정말 덧셈인 해석에만 관심이 있기 때문이다. 예외는 §3.8 에서 다룬다.

이 주제는 코드로 옮기지 않는다. 증명론 전체가 따라와야 하고 Reynolds 도 다루지 않는다. -/

end Reynolds.Answers.Ch01
