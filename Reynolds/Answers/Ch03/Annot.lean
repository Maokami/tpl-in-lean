/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Answers.Ch03.Soundness

/-!
# §3.4 주석 명세와 검증 조건

`{p} c {q}` 의 유도 나무는 크다. Reynolds 는 그것을 **명령 안에 단언을 끼워 넣은** 모양으로
줄여 적는다.

```
{ x = a ∧ y = b }
t := x ;
{ t = a ∧ y = b }
x := y ;
{ t = a ∧ x = b }
y := t
{ y = a ∧ x = b }
```

규칙이 정하지 못하는 것은 둘뿐이다 — 순차 합성의 **이음매**와 반복의 **불변식**. 나머지는
규칙이 계산한다. 대입 공리는 사후조건에서 사전조건을 만들고, 결과 규칙은 이음매마다
"이것이 저것보다 강한가" 를 묻는다.

## 두 길

가장 값싼 길은 `Hoare` 의 항 자체를 주석 명세로 읽는 것이다. `Hoare.seq (Hoare.assign _ _ _)
(Hoare.assign _ _ _)` 에 이음매가 보인다. `Hoare.lean` 의 `swap_hoare` 가 그 길이다.

이 파일은 한 걸음 더 간다. 이음매와 불변식만 붙인 구문 `Annot` 을 두고, 거기서 **확인해야
할 함의들**(검증 조건, verification condition) 을 뽑아 내는 함수 `vcg` 를 만든다. 뽑힌 함의가
전부 타당하면 유도가 있다 (`Annot.vcg_sound`). 실제 검증 도구(Dafny, Why3)가 하는 일의
축소판이고, §3.8·§3.9 의 예제가 "함의 몇 개를 `omega` 로 닫는다" 로 줄어든다.

## 뒤로 간다

`vcg` 는 사후조건에서 출발해 **뒤로** 간다. 대입 공리가 거꾸로이기 때문이다 (`Assign.lean`).
그래서 `Annot.vcg a q` 는 "사후조건 `q` 에 대해 `a` 가 요구하는 사전조건" 과 도중에 쌓인
검증 조건들의 쌍이다.

## 읽는 순서
`Assign.lean` → 이 파일.
-/

@[expose] public section

namespace Reynolds.Answers.Ch03

open Reynolds Reynolds.Answers.Ch01 Reynolds.Answers.Ch02

universe u

variable {V : Type u} [DecidableEq V]

/-! ## 1. 주석 명령 -/

-- ANCHOR: annot
/-- 주석 명령. 이음매(`seq` 의 가운데)와 불변식(`wh` 의 첫 인자)만 사람이 적는다. -/
inductive Annot (V : Type u) where
  | assign : V → IntExp V → Annot V
  | skip
  /-- `a₀ ; {r} a₁` — 가운데가 이음매. -/
  | seq : Annot V → Assert V → Annot V → Annot V
  | ite : BoolExp V → Annot V → Annot V → Annot V
  /-- `while b do {i} a` — `i` 가 불변식. -/
  | wh : Assert V → BoolExp V → Annot V → Annot V
  | newvar : V → IntExp V → Annot V → Annot V

/-- 주석을 지우면 명령이다. -/
def Annot.erase : Annot V → Comm V
  | .assign v e     => .assign v e
  | .skip           => .skip
  | .seq a₀ _ a₁    => .seq a₀.erase a₁.erase
  | .ite b a₀ a₁    => .ite b a₀.erase a₁.erase
  | .wh _ b a       => .wh b a.erase
  | .newvar v e a   => .newvar v e a.erase
-- ANCHOR_END: annot

/-! ## 2. 검증 조건 생성기

사후조건에서 뒤로 가며 사전조건을 계산하고, 도중에 확인할 함의 `(강한 쪽, 약한 쪽)` 을 모은다.

- 대입 — 치환. 조건 없음.
- 순차 — 이음매 `r` 가 `a₁` 의 사전조건보다 강해야 한다.
- 조건 — 사전조건은 `(b ⇒ p₀) ∧ (¬b ⇒ p₁)`. 조건 없음.
- 반복 — 사전조건은 불변식. `i ∧ b` 가 본체의 사전조건보다, `i ∧ ¬b` 가 `q` 보다 강해야 한다.
- 변수 선언 — 사전조건은 `∀ v. v = e ⇒ p`. 결합자를 밖으로 내보내지 않는 방법이다.
-/

-- ANCHOR: vcg
/-- 검증 조건 생성기. `(사전조건, 확인할 함의들)`. -/
def Annot.vcg [HasFresh V] : Annot V → Assert V → Assert V × List (Assert V × Assert V)
  | .assign v e, q   => (q /[v := e], [])
  | .skip, q         => (q, [])
  | .seq a₀ r a₁, q  => ((a₀.vcg r).1, (r, (a₁.vcg q).1) :: ((a₀.vcg r).2 ++ (a₁.vcg q).2))
  | .ite b a₀ a₁, q  =>
      (.bin .and (.bin .imp b.toAssert (a₀.vcg q).1) (.bin .imp (.not b.toAssert) (a₁.vcg q).1),
        (a₀.vcg q).2 ++ (a₁.vcg q).2)
  | .wh i b a, q     =>
      (i, (i ⋀ b.toAssert, (a.vcg i).1) :: (i ⋀ .not b.toAssert, q) :: (a.vcg i).2)
  | .newvar v e a, q => (.quant .all v (.bin .imp (.cmp .eq (.var v) e) (a.vcg q).1), (a.vcg q).2)
-- ANCHOR_END: vcg

/-- 변수 선언의 결합자가 그 자리의 사후조건과 초기값 식에 안 나온다. `vcg` 가 만드는 사전조건은
결합자를 `∀` 로 가두므로 그쪽 조건은 저절로 된다. -/
def Annot.NewvarFresh : Annot V → Assert V → Prop
  | .assign _ _, _    => True
  | .skip, _          => True
  | .seq a₀ r a₁, q   => a₀.NewvarFresh r ∧ a₁.NewvarFresh q
  | .ite _ a₀ a₁, q   => a₀.NewvarFresh q ∧ a₁.NewvarFresh q
  | .wh i _ a, _      => a.NewvarFresh i
  | .newvar v e a, q  => v ∉ q.fv ∧ v ∉ e.fv ∧ a.NewvarFresh q

/-! ## 3. 검증 조건이 전부 타당하면 유도가 있다 -/

/-- `(b ⇒ p₀) ∧ (¬b ⇒ p₁)` 에 `b` 를 더하면 `p₀` 다. -/
theorem ite_pre_then (b : BoolExp V) (p₀ p₁ : Assert V) :
    Stronger (Assert.bin .and (.bin .imp b.toAssert p₀) (.bin .imp (.not b.toAssert) p₁)
      ⋀ b.toAssert) p₀ := by
  intro σ h
  obtain ⟨⟨h₀, _⟩, hb⟩ := (Assert.eval_and _ _ _).mp h
  exact h₀ hb

/-- `(b ⇒ p₀) ∧ (¬b ⇒ p₁)` 에 `¬b` 를 더하면 `p₁` 다. -/
theorem ite_pre_else (b : BoolExp V) (p₀ p₁ : Assert V) :
    Stronger (Assert.bin .and (.bin .imp b.toAssert p₀) (.bin .imp (.not b.toAssert) p₁)
      ⋀ .not b.toAssert) p₁ := by
  intro σ h
  obtain ⟨⟨_, h₁⟩, hb⟩ := (Assert.eval_and _ _ _).mp h
  exact h₁ hb

/-- `∀ v. v = e ⇒ p` 에 `v = e` 를 더하면 `p` 다. `v` 자리에 `v` 자신의 값을 넣는다. -/
theorem newvar_pre (v : V) (e : IntExp V) (p : Assert V) :
    Stronger (Assert.quant .all v (.bin .imp (.cmp .eq (.var v) e) p) ⋀ .cmp .eq (.var v) e) p := by
  intro σ h
  obtain ⟨hall, hv⟩ := (Assert.eval_and _ _ _).mp h
  have := hall (σ v)
  rw [State.subst_def, Function.update_eq_self] at this
  exact this hv

-- ANCHOR: vcgSound
/--
**검증 조건이 전부 타당하면 유도가 있다.**

`Annot` 에 대한 귀납. 절마다 규칙 하나와 결과 규칙의 반쪽이 든다 — 이음매와 불변식에서는
검증 조건이, 조건과 변수 선언에서는 위의 세 보조 함의가.
-/
@[exercise "§3.4 vcg-sound" 3]
theorem Annot.vcg_sound [HasFresh V] (a : Annot V) (q : Assert V) (hf : a.NewvarFresh q)
    (hvc : ∀ vc ∈ (a.vcg q).2, Stronger vc.1 vc.2) : Hoare (a.vcg q).1 a.erase q := by
  induction a generalizing q with
  | assign v e => exact Hoare.assign q v e
  | «skip» => exact Hoare.skip q
  | seq a₀ r a₁ ih₀ ih₁ =>
    obtain ⟨hf₀, hf₁⟩ := hf
    simp only [Annot.vcg, List.mem_cons, List.mem_append] at hvc
    have h₀ := ih₀ r hf₀ fun vc hvc' => hvc vc (Or.inr (Or.inl hvc'))
    have h₁ := ih₁ q hf₁ fun vc hvc' => hvc vc (Or.inr (Or.inr hvc'))
    exact Hoare.seq h₀ (Hoare.strengthen (hvc _ (Or.inl rfl)) h₁)
  | ite b a₀ a₁ ih₀ ih₁ =>
    obtain ⟨hf₀, hf₁⟩ := hf
    simp only [Annot.vcg, List.mem_append] at hvc
    have h₀ := ih₀ q hf₀ fun vc hvc' => hvc vc (Or.inl hvc')
    have h₁ := ih₁ q hf₁ fun vc hvc' => hvc vc (Or.inr hvc')
    exact Hoare.ite (Hoare.strengthen (ite_pre_then b _ _) h₀)
      (Hoare.strengthen (ite_pre_else b _ _) h₁)
  | wh i b a ih =>
    simp only [Annot.vcg, List.mem_cons] at hvc
    have h := ih i hf fun vc hvc' => hvc vc (Or.inr (Or.inr hvc'))
    exact Hoare.weaken (Hoare.wh (Hoare.strengthen (hvc _ (Or.inl rfl)) h))
      (hvc _ (Or.inr (Or.inl rfl)))
  | «newvar» v e a ih =>
    obtain ⟨hq, he, hf'⟩ := hf
    have h := ih q hf' hvc
    refine Hoare.newvar ?_ hq he (Hoare.strengthen (newvar_pre v e _) h)
    simp [Annot.vcg, Assert.fv]
-- ANCHOR_END: vcgSound

/-! ## 4. 맞바꾸기, 세 번째

§2.5 는 계산으로, `Hoare.lean` 은 유도 나무로, 여기서는 주석 명세로. 이음매 둘을 적고 나면
검증 조건은 둘이고, 남는 것은 맨 앞의 함의 하나다. -/

-- ANCHOR: swapAnnot
/-- 주석 붙은 맞바꾸기. 이음매가 Reynolds §3.4 의 주석 그대로다. -/
def swapAnnot : Annot String :=
  .seq (.assign "t" ⟪ x ⟫ₑ) (⟪ t = a ∧ y = b ⟫ₐ)
    (.seq (.assign "x" ⟪ y ⟫ₑ) (⟪ t = a ∧ x = b ⟫ₐ) (.assign "y" ⟪ t ⟫ₑ))

/-- 주석을 지우면 §2.5 의 `swap` 이다. -/
theorem swapAnnot_erase : swapAnnot.erase = swap := rfl

/-- 검증 조건 두 개와 맨 앞의 함의 하나. 셋 다 치환을 펼치면 항등이다. -/
theorem swap_hoare' : Hoare (⟪ x = a ∧ y = b ⟫ₐ) swap (⟪ y = a ∧ x = b ⟫ₐ) := by
  rw [← swapAnnot_erase]
  refine Hoare.strengthen ?_ (Annot.vcg_sound swapAnnot _ ⟨trivial, trivial, trivial⟩ ?_)
  · intro σ h
    simpa [swapAnnot, Annot.vcg, Assert.subst, IntExp.subst, Assert.eval, IntExp.eval,
      Cmp.denote, LogOp.denote, Function.update] using h
  · intro vc hvc σ h
    simp only [swapAnnot, Annot.vcg, List.nil_append, List.append_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hvc
    rcases hvc with rfl | rfl <;>
      simpa [Assert.subst, IntExp.subst, Assert.eval, IntExp.eval, Cmp.denote, LogOp.denote,
        Function.update] using h
-- ANCHOR_END: swapAnnot

/-! ## 5. 여기서 어디로 가나

`vcg` 는 부분 정확성만 안다. 종료를 말하려면 반복마다 **변항**을 더 적어야 하고, 그것이
§3.5 의 전체 정확성 규칙이다 (`Total.lean`). -/

end Reynolds.Answers.Ch03
