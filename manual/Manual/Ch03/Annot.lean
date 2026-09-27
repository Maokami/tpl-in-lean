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
-- 긴 증명을 인용하는 쪽이라 하이라이트 재구성이 기본 한도를 넘는다.
set_option maxHeartbeats 1000000
set_option verso.exampleModule "Reynolds.Answers.Ch03.Annot"

#doc (Manual) "§3.4~3.5 주석 명세와 전체 정확성" =>
%%%
tag := "ch03-annot"
file := "ch03-annot"
number := false
%%%

유도 나무는 금방 커진다. Reynolds는 그것을 명령 사이사이에 단언을 끼워 넣은 _주석
명세_(annotated specification)로 줄여 적는다. 규칙이 스스로 정하지 못하는 것은 두 가지뿐이다.
순차 합성의 _이음매_와 반복의 _불변식_이다. 나머지는 규칙이 계산한다.

# 주석 명령
%%%
tag := "ch03-annot-syntax"
file := "ch03-annot-syntax"
number := false
%%%

사람이 적어야 하는 것만 붙인 구문을 둔다. 주석을 지우면 명령이 된다.

```anchor annot (module := Reynolds.Answers.Ch03.Annot)
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
```

# 검증 조건 생성기
%%%
tag := "ch03-vcg"
file := "ch03-vcg"
number := false
%%%

사후조건에서 _뒤로_ 가며 사전조건을 계산하고, 도중에 확인해야 할 함의들을 모은다.
대입 공리가 거꾸로 가기 때문에 계산도 거꾸로 간다.

```anchor vcg (module := Reynolds.Answers.Ch03.Annot)
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
```

: 대입

  사후조건에 치환을 건다. 확인할 것은 없다.

: 순차 합성

  이음매 `r`이 뒤쪽 명령의 사전조건보다 강해야 한다. 이것이 검증 조건 하나다.

: 조건

  `(b ⇒ p₀) ∧ (¬b ⇒ p₁)`. 확인할 것은 없다.

: 반복

  사전조건은 불변식이다. `i ∧ b`가 본체의 사전조건보다 강한지, `i ∧ ¬b`가 사후조건보다
  강한지를 확인해야 한다.

: 변수 선언

  `∀ v. v = e ⇒ p`. 결합자를 `∀`로 가두면 바깥 단언에 새지 않는다.

검증 조건이 전부 타당하면 `Hoare` 유도가 있다(`Annot.vcg_sound`). Dafny나 Why3 같은 검증
도구가 하는 일의 축소판이다. 맞바꾸기에 주석을 달면 남는 일은 치환을 펼치는 것뿐이다.

```anchor swapAnnot (module := Reynolds.Answers.Ch03.Annot)
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
```

# 전체 정확성 — 변항
%%%
tag := "ch03-total"
file := "ch03-total"
number := false
%%%

전체 정확성 체계는 `while` 규칙만 다르다. 끝난다는 것을 말하려면 한 바퀴마다 _줄어드는
양_, 곧 변항(variant)이 있어야 한다.

```anchor hoareT (module := Reynolds.Answers.Ch03.Total)
/-- 전체 정확성의 추론 체계. `wh` 만 `Hoare` 와 다르다. -/
inductive HoareT [HasFresh V] : Assert V → Comm V → Assert V → Prop where
  | skip (p : Assert V) : HoareT p .skip p
  | assign (q : Assert V) (v : V) (e : IntExp V) :
      HoareT (q /[v := e]) (.assign v e) q
  | seq {p r q : Assert V} {c₀ c₁ : Comm V} :
      HoareT p c₀ r → HoareT r c₁ q → HoareT p (.seq c₀ c₁) q
  | ite {p q : Assert V} {b : BoolExp V} {c₀ c₁ : Comm V} :
      HoareT (p ⋀ b.toAssert) c₀ q → HoareT (p ⋀ .not b.toAssert) c₁ q →
      HoareT p (.ite b c₀ c₁) q
  /-- 반복. `i` 가 불변식, `e` 가 변항, `z` 가 한 바퀴 시작의 `e` 값을 붙드는 유령 변수. -/
  | wh {i : Assert V} {b : BoolExp V} {c : Comm V} {e : IntExp V} {z : V}
      (hzi : z ∉ i.fv) (hzb : z ∉ b.fv) (hzc : z ∉ c.fv) (hze : z ∉ e.fv)
      (hnonneg : Stronger (i ⋀ b.toAssert) (.cmp .le (.num 0) e)) :
      HoareT (i ⋀ b.toAssert ⋀ .cmp .eq e (.var z)) c (i ⋀ .cmp .lt e (.var z)) →
      HoareT i (.wh b c) (i ⋀ .not b.toAssert)
  | newvar {p q : Assert V} {v : V} {e : IntExp V} {c : Comm V}
      (hp : v ∉ p.fv) (hq : v ∉ q.fv) (he : v ∉ e.fv) :
      HoareT (p ⋀ .cmp .eq (.var v) e) c q → HoareT p (.newvar v e c) q
  | conseq {p p' q q' : Assert V} {c : Comm V} :
      Stronger p' p → HoareT p c q → Stronger q q' → HoareT p' c q'
```

`z`는 본체 실행 전의 `e` 값을 기억하는 _유령 변수_다. 명세에는 나오지만 명령에는
자유롭게 나오지 않는다. `z ∉ FV(c)`는 본체가 이 값을 보존한다는 사실뿐 아니라,
`z`를 바꾼 입력에서의 실행 결과를 원래 입력으로 옮기는 데도 쓰인다. 값의 보존만
말할 때는 더 약한 `z ∉ FA(c)`로 충분하다.

§3.1에서 보았듯 전체 정확성은 극한을 통과하지만, `⊥`에서 종료를 보일 수 없어 Scott
귀납법의 시작 조건이 막힌다. 그래서 건전성 증명은 측도 위의 정초 귀납을 쓴다.
2장에서 구체적인 루프의 값을 계산할 때 손으로
잡던 측도를 이제는 규칙이 인자로 받는다.

의미 단언에서는 실행 전 변항 값을 `n : Int`로 기억한다. 연습에서는 변항보다 큰
자연수 상계를 줄이는 귀납법을 구성한다. 비음수 조건은 반복 조건이 참일 때만 필요하므로,
마지막 본체 실행이 변항을 음수로 만들어도 다음 조건이 거짓이면 된다.

```anchor stmtWhtSound (module := Reynolds.Answers.Ch03.Semantic)
/--
WHT (§3.4). 본체가 불변식을 보존하고 정수 변항을 엄격히 줄이면 반복이 종료한다.
변항의 비음수 조건은 불변식과 반복 조건이 참인 상태에만 요구한다.
마지막 실행 뒤 조건이 거짓이면 변항은 음수여도 된다.

**책과의 차이**: 책 p64의 유령 변수 대신 본체 실행 전의 값을 `n : Int`로 고정한다.
구문 단언의 유령 변수 규칙은 `Total.lean`에서 이 정리의 따름정리로 얻는다.
-/
@[exercise "§3.4 wht-sound" 3]
theorem TotalCorrectS.wh {I : State V → Prop} {E : State V → Int}
    {b : BoolExp V} {c : Comm V}
    (hbody : ∀ n : Int, TotalCorrectS
      (fun σ => I σ ∧ ⟦b⟧ᵇ σ = true ∧ E σ = n) c (fun σ => I σ ∧ E σ < n))
    (hnonneg : ∀ σ, I σ → ⟦b⟧ᵇ σ = true → 0 ≤ E σ) :
    TotalCorrectS I (.wh b c) (fun σ => I σ ∧ ⟦b⟧ᵇ σ = false)
```

구문 판 `whT_sound`는 책 p64의 유령 변수 규칙을 그대로 유지하는 제공 정리다.
본체를 `σ[z := n]`에서 실행한 뒤, 명제 2.6으로 `z` 밖의 결과를 원래 입력의 실행에
옮긴다. 이 과정은 의미 규칙에 줄 전제를 만들며, 반복의 종료는 위 연습이 증명한다.


명제 2.6의 두 반쪽이 모두 쓰인다. (b)는 본체가 `z`를 건드리지 않음을, (a)는 `z`만 다른 두
시작 상태에서 본체의 결과가 불변식과 변항이 보는 변수들 위에서 같음을 준다.

§2.8의 백까지 세기를 규칙만으로 유도하면, 이번에는 끝난다는 것까지 얻는다.

```anchor countT (module := Reynolds.Answers.Ch03.Total)
/-- `[x ≤ 100] while x < 100 do x := x + 1 [x = 100]`. -/
theorem countTo100_total :
    HoareT (⟪ x ≤ 100 ⟫ₐ) ⟪ while x < 100 do x := x + 1 ⟫ᶜ (⟪ x = 100 ⟫ₐ) := by
  refine HoareT.weaken (HoareT.wh (e := ⟪ 100 - x ⟫ₑ) (z := "z") ?_ ?_ ?_ ?_ ?_ ?_) ?_
  · simp [Assert.fv, IntExp.fv]
  · simp [BoolExp.fv, IntExp.fv]
  · simp [Comm.fv, IntExp.fv]
  · simp [IntExp.fv]
  · intro σ h
    simp [BoolExp.toAssert, Assert.eval, IntExp.eval, IntOp.denote, Cmp.denote, LogOp.denote] at h ⊢
    omega
  · refine HoareT.strengthen ?_ (HoareT.assign _ "x" _)
    intro σ h
    simp [BoolExp.toAssert, Assert.subst, IntExp.subst, Assert.eval, IntExp.eval, IntOp.denote,
      Cmp.denote, LogOp.denote, Function.update] at h ⊢
    omega
  · intro σ h
    simp [BoolExp.toAssert, Assert.eval, IntExp.eval, Cmp.denote, LogOp.denote] at h ⊢
    omega

/-- 그러니 §2.8 에서 계산으로 얻은 것을 규칙만으로 다시 얻는다 — 그리고 이번에는 끝난다는 것까지. -/
example : ［⟪ x ≤ 100 ⟫ₐ］⟪ while x < 100 do x := x + 1 ⟫ᶜ［⟪ x = 100 ⟫ₐ］ :=
  countTo100_total.sound
```
