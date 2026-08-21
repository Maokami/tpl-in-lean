/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Answers.Ch01.FreeVars
public import Reynolds.Answers.Ch01.Validity
public import Cslib.Foundations.Data.HasFresh

/-!
# §1.4 치환 (Substitution)

Reynolds §1.4 (pp. 18–21) 에 대응한다.

## 다루는 것
- 치환 사상 `Subst V` 와 동시 치환 `p /ₛ δ`
- 변수 포획(capture)을 피하는 법
- 명제 1.2 (a)(b)(c) — 치환의 구문적 성질
- 명제 1.3 (치환 정리) · 1.4 (유한 치환) · 1.5 (이름 바꾸기 정리)
- §1.3 의 공리꼴 `(∀v. p) ⇒ p / v ↦ e` 가 타당함

## 배경

Reynolds 는 이 절을 반례로 연다. 공리꼴

```
(∀v. p) ⇒ (p / v → e)
```

에서 `p := ∃y. y > x`, `v := x`, `e := y + 1` 을 넣으면 결론은

```
(∀x. ∃y. y > x)  ⇒  ((∃y. y > x) / x → y+1)
```

왼쪽은 어떤 상태에서도 참이다. 그런데 오른쪽을 `x` 자리에 `y + 1` 을 그냥 밀어 넣어
계산하면 `∃y. y > y + 1` 이 되어 어떤 상태에서도 거짓이다.

`y + 1` 의 자유 변수 `y` 가 `∃y` 에 잡아먹힌 것이다. 이것을 포획(capture)이라고 한다.
치환은 이 일이 생기지 않도록 결합 변수를 먼저 새 이름으로 바꾼 뒤 밀어 넣어야 한다.

## 읽는 순서
`FreeVars.lean` → 이 파일 → `Depth/TermMonad.lean` (선택)

## 책과의 차이
Reynolds 는 새 이름 `vnew` 를 "어떤 표준 순서에서 첫 번째" 로 정한다.
여기서는 `HasFresh.fresh` 로 뽑는다. 이어지는 명제들이 쓰는 성질은
`vnew` 가 특정 유한 집합 밖에 있다는 것 하나뿐이라, 어느 쪽이든 증명이 같다.
-/

@[expose] public section

namespace Reynolds.Answers.Ch01

open Reynolds

universe u

variable {V : Type u} [DecidableEq V]

/-! ## 1. 치환 사상과 정수 식의 치환 -/

-- ANCHOR: subst
/--
치환 사상(substitution map). Reynolds 의 `Θ = ⟨var⟩ → ⟨intexp⟩`.

변수 하나가 아니라 **모든 변수를 한꺼번에** 옮기는 함수다.
Reynolds가 동시 치환을 기본으로 둔 덕분에 이 파일 §3의 이름 있는 포획 회피 정의를
평범한 구조적 재귀로 적을 수 있다. 한 변수 치환도 별도의 종료 증명을 주거나 다른 변수
표현을 택하면 정의할 수 있지만, 같은 직접 재귀식으로는 처리되지 않는다.
-/
abbrev Subst (V : Type u) := V → IntExp V

/-- `e /ₛ δ` — 정수 식에 대한 동시 치환. 결합자가 없어서 그냥 훑으며 갈아 끼우면 된다. -/
def IntExp.subst : IntExp V → Subst V → IntExp V
  | .num n,        _ => .num n
  | .var v,        δ => δ v
  | .neg e,        δ => .neg (e.subst δ)
  | .bin op e₀ e₁, δ => .bin op (e₀.subst δ) (e₁.subst δ)
-- ANCHOR_END: subst

@[inherit_doc IntExp.subst]
scoped infixl:80 " /ₑ " => IntExp.subst

/-! ## 2. 새 결합 변수 고르기

`∀v. p` 에 `δ` 를 적용할 때, `v` 를 그대로 두면 `δ w` 안의 자유 변수가 `v` 에 잡힐 수 있다.
잡히면 안 되는 변수를 전부 모은 집합이 아래 `captureSet` 이고,
새 결합 변수는 그 집합 밖에서 고른다. -/

/--
`∀v. p` 를 `δ` 로 치환할 때 새 결합 변수가 피해야 할 변수들.

`p` 의 자유 변수 중 `v` 가 아닌 것들이 `δ` 로 가서 만들어 낼 자유 변수를 전부 모은 것이다.
`v` 자신은 `δ` 로 대체되어 사라지므로 뺀다.
-/
def captureSet (p : Assert V) (v : V) (δ : Subst V) : Finset V :=
  (p.fv.erase v).biUnion fun w => (δ w).fv

/--
새 결합 변수. Reynolds 의 `vnew`.

`v` 자체가 안전하면 `v` 를 그대로 쓴다. 불필요한 이름 바꾸기를 피하기 위해서다
(Reynolds 도 같은 조건을 붙인다). 안전하지 않을 때만 `HasFresh.fresh` 로 새로 뽑는다.
-/
def newBinder [HasFresh V] (p : Assert V) (v : V) (δ : Subst V) : V :=
  if v ∈ captureSet p v δ then Cslib.HasFresh.fresh (captureSet p v δ) else v

/-- 새 결합 변수는 어느 쪽 분기를 타든 피해야 할 집합 밖에 있다. -/
theorem newBinder_notMem [HasFresh V] (p : Assert V) (v : V) (δ : Subst V) :
    newBinder p v δ ∉ captureSet p v δ := by
  unfold newBinder
  split
  · exact Cslib.HasFresh.fresh_notMem _
  · assumption

/-- `w` 가 `p` 의 자유 변수이고 `v` 가 아니면, `δ w` 의 자유 변수에 새 결합 변수가 없다. -/
theorem newBinder_notMem_fv [HasFresh V] {p : Assert V} {v w : V} {δ : Subst V}
    (hw : w ∈ p.fv) (hne : w ≠ v) : newBinder p v δ ∉ (δ w).fv := by
  intro hmem
  exact newBinder_notMem p v δ
    (Finset.mem_biUnion.mpr ⟨w, Finset.mem_erase.mpr ⟨hne, hw⟩, hmem⟩)

/-! ## 3. 단언의 치환 -/

-- ANCHOR: assertSubst
/--
`p /ₛ δ` — 단언에 대한 동시 치환.

양화사 절만 특별하다.

```
(∀v. p) /ₛ δ = ∀ vnew. (p /ₛ δ[v := var vnew])
```

`v`를 새 이름 `vnew`로 바꾸고, 치환 사상 쪽에서도 `v`를 `var vnew`로 보내도록 고친다.
`vnew`는 `newBinder`가 골라 주므로, 실제로 본문에 자유롭게 나타나 치환되는
`w ∈ p.fv.erase v`에 대해 `δ w`의 자유 변수와 겹치지 않는다.

**정지성**: 재귀 호출이 `p` 라는 진부분항에 대해 일어나므로 구조적 재귀다.
"먼저 이름을 바꾸고 다시 치환한다"는 이름 있는 단일 치환의 직접 정의에는 별도의 정지성
증명이 필요하다. Reynolds의 동시 치환 정의는 그 추가 증명 없이 구조적 재귀로 받아들여진다.
-/
def Assert.subst [HasFresh V] : Assert V → Subst V → Assert V
  | .tru,          _ => .tru
  | .fls,          _ => .fls
  | .cmp c e₀ e₁,  δ => .cmp c (e₀ /ₑ δ) (e₁ /ₑ δ)
  | .not p,        δ => .not (p.subst δ)
  | .bin op p q,   δ => .bin op (p.subst δ) (q.subst δ)
  | .quant q v p,  δ =>
      .quant q (newBinder p v δ) (p.subst (Function.update δ v (.var (newBinder p v δ))))
-- ANCHOR_END: assertSubst

@[inherit_doc Assert.subst]
scoped infixl:80 " /ₛ " => Assert.subst

/-- `p / v ↦ e` — 한 변수만 바꾸는 치환. Reynolds 의 `p / v → e`. -/
scoped notation:80 p:80 " /[" v ":=" e "] " => Assert.subst p (Function.update IntExp.var v e)

/-! ## 4. 명제 1.2 — 치환의 구문적 성질 -/

-- ANCHOR: prop12
/-- **명제 1.2(a)** — 자유 변수 위에서 같은 치환 사상은 같은 결과를 낸다. 정수 식 판. -/
@[exercise "Prop 1.2a" 2]
theorem subst_congr_intExp :
    ∀ (e : IntExp V) (δ δ' : Subst V), (∀ w ∈ e.fv, δ w = δ' w) → e /ₑ δ = e /ₑ δ' := by
  intro e
  induction e with
  | num n => intro _ _ _; rfl
  | var v => intro _ _ h; exact h v (by simp [IntExp.fv])
  | neg e ih => intro δ δ' h; simp [IntExp.subst, ih δ δ' h]
  | bin op e₀ e₁ ih₀ ih₁ =>
      intro δ δ' h
      simp [IntExp.subst,
        ih₀ δ δ' fun w hw => h w (by simp [IntExp.fv, hw]),
        ih₁ δ δ' fun w hw => h w (by simp [IntExp.fv, hw])]

omit [DecidableEq V] in
/--
**명제 1.2(b)** — 항등 치환. Reynolds 의 `p / c_var = p`.

Reynolds 가 이 항목에 붙이는 주석이 있다.

> *"Note that part (b) of this proposition asserts that the constructor `c_var`, which injects
> variables into the corresponding integer expressions, acts as an identity substitution."*

이 등식이 모나드 우단위 법칙과 같은 자리에 있다는 것은 `Depth/TermMonad.lean` 에서 본다. (선택)
-/
theorem subst_var_intExp (e : IntExp V) : e /ₑ IntExp.var = e := by
  induction e with
  | num n => rfl
  | var v => rfl
  | neg e ih => simp [IntExp.subst, ih]
  | bin op e₀ e₁ ih₀ ih₁ => simp [IntExp.subst, ih₀, ih₁]

/-- **명제 1.2(c)** — 치환 후의 자유 변수. -/
@[exercise "Prop 1.2c" 2]
theorem fv_subst_intExp (e : IntExp V) (δ : Subst V) :
    (e /ₑ δ).fv = e.fv.biUnion fun w => (δ w).fv := by
  induction e with
  | num n => simp [IntExp.subst, IntExp.fv]
  | var v => simp [IntExp.subst, IntExp.fv]
  | neg e ih => simpa [IntExp.subst, IntExp.fv] using ih
  | bin op e₀ e₁ ih₀ ih₁ =>
      simp only [IntExp.subst, IntExp.fv, ih₀, ih₁]
      ext w
      simp only [Finset.mem_union, Finset.mem_biUnion]
      constructor
      · rintro (⟨a, ha, hb⟩ | ⟨a, ha, hb⟩)
        · exact ⟨a, Or.inl ha, hb⟩
        · exact ⟨a, Or.inr ha, hb⟩
      · rintro ⟨a, ha | ha, hb⟩
        · exact Or.inl ⟨a, ha, hb⟩
        · exact Or.inr ⟨a, ha, hb⟩
-- ANCHOR_END: prop12

/-- 단언 판의 명제 1.2(b). 양화사 절에서 `newBinder` 가 `v` 를 그대로 돌려주는 것이 핵심이다. -/
@[exercise "Prop 1.2b-assert" 3]
theorem subst_var_assert [HasFresh V] (p : Assert V) : p /ₛ IntExp.var = p := by
  induction p with
  | tru | fls => rfl
  | cmp c e₀ e₁ => simp [Assert.subst, subst_var_intExp]
  | not p ih => simp [Assert.subst, ih]
  | bin op p q ihp ihq => simp [Assert.subst, ihp, ihq]
  | quant q v p ih =>
      -- 항등 치환에서는 피해야 할 집합이 `p.fv.erase v` 로 줄어들고, `v` 는 거기 없다.
      have hcap : captureSet p v IntExp.var = p.fv.erase v := by
        simp [captureSet, IntExp.fv]
      have hv : newBinder p v IntExp.var = v := by
        simp [newBinder, hcap]
      have hupd : Function.update (IntExp.var : Subst V) v (.var v) = IntExp.var := by
        funext w; by_cases h : w = v <;> simp [h]
      simp [Assert.subst, hv, ih]

/-! ## 5. 명제 1.3 — 치환 정리 -/

-- ANCHOR: substThm
/--
**명제 1.3 (치환 정리)** — 정수 식 판.

> *"If p is a phrase of type θ, and σw = ⟦δw⟧intexp σ' for all w ∈ FV_θ(p),
> then ⟦p/δ⟧ σ' = ⟦p⟧ σ."*

구문을 먼저 바꾸고 나중에 평가하는 것과, 치환 사상을 먼저 평가해 상태를 만들고
거기서 평가하는 것이 같다는 말이다. 구문 조작과 상태 조작이 서로 대응한다.

Exercises 트리에서는 이 정수 식 판을 완성된 채로 준다. 단언 판이 이것을 쓰기 때문이다
(`AGENTS.md` §1-9). 직접 해 보고 싶으면 증명을 지우고 다시 써 보면 된다.
-/
theorem substitution_intExp :
    ∀ (e : IntExp V) (δ : Subst V) (σ σ' : State V),
      (∀ w ∈ e.fv, σ w = ⟦δ w⟧ₑ σ') → ⟦e /ₑ δ⟧ₑ σ' = ⟦e⟧ₑ σ := by
  intro e
  induction e with
  | num n => intro _ _ _ _; rfl
  | var v => intro _ _ _ h; exact (h v (by simp [IntExp.fv])).symm
  | neg e ih => intro δ σ σ' h; simp [IntExp.subst, IntExp.eval, ih δ σ σ' h]
  | bin op e₀ e₁ ih₀ ih₁ =>
      intro δ σ σ' h
      simp [IntExp.subst, IntExp.eval,
        ih₀ δ σ σ' fun w hw => h w (by simp [IntExp.fv, hw]),
        ih₁ δ σ σ' fun w hw => h w (by simp [IntExp.fv, hw])]

/--
**명제 1.3 (치환 정리)** — 단언 판.

양화사 절이 이 파일에서 가장 손이 많이 가는 자리다. 순서는 이렇다.

1. 결론을 `∀ n` (또는 `∃ n`) 아래로 내린다.
2. 귀납 가설을 `σ[v := n]`, `σ'[vnew := n]`, `δ[v := var vnew]` 에 적용한다.
3. 그러려면 `∀ w ∈ p.fv, σ[v := n] w = ⟦δ[v := var vnew] w⟧ₑ (σ'[vnew := n])` 이 필요하다.
   - `w = v` 면 양쪽 다 `n` 이다.
   - `w ≠ v` 면 원래 가설이 `σ w = ⟦δ w⟧ₑ σ'` 를 준다. 남는 것은
     `σ'` 를 `vnew` 자리에서 덮어써도 `⟦δ w⟧ₑ` 가 안 변한다는 사실인데,
     `newBinder_notMem_fv` 와 일치 정리(`coincidence_intExp`)가 그것을 준다.
-/
@[exercise "Prop 1.3-assert" 3]
theorem substitution_assert [HasFresh V] :
    ∀ (p : Assert V) (δ : Subst V) (σ σ' : State V),
      (∀ w ∈ p.fv, σ w = ⟦δ w⟧ₑ σ') → (⟦p /ₛ δ⟧ₐ σ' ↔ ⟦p⟧ₐ σ) := by
  intro p
  induction p with
  | tru | fls => intro _ _ _ _; rfl
  | cmp c e₀ e₁ =>
      intro δ σ σ' h
      have h₀ := substitution_intExp e₀ δ σ σ' fun w hw => h w (by simp [Assert.fv, hw])
      have h₁ := substitution_intExp e₁ δ σ σ' fun w hw => h w (by simp [Assert.fv, hw])
      simp [Assert.subst, Assert.eval, h₀, h₁]
  | not p ih => intro δ σ σ' h; simp [Assert.subst, Assert.eval, ih δ σ σ' h]
  | bin op p q ihp ihq =>
      intro δ σ σ' h
      have hp := ihp δ σ σ' fun w hw => h w (by simp [Assert.fv, hw])
      have hq := ihq δ σ σ' fun w hw => h w (by simp [Assert.fv, hw])
      cases op <;> simp [Assert.subst, Assert.eval, LogOp.denote, hp, hq]
  | quant q v p ih =>
      intro δ σ σ' h
      set vnew := newBinder p v δ with hvnew
      -- 갱신된 상태와 갱신된 치환 사상에 대해 귀납 가설의 전제를 확인한다.
      have key : ∀ n : Int,
          (⟦p /ₛ Function.update δ v (.var vnew)⟧ₐ (σ'[vnew := n]) ↔ ⟦p⟧ₐ (σ[v := n])) := by
        intro n
        refine ih (Function.update δ v (.var vnew)) _ _ ?_
        intro w hw
        by_cases hwv : w = v
        · subst hwv; simp [IntExp.eval]
        · -- `w` 는 `∀v. p` 의 자유 변수이므로 원래 가설을 쓸 수 있다.
          have hww : σ w = ⟦δ w⟧ₑ σ' := h w (by simp [Assert.fv, Finset.mem_erase, hwv, hw])
          -- `vnew` 는 `δ w` 의 자유 변수가 아니므로 `σ'` 를 거기서 덮어써도 값이 같다.
          have hfresh : vnew ∉ (δ w).fv := newBinder_notMem_fv hw hwv
          have hcoin : ⟦δ w⟧ₑ (σ'[vnew := n]) = ⟦δ w⟧ₑ σ' := by
            refine coincidence_intExp (δ w) _ σ' ?_
            intro u hu
            have : u ≠ vnew := by rintro rfl; exact hfresh hu
            simp [this]
          simp [hwv, hcoin, hww]
      cases q
      · simpa [Assert.subst, Assert.eval, ← hvnew] using forall_congr' key
      · simpa [Assert.subst, Assert.eval, ← hvnew] using exists_congr key
-- ANCHOR_END: substThm

/-! ## 6. 명제 1.4 — 유한 치환 -/

/--
**명제 1.4 (유한 치환 정리)** — 한 변수만 바꾸는 경우.

명제 1.3 에서 `σ := σ'[v := ⟦e⟧ₑ σ']` 로 두면 바로 나온다.
Reynolds 는 여러 변수를 동시에 바꾸는 형태로 쓰지만, 이어지는 §7 에서 필요한 것은
한 변수 판이므로 그것만 적는다.
-/
theorem substitution_single [HasFresh V] (p : Assert V) (v : V) (e : IntExp V) (σ : State V) :
    (⟦p /[v := e] ⟧ₐ σ ↔ ⟦p⟧ₐ (σ[v := ⟦e⟧ₑ σ])) := by
  refine substitution_assert p _ _ σ ?_
  intro w _
  by_cases hwv : w = v
  · subst hwv; simp
  · simp [hwv, IntExp.eval]

/-! ## 7. 명제 1.5 — 이름 바꾸기 정리 -/

/--
**명제 1.5 (이름 바꾸기 정리)** — α-변환은 뜻을 보존한다.

`vnew` 가 `FV(p) \ {v}` 밖에 있으면 `∀vnew. (p / v ↦ vnew)` 와 `∀v. p` 의 뜻이 같다.

Reynolds 가 이 명제 뒤에 붙이는 말을 옮겨 둔다.

> *"The principle that renaming preserves meaning is a property of all languages with
> well-behaved binding. (We will see in Section 11.7, however, that this does not include
> all well-known programming languages.)"*

§11.7 의 동적 결합(dynamic binding)이 이 성질을 깨뜨린다는 예고다.
-/
theorem renaming_assert [HasFresh V] (q : Quant) (v vnew : V) (p : Assert V)
    (hfresh : vnew ∉ p.fv.erase v) (σ : State V) :
    (⟦Assert.quant q vnew (p /[v := IntExp.var vnew] )⟧ₐ σ ↔ ⟦Assert.quant q v p⟧ₐ σ) := by
  have key : ∀ n : Int,
      (⟦p /[v := IntExp.var vnew] ⟧ₐ (σ[vnew := n]) ↔ ⟦p⟧ₐ (σ[v := n])) := by
    intro n
    refine substitution_assert p _ _ _ ?_
    intro w hw
    by_cases hwv : w = v
    · subst hwv; simp [IntExp.eval]
    · have hne : w ≠ vnew := by
        rintro rfl; exact hfresh (Finset.mem_erase.mpr ⟨hwv, hw⟩)
      simp [hwv, IntExp.eval, hne]
  cases q
  · simpa [Assert.eval] using forall_congr' key
  · simpa [Assert.eval] using exists_congr key

/-! ## 8. §1.3 의 공리꼴이 타당하다 -/

/--
Reynolds 가 §1.4 를 여는 공리꼴 `(∀v. p) ⇒ (p / v ↦ e)` 가 타당하다.

이 절 첫머리의 반례가 여기서 정리된다. 포획을 피하도록 치환을 정의했기 때문에
`p := ∃y. y > x`, `v := x`, `e := y + 1` 을 넣어도 결론이 거짓이 되지 않는다.
-/
theorem valid_instAll [HasFresh V] (v : V) (p : Assert V) (e : IntExp V) :
    Valid (.bin .imp (.quant .all v p) (p /[v := e] )) := by
  intro σ hall
  exact (substitution_single p v e σ).mpr (hall _)

end Reynolds.Answers.Ch01
