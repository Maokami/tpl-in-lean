/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Answers.Ch03.Total

/-!
# §3.5 구조 규칙과 추가 의미 규칙

Reynolds §3.5의 CA·DA·CSP·CST는 `Hoare`와 `HoareT`의 생성자다.
이 파일은 부분 CST를 CSP·CA로 유도하고, 기존 의미 판 API를 제공한다.

## 두 상수 규칙
CSP는 명세 전제 없이 `{p} c {p}`를 준다. CST는 `[p] c [q]`라는 종료 전제를
받아 `[p ∧ r] c [q ∧ r]`를 준다. 부분 CST는 CSP와 CA를 조합하면 된다(p.69).

## 앞 장의 정리가 하나씩
- 상수 규칙은 명제 2.6(b)의 쓰기 집합과 명제 1.1의 단언 일치를 쓴다.
- ∃ 규칙은 명제 2.6(a), 치환 규칙은 연습 2.8의 약한 치환 정리를 쓴다.

## 읽는 순서
`Semantic.lean` → `Hoare.lean` → `Total.lean` → 이 파일.

## 책과의 차이
아래의 ∃·치환 규칙은 기존 의미 판 보충 자료다.
-/

@[expose] public section

namespace Reynolds.Answers.Ch03

open Reynolds Reynolds.Answers.Ch01 Reynolds.Answers.Ch02

universe u

variable {V : Type u} [DecidableEq V]

/-! ## 1. 상수 규칙 -/

/-- 부분 CST는 CA의 두 번째 전제로 CSP를 넣어 유도한다 (§3.5 p.69). -/
theorem Hoare.frame [HasFresh V] {p q r : Assert V} {c : Comm V}
    (hr : Disjoint c.fa r.fv) (h : Hoare p c q) : Hoare (p ⋀ r) c (q ⋀ r) :=
  Hoare.conj h (Hoare.constancy hr)

-- ANCHOR: constancy
-- ANCHOR: stmtConstancy
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
-- ANCHOR_END: stmtConstancy
    := by
  intro σ hpr τ hτ
  obtain ⟨hp, hrσ⟩ := (Assert.eval_and _ _ _).mp hpr
  refine (Assert.eval_and _ _ _).mpr ⟨h σ hp τ hτ, ?_⟩
  exact (coincidence_assert r σ τ fun w hw =>
    (Comm.eval_agree_outside_fa c σ τ hτ w (Finset.disjoint_right.mp hr hw)).symm).mp hrσ
-- ANCHOR_END: constancy

/-! ## 2. 연언 · 선언 규칙

의미 수준에서는 정의를 펼치면 끝난다. 같은 명령 `c` 의 두 명세를 하나로 합친다. -/

-- ANCHOR: conjDisj
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
-- ANCHOR_END: conjDisj

/-! ## 3. 유령 변수의 ∃ 규칙 -/

-- ANCHOR: ghostExists
/--
**∃ 규칙.** 명령도 사후조건도 보지 않는 변수는 사전조건에서 존재 양화로 감출 수 있다.

```
{ p } c { q }
--------------------------   v ∉ FV(c) ∪ FV(q)
{ ∃v. p } c { q }
```

증인 `n` 을 꺼내 `σ[v := n]` 에서 전제를 쓴다. `σ` 와 `σ[v := n]` 은 `v` 를 뺀 모든 곳에서
같으므로 `c` 의 결과도 `FV(c) ∪ FV(q)` 위에서 같고 (명제 2.6(a)), `q` 는 그 위만 본다.
§3.3 의 앞으로 가는 대입 규칙이 사후조건에 `∃ v₀` 를 들고 있는 이유가 이 규칙의 거울상이다.
-/
@[exercise "§3.7 ghost-exists" 2]
theorem exists_sound {p q : Assert V} {c : Comm V} {v : V} (hc : v ∉ c.fv) (hq : v ∉ q.fv)
    (h : ｛p｝c｛q｝) : ｛Assert.quant .ex v p｝c｛q｝ := by
  intro σ hex τ hτ
  obtain ⟨n, hn⟩ := (Assert.eval_ex _ _ _).mp hex
  have hag := Comm.coincidence_general c (c.fv ∪ q.fv) Finset.subset_union_left σ (σ[v := n])
    fun w hw => (State.subst_of_ne σ v w n fun (hwv : w = v) => by
      subst hwv
      rcases Finset.mem_union.mp hw with h' | h'
      · exact hc h'
      · exact hq h').symm
  rw [hτ] at hag
  rcases hτ' : c.eval (σ[v := n]) with _ | τ'
  · rw [hτ'] at hag; simp [AgreeOn] at hag
  · rw [hτ'] at hag
    change ∀ w ∈ _, τ w = τ' w at hag
    exact (coincidence_assert q τ τ' fun w hw =>
      hag w (Finset.mem_union_right _ hw)).mpr (h _ hn τ' hτ')
-- ANCHOR_END: ghostExists

/-! ## 4. 치환 규칙 -/

-- ANCHOR: substRule
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
@[exercise "§3.7 subst-rule" 3]
theorem subst_rule_sound [HasFresh V] {p q : Assert V} {c : Comm V} (δ : Ren V)
    (hinj : ∀ u ∈ c.fa, ∀ w ∈ c.fv ∪ p.fv ∪ q.fv, δ u = δ w → u = w)
    (h : ｛p｝c｛q｝) : ｛p /ₛ δ.toSubst｝(c /ᶜ δ)｛q /ₛ δ.toSubst｝ := by
  intro σ' hp τ' hτ'
  have hag := Ex.Comm.substitution_weak c δ (c.fv ∪ p.fv ∪ q.fv)
    (le_trans Finset.subset_union_left Finset.subset_union_left) hinj
    (fun w => σ' (δ w)) σ' fun _ _ => rfl
  rw [hτ'] at hag
  rcases hc : c.eval (fun w => σ' (δ w)) with _ | τ
  · rw [hc] at hag; exact absurd hag AgreeVia.none_some
  · rw [hc, AgreeVia.some_some] at hag
    have hpσ := (substitution_assert p δ.toSubst (fun w => σ' (δ w)) σ' fun _ _ => rfl).mp hp
    exact (substitution_assert q δ.toSubst τ τ' fun w hw =>
      hag w (Finset.mem_union_right _ hw)).mpr (h _ hpσ τ hc)
-- ANCHOR_END: substRule

/-! ## 5. 여기서 어디로 가나

CA·DA는 생성자이고 부분 CST는 위에서 유도했다.
모든 타당한 명세에 유도가 있는지는 별도의 완전성 문제다. -/

end Reynolds.Answers.Ch03
