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
set_option verso.exampleModule "Reynolds.Answers.Ch03.Derived"

#doc (Manual) "§3.7 더 많은 규칙" =>
%%%
tag := "ch03-derived"
file := "ch03-derived"
number := false
%%%

Reynolds가 §3.7에 모아 둔 규칙들을 여기서는 모두 _의미 수준에서_ 증명한다. `Hoare`에
생성자를 더하지 않고도, 이미 타당한 명세들을 이어 붙이는 데 쓸 수 있다.

두 물음을 갈라 두어야 한다. 규칙이 _뜻으로 건전한가_와 규칙이 _체계 안에서 유도되는가_는
다른 물음이다. 연언 규칙은 뜻으로는 자명하지만 `Hoare` 안에서 유도되는지는 자명하지 않다.
두 유도를 하나로 합칠 규칙이 체계에 없기 때문이다. 이 간극을 메우는 것이 완전성이다(§3.10).

# 상수 규칙
%%%
tag := "ch03-constancy"
file := "ch03-constancy"
number := false
%%%

`c`가 _대입하지 않는_ 변수에 대한 주장은 `c`를 지나도 그대로다.

````anchor constancy (module := Reynolds.Answers.Ch03.Derived)
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
@[exercise "§3.7 constancy" 2]
theorem constancy_sound {p q r : Assert V} {c : Comm V} (hr : Disjoint c.fa r.fv)
    (h : ｛p｝c｛q｝) : ｛p ⋀ r｝c｛q ⋀ r｝ := by
  intro σ hpr τ hτ
  obtain ⟨hp, hrσ⟩ := (Assert.eval_and _ _ _).mp hpr
  refine (Assert.eval_and _ _ _).mpr ⟨h σ hp τ hτ, ?_⟩
  exact (coincidence_assert r σ τ fun w hw =>
    (Comm.eval_agree_outside_fa c σ τ hτ w (Finset.disjoint_right.mp hr hw)).symm).mp hrσ
````

§2.5에서 자유 변수를 _읽기_(`FV`)와 _쓰기_(`FA`)로 가른 이유가 여기서 드러난다. 요구하는
것은 `FV(r)`과 `FA(c)`가 겹치지 않는 것뿐이다. `c`가 `r`의 변수를 읽는 것은 괜찮다.

# 유령 변수의 ∃ 규칙
%%%
tag := "ch03-ghost-exists"
file := "ch03-ghost-exists"
number := false
%%%

명령도 사후조건도 보지 않는 변수는 사전조건에서 존재 양화로 감출 수 있다.

````anchor ghostExists (module := Reynolds.Answers.Ch03.Derived)
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
````

§3.3에서 Floyd의 앞으로 가는 대입 규칙이 사후조건에 `∃ v₀`를 달고 있던 것과 거울상을
이룬다.

# 치환 규칙
%%%
tag := "ch03-subst-rule"
file := "ch03-subst-rule"
number := false
%%%

명세의 변수 이름을 통째로 바꿔도 된다. 건전성은 1장의 명제 1.3과 2장의 명제 2.7을 합친
것이다.

````anchor substRule (module := Reynolds.Answers.Ch03.Derived)
/--
**치환 규칙.** 명세의 변수 이름을 통째로 바꿔도 된다.

```
{ p } c { q }
------------------------------   δ 가 FA(c) 위에서 단사
{ p/δ } c/δ { q/δ }
```

치환된 쪽의 시작 상태 `σ'` 에서 원래 쪽의 시작 상태를 `fun w => σ' (δ w)` 로 만든다. 그러면

- `p/δ` 가 `σ'` 에서 참 ↔ `p` 가 그 상태에서 참 (명제 1.3),
- 두 실행의 결과가 `δ` 를 사이에 두고 일치 (명제 2.7, 연습 2.8 의 약한 판),
- `q` 가 원래 결과에서 참 ↔ `q/δ` 가 치환된 결과에서 참 (명제 1.3).

단사 조건이 `FV(c)` 전체가 아니라 `FA(c)` 위에서만이면 된다 — 읽기만 하는 변수는 합쳐도
된다. 명제 2.7 의 원래 조건으로는 이 흔한 사용법이 막힌다.
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
````

명제 2.7의 원래 진술은 이름 바꾸기가 `FV(c)` _전체에서_ 단사일 것을 요구한다. 그 조건으로는
읽기만 하는 변수 둘을 하나로 합치는 흔한 사용법이 막힌다. 연습 2.8이 조건을 `FA(c)` 위의
단사로 약화했는데, 그 약한 판이 이 규칙에 정확히 들어맞는다. 2장에서 조건을 약화하라고 한
연습이 3장의 규칙 하나를 위한 준비였던 셈이다.
