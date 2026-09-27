/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Exercises.Ch03.Total

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

namespace Reynolds.Exercises.Ch03

open Reynolds Reynolds.Answers.Ch01 Reynolds.Answers.Ch02

universe u

variable {V : Type u} [DecidableEq V]

/-! ## 1. 상수 규칙 -/

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


/-! ## 2. 연언 · 선언 규칙

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

/-! ## 3. 유령 변수의 ∃ 규칙 -/

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
  -- 먼저 볼 것: §2.5 의 `Comm.coincidence_general` (명제 2.6(a)) 과 `AgreeOn`,
  --            `Assert.eval_ex`, `coincidence_assert`. `Total.lean`의 `whT_sound` 안에서
  --            본체 결과를 전달할 때도 같은 수법을 쓴다.
  -- 힌트 1: 증인 `n` 을 꺼낸다. 전제는 `σ[v := n]` 에서 쓸 수 있다.
  -- 힌트 2: `S := c.fv ∪ q.fv` 에 명제 2.6(a) 를 쓰면 `⟦c⟧ σ` 와 `⟦c⟧ (σ[v := n])` 가 `S` 에서
  --         일치한다. `rcases hτ' : c.eval (σ[v := n])` 로 나눠 `Flat.none` 쪽은 모순으로 닫는다.
  -- 힌트 3: `q` 는 `S` 만 보므로 두 결과에서 진릿값이 같다.
  sorry


/-! ## 4. 치환 규칙 -/

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
  -- 먼저 볼 것: 연습 2.8 의 `Ex.Comm.substitution_weak` 와 `AgreeVia` (`AgreeVia.some_some`,
  --            `AgreeVia.none_some`), §1.4 의 `substitution_assert` (명제 1.3).
  -- 힌트 1: 원래 쪽 시작 상태를 `fun w => σ' (δ w)` 로 잡는다. 그러면 `substitution_weak` 와
  --         `substitution_assert` 의 가설이 둘 다 `rfl` 이다.
  -- 힌트 2: `substitution_weak` 를 `S := c.fv ∪ p.fv ∪ q.fv` 로 부르고, 원래 쪽 실행을
  --         `rcases hc : c.eval (fun w => σ' (δ w))` 로 나눈다.
  -- 힌트 3: 사전조건은 명제 1.3 으로 원래 쪽에 옮기고, 사후조건은 명제 1.3 으로 되돌린다.
  sorry


/-! ## 5. 여기서 어디로 가나

CA·DA는 생성자이고 부분 CST는 위에서 유도했다.
모든 타당한 명세에 유도가 있는지는 별도의 완전성 문제다. -/

end Reynolds.Exercises.Ch03
