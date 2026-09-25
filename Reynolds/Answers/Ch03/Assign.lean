/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Answers.Ch03.Soundness

/-!
# §3.3 대입 공리는 왜 거꾸로인가

```
{ q/v→e } v := e { q }
```

사후조건 `q` 에서 사전조건을 **만든다.** 방향이 거꾸로라 처음 보면 어색하지만 이유는
정확하다 — 대입 뒤에 `q` 가 참이려면 대입 전에 "`v` 자리에 `e` 를 넣은 `q`" 가 참이어야
한다. 대입이 `v` 를 `e` 의 값으로 바꾸므로.

앞으로 가는 판도 있다 (Floyd).

```
{ p } v := e { ∃ v₀. p/v→v₀ ∧ v = e/v→v₀ }
```

대입 전의 값을 새 변수 `v₀` 로 기억해 두는 방식이다. 옳지만 사후조건에 `∃` 와 신선한 변수가
들어와 다루기 나쁘다. 뒤로 가는 판은 `q` 에 아무것도 덧붙이지 않는다.

이 파일은 두 판을 나란히 놓고 세 가지를 보인다.

1. 앞으로 가는 판도 **건전**하다 (`assign_forward_sound`). 신선함 조건 셋이 든다.
2. 앞으로 가는 판은 뒤로 가는 판과 결과 규칙으로 **유도**된다 (`Hoare.assign_forward`).
3. 거꾸로도 된다 (`Hoare.assign_of_forward`). 힘은 같다.

그러니 Hoare 가 뒤로 가는 판을 고른 이유는 힘이 아니라 **모양**이다 — `∃` 도 새 변수도
없이 치환 하나로 끝난다. 그리고 그 치환이 1장 §1.4 에서 포획을 피해 만든 그것이다.

## 읽는 순서
`Soundness.lean` → 이 파일.
-/

@[expose] public section

namespace Reynolds.Answers.Ch03

open Reynolds Reynolds.Answers.Ch01 Reynolds.Answers.Ch02

universe u

variable {V : Type u} [DecidableEq V]

/-! ## 1. 앞으로 가는 판의 사후조건 -/

-- ANCHOR: floydPost
/-- `v` 를 `v₀` 로 바꾼 정수 식. 단언의 `p /[v := .var v₀]` 에 대응하는 식 판이다. -/
def IntExp.renameTo (e : IntExp V) (v v₀ : V) : IntExp V :=
  e /ₑ Function.update IntExp.var v (.var v₀)

/-- Floyd 의 사후조건 `∃ v₀. p/v→v₀ ∧ v = e/v→v₀`. `v₀` 가 대입 전의 `v` 값을 붙든다. -/
def floydPost [HasFresh V] (p : Assert V) (v v₀ : V) (e : IntExp V) : Assert V :=
  .quant .ex v₀ ((p /[v := .var v₀]) ⋀ .cmp .eq (.var v) (IntExp.renameTo e v v₀))
-- ANCHOR_END: floydPost

/-! ## 2. 앞으로 가는 판도 건전하다 -/

-- ANCHOR: assignForward
/--
**앞으로 가는 대입 규칙의 건전성.** 대입 뒤 상태 `σ[v := ⟦e⟧ σ]` 에서 `v₀` 의 값으로
옛 `σ v` 를 잡으면 된다. 신선함 조건 셋이 각각 든다.

- `v₀ ∉ FV(p)` — `v₀` 를 새로 잡아도 `p` 가 그대로 (명제 1.1).
- `v₀ ∉ FV(e)` — `v₀` 를 새로 잡아도 `e` 가 그대로 (명제 1.1, 식 판).
- `v₀ ≠ v` — 두 갱신이 서로를 안 건드린다.

치환은 명제 1.4 (`substitution_single`) 와 그 식 판 `substitution_intExp` 로 뜻으로 옮긴다.
-/
@[exercise "§3.3 assign-forward" 2]
theorem assign_forward_sound [HasFresh V] (p : Assert V) (v v₀ : V) (e : IntExp V)
    (h₀ : v₀ ∉ p.fv) (h₁ : v₀ ∉ e.fv) (h₂ : v₀ ≠ v) :
    ｛p｝(Comm.assign v e)｛floydPost p v v₀ e｝ := by
  intro σ hp τ hτ
  change some (σ[v := ⟦e⟧ₑ σ]) = some τ at hτ
  obtain rfl := Option.some.inj hτ
  refine (Assert.eval_ex _ _ _).mpr ⟨σ v, (Assert.eval_and _ _ _).mpr ⟨?_, ?_⟩⟩
  · -- `p/v→v₀` : `v` 자리에 옛 값이 돌아오니 `p` 가 `σ` 에서 참인 것과 같다.
    refine (substitution_single p v _ _).mpr ((coincidence_assert p σ _ fun w hw => ?_).mp hp)
    have hw₀ : w ≠ v₀ := fun h => h₀ (h ▸ hw)
    by_cases hwv : w = v
    · subst hwv; simp [IntExp.eval]
    · simp [State.subst_of_ne _ _ _ _ hw₀, State.subst_of_ne _ _ _ _ hwv]
  · -- `v = e/v→v₀` : 왼쪽은 새 값 `⟦e⟧ σ`, 오른쪽은 `v₀` 자리의 옛 값으로 `e` 를 계산한 것.
    refine (Assert.eval_eq _ _ _).mpr ?_
    change (σ[v := ⟦e⟧ₑ σ][v₀ := σ v]) v = ⟦IntExp.renameTo e v v₀⟧ₑ (σ[v := ⟦e⟧ₑ σ][v₀ := σ v])
    rw [State.subst_of_ne _ _ _ _ h₂.symm, State.subst_self]
    refine (substitution_intExp e _ σ _ fun w hw => ?_).symm
    have hw₀ : w ≠ v₀ := fun h => h₁ (h ▸ hw)
    by_cases hwv : w = v
    · subst hwv; simp [IntExp.eval]
    · simp [IntExp.eval, Function.update_of_ne hwv, State.subst_of_ne _ _ _ _ hw₀,
        State.subst_of_ne _ _ _ _ hwv]
-- ANCHOR_END: assignForward

/-! ## 3. 두 판은 서로를 유도한다 -/

-- ANCHOR: forwardOfBackward
/-- **앞으로 가는 판은 뒤로 가는 판에서 나온다.** 공리가 주는 사전조건
`(∃ v₀. …)/v→e` 가 `p` 보다 약하다는 것이 `assign_forward_sound` 의 내용 그대로다. -/
theorem Hoare.assign_forward [HasFresh V] (p : Assert V) (v v₀ : V) (e : IntExp V)
    (h₀ : v₀ ∉ p.fv) (h₁ : v₀ ∉ e.fv) (h₂ : v₀ ≠ v) :
    Hoare p (.assign v e) (floydPost p v v₀ e) :=
  Hoare.strengthen
    (fun σ hp => (substitution_single _ v e σ).mpr
      (assign_forward_sound p v v₀ e h₀ h₁ h₂ σ hp _ rfl))
    (Hoare.assign _ v e)
-- ANCHOR_END: forwardOfBackward

-- ANCHOR: backwardOfForward
/--
**Floyd 의 사후조건에서 `q` 로 돌아온다.** `p := q/v→e` 로 앞으로 가는 판을 쓰면 사후조건이
`∃ v₀. (q/v→e)/v→v₀ ∧ v = e/v→v₀` 인데, 이것이 `q` 보다 강하다. `v₀` 의 증인 `n` 을 잡고
치환 둘을 명제 1.4 로 풀면 `q` 가 "`v` 에 `v` 자신의 값을 넣은 상태" 에서 참이라는 말이
되고, 그 상태는 원래 상태다.
-/
@[exercise "§3.3 backward-of-forward" 2]
theorem floydPost_stronger [HasFresh V] (q : Assert V) (v v₀ : V) (e : IntExp V)
    (h₀ : v₀ ∉ q.fv) (h₁ : v₀ ∉ e.fv) (h₂ : v₀ ≠ v) :
    Stronger (floydPost (q /[v := e] ) v v₀ e) q := by
  intro τ h
  obtain ⟨n, hn⟩ := (Assert.eval_ex _ _ _).mp h
  obtain ⟨hq, hv⟩ := (Assert.eval_and _ _ _).mp hn
  -- `v = e/v→v₀` 를 `τ v = ⟦e⟧ (τ[v₀ := n][v := n])` 으로 읽는다.
  change (τ[v₀ := n]) v = ⟦IntExp.renameTo e v v₀⟧ₑ (τ[v₀ := n]) at hv
  rw [State.subst_of_ne _ _ _ _ h₂.symm] at hv
  rw [IntExp.renameTo, substitution_intExp e _ (τ[v₀ := n][v := n]) _ fun w hw => ?_] at hv
  · -- 치환 둘을 풀면 `q` 가 `τ[v₀ := n][v := n][v := τ v]` 에서 참이다.
    have hq' := (substitution_single _ v (.var v₀) _).mp hq
    simp only [IntExp.eval, State.subst_self] at hq'
    have hq'' := (substitution_single q v e _).mp hq'
    rw [← hv] at hq''
    -- 그 상태는 `q` 가 보는 변수들에서 `τ` 와 같다.
    refine (coincidence_assert q _ τ fun w hw => ?_).mp hq''
    have hw₀ : w ≠ v₀ := fun h => h₀ (h ▸ hw)
    by_cases hwv : w = v
    · subst hwv; simp
    · simp [State.subst_of_ne _ _ _ _ hwv, State.subst_of_ne _ _ _ _ hw₀]
  · have hw₀ : w ≠ v₀ := fun h => h₁ (h ▸ hw)
    by_cases hwv : w = v
    · subst hwv; simp [IntExp.eval]
    · simp [IntExp.eval, Function.update_of_ne hwv, State.subst_of_ne _ _ _ _ hwv]
-- ANCHOR_END: backwardOfForward

/-- **뒤로 가는 판은 앞으로 가는 판에서 나온다.** 앞으로 가는 규칙의 사례 하나를 가정으로
받아 결론 약화만으로 대입 공리를 얻는다. 두 판의 힘이 같다는 뜻이다. -/
theorem Hoare.assign_of_forward [HasFresh V] (q : Assert V) (v v₀ : V) (e : IntExp V)
    (h₀ : v₀ ∉ q.fv) (h₁ : v₀ ∉ e.fv) (h₂ : v₀ ≠ v)
    (hF : Hoare (q /[v:=e] ) (.assign v e) (floydPost (q /[v:=e] ) v v₀ e)) :
    Hoare (q /[v := e] ) (.assign v e) q :=
  Hoare.weaken hF (floydPost_stronger q v v₀ e h₀ h₁ h₂)

/-! ## 4. 여기서 어디로 가나

힘이 같으니 남는 것은 쓰기 편한 쪽이고, 그것이 뒤로 가는 판이다. §3.4 의 주석 붙은 명세는
이 방향을 그대로 따른다 — 사후조건에서 출발해 위로 올라가며 사전조건을 채운다. -/

end Reynolds.Answers.Ch03
