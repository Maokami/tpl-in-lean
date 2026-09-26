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
set_option verso.exampleModule "Reynolds.Answers.Ch03.Hoare"

#doc (Manual) "§3.2~3.6 추론 규칙과 건전성" =>
%%%
tag := "ch03-rules"
file := "ch03-rules"
number := false
%%%

§3.1은 명세가 _무엇을 뜻하는지_ 정했다. 이 절들은 명세를 _증명하는 규칙_을 세운다. 규칙은
구문 위의 조작이고, 뜻과는 따로 있다. 그래서 규칙이 뜻에 대해 옳다는 것, 곧
_건전성_(soundness)을 따로 증명해야 한다.

# 규칙 하나가 생성자 하나
%%%
tag := "ch03-hoare"
file := "ch03-hoare"
number := false
%%%

§1.3의 `Proof`와 같은 모양이다. 전제가 인자이고 결론이 결과 타입이다. Lean의 화살표가
Reynolds의 가로선 노릇을 한다.

```anchor hoare (module := Reynolds.Answers.Ch03.Hoare)
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
```

규칙 몇 개에 눈여겨볼 점이 있다.

: 대입

  사후조건에서 사전조건을 _만든다_. 방향이 거꾸로다. 아래에서 따로 본다.

: 순차 합성

  가운데 단언 `r`이 전제에만 나온다. 규칙이 `r`을 정해 주지 않으므로 유도하는 사람이
  골라야 한다. §3.4의 주석 명세가 이 선택을 적는 방법이다.

: 반복

  `i`가 _불변식_이다. 규칙은 불변식을 찾아 주지 않는다. 프로그램 검증에서 사람이 하는 일의
  대부분이 이 선택이다.

: 결과 규칙

  전제 `Stronger p' p`는 `∀ σ, ⟦p'⟧ σ → ⟦p⟧ σ`다. 단언 사이의 함의가 _타당하다_는 의미적
  사실이고, 1장의 `Proof`로 증명했다는 뜻이 아니다. Hoare 논리는 단언 논리를 _오라클_로
  쓴다. 완전성을 말할 때 "단언의 타당성에 상대적으로"라는 단서가 붙는 이유다(§3.10).

첫 유도는 대입 공리 하나와 결과 규칙 하나다.

```anchor firstDeriv (module := Reynolds.Answers.Ch03.Hoare)
/-- `{x = 1} x := x + 1 {x = 2}`. 공리가 주는 사전조건은 `x + 1 = 2` 고, `x = 1` 이 그보다
강하다. -/
theorem incr_hoare : Hoare (⟪ x = 1 ⟫ₐ) ⟪ x := x + 1 ⟫ᶜ (⟪ x = 2 ⟫ₐ) := by
  refine Hoare.strengthen ?_ (Hoare.assign _ "x" _)
  intro σ h
  simp [Assert.subst, IntExp.subst, Assert.eval, IntExp.eval, IntOp.denote, Cmp.denote] at h ⊢
  omega
```

# 규칙마다 앞 장의 정리 하나
%%%
tag := "ch03-soundness"
file := "ch03-soundness"
number := false
%%%

건전성은 `Hoare`에 대한 구조적 귀납이고, 절마다 앞 장의 정리 하나가 받친다. 규칙끼리
서로 기대지 않으므로 절마다 따로 떼어 연습으로 낼 수 있다.

대입 공리의 건전성은 1장 명제 1.4 그대로다. §1.4에서 포획을 피하는 치환을 애써 만든 것이
이 한 줄을 위해서였다.

```anchor assignSound (module := Reynolds.Answers.Ch03.Soundness)
/--
**대입 공리의 건전성 — 명제 1.4 한 줄.**

대입 뒤의 상태는 `σ[v := ⟦e⟧ σ]` 이고, 거기서 `q` 가 참이라는 것은 `σ` 에서 `q/v→e` 가
참이라는 것과 같다. 그것이 `substitution_single` 이다.
-/
@[exercise "§3.3 assign-sound" 1]
theorem assign_sound [HasFresh V] (q : Assert V) (v : V) (e : IntExp V) :
    ｛q /[v := e]｝(Comm.assign v e)｛q｝ := by
  intro σ hp τ hτ
  change some (σ[v := ⟦e⟧ₑ σ]) = some τ at hτ
  obtain rfl := Option.some.inj hτ
  exact (substitution_single q v e σ).mp hp
```

`while` 규칙의 건전성은 §2.4의 Scott 귀납법이다. §3.1에서 본 두 사실, 곧 `⊥`가 모든
사후조건을 만족한다는 것과 `Sat`이 극한을 통과한다는 것이 귀납의 두 의무를 채운다.

```anchor whSound (module := Reynolds.Answers.Ch03.Soundness)
/--
**`while` 규칙의 건전성 — Scott 귀납법.**

`⟦while b do c⟧` 는 `whileF b ⟦c⟧` 의 최소 고정점이다. 그 고정점이 "`i` 에서 출발해 끝나면
`i ∧ ¬b`" 를 만족한다는 것을 §2.4 의 `scott_induction` 으로 얻는다. 세 의무가 §3.1 에서
말한 것과 맞물린다.

- 허용 가능 — `Sat.admissible`. `⊥` 가 모든 사후조건을 만족한다는 것의 사슬 판.
- `⊥` — `Sat.bot`. 끝나지 않으므로 공허.
- 한 바퀴 — 조건이 참이면 본체가 `i` 를 지키고(전제) 나머지에 넘긴다(가설). 거짓이면 그
  자리에서 `i ∧ ¬b` 다.

명제 2.6, 명제 2.7 에 이어 Scott 귀납법을 세 번째 쓰는 자리다. 이번에는 성질이 두 상태의
관계가 아니라 한 상태의 술어라 더 단순하다.
-/
@[exercise "§3.5 wh-sound" 3]
theorem wh_sound {i : Assert V} {b : BoolExp V} {c : Comm V}
    (hbody : ｛i ⋀ b.toAssert｝c｛i｝) : ｛i｝(Comm.wh b c)｛i ⋀ .not b.toAssert｝ := by
  change Sat ⟦i⟧ₐ (fix (whileF b ⟦c⟧ᶜ) (whileF_monotone b ⟦c⟧ᶜ)) ⟦i ⋀ .not b.toAssert⟧ₐ
  refine scott_induction (whileF_monotone b ⟦c⟧ᶜ)
    (P := fun w => Sat ⟦i⟧ₐ w ⟦i ⋀ .not b.toAssert⟧ₐ) ?_ ?_ ?_
  · exact fun d hd => Sat.admissible _ _ d hd
  · exact Sat.bot _ _
  · intro w hw σ hi τ hτ
    change (if ⟦b⟧ᵇ σ then Option.bind (⟦c⟧ᶜ σ) w else some σ) = some τ at hτ
    by_cases hb : ⟦b⟧ᵇ σ = true
    · rw [if_pos hb] at hτ
      rcases hc : ⟦c⟧ᶜ σ with _ | ρ
      · rw [hc] at hτ; simp at hτ
      · rw [hc] at hτ
        change w ρ = some τ at hτ
        exact hw ρ (hbody σ ((Assert.eval_and _ _ _).mpr
          ⟨hi, (boolExp_eval_iff b σ).mpr hb⟩) ρ hc) τ hτ
    · rw [if_neg hb] at hτ
      obtain rfl := Option.some.inj hτ
      exact (Assert.eval_and _ _ _).mpr
        ⟨hi, (Assert.eval_not _ _).mpr fun h => hb ((boolExp_eval_iff b σ).mp h)⟩
```

§2.5의 명제 2.6, 명제 2.7에 이어 Scott 귀납법을 세 번째로 쓰는 자리다. 앞의 둘은 두 상태
사이의 _관계_를 다뤘고 이번에는 한 상태의 _술어_라 더 단순하다.

변수 선언 규칙에는 신선함 조건이 셋 붙는다. 각각이 명제 1.1을 한 번씩 부른다.

```anchor newvarSound (module := Reynolds.Answers.Ch03.Soundness)
/--
**변수 선언 규칙의 건전성 — 명제 1.1 세 번.**

`⟦newvar v := e in c⟧ σ = restore v σ (⟦c⟧ (σ[v := ⟦e⟧ σ]))` 다. 세 신선함 조건이 각각
다른 자리에서 쓰인다.

- `v ∉ FV(p)` — `v` 를 갱신해도 `p` 가 그대로 참이다.
- `v ∉ FV(e)` — `v` 를 갱신해도 `e` 의 값이 그대로라 안쪽에서 `v = e` 가 참이다.
- `v ∉ FV(q)` — `v` 를 복원해도 `q` 가 그대로 참이다.
-/
@[exercise "§3.6 newvar-sound" 2]
theorem newvar_sound {p q : Assert V} {v : V} {e : IntExp V} {c : Comm V}
    (hp : v ∉ p.fv) (hq : v ∉ q.fv) (he : v ∉ e.fv)
    (h : ｛p ⋀ .cmp .eq (.var v) e｝c｛q｝) : ｛p｝(Comm.newvar v e c)｛q｝ := by
  intro σ hpσ τ hτ
  change restore v σ (⟦c⟧ᶜ (σ[v := ⟦e⟧ₑ σ])) = some τ at hτ
  rcases hc : ⟦c⟧ᶜ (σ[v := ⟦e⟧ₑ σ]) with _ | ρ
  · rw [hc] at hτ; simp [restore] at hτ
  · rw [hc] at hτ
    simp only [restore, Option.map_some, Option.some.injEq] at hτ
    subst hτ
    -- 안쪽 사전조건. `p` 는 `v` 를 안 보고, `v = e` 는 갱신으로 참이다.
    have hp' : ⟦p⟧ₐ (σ[v := ⟦e⟧ₑ σ]) :=
      (coincidence_assert p σ _ fun w hw =>
        (State.subst_of_ne σ v w _ fun (hwv : w = v) => hp (hwv ▸ hw)).symm).mp hpσ
    have hv : ⟦Assert.cmp .eq (.var v) e⟧ₐ (σ[v := ⟦e⟧ₑ σ]) := by
      change (σ[v := ⟦e⟧ₑ σ]) v = ⟦e⟧ₑ (σ[v := ⟦e⟧ₑ σ])
      rw [State.subst_self]
      exact coincidence_intExp e σ _ fun w hw =>
        (State.subst_of_ne σ v w _ fun (hwv : w = v) => he (hwv ▸ hw)).symm
    -- 안쪽 결과에서 `q` 가 참이고, `v` 를 복원해도 `q` 는 `v` 를 안 보므로 그대로다.
    have hq' := h _ ((Assert.eval_and _ _ _).mpr ⟨hp', hv⟩) ρ hc
    exact (coincidence_assert q ρ (ρ[v := σ v]) fun w hw =>
      (State.subst_of_ne ρ v w _ fun (hwv : w = v) => hq (hwv ▸ hw)).symm).mp hq'
```

절들을 모으면 건전성이다.

```anchor sound (module := Reynolds.Answers.Ch03.Soundness)
/--
**건전성.** 유도된 명세는 타당하다.

`Hoare` 에 대한 구조적 귀납이고 절마다 위의 정리 하나다. 채점 연습이 아니다 — 각 절이
이미 연습이라 비우면 비운 것끼리 의존한다 (연습 독립성 원칙, `AGENTS.md` §1-9).
-/
theorem Hoare.sound [HasFresh V] {p q : Assert V} {c : Comm V} :
    Hoare p c q → ｛p｝c｛q｝ := by
  intro h
  induction h with
  | skip p => exact skip_sound p
  | assign q v e => exact assign_sound q v e
  | seq _ _ ih₀ ih₁ => exact seq_sound ih₀ ih₁
  | ite _ _ ih₀ ih₁ => exact ite_sound ih₀ ih₁
  | wh _ ih => exact wh_sound ih
  | newvar hp hq he _ ih => exact newvar_sound hp hq he ih
  | conseq hp _ hq ih => exact PartialCorrect.conseq hp ih hq
```

# 대입 공리는 왜 거꾸로인가
%%%
tag := "ch03-assign"
file := "ch03-assign"
number := false
%%%

`{q/v→e} v := e {q}`는 사후조건에서 출발한다. 앞으로 가는 판도 있다. Floyd의 판은 대입 전
값을 새 변수 `v₀`로 기억해 둔다.

```anchor floydPost (module := Reynolds.Answers.Ch03.Assign)
/-- `v` 를 `v₀` 로 바꾼 정수 식. 단언의 `p /[v := .var v₀]` 에 대응하는 식 판이다. -/
def IntExp.renameTo (e : IntExp V) (v v₀ : V) : IntExp V :=
  e /ₑ Function.update IntExp.var v (.var v₀)

/-- Floyd 의 사후조건 `∃ v₀. p/v→v₀ ∧ v = e/v→v₀`. `v₀` 가 대입 전의 `v` 값을 붙든다. -/
def floydPost [HasFresh V] (p : Assert V) (v v₀ : V) (e : IntExp V) : Assert V :=
  .quant .ex v₀ ((p /[v := .var v₀]) ⋀ .cmp .eq (.var v) (IntExp.renameTo e v v₀))
```

이 판도 건전하다. 신선함 조건이 셋 필요하다.

```anchor assignForward (module := Reynolds.Answers.Ch03.Assign)
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
```

그리고 두 판은 결과 규칙으로 서로를 유도한다. 앞으로 가는 판은 뒤로 가는 판의 사례에
전제 강화를 붙인 것이다.

```anchor forwardOfBackward (module := Reynolds.Answers.Ch03.Assign)
/-- **앞으로 가는 판은 뒤로 가는 판에서 나온다.** 공리가 주는 사전조건
`(∃ v₀. …)/v→e` 가 `p` 보다 약하다는 것이 `assign_forward_sound` 의 내용 그대로다. -/
theorem Hoare.assign_forward [HasFresh V] (p : Assert V) (v v₀ : V) (e : IntExp V)
    (h₀ : v₀ ∉ p.fv) (h₁ : v₀ ∉ e.fv) (h₂ : v₀ ≠ v) :
    Hoare p (.assign v e) (floydPost p v v₀ e) :=
  Hoare.strengthen
    (fun σ hp => (substitution_single _ v e σ).mpr
      (assign_forward_sound p v v₀ e h₀ h₁ h₂ σ hp _ rfl))
    (Hoare.assign _ v e)
```

반대 방향도 된다(`Hoare.assign_of_forward`). 그러니 두 판은 _힘이 같다_. Hoare가 뒤로
가는 판을 고른 이유는 힘이 아니라 _모양_이다. `∃`도 새 변수도 없이 치환 하나로 끝나고,
그 치환은 1장에서 이미 만들어 두었다.
