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
set_option verso.exampleModule "Reynolds.Answers.Ch03.Wlp"

#doc (Manual) "§3.10 최약 사전조건과 완전성" =>
%%%
tag := "ch03-wlp"
file := "ch03-wlp"
number := false
%%%

건전성의 역이 완전성이다. 타당한 명세는 모두 유도되는가? 답은 _아니오_, 그리고 _조건부로
예_다.

: 아니오

  결과 규칙의 전제는 단언의 타당성이다. 정수 산술을 담은 단언의 타당성에는 괴델 불완전성
  정리 때문에 완전한 공리계가 없다. 단언 논리의 증명까지 세면 Hoare 논리는 완전할 수 없다.

: 조건부로 예

  단언의 타당성을 _오라클_로 두면 완전성이 성립한다. 우리 `conseq`가 바로 그렇게 한다.
  Cook의 _상대 완전성_(relative completeness)이다. 단, 모든 명령과 사후조건에 대해 최약
  사전조건을 단언으로 _적을 수 있어야_ 한다.

# 의미적 최약 자유 사전조건
%%%
tag := "ch03-wlp-def"
file := "ch03-wlp-def"
number := false
%%%

```anchor wlp (module := Reynolds.Answers.Ch03.Wlp)
/-- 의미적 최약 자유 사전조건(weakest liberal precondition). `c` 가 끝나면 `Q` 가 참인 상태들. -/
def wlp (c : Comm V) (Q : State V → Prop) : State V → Prop :=
  fun σ => ∀ τ, ⟦c⟧ᶜ σ = some τ → Q τ

/-- 부분 정확성은 wlp 로 다시 쓰인다. 정의 그대로다. 그러니 `wlp c Q` 는 `{P} c {Q}` 를 만족하는
가장 약한 `P` 다. -/
theorem partialCorrectS_iff_wlp {P Q : State V → Prop} {c : Comm V} :
    PartialCorrectS P c Q ↔ ∀ σ, P σ → wlp c Q σ := Iff.rfl
```

`wlp c Q`는 `{P} c {Q}`를 만족하는 가장 약한 `P`다. 정의에서 바로 나온다.

# wlp는 최대 고정점이다
%%%
tag := "ch03-wlp-gfp"
file := "ch03-wlp-gfp"
number := false
%%%

`while`의 wlp는 2장의 풀기 방정식을 한 번 펼친 방정식을 만족한다.

```anchor wlpWhEq (module := Reynolds.Answers.Ch03.Wlp)
/-- **`while` 의 wlp 는 풀기 방정식을 만족한다.** 2장의 풀기 방정식을 한 번 펼친 것이다. -/
theorem wlp_wh_eq (b : BoolExp V) (c : Comm V) (Q : State V → Prop) (σ : State V) :
    wlp (.wh b c) Q σ ↔
      (⟦b⟧ᵇ σ = false ∧ Q σ) ∨ (⟦b⟧ᵇ σ = true ∧ wlp c (wlp (.wh b c) Q) σ) := by
  have whileEq := Comm.eval_isSemantics.2.2.2.2.1 b c σ
  unfold wlp
  rw [whileEq]
  cases hb : ⟦b⟧ᵇ σ
  · simp
  · simp only [if_true, Bool.true_eq_false, false_and, true_and, false_or]
    constructor
    · intro h ρ hρ τ hτ
      exact h τ (by rw [hρ]; exact hτ)
    · intro h τ hτ
      rcases hρ : ⟦c⟧ᶜ σ with _ | ρ
      · rw [hρ] at hτ; simp at hτ
      · rw [hρ] at hτ; exact h ρ hρ τ hτ
```

그리고 그 방정식의 _가장 큰_ 해다.

```anchor wlpWhGreatest (module := Reynolds.Answers.Ch03.Wlp)
/--
**그리고 가장 큰 해다.** 방정식의 오른쪽을 함의하는 술어 `X` (후고정점) 는 모두 wlp 보다
강하다.

`X` 가 바로 불변식이다 — 한 바퀴를 견디고, 끝난 자리에서 `Q` 를 준다. 그러니 이것은 `while`
규칙의 의미 판이고, 증명은 `wh_sound` 와 같은 Scott 귀납법이다. 최대 고정점에 대한 성질을
최소 고정점(`⟦while⟧ = fix …`) 위의 귀납으로 얻는다.
-/
@[exercise "§3.10 wlp-gfp" 3]
theorem wlp_wh_greatest {b : BoolExp V} {c : Comm V} {Q X : State V → Prop}
    (hX : ∀ σ, X σ → (⟦b⟧ᵇ σ = false ∧ Q σ) ∨ (⟦b⟧ᵇ σ = true ∧ wlp c X σ)) :
    ∀ σ, X σ → wlp (.wh b c) Q σ := by
  change Sat X (fix (whileF b ⟦c⟧ᶜ) (whileF_monotone b ⟦c⟧ᶜ)) Q
  refine scott_induction (whileF_monotone b ⟦c⟧ᶜ) (P := fun w => Sat X w Q)
    (fun d hd => Sat.admissible _ _ d hd) (Sat.bot _ _) ?_
  intro w hw σ hx τ hτ
  change (if ⟦b⟧ᵇ σ then Option.bind (⟦c⟧ᶜ σ) w else some σ) = some τ at hτ
  rcases hX σ hx with ⟨hb, hq⟩ | ⟨hb, hc⟩
  · rw [hb] at hτ
    obtain rfl := Option.some.inj hτ
    exact hq
  · rw [hb, if_pos rfl] at hτ
    rcases hρ : ⟦c⟧ᶜ σ with _ | ρ
    · rw [hρ] at hτ; simp at hτ
    · rw [hρ] at hτ
      exact hw ρ (hc ρ hρ) τ hτ
```

2장에서 `while`의 _뜻_은 최소 고정점이었다. `while`의 _최약 자유 사전조건_은 최대 고정점이다.
방정식의 모양은 같은데 고르는 해가 반대다. 부분 정확성은 발산을 허용하므로, 발산하는
입력에서 사전조건이 참이어도 상관없다. 그래서 가장 너그러운 해가 최약 사전조건이다.

상태 변환기의 정보 순서에서 `⊥`가 아래에 있는 것과, 술어의 함의 순서에서 "모두 허용"이
위에 있는 것이 서로 뒤집힌 상이다. 그런데 최대 고정점 성질의 증명이 _최소_ 고정점 위의
Scott 귀납법이라는 점을 보아 둘 만하다. 후고정점 `X`가 곧 불변식이고, 이 정리는 `while`
규칙의 의미 판이다.

# while 없는 조각의 완전성
%%%
tag := "ch03-complete"
file := "ch03-complete"
number := false
%%%

`Assert`는 정수 산술과 양화사를 갖고 있어서 이론적으로는 표현력이 충분하다. 괴델의
β-함수로 유한 수열을 정수 하나로 부호화하면 반복의 최약 사전조건도 적을 수 있다. 그러나
그것을 형식화하는 일은 이 장의 범위를 넘는다. 그래서 완전성은 `while` 없는 조각에서만
증명한다. 거기서는 최약 사전조건이 치환만으로 계산된다(Dijkstra).

```anchor wp (module := Reynolds.Answers.Ch03.Wlp)
/--
`while` 없는 명령의 최약 사전조건을 **구문으로** 계산한다 (Dijkstra). 치환만으로 된다.

- `while` 에서 `none` — 여기가 표현력이 필요한 자리다.
- `newvar` 에서 결합자가 사후조건이나 초기값 식에 나오면 `none` — 이름을 바꿔 다시 부르면
  된다 (§2.5 `Comm.newvar_rename`).

이름이 `Comm.wp` 이지만 3장 이름공간에 있어 `c.wp` 점 표기는 안 된다 (`Comm` 은 2장 타입).
-/
def Comm.wp [HasFresh V] : Comm V → Assert V → Option (Assert V)
  | .assign v e, q => some (q /[v := e] )
  | .skip, q => some q
  | .seq c₀ c₁, q => (Comm.wp c₁ q).bind (Comm.wp c₀)
  | .ite b c₀ c₁, q =>
      (Comm.wp c₀ q).bind fun p₀ => (Comm.wp c₁ q).map fun p₁ =>
        .bin .and (.bin .imp b.toAssert p₀) (.bin .imp (.not b.toAssert) p₁)
  | .wh _ _, _ => none
  | .newvar v e c, q =>
      if v ∈ q.fv ∨ v ∈ e.fv then none
      else (Comm.wp c q).map fun p => .quant .all v (.bin .imp (.cmp .eq (.var v) e) p)
```

`while` 절에서 `none`이 나온다. 표현력이 필요한 자리가 바로 거기다.

계산한 사전조건에서 유도가 있고,

```anchor wpSound (module := Reynolds.Answers.Ch03.Wlp)
/-- **`wp` 는 유도를 준다.** 계산한 사전조건에서 `Hoare` 유도가 있다. `Annot.lean` 의 세 보조
함의(`ite_pre_then` · `ite_pre_else` · `newvar_pre`)가 그대로 쓰인다. -/
@[exercise "§3.10 wp-sound" 2]
theorem wp_sound [HasFresh V] (c : Comm V) :
    ∀ q p, Comm.wp c q = some p → Hoare p c q := by
  induction c with
  | assign v e => intro q p h; cases h; exact Hoare.assign q v e
  | skip => intro q p h; cases h; exact Hoare.skip q
  | seq c₀ c₁ ih₀ ih₁ =>
    intro q p h
    simp only [Comm.wp] at h
    rcases h₁ : Comm.wp c₁ q with _ | r
    · rw [h₁] at h; simp at h
    · rw [h₁] at h
      exact Hoare.seq (ih₀ r p h) (ih₁ q r h₁)
  | ite b c₀ c₁ ih₀ ih₁ =>
    intro q p h
    simp only [Comm.wp] at h
    rcases h₀ : Comm.wp c₀ q with _ | p₀
    · rw [h₀] at h; simp at h
    rcases h₁ : Comm.wp c₁ q with _ | p₁
    · rw [h₀, h₁] at h; simp at h
    rw [h₀, h₁] at h
    simp only [Option.bind_some, Option.map_some, Option.some.injEq] at h
    subst h
    exact Hoare.ite (Hoare.strengthen (ite_pre_then b _ _) (ih₀ q p₀ h₀))
      (Hoare.strengthen (ite_pre_else b _ _) (ih₁ q p₁ h₁))
  | wh b c _ => intro q p h; simp [Comm.wp] at h
  | newvar v e c ih =>
    intro q p h
    simp only [Comm.wp] at h
    by_cases hv : v ∈ q.fv ∨ v ∈ e.fv
    · rw [if_pos hv] at h; simp at h
    · rw [if_neg hv] at h
      rw [not_or] at hv
      rcases hc : Comm.wp c q with _ | p'
      · rw [hc] at h; simp at h
      · rw [hc] at h
        simp only [Option.map_some, Option.some.injEq] at h
        subst h
        exact Hoare.newvar (by simp [Assert.fv]) hv.1 hv.2
          (Hoare.strengthen (newvar_pre v e _) (ih q p' hc))
```

그 사전조건은 가장 약하다.

```anchor wpWeakest (module := Reynolds.Answers.Ch03.Wlp)
/--
**`wp` 는 가장 약하다.** 의미적 wlp 가 참인 곳에서는 계산한 `wp` 도 참이다.

변수 선언 절이 요점이다. `∀ v. v = e ⇒ p` 에서 `v` 를 `⟦e⟧ σ` 로 고정하면 (`v ∉ FV(e)`),
안쪽 명령이 끝난 상태 `ρ` 에서 `q` 가 참이어야 하는데, 바깥에서 아는 것은 `v` 를 복원한
`ρ[v := σ v]` 에서 `q` 가 참이라는 것뿐이다. `v ∉ FV(q)` 가 둘을 잇는다 (명제 1.1).
-/
@[exercise "§3.10 wp-weakest" 3]
theorem wp_weakest [HasFresh V] (c : Comm V) :
    ∀ q p, Comm.wp c q = some p → ∀ σ, wlp c ⟦q⟧ₐ σ → ⟦p⟧ₐ σ := by
  induction c with
  | assign v e =>
    intro q p h σ hw
    cases h
    exact (substitution_single q v e σ).mpr (hw _ rfl)
  | skip => intro q p h σ hw; cases h; exact hw σ rfl
  | seq c₀ c₁ ih₀ ih₁ =>
    intro q p h σ hw
    simp only [Comm.wp] at h
    rcases h₁ : Comm.wp c₁ q with _ | r
    · rw [h₁] at h; simp at h
    · rw [h₁] at h
      refine ih₀ r p h σ fun ρ hρ => ih₁ q r h₁ ρ fun τ hτ => hw τ ?_
      change Option.bind (⟦c₀⟧ᶜ σ) ⟦c₁⟧ᶜ = some τ
      rw [hρ]; exact hτ
  | ite b c₀ c₁ ih₀ ih₁ =>
    intro q p h σ hw
    simp only [Comm.wp] at h
    rcases h₀ : Comm.wp c₀ q with _ | p₀
    · rw [h₀] at h; simp at h
    rcases h₁ : Comm.wp c₁ q with _ | p₁
    · rw [h₀, h₁] at h; simp at h
    rw [h₀, h₁] at h
    simp only [Option.bind_some, Option.map_some, Option.some.injEq] at h
    subst h
    change (⟦b.toAssert⟧ₐ σ → ⟦p₀⟧ₐ σ) ∧ (¬ ⟦b.toAssert⟧ₐ σ → ⟦p₁⟧ₐ σ)
    refine ⟨fun hb => ih₀ q p₀ h₀ σ fun τ hτ => hw τ ?_,
      fun hb => ih₁ q p₁ h₁ σ fun τ hτ => hw τ ?_⟩
    · change (if ⟦b⟧ᵇ σ then ⟦c₀⟧ᶜ σ else ⟦c₁⟧ᶜ σ) = some τ
      rw [if_pos ((boolExp_eval_iff b σ).mp hb)]; exact hτ
    · change (if ⟦b⟧ᵇ σ then ⟦c₀⟧ᶜ σ else ⟦c₁⟧ᶜ σ) = some τ
      rw [if_neg fun h => hb ((boolExp_eval_iff b σ).mpr h)]; exact hτ
  | wh b c _ => intro q p h; simp [Comm.wp] at h
  | newvar v e c ih =>
    intro q p h σ hw
    simp only [Comm.wp] at h
    by_cases hv : v ∈ q.fv ∨ v ∈ e.fv
    · rw [if_pos hv] at h; simp at h
    · rw [if_neg hv] at h
      rw [not_or] at hv
      rcases hc : Comm.wp c q with _ | p'
      · rw [hc] at h; simp at h
      · rw [hc] at h
        simp only [Option.map_some, Option.some.injEq] at h
        subst h
        intro n hn
        change (σ[v := n]) v = ⟦e⟧ₑ (σ[v := n]) at hn
        have he : ⟦e⟧ₑ (σ[v := n]) = ⟦e⟧ₑ σ :=
          (coincidence_intExp e σ _ fun w hw =>
            (State.subst_of_ne σ v w _ fun (h : w = v) => hv.2 (h ▸ hw)).symm).symm
        rw [State.subst_self, he] at hn
        subst hn
        refine ih q p' hc _ fun ρ hρ => ?_
        have hq := hw (ρ[v := σ v]) (by
          change restore v σ (⟦c⟧ᶜ (σ[v := ⟦e⟧ₑ σ])) = some (ρ[v := σ v])
          rw [hρ]; rfl)
        exact (coincidence_assert q ρ (ρ[v := σ v]) fun w hw =>
          (State.subst_of_ne ρ v w _ fun (h : w = v) => hv.1 (h ▸ hw)).symm).mpr hq
```

둘을 결과 규칙의 전제 강화 하나로 이으면 상대 완전성이다.

```anchor completeLoopFree (module := Reynolds.Answers.Ch03.Wlp)
/--
**`while` 없는 조각의 상대 완전성.** 타당한 명세는 모두 유도된다 — 단언의 타당성을 결과 규칙의
오라클로 두는 한에서.

`wp_sound` 가 유도를, `wp_weakest` 가 그 유도의 사전조건이 어떤 타당한 사전조건보다도
약하다는 것을 준다. 결과 규칙의 전제 강화 하나로 잇는다. 두 연습에 기대므로 채점 연습이
아니다 (연습 독립성 원칙).
-/
theorem complete_loopFree [HasFresh V] {c : Comm V} {p p' q : Assert V}
    (hwp : Comm.wp c q = some p) (h : ｛p'｝c｛q｝) : Hoare p' c q :=
  Hoare.strengthen (fun σ hp' => wp_weakest c q p hwp σ fun τ hτ => h σ hp' τ hτ)
    (wp_sound c q p hwp)
```

# 이 장이 다루지 않는 것
%%%
tag := "ch03-limits"
file := "ch03-limits"
number := false
%%%

: 유령 변수

  유령 변수도 `V`의 원소다. "유령"은 타입이 아니라 _`FA(c)`에 없다_는 성질이다. 상수
  규칙과 전체 정확성 `while` 규칙의 `z ∉ FV(c)`가 그것을 요구한다.

: 산술 오류

  §2.7에서 나눗셈을 전함수로 만든 덕에 이 장의 규칙에는 "식이 정의된다"는 전제가 없다.

: 배열

  4장의 배열이 들어오면 대입 공리가 깨진다. `a[i] := e`는 `i = j`일 때 `a[j]`도 바꾼다.
  §2.5에서 치환 정리를 깨뜨린 별칭이 대입 공리도 깨뜨린다.
