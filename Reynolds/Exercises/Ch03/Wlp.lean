/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Exercises.Ch03.Examples.FastExp

/-!
# §3.10 최약 사전조건 · 완전성 · 한계

건전성의 역이 완전성이다 — 타당한 명세는 모두 유도되는가? 답은 **아니오**, 그리고
**조건부로 예** 다.

- **아니오** — 결과 규칙의 전제가 단언의 타당성이고, 정수 산술을 담은 단언의 타당성에는
  (괴델 불완전성 정리에 의해) 완전한 공리계가 없다. 단언 논리의 증명까지 세면 Hoare 논리는
  완전할 수 없다.
- **조건부로 예** — 단언의 타당성을 **오라클**로 두면 (우리 `conseq` 가 그렇게 한다) 완전성이
  성립한다. Cook 의 **상대 완전성**이다. 단, 모든 명령과 사후조건에 대해 최약 사전조건을
  단언으로 **적을 수 있어야** 한다 (표현력).

우리 `Assert` 는 정수 산술과 양화사가 있어 이론적으로는 표현력이 충분하다 — 괴델의 β-함수로
유한 수열을 부호화하면 반복의 최약 사전조건을 적을 수 있다. 그것을 형식화하는 것은 이 장의
범위를 넘으므로, **완전성은 `while` 없는 조각에서만 증명한다.** 거기서는 최약 사전조건이
치환만으로 계산된다 (§3 의 `Comm.wp`). `while` 절에서 `none` 이 나오는 그 자리가 표현력이
필요한 자리다.

## wlp 는 최대 고정점이다

2장에서 `while` 의 **뜻**은 최소 고정점이었다. `while` 의 **최약 자유 사전조건**은 최대
고정점이다.

```
wlp (while b do c) Q  =  νX. (¬b ∧ Q) ∨ (b ∧ wlp c X)
```

방정식의 모양은 같은데 고르는 해가 반대다. 부분 정확성은 비종료를 **허용**하므로, 발산하는
입력에서 사전조건이 참이어도 상관없다 — 가장 너그러운(최대) 해가 최약 사전조건이다. 상태
변환기의 정보 순서에서 `⊥` 가 아래에 있는 것과, 술어의 함의 순서에서 "모두 허용" 이 위에
있는 것이 서로 뒤집힌 상이다. `wlp_wh_greatest` 가 `fix_least` 의 거울상이다 — 그런데 증명은
**여전히 Scott 귀납법**이다. 최대 고정점 성질이 최소 고정점 위의 귀납으로 증명된다.

## 유령 변수, 산술 오류, 이 장이 다루지 않는 것

- 유령 변수도 `V` 의 원소다. "유령" 은 타입이 아니라 **`FA(c)` 에 없다**는 성질이다. 상수
  규칙과 전체 정확성 `while` 규칙의 `z ∉ FV(c)` 가 그것을 요구한다.
- §2.7 에서 나눗셈을 전함수로 만든 덕에 이 장의 규칙에 "식이 정의된다" 는 전제가 없다.
- 배열(4장)이 들어오면 대입 공리가 깨진다 — `a[i] := e` 는 `i = j` 일 때 `a[j]` 도 바꾼다.
  §2.5 에서 치환 정리를 깨뜨린 별칭이 대입 공리도 깨뜨린다.

## 읽는 순서
`Examples/FastExp.lean` → 이 파일. 3장의 끝이다.
-/

@[expose] public section

namespace Reynolds.Exercises.Ch03

open Reynolds Reynolds.Answers.Ch01 Reynolds.Answers.Ch02

universe u

variable {V : Type u} [DecidableEq V]

/-! ## 1. 의미적 최약 자유 사전조건 -/

/-- 의미적 최약 자유 사전조건(weakest liberal precondition). `c` 가 끝나면 `Q` 가 참인 상태들. -/
def wlp (c : Comm V) (Q : State V → Prop) : State V → Prop :=
  fun σ => ∀ τ, ⟦c⟧ᶜ σ = some τ → Q τ

/-- 부분 정확성은 wlp 로 다시 쓰인다. 정의 그대로다. 그러니 `wlp c Q` 는 `{P} c {Q}` 를 만족하는
가장 약한 `P` 다. -/
theorem partialCorrectS_iff_wlp {P Q : State V → Prop} {c : Comm V} :
    PartialCorrectS P c Q ↔ ∀ σ, P σ → wlp c Q σ := Iff.rfl

/-! ## 2. `while` 의 wlp 는 최대 고정점이다 -/

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
  -- 먼저 볼 것: `Soundness.lean` 의 `wh_sound` 를 풀었다면 같은 증명이다.
  --            §2.4 `scott_induction`, §3.1 `Sat.admissible` · `Sat.bot`.
  -- 힌트 1: 목표는 정의상 `Sat X (fix (whileF b ⟦c⟧ᶜ) (whileF_monotone b ⟦c⟧ᶜ)) Q` 다 (`change`).
  -- 힌트 2: `scott_induction … (P := fun w => Sat X w Q)` 의 한 바퀴에서 `hX σ hx` 로 나눈다.
  --         조건이 거짓이면 그 자리에서 `Q`, 참이면 본체가 끝난 상태에서 `X` 가 되어 가설로 넘긴다.
  sorry


/-! ## 3. `while` 없는 조각 — 구문적 최약 사전조건 -/

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

/-- **`wp` 는 유도를 준다.** 계산한 사전조건에서 `Hoare` 유도가 있다. `Annot.lean` 의 세 보조
함의(`ite_pre_then` · `ite_pre_else` · `newvar_pre`)가 그대로 쓰인다. -/
@[exercise "§3.10 wp-sound" 2]
theorem wp_sound [HasFresh V] (c : Comm V) :
    ∀ q p, Comm.wp c q = some p → Hoare p c q := by
  -- 먼저 볼 것: `Hoare` 의 생성자들, `Hoare.strengthen`, `Annot.lean` 의 `ite_pre_then` ·
  --            `ite_pre_else` · `newvar_pre`. `Annot.vcg_sound` 와 같은 모양이다.
  -- 힌트 1: `induction c` — 각 절에서 `simp only [Comm.wp] at h` 로 계산을 펼친다.
  -- 힌트 2: `Option` 이 `none` 인 경우는 `h` 가 모순이다. `rcases h₀ : Comm.wp c₀ q with _ | p₀`
  --         처럼 이름을 붙여 나누고 `simp only [Option.bind_some, Option.map_some,
  --         Option.some.injEq] at h` 로 `p` 를 드러낸다.
  -- 힌트 3: `newvar` 는 `by_cases hv : v ∈ q.fv ∨ v ∈ e.fv` 로 나눈다. 결합자는 `∀` 가 가둔다.
  sorry


/--
**`wp` 는 가장 약하다.** 의미적 wlp 가 참인 곳에서는 계산한 `wp` 도 참이다.

변수 선언 절이 요점이다. `∀ v. v = e ⇒ p` 에서 `v` 를 `⟦e⟧ σ` 로 고정하면 (`v ∉ FV(e)`),
안쪽 명령이 끝난 상태 `ρ` 에서 `q` 가 참이어야 하는데, 바깥에서 아는 것은 `v` 를 복원한
`ρ[v := σ v]` 에서 `q` 가 참이라는 것뿐이다. `v ∉ FV(q)` 가 둘을 잇는다 (명제 1.1).
-/
@[exercise "§3.10 wp-weakest" 3]
theorem wp_weakest [HasFresh V] (c : Comm V) :
    ∀ q p, Comm.wp c q = some p → ∀ σ, wlp c ⟦q⟧ₐ σ → ⟦p⟧ₐ σ := by
  -- 먼저 볼 것: `substitution_single` (명제 1.4), `boolExp_eval_iff`,
  --            `coincidence_assert` · `coincidence_intExp` (명제 1.1), `restore`.
  -- 힌트 1: `induction c`. 각 절에서 `wlp` 가 주는 "끝나면 `q`" 를 안쪽 명령의 `wlp` 로 옮겨
  --         귀납 가설에 넘긴다. 순차 합성은 가운데 상태 `ρ` 를, 조건은 `if_pos`/`if_neg` 를 쓴다.
  -- 힌트 2: `newvar` — `∀ n, σ[v := n] v = ⟦e⟧ (σ[v := n]) → …` 에서 `n = ⟦e⟧ σ` 다
  --         (`v ∉ FV(e)`). 안쪽이 끝난 상태 `ρ` 에서 `q` 를 얻으려면, 바깥이 끝난 상태
  --         `ρ[v := σ v]` 에서의 `q` 를 명제 1.1 로 옮긴다 (`v ∉ FV(q)`).
  sorry


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

/-! ## 4. 여기서 어디로 가나

3장은 여기까지다. 규칙은 건전하고(§3.2~3.7), 예제는 끝까지 유도되며(§3.8 · §3.9), 완전성은
`while` 없는 조각에서 성립한다(이 파일). 4장의 배열은 대입 공리의 전제 — 변수 하나를 바꾸면
그 변수만 바뀐다 — 를 무너뜨린다. -/

end Reynolds.Exercises.Ch03
