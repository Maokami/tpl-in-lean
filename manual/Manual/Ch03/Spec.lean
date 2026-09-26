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
set_option verso.exampleModule "Reynolds.Answers.Ch03.Spec"

#doc (Manual) "§3.1 명세의 구문과 뜻" =>
%%%
tag := "ch03-spec"
file := "ch03-spec"
number := false
%%%

명세는 명령 앞뒤에 단언을 하나씩 놓은 것이다. 두 종류가 있고, 차이는 _끝나지 않는
실행을 어떻게 세느냐_ 하나뿐이다.

: 부분 정확성(partial correctness) `{p} c {q}`

  `p`에서 시작해 `c`가 _끝나면_ `q`다. 끝나지 않으면 아무것도 약속하지 않는다.

: 전체 정확성(total correctness) `[p] c [q]`

  `p`에서 시작하면 `c`가 _반드시 끝나고_ 끝난 상태가 `q`다.

책의 `{ }`와 `[ ]`는 Lean에서 이미 다른 뜻이 있어서 전각 괄호 `｛p｝c｛q｝`와
`［p］c［q］`로 쓴다.

# 뜻은 2장 위에 그대로
%%%
tag := "ch03-sat"
file := "ch03-sat"
number := false
%%%

명세의 뜻은 새로 만들 것이 없다. 2장의 `⟦c⟧ : State V → Option (State V)`가 이미 있으므로,
그 함수가 단언 둘 사이에서 어떻게 행동하는지 말하면 된다. 알맹이를 상태 변환기 `w` 하나에
대한 성질로 떼어 둔다.

```anchor Sat (module := Reynolds.Answers.Ch03.Spec)
/--
`w` 가 `P` 에서 출발해 끝나면 `Q` 다. 부분 정확성의 알맹이.

`w σ = ⊥` 면 조건 없이 참이다 — `⊥` 는 모든 사후조건을 만족한다.
-/
def Sat (P : State V → Prop) (w : State V → SigmaBot V) (Q : State V → Prop) : Prop :=
  ∀ σ, P σ → ∀ τ, w σ = some τ → Q τ
```

`w σ = none`이면 조건이 공허하게 참이다. *`⊥`는 모든 사후조건을 만족한다.* 사소해
보이지만 이 장 전체를 떠받치는 사실이다. `while`의 뜻은 `⊥`에서 출발한 근사들의 극한이었고
(§2.4), 그 출발점이 어떤 명세든 만족하므로 귀납이 시작될 수 있다.

# 극한을 통과한다
%%%
tag := "ch03-admissible"
file := "ch03-admissible"
number := false
%%%

Scott 귀납법(§2.4)은 성질이 _허용 가능_할 것을 요구한다. 사슬의 모든 항이 만족하면
극한도 만족해야 한다. `Sat P · Q`가 그렇다.

```anchor satAdmissible (module := Reynolds.Answers.Ch03.Spec)
omit [DecidableEq V] in
/--
**사후조건 만족은 극한을 통과한다.** 상태 `σ` 하나를 고정한 판.

`d.lub σ` 는 `Σ⊥` 의 사슬 `d.apply σ` 의 극한이고, 평평한 사슬의 극한은 어느 항
`d.seq k σ` 와 같다 (`Chain.flat_lub_mem_range`). 그 항에서 가정이 `Q` 를 준다.

이것이 §2.4 에서 말한 **허용 가능성**이다. §2.5 의 `AgreeOn.admissible` 과 같은 논증인데
관계가 아니라 술어라 더 짧다.
-/
@[exercise "§3.1 sat-admissible" 2]
theorem sat_admissible (Q : State V → Prop) (σ : State V) (d : Chain (State V → SigmaBot V))
    (h : ∀ n τ, d.seq n σ = some τ → Q τ) : ∀ τ, d.lub σ = some τ → Q τ := by
  intro τ hτ
  rw [Chain.lub_apply] at hτ
  obtain ⟨k, hk⟩ := (d.apply σ).flat_lub_mem_range
  rw [← hk] at hτ
  exact h k τ hτ
```

증명의 요점은 §2.3의 평평한 순서다. `Option (State V)`의 사슬은 `none`에서 `some τ` 하나로
한 번 올라가고 멈춘다. 그래서 극한은 _어느 항과 같고_, 그 항에서 이미 성질이 성립한다.

반대쪽 성질인 "반드시 끝난다"는 허용 가능하지 _않다_. 모든 항이 `none`인 사슬의 극한은
`none`이다. 그래서 전체 정확성의 `while` 규칙은 Scott 귀납법이 아니라 단계를 세는 정초
귀납으로 증명해야 한다(§3.5). 이 비대칭이 3장의 두 `while` 규칙이 서로 다른 모양을 하는
이유다.

# 명령의 명세
%%%
tag := "ch03-spec-defs"
file := "ch03-spec-defs"
number := false
%%%

단언을 _구문_(`Assert`)으로 둘지 _의미_(`State V → Prop`)로 둘지는 두 판을 다 두는 것으로
답한다.

```anchor spec (module := Reynolds.Answers.Ch03.Spec)
/-- 의미 판 부분 정확성. 단언이 상태 위의 술어다. -/
def PartialCorrectS (P : State V → Prop) (c : Comm V) (Q : State V → Prop) : Prop :=
  Sat P ⟦c⟧ᶜ Q

/-- 의미 판 전체 정확성. 끝나야 하고, 끝난 상태가 `Q` 다. -/
def TotalCorrectS (P : State V → Prop) (c : Comm V) (Q : State V → Prop) : Prop :=
  ∀ σ, P σ → ∃ τ, ⟦c⟧ᶜ σ = some τ ∧ Q τ

/-- **부분 정확성** `{ p } c { q }`. Reynolds §3.1. 발산하면 공허하게 참. -/
def PartialCorrect (p : Assert V) (c : Comm V) (q : Assert V) : Prop :=
  PartialCorrectS ⟦p⟧ₐ c ⟦q⟧ₐ

/-- **전체 정확성** `[ p ] c [ q ]`. Reynolds §3.1. 반드시 끝나고 `q` 다. -/
def TotalCorrect (p : Assert V) (c : Comm V) (q : Assert V) : Prop :=
  TotalCorrectS ⟦p⟧ₐ c ⟦q⟧ₐ
```

: 구문 판

  추론 규칙이 여기에 선다. 대입 공리가 단언에 _치환_을 걸어야 하므로 단언이 구문이어야
  한다.

: 의미 판

  불변식에 `fib`나 거듭제곱이 드는 예제(§3.8, §3.9)가 여기에 선다. `Assert`로는 그런
  술어를 적을 수 없다(적으려면 괴델 부호화가 필요하다. §3.10).

구문 판은 `⟦p⟧ₐ`를 거쳐 의미 판의 특수 경우가 된다. 둘을 잇는 데 정리가 필요 없다.

# 부분과 전체
%%%
tag := "ch03-total-partial"
file := "ch03-total-partial"
number := false
%%%

전체 정확성은 부분 정확성보다 강하다.

```anchor totalToPartial (module := Reynolds.Answers.Ch03.Spec)
/-- **전체 정확성은 부분 정확성을 준다.** 끝나는데 `q` 이니, 끝났다면 `q` 다. -/
@[exercise "§3.1 total-to-partial" 1]
theorem TotalCorrect.toPartial {p q : Assert V} {c : Comm V} (h : ［p］c［q］) :
    ｛p｝c｛q｝ := by
  intro σ hp τ hτ
  obtain ⟨τ', hτ', hq⟩ := h σ hp
  obtain rfl := Option.some.inj (hτ.symm.trans hτ')
  exact hq
```

그리고 둘의 차이는 정확히 종료다.

```anchor haltsIff (module := Reynolds.Answers.Ch03.Spec)
/--
**전체 정확성 = 부분 정확성 + 종료.** 비종료를 어느 쪽으로 세느냐가 두 명세의 유일한
차이라는 것을 한 등식으로 적은 것이다.
-/
@[exercise "§3.1 halts-iff" 1]
theorem totalCorrect_iff_partial_halts {p q : Assert V} {c : Comm V} :
    ［p］c［q］ ↔ ｛p｝c｛q｝ ∧ Halts p c := by
  constructor
  · intro h
    refine ⟨fun σ hp τ hτ => ?_, fun σ hp => ?_⟩
    · obtain ⟨τ', hτ', hq⟩ := h σ hp
      obtain rfl := Option.some.inj (hτ.symm.trans hτ')
      exact hq
    · obtain ⟨τ, hτ, _⟩ := h σ hp
      simp [hτ]
  · rintro ⟨hpc, hh⟩ σ hp
    obtain ⟨τ, hτ⟩ := Option.isSome_iff_exists.mp (hh σ hp)
    exact ⟨τ, hτ, hpc σ hp τ hτ⟩
```

두 정리 모두 정의를 펼치면 나오지만, 한 가지를 짚어 둔다. `some τ' = some τ`에서
`τ' = τ`를 얻는 것이 _결정적_ 의미의 성질이라는 점이다. 2장의 명령은 결정적이라 끝나면
결과가 하나뿐이다. 비결정적 언어(7장)에서는 이 등식이 깨지고, 부분·전체 정확성의 관계도
다시 따져야 한다.
