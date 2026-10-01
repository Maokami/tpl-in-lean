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

명세의 뜻은 새로 만들 것이 없다. 2장의 `⟦c⟧ : State V → Flat (State V)`가 이미 있으므로,
그 함수가 단언 둘 사이에서 어떻게 행동하는지 말하면 된다. 알맹이를 상태 변환기 `w` 하나에
대한 성질로 떼어 둔다.

```anchor Sat (module := Reynolds.Answers.Ch03.Spec)
/--
`w` 가 `P` 에서 출발해 끝나면 `Q` 다. 부분 정확성의 알맹이.

`w σ = ⊥` 면 조건 없이 참이다 — `⊥` 는 모든 사후조건을 만족한다.
-/
def Sat (P : State V → Prop) (w : State V → SigmaBot V) (Q : State V → Prop) : Prop :=
  ∀ σ, P σ → ∀ τ, w σ = Flat.some τ → Q τ
```

`w σ = Flat.none`이면 조건이 공허하게 참이다. *`⊥`는 모든 사후조건을 만족한다.* 사소해
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
theorem sat_admissible (Q : State V → Prop) (σ : State V) (d : Chain (State V → SigmaBot V))
    (h : ∀ n τ, d.seq n σ = Flat.some τ → Q τ) : ∀ τ, d.lub σ = Flat.some τ → Q τ := by
  intro τ hτ
  rw [Chain.lub_apply] at hτ
  obtain ⟨k, hk⟩ := (d.apply σ).flat_lub_mem_range
  rw [← hk] at hτ
  exact h k τ hτ
```

증명의 요점은 §2.3의 평평한 순서다. `Flat (State V)`의 사슬은 `Flat.none`에서 `Flat.some τ` 하나로
한 번 올라가고 멈춘다. 그래서 극한은 _어느 항과 같고_, 그 항에서 이미 성질이 성립한다.

전체 정확성도 사슬의 극한을 통과한다. 그러나 사전조건을 만족하는 상태가 있으면
`Flat.none`으로만 이루어진 사슬의 첫 항 `⊥`는 전체 정확성을 만족하지 않는다. Scott 귀납법의
시작 조건이 성립하지 않으므로, 전체 정확성의 `while` 규칙은 종료까지 보이는 측도를
사용해 정초 귀납으로 증명한다(§3.4).

이 두 주장을 하나의 연습으로 확인한다. 첫 성분은 모든 사슬 항의 종료 증인에서
극한의 종료 증인을 얻는다. 둘째 성분의 `∃ σ, P σ`는 필요하다. 사전조건을 만족하는
상태가 없으면 바닥 함수에서도 전체 정확성이 공허하게 참이기 때문이다.

```anchor stmtTotalAdmissible (module := Reynolds.Answers.Ch03.Spec)
omit [DecidableEq V] in
/--
전체 정확성도 사슬의 극한에서 보존된다. 그러나 사전조건을 만족하는 상태가 있으면
바닥 함수는 종료 결과를 줄 수 없다. 따라서 이 극한 보존만으로 Scott 귀납법을 쓸 수 없다.

**책과의 차이**: §3.1의 명세 의미를 평평한 상태 변환기에 적용하는 보충 연습이다.
책이 명시한 전체 정확성의 위쪽 닫힘(`m' ⊒ m` 이면 `m` 에서 성립한 명세가 `m'` 에서도
성립함, p.56)은 여기 첫 연언의 특수 경우라 따로 정리로 두지 않는다 — 두면 이 연습의
첫 연언이 자명해진다(연습 독립성 원칙). 대신 극한 보존과 바닥에서의 실패를 함께 확인한다.
-/
@[exercise "§3.1 total-admissible" 2]
theorem total_admissible (P Q : State V → Prop) :
    (∀ d : Chain (State V → SigmaBot V),
      (∀ n σ, P σ → ∃ τ, d.seq n σ = Flat.some τ ∧ Q τ) →
      ∀ σ, P σ → ∃ τ, d.lub σ = Flat.some τ ∧ Q τ) ∧
    ((∃ σ, P σ) →
      ¬ (∀ σ, P σ → ∃ τ, (⊥ : State V → SigmaBot V) σ = Flat.some τ ∧ Q τ))
```

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
  ∀ σ, P σ → ∃ τ, ⟦c⟧ᶜ σ = Flat.some τ ∧ Q τ

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

  불변식에 `fib`나 거듭제곱이 드는 예제(§3.6, §3.7)가 여기에 선다. `Assert`로는 그런
  술어를 적을 수 없다(적으려면 괴델 부호화가 필요하다 — 보충 `Wlp.lean` 참고).

구문 판은 `⟦p⟧ₐ`를 거쳐 의미 판의 특수 경우가 된다. 둘을 잇는 데 정리가 필요 없다.

# 부분과 전체
%%%
tag := "ch03-total-partial"
file := "ch03-total-partial"
number := false
%%%

전체 정확성은 부분 정확성보다 강하다.

```anchor stmtTotalToPartial (module := Reynolds.Answers.Ch03.Spec)
/-- **전체 정확성은 부분 정확성을 준다.** 끝나는데 `q` 이니, 끝났다면 `q` 다. -/
@[exercise "§3.1 total-to-partial" 1]
theorem TotalCorrect.toPartial {p q : Assert V} {c : Comm V} (h : ［p］c［q］) :
    ｛p｝c｛q｝
```

힌트: 두 정의를 펼치면 (`intro σ hp τ hτ`) 전체 정확성이 준 종료 증인과 가정의 `τ`가
같은 `Flat.some`의 안이다. `Flat.some.inj`로 둘을 같게 만든다.

그리고 둘의 차이는 정확히 종료다.

```anchor stmtHaltsIff (module := Reynolds.Answers.Ch03.Spec)
/--
**전체 정확성 = 부분 정확성 + 종료.** 비종료를 어느 쪽으로 세느냐가 두 명세의 유일한
차이라는 것을 한 등식으로 적은 것이다.
-/
@[exercise "§3.1 halts-iff" 1]
theorem totalCorrect_iff_partial_halts {p q : Assert V} {c : Comm V} :
    ［p］c［q］ ↔ ｛p｝c｛q｝ ∧ Halts p c
```

힌트: `→`는 전체 정확성이 준 종료 상태로 두 성분을 각각 만든다. `←`는
`Flat.isSome_iff_exists`로 종료 상태를 꺼낸 뒤 부분 정확성에 넣는다.

두 정리 모두 정의를 펼치면 나오지만, 한 가지를 짚어 둔다. `Flat.some τ' = Flat.some τ`에서
`τ' = τ`를 얻는 것이 _결정적_ 의미의 성질이라는 점이다. 2장의 명령은 결정적이라 끝나면
결과가 하나뿐이다. 비결정적 언어(7장)에서는 이 등식이 깨지고, 부분·전체 정확성의 관계도
다시 따져야 한다.

# 순서로 본 명세 — 식 (3.1)·(3.2)
%%%
tag := "ch03-spec-order"
file := "ch03-spec-order"
number := false
%%%

책은 명세의 뜻을 한 번 더, 두 원소 도메인 `{⊥, ⊤}` 위의 함의로 적는다(p.56). 쓰는 함수는
둘뿐이다.

: 성공 램프(success lamp) `pt`

  참이면 ⊤, 거짓이면 ⊥. 전체 정확성이 묻는다 — "사전조건이 참이면 결과도 참이어야 한다."

: 위반 경보(violation alarm) `pf`

  거짓이면 ⊤, 참이면 ⊥. 부분 정확성이 묻는다 — "결과가 거짓(위반)이면 사전조건도
  거짓(위반)이었어야 한다."

`⊤`를 `Flat.some ()`, `⊥`를 `Flat.none`으로 두면 `Flat Unit`이 그 도메인이고, `⊑`는
함의다. 책의 강한 확장 `f⊥⊥`는 `Flat.bind`다(§2.3 끝).

```anchor stmtSpecOrder (module := Reynolds.Answers.Ch03.Spec)
open Classical in
/--
**성공 램프(success lamp) `pt`.** 참이면 ⊤(`Flat.some ()`), 거짓이면 ⊥(`Flat.none`).
Reynolds §3.1 p.56. 결정 가능성은 `Prop`에 일반 `Decidable` 인스턴스가 없으므로
classical(`Classical.propDecidable`)로 얻는다 — `open Classical in` 이 그 인스턴스를 연다.
-/
noncomputable def pt (P : Prop) : Flat Unit := if P then .some () else .none

open Classical in
/-- **위반 경보(violation alarm) `pf`.** 거짓이면 ⊤, 참이면 ⊥ — `pt (¬P)` 와 같은 값이다. -/
noncomputable def pf (P : Prop) : Flat Unit := if P then .none else .some ()

/--
**식 (3.1) — 부분 정확성의 순서 판.** 결과의 위반 경보가 사전조건의 위반 경보보다
정보가 적어야(⊑) 한다. `c` 가 발산하면 `Flat.bind` 가 바닥을 내므로 조건 없이 성립한다.
-/
theorem partialCorrect_iff_pf (p q : Assert V) (c : Comm V) :
    ｛p｝c｛q｝ ↔
      (fun σ => Flat.bind (⟦c⟧ᶜ σ) (fun τ => pf (⟦q⟧ₐ τ))) ≤ (fun σ => pf (⟦p⟧ₐ σ))
```

```anchor stmtSpecOrderTotal (module := Reynolds.Answers.Ch03.Spec)
/--
**식 (3.2) — 전체 정확성의 순서 판.** 사전조건의 성공 램프가 결과의 성공 램프보다
정보가 적어야 한다. `c` 가 발산하면 결과가 ⊥(`Flat.bind` 의 바닥)라 사전조건이 참일 때
만족할 수 없다 — 그래서 종료까지 요구한다.
-/
theorem totalCorrect_iff_pt (p q : Assert V) (c : Comm V) :
    ［p］c［q］ ↔
      (fun σ => pt (⟦p⟧ₐ σ)) ≤ (fun σ => Flat.bind (⟦c⟧ᶜ σ) (fun τ => pt (⟦q⟧ₐ τ)))
```

두 등가는 정의를 펼치고 `Flat Unit`의 두 원소(`none`, `some ()`)로 나누면 나온다 — 증명은
`Spec.lean`에 있다. 전체 정확성 쪽은 `c`가 발산하면 `Flat.bind`도 바닥이라 사전조건이
참일 때 성립할 수 없다는 것이 핵심이다. 부분 정확성의 *아래로 닫힘*(`m' ⊑ m`이면
`m`에서 성립한 명세가 `m'`에서도 성립함)은 `Sat.of_le`가 준다.
