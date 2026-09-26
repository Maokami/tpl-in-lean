/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Answers.Ch02

/-!
# §3.1 명세의 구문과 뜻

Reynolds §3.1 에 대응한다.

## 명세는 새 의미론이 아니다

명령 앞뒤에 단언을 놓는다.

```
{ p } c { q }     부분 정확성(partial correctness)
[ p ] c [ q ]     전체 정확성(total correctness)
```

`p` 는 사전조건, `q` 는 사후조건이다. 둘 다 1장의 단언이고, 가운데는 2장의 명령이다.
그래서 명세의 뜻을 정하는 데 새로 만들 것이 없다 — 2장의 `⟦c⟧ᶜ : State V → SigmaBot V`
에 단언 둘을 붙이면 끝이다.

- 부분 정확성: `c` 가 `σ` 에서 **끝났다면** 그 상태가 `q` 를 만족한다.
- 전체 정확성: `c` 가 `σ` 에서 **끝나고**, 그 상태가 `q` 를 만족한다.

차이는 비종료를 어느 쪽으로 세느냐뿐이다.

## `⊥` 는 모든 사후조건을 만족한다

부분 정확성의 정의를 `Σ⊥` 의 눈으로 다시 읽으면 "`⟦c⟧ σ = ⊥` 이거나, 상태이고 `q`" 다.
`⊥` 가 아무 사후조건이나 만족한다는 것은 정보 순서에서 `⊥` 가 맨 아래라는 것의 논리적
판이다 — 정보가 없으니 어떤 주장과도 어긋나지 않는다.

이 관찰이 이 장의 가장 깊은 지점과 바로 닿는다. **부분 정확성은 사슬의 극한을 통과한다.**
`Σ⊥` 가 평평하므로 극한은 사슬의 어느 항과 같고(§2.3 `Chain.flat_lub_mem_range`), 그 항에서
성립하던 것이 극한에서도 성립한다. §2.4 의 말로 부분 정확성은 **허용 가능**하고, 그래서
`while` 규칙의 건전성이 Scott 귀납법이 된다(§3.5). 전체 정확성은 그렇지 않다 — "끝난다" 는
어느 단계부터인지를 말해 주지 않으면 극한으로 올라가지 않는다. 그쪽은 측도가 필요하다.

## 단언은 구문이면서 의미다

명세의 뜻은 `⟦p⟧ₐ` 만 쓰므로, 사실 상태 위의 술어 `P : State V → Prop` 만 있으면 정의된다.
그래서 의미 판(`Sat`, `PartialCorrectS`)을 먼저 두고 구문 판(`PartialCorrect`)을 그 특수
경우로 잇는다. 규칙(§3.2)은 구문 판에 대해 세운다 — 대입 공리처럼 단언의 **구문**을
조작하는 규칙은 `Assert` 위에서만 뜻이 있다. 예제(§3.8~3.9)는 불변식이 `Assert` 로
안 적힐 때 의미 판을 쓴다. 그 자리가 §3.10 표현력 논점의 실물이다.

## 읽는 순서
2장을 다 읽은 뒤. 이 파일 → `Hoare.lean` (§3.2, 추론 규칙).

## 책과의 차이
책의 `{ }`·`[ ]` 는 Lean 에서 이미 다른 뜻이라 전각 괄호 `｛ ｝`·［ ］ 를 쓴다.
-/

@[expose] public section

namespace Reynolds.Exercises.Ch03

open Reynolds Reynolds.Answers.Ch01 Reynolds.Answers.Ch02

universe u

variable {V : Type u} [DecidableEq V]

/-! ## 1. 상태 변환기에 대한 삼중항

명령이 아니라 그 **뜻** `w : State V → SigmaBot V` 에 대해 먼저 정의한다. §3.5 에서
`while` 의 근사열 `Fⁿ(⊥)` 에 대해 말하려면 명령이 아닌 함수에 대한 판이 필요하다. -/

/--
`w` 가 `P` 에서 출발해 끝나면 `Q` 다. 부분 정확성의 알맹이.

`w σ = ⊥` 면 조건 없이 참이다 — `⊥` 는 모든 사후조건을 만족한다.
-/
def Sat (P : State V → Prop) (w : State V → SigmaBot V) (Q : State V → Prop) : Prop :=
  ∀ σ, P σ → ∀ τ, w σ = some τ → Q τ

omit [DecidableEq V] in
/-- **`⊥` 는 모든 사후조건을 만족한다.** 아무 데서도 끝나지 않으므로 확인할 것이 없다. -/
theorem Sat.bot (P Q : State V → Prop) : Sat P (⊥ : State V → SigmaBot V) Q :=
  fun _ _ _ h => by simp at h

/-! ## 2. 극한을 통과한다

§3.5 의 `while` 규칙이 쓸 꼴이다. 사슬의 각 항이 사후조건을 지키면 극한도 지킨다.
평평함이 전부다 — 극한은 어느 항과 같다. -/

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
  -- 먼저 볼 것: §2.3 의 `Chain.flat_lub_mem_range` 와 `Chain.lub_apply`, 그리고 §2.5 의
  --            `AgreeOn.admissible` — 같은 논증인데 관계가 아니라 술어라 더 짧다.
  -- 힌트 1: `Chain.lub_apply` 로 `d.lub σ` 를 `Σ⊥` 사슬 `d.apply σ` 의 극한으로 바꾼다.
  -- 힌트 2: 평평한 사슬의 극한은 어느 항과 같다. 그 항 `k` 에서 가정 `h k` 가 `Q` 를 준다.
  sorry


omit [DecidableEq V] in
/-- 삼중항 판. Scott 귀납법의 `hadm` 자리에 그대로 들어간다.

`sat_admissible` 을 부르지 않고 같은 논증을 다시 적는다 — §3.5 의 `while` 규칙 건전성
(그 자체가 연습) 이 이것에 기대므로, 연습이 연습에 기대지 않게 한다 (연습 독립성 원칙,
`AGENTS.md` §1-9). -/
theorem Sat.admissible (P Q : State V → Prop) (d : Chain (State V → SigmaBot V))
    (h : ∀ n, Sat P (d.seq n) Q) : Sat P d.lub Q := by
  intro σ hσ τ hτ
  rw [Chain.lub_apply] at hτ
  obtain ⟨k, hk⟩ := (d.apply σ).flat_lub_mem_range
  rw [← hk] at hτ
  exact h k σ hσ τ hτ

/-! ## 3. 명령에 대한 명세 -/

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

/-- 책의 `{ p } c { q }`. 전각 괄호를 쓴다 — `{ }` 는 Lean 에서 이미 다른 뜻이다. -/
scoped syntax:max "｛" term "｝" term:max "｛" term "｝" : term
/-- 책의 `[ p ] c [ q ]`. -/
scoped syntax:max "［" term "］" term:max "［" term "］" : term

scoped macro_rules
  | `(｛$p｝ $c ｛$q｝) => `(PartialCorrect $p $c $q)
scoped macro_rules
  | `(［$p］ $c ［$q］) => `(TotalCorrect $p $c $q)

/-- 구문 판은 정의상 의미 판이다. 펼치면 §3.1 의 문장 그대로다. -/
theorem partialCorrect_iff (p : Assert V) (c : Comm V) (q : Assert V) :
    ｛p｝c｛q｝ ↔ ∀ σ, ⟦p⟧ₐ σ → ∀ τ, ⟦c⟧ᶜ σ = some τ → ⟦q⟧ₐ τ := Iff.rfl

theorem totalCorrect_iff (p : Assert V) (c : Comm V) (q : Assert V) :
    ［p］c［q］ ↔ ∀ σ, ⟦p⟧ₐ σ → ∃ τ, ⟦c⟧ᶜ σ = some τ ∧ ⟦q⟧ₐ τ := Iff.rfl

-- 첫 명세. `x = 1` 에서 `x := x + 1` 을 돌리면 `x = 2` 다. 정의만으로 계산된다.
example : ｛⟪ x = 1 ⟫ₐ｝⟪ x := x + 1 ⟫ᶜ｛⟪ x = 2 ⟫ₐ｝ := by
  intro σ h τ hτ
  change some (σ["x" := σ "x" + 1]) = some τ at hτ
  obtain rfl := Option.some.inj hτ
  simp [Assert.eval, IntExp.eval, Cmp.denote] at h ⊢
  omega

/-! ## 4. 부분과 전체의 관계

전체는 부분에 종료를 더한 것이다. 정의에서 바로 나온다. -/

/-- **전체 정확성은 부분 정확성을 준다.** 끝나는데 `q` 이니, 끝났다면 `q` 다. -/
@[exercise "§3.1 total-to-partial" 1]
theorem TotalCorrect.toPartial {p q : Assert V} {c : Comm V} (h : ［p］c［q］) :
    ｛p｝c｛q｝ := by
  -- 힌트: 두 정의를 펼치면 (`intro σ hp τ hτ`) 전체 정확성이 준 `τ'` 와 가정의 `τ` 가
  --       같은 `some` 의 안이다. `Option.some.inj` 로 둘을 같게 만든다.
  sorry


/-- `p` 에서 출발하면 반드시 끝난다. -/
def Halts (p : Assert V) (c : Comm V) : Prop := ∀ σ, ⟦p⟧ₐ σ → (⟦c⟧ᶜ σ).isSome

/--
**전체 정확성 = 부분 정확성 + 종료.** 비종료를 어느 쪽으로 세느냐가 두 명세의 유일한
차이라는 것을 한 등식으로 적은 것이다.
-/
@[exercise "§3.1 halts-iff" 1]
theorem totalCorrect_iff_partial_halts {p q : Assert V} {c : Comm V} :
    ［p］c［q］ ↔ ｛p｝c｛q｝ ∧ Halts p c := by
  -- 힌트 1: `→` 는 전체 정확성이 준 종료 상태로 두 성분을 각각 만든다. 종료 쪽은
  --         `simp [hτ]` 가 `isSome` 을 닫는다.
  -- 힌트 2: `←` 는 `Option.isSome_iff_exists` 로 종료 상태를 꺼낸 뒤 부분 정확성에 넣는다.
  sorry


/-! ## 5. 사전조건은 강하게, 사후조건은 약하게

§3.2 의 결과 규칙이 될 사실이다. 여기서는 규칙이 아니라 뜻에 대한 정리로 적는다.
전제가 `Stronger` — 단언의 **타당성**이다. Hoare 논리가 단언 논리를 오라클로 쓴다는 것이
이 한 정리에 이미 들어 있다. -/

/-- 사전조건을 강하게 하고 사후조건을 약하게 해도 명세는 유지된다. -/
theorem PartialCorrect.conseq {p p' q q' : Assert V} {c : Comm V}
    (hp : Stronger p' p) (h : ｛p｝c｛q｝) (hq : Stronger q q') : ｛p'｝c｛q'｝ :=
  fun σ hp' τ hτ => hq τ (h σ (hp σ hp') τ hτ)

/-- 전체 정확성 판. -/
theorem TotalCorrect.conseq {p p' q q' : Assert V} {c : Comm V}
    (hp : Stronger p' p) (h : ［p］c［q］) (hq : Stronger q q') : ［p'］c［q'］ :=
  fun σ hp' => let ⟨τ, hτ, hqτ⟩ := h σ (hp σ hp'); ⟨τ, hτ, hq τ hqτ⟩

/-! ## 6. 명세의 자유 변수

`FV({p} c {q}) = FV(p) ∪ FV(c) ∪ FV(q)`. §3.6 의 변수 선언 규칙과 §3.7 의 치환 규칙이 쓴다.
1장의 `Assert.fv` 와 2장의 `Comm.fv` 를 합치면 끝이다. -/

/-- 명세의 자유 변수. -/
def Spec.fv (p : Assert V) (c : Comm V) (q : Assert V) : Finset V := p.fv ∪ c.fv ∪ q.fv

/-! ## 7. 여기서 어디로 가나

명세의 뜻을 정했고, 그것이 극한을 통과한다는 것(`Sat.admissible`)까지 챙겼다. 다음은
§3.2~3.3 의 추론 규칙이다. §1.3 의 `Proof` 처럼 규칙 하나가 생성자 하나인 귀납 술어
`Hoare` 를 두고, 건전성을 규칙마다 1·2장의 정리 하나로 증명한다. 대입 공리가 명제 1.4 인
것이 첫 번째다. -/

end Reynolds.Exercises.Ch03
