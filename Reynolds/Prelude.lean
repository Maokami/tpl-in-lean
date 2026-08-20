/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Init
public import Mathlib.Data.Finset.Union

/-!
# 공통 기반 — 변수와 상태

Reynolds의 책 전체에서 쓰이는 두 가지를 여기서 정한다: **변수**와 **상태**.

## 변수 — 왜 타입 하나로 고정하지 않는가

Reynolds §1.1:

> *"⟨var⟩ is a predefined nonterminal denoting a countably infinite set of
> variables (with unspecified representations)."*

즉 변수 집합은 **가산 무한**이기만 하면 되고, 그것이 문자열인지 자연수인지는
책의 어떤 명제에도 영향을 주지 않는다. 그래서 우리도 타입을 고정하지 않고
타입 변수 `V`로 두고, 필요한 성질만 타입클래스로 요구한다.

- `DecidableEq V` — 두 변수가 같은지 판정할 수 있어야 자유 변수와 치환을 **계산**할 수 있다.
- `HasFresh V`    — 어떤 유한 집합이 주어져도 그 안에 없는 변수를 하나 만들 수 있다.
                    §1.4에서 변수 포획(capture)을 피할 때 반드시 필요하다.

Reynolds는 §1.4에서 새 변수를 "어떤 표준 순서에서 첫 번째"로 정하는데,
**그 표준 순서가 무엇인지는 아무 명제도 건드리지 않는다.** 필요한 건
"항상 새 이름을 얻는다"뿐이고 그것이 `HasFresh.fresh_notMem`이다.

CSlib가 이 추상화를 이미 갖고 있다는 사실 자체가, 이것이 언어를 형식화할 때
**반복해서 나타나는 패턴**이라는 증거다.

## 상태

`State V = V → ℤ` 는 Reynolds의 Σ 다. 논리학자가 "assignment"라 부르는 것이고,
프로그래머가 "메모리"라 부르는 것이다.

상태 갱신 `[σ | v: n]` 표기는 **새로 만들지 않는다.** CSlib에 이미 있다:
`HasSubstitution (α → β) α β` 인스턴스가 `Function.update`이므로 `σ[v := n]`이 그대로 된다.

이 대응이 중요하다. Reynolds는 §1.2에서 상태 갱신을, §1.4에서 치환을 따로 도입하는데
**둘은 같은 모양**이다 — 상태는 `⟨var⟩ → ℤ`, 치환 사상은 `⟨var⟩ → ⟨intexp⟩`이고
둘 다 "한 변수에서만 바꾸기"를 한다. §1.4의 치환 정리가 훨씬 자연스럽게 들어온다.
-/

@[expose] public section

namespace Reynolds

open Cslib

universe u

/--
상태(state). Reynolds의 `Σ = ⟨var⟩ → ℤ`.

`⟦e⟧ σ` 처럼 의미 함수의 두 번째 인자로 쓰인다. 2장에서 명령의 의미가
`Σ → Σ⊥` 가 되면서 이 타입이 이야기의 중심이 된다.
-/
abbrev State (V : Type u) := V → Int

/-!
## 상태 갱신을 다루는 다리 보조정리

CSlib 의 `σ[v := n]` 은 `HasSubstitution.subst` 의 표기이고, 그 인스턴스가
`Function.update` 다. 그런데 타입클래스 프로젝션이라 증명에서 바로 풀리지 않는다.
그래서 **필요한 사실 둘만** 꺼내 `simp` 보조정리로 둔다.
§1.4 의 일치 정리·치환 정리에서 계속 쓰인다.
-/

section StateUpdate
variable {V : Type u} [DecidableEq V] (σ : State V) (v w : V) (n : Int)

/-- `σ[v := n]` 은 `Function.update σ v n` 이다. Reynolds 의 `[σ | v: n]`. -/
theorem State.subst_def : σ[v := n] = Function.update σ v n := rfl

/-- 덮어쓴 자리의 값. -/
@[simp] theorem State.subst_self : σ[v := n] v = n := by
  simp [State.subst_def]

/-- 덮어쓰지 않은 자리의 값. -/
@[simp] theorem State.subst_of_ne (h : w ≠ v) : σ[v := n] w = σ w := by
  simp [State.subst_def, h]

end StateUpdate

/--
모든 변수를 `n` 으로 보내는 상수 상태. 예제와 `#eval` 에서 쓴다.

실제 프로그램은 유한 개의 변수만 보므로(§1.4 명제 1.1, 일치 정리),
나머지 변수를 무엇으로 두든 상관없다. 그 사실을 이용한 편의 함수다.
-/
def State.const {V : Type u} (n : Int) : State V := fun _ => n

end Reynolds
