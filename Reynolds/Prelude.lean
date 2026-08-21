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

## 변수를 타입 하나로 고정하지 않는 이유

Reynolds §1.1 은 변수 집합을 이렇게 소개한다.

> *"⟨var⟩ is a predefined nonterminal denoting a countably infinite set of
> variables (with unspecified representations)."*

문자열인지 자연수인지는 책의 어떤 명제에도 걸리지 않는다. 코드에서는 정의마다 실제로
필요한 조건만 요구한다. 구문과 정수 식의 의미에는 `V`에 관한 조건이 없다. 자유 변수 계산,
상태 갱신, 일치 정리에는 `DecidableEq V`가 필요하고, 포획 회피 치환에는 `HasFresh V`가
추가로 필요하다.

- `DecidableEq V` — 두 변수가 같은지 판정할 수 있어야 자유 변수와 치환이 계산된다.
- `HasFresh V` — 유한 집합이 주어지면 그 안에 없는 변수를 하나 만들 수 있다.
  §1.4 에서 변수 포획(capture)을 피할 때 쓴다.

**책과의 차이**: Reynolds 는 변수 집합을 가산 무한으로 가정한다. `HasFresh V` 는
무한성을 주지만 가산성까지 요구하지는 않는다. 이 일반화는 이 저장소에서 증명하는
정리들의 내용에는 영향을 주지 않는다.

Reynolds 는 §1.4 에서 새 변수를 "어떤 표준 순서에서 첫 번째" 로 정한다.
그 순서가 무엇인지는 이어지는 어떤 명제에도 쓰이지 않고, 필요한 것은
언제나 새 이름을 얻는다는 사실뿐이다. `HasFresh.fresh_notMem` 이 그 사실이다.

## 상태

`State V = V → ℤ` 가 Reynolds 의 Σ 다. 논리학자는 assignment, 프로그래머는 메모리라고 부른다.

상태 갱신 `[σ | v: n]` 은 새로 만들지 않고 CSlib 것을 쓴다.
`HasSubstitution (α → β) α β` 인스턴스가 `Function.update` 라서 `σ[v := n]` 이 그대로 된다.

Reynolds 는 상태 갱신을 §1.2 에서, 치환을 §1.4 에서 따로 도입하지만 모양이 겹친다.
상태는 `⟨var⟩ → ℤ`, 치환 사상은 `⟨var⟩ → ⟨intexp⟩` 이고 둘 다 한 변수 자리만 바꾼다.
CSlib 가 둘을 같은 타입클래스로 묶어 둔 것도 그래서다.
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

`σ[v := n]` 은 `HasSubstitution.subst` 의 표기이고 인스턴스가 `Function.update` 인데,
타입클래스 프로젝션이라 증명에서 바로 풀리지 않는다.
필요한 사실 둘만 꺼내 `simp` 보조정리로 둔다. §1.4 의 정리들에서 계속 쓴다.
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

/-!
## 예제용 변수 타입

`String` 을 변수로 쓰면 예제가 읽힌다. 그런데 §1.4 의 치환은 `HasFresh` 를 요구하고,
Mathlib 이 주는 `Infinite String` 경유 인스턴스는 계산 불가능해서 `#eval` 이나 `#guard` 로
돌려 볼 수가 없다. 그래서 계산되는 인스턴스를 직접 만든다.
-/

/--
`ℕ ↪ String`. `n` 을 `'x'` 를 `n+1` 번 반복한 문자열로 보낸다: `x`, `xx`, `xxx`, ….

`n` 번이 아니라 `n+1` 번인 이유는 `n = 0` 일 때 빈 문자열이 나오지 않게 하려는 것이다.
빈 문자열도 `String` 이긴 하지만 새 결합 변수 이름으로 나오면 예제가 읽히지 않는다.
-/
def natToString : ℕ ↪ String where
  toFun n := String.ofList ('x' :: List.replicate n 'x')
  inj' a b h := by
    have hl := String.ofList_injective h
    simpa using congrArg List.length hl

/-- 계산 가능한 `HasFresh String`. `Nat.find` 로 아직 안 쓴 이름을 찾는다. -/
instance hasFreshString : Cslib.HasFresh String := Cslib.HasFresh.ofNatEmbed natToString

/--
모든 변수를 `n` 으로 보내는 상수 상태. 예제와 `#eval` 에서 쓴다.

일치 정리(§1.4 명제 1.1)에 따라 구는 자유 변수 위의 값에만 의존하므로,
예제에서 나머지 변수를 무엇으로 두든 결과가 달라지지 않는다.
-/
def State.const {V : Type u} (n : Int) : State V := fun _ => n

end Reynolds
