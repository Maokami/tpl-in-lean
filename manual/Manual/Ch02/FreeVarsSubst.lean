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
set_option verso.exampleModule "Reynolds.Answers.Ch02.FreeVars"

#doc (Manual) "§2.5 자유 변수와 치환" =>
%%%
tag := "ch02-freevars-subst"
file := "ch02-freevars-subst"
number := false
%%%

1장에서 자유 변수는 집합 하나였다. 명령형 언어에서는 변수를 *읽는* 일과 *쓰는* 일이
다르고, 그래서 집합이 둘로 갈라진다. 그 구분 위에서 일치 정리가 다시 서고, 치환 정리에
1장에 없던 가정이 붙는다.

# 자유 변수가 둘로 갈라진다
%%%
tag := "ch02-fv-fa"
file := "ch02-fv-fa"
number := false
%%%

`FV(c)`는 명령이 읽거나 쓰는 변수 전부이고, `FA(c)`는 _대입하는_ 변수다.

```anchor fvFa (module := Reynolds.Answers.Ch02.FreeVars)
/--
`FV(c)` — 명령이 읽거나 쓰는 변수 전부. Reynolds §2.5.

결합이 있는 절은 `newvar` 하나다. `newvar v := e in c` 에서 `v` 는 `c` 에서만 묶이고,
초기값 `e` 는 범위 밖이라 `e` 의 자유 변수는 지우지 않는다 — 연습 1.5 의 합 식에서
상계가 범위 밖이었던 것과 같은 비대칭이다.
-/
def Comm.fv : Comm V → Finset V
  | .assign v e   => insert v e.fv
  | .skip         => ∅
  | .seq c₀ c₁    => c₀.fv ∪ c₁.fv
  | .ite b c₀ c₁  => b.fv ∪ c₀.fv ∪ c₁.fv
  | .wh b c       => b.fv ∪ c.fv
  | .newvar v e c => e.fv ∪ (c.fv.erase v)

/--
`FA(c)` — 명령이 **대입하는** 변수. Reynolds §2.5.

조건과 반복의 불 식은 읽기만 하므로 들어가지 않는다. `newvar` 의 결합 변수에 대한
대입은 바깥에서 보이지 않으므로 지운다.
-/
def Comm.fa : Comm V → Finset V
  | .assign v _   => {v}
  | .skip         => ∅
  | .seq c₀ c₁    => c₀.fa ∪ c₁.fa
  | .ite _ c₀ c₁  => c₀.fa ∪ c₁.fa
  | .wh _ c       => c.fa
  | .newvar v _ c => c.fa.erase v
```

`FA ⊆ FV`가 성립한다. 대입하는 변수는 당연히 관여하는 변수이기 때문이다.

구분이 값을 하는 자리는 명제 2.6(b)다. "이 명령은 그 변수를 안 건드린다"를 문장으로
만들려면 읽기와 쓰기를 갈라야 한다. §2.6의 `for` 제약도, §2.8의 별칭 이야기도 이
구분 위에 선다.

결합이 있는 절은 `newvar` 하나다. `newvar v := e in c`에서 `v`는 `c`에서만 묶이고
초기값 `e`는 범위 밖이라, `e`의 자유 변수는 지우지 않는다.

# 비종료가 있는 "같다"
%%%
tag := "ch02-agree-on"
file := "ch02-agree-on"
number := false
%%%

1장의 일치 정리는 "자유 변수 위에서 같으면 뜻이 같다" 한 줄이었다. 여기서는 결과가
`Σ⊥`라서 "같다"를 두 경우로 나눠 말해야 한다.

```anchor agreeOn (module := Reynolds.Answers.Ch02.FreeVars)
/-- `S` 위에서의 일치. 명제 2.6 의 결론을 담는 관계다. -/
def AgreeOn (S : Finset V) : SigmaBot V → SigmaBot V → Prop
  | none,   none    => True
  | some τ, some τ' => ∀ w ∈ S, τ w = τ' w
  | _,      _       => False
```

둘 다 `⊥`이거나, 둘 다 상태이고 그 상태들이 다시 자유 변수 위에서 같거나. 하나만 `⊥`인
경우는 거짓이다.

명제 2.6의 증명에는 두 가지 새 도구가 든다.

: 진술 강화

  `FV(c)` 위에서의 일치만으로는 `seq` 절이 돌지 않는다. `c₀`를 지난 상태들은 `FV(c₀)`
  위에서만 일치한다고 알게 되는데, `c₁`은 그 밖의 변수도 읽기 때문이다. 진술을
  "임의의 `S ⊇ FV(c)` 위에서"로 올리면 그 간극이 사라진다. 1장에서 상태를 `∀`로 묶어야
  했던 것과 같은 종류의 일반화이고, 이번에는 집합을 묶는다.

: Scott 귀납법

  `while` 절은 `fix`에 대한 주장이므로 성질이 극한을 통과해야 한다. `AgreeOn`이 허용
  가능하다는 것은 `Σ⊥`의 평평함에서 나온다. 두 극한이 각각 어느 단계에서 이미 결정되어
  있으므로, 극한끼리의 주장이 한 단계끼리의 주장으로 내려온다.

코드에서는 `Comm.coincidence_general`이 명제 2.6(a)이고 `Comm.eval_agree_outside_fa`가
2.6(b)다.

# 명령의 치환은 변수를 변수로만 보낸다
%%%
tag := "ch02-ren"
file := "ch02-ren"
number := false
%%%

1장의 치환 사상은 `⟨var⟩ → ⟨intexp⟩`였다. 변수 자리에 임의의 식을 넣을 수 있었다.
명령에서는 그것이 불가능하다. `x := e`의 왼쪽과 `newvar v := e in c`의 결합자는
_변수 자리_라서, `x`를 `x + 1`로 보내는 치환은 구문에 없는 것을 만들어 낸다.

```anchor Ren (module := Reynolds.Answers.Ch02.Substitution)
/--
명령의 치환 사상. Reynolds 의 `Δ = ⟨var⟩ → ⟨var⟩`.

1장의 `Subst V = V → IntExp V` 와 달리 변수를 **변수로만** 보낸다. 대입의 왼쪽과
`newvar` 의 결합자가 변수 자리이기 때문이다 — 타입이 반칙을 막는다.
-/
abbrev Ren (V : Type u) := V → V

/-- 이름 바꾸기를 1장의 일반 치환으로 읽는다. `w ↦ var (δ w)`. -/
def Ren.toSubst (δ : Ren V) : Subst V := fun w => .var (δ w)
```

형식화에서는 이 제약이 저절로 지켜진다. 타입이 `V → V`라서 변수 아닌 것을 넣는 치환은
아예 적을 수 없다.

```anchor commSubst (module := Reynolds.Answers.Ch02.Substitution)
/--
`c /ᶜ δ` — 명령에 대한 동시 이름 바꾸기.

대입의 왼쪽은 `δ v` 로, 오른쪽 식과 조건 식은 1장의 치환으로 처리한다.
`newvar` 절은 1장의 양화사 절과 같은 수법이다 — 결합자를 새 이름으로 바꾸고,
치환 사상 쪽에서도 `v` 를 새 이름으로 보내도록 고친다.
-/
def Comm.subst [HasFresh V] : Comm V → Ren V → Comm V
  | .assign v e,   δ => .assign (δ v) (e /ₑ δ.toSubst)
  | .skip,         _ => .skip
  | .seq c₀ c₁,    δ => .seq (c₀.subst δ) (c₁.subst δ)
  | .ite b c₀ c₁,  δ => .ite (b /ᵇ δ.toSubst) (c₀.subst δ) (c₁.subst δ)
  | .wh b c,       δ => .wh (b /ᵇ δ.toSubst) (c.subst δ)
  | .newvar v e c, δ =>
      .newvar (c.newBinder v δ) (e /ₑ δ.toSubst)
        (c.subst (Function.update δ v (c.newBinder v δ)))
```

`newvar` 절은 1장의 양화사 절과 같은 수법이다. 결합자를 새 이름으로 바꾸고, 치환 사상
쪽에서도 그 변수를 새 이름으로 보내도록 고친다.

# 치환 정리에 단사 가정이 붙는다
%%%
tag := "ch02-prop27"
file := "ch02-prop27"
number := false
%%%

원래 프로그램의 `w`를 치환된 프로그램의 `δ w`와 비교해야 하므로, 사상을 사이에 둔
일치 관계가 필요하다.

```anchor agreeVia (module := Reynolds.Answers.Ch02.Substitution)
/-- `δ` 를 사이에 둔 `S` 위에서의 일치. 원래 결과의 `w` 값과 치환된 결과의 `δ w` 값을
비교한다. `δ = id` 로 두면 `AgreeOn` 이다. -/
def AgreeVia (δ : Ren V) (S : Finset V) : SigmaBot V → SigmaBot V → Prop
  | none,   none    => True
  | some τ, some τ' => ∀ w ∈ S, τ w = τ' (δ w)
  | _,      _       => False
```

명제 2.7(`Comm.substitution_general`)에는 가정이 둘 붙는다.

: `S ⊇ FV(c)`로의 일반화

  명제 2.6(a)와 똑같은 이유다. `seq` 절에서 `c₀`의 귀납 가설이 주는 일치가 `FV(c₀)`
  위뿐이면 `c₁`이 읽는 나머지를 잇지 못한다.

: `S` 위에서의 단사

  1장에는 없던 가정이다. 서로 다른 두 변수가 같은 변수로 가면 원래 프로그램에서 서로
  다른 저장 공간이던 것이 치환 후에는 같은 공간이 된다.

`while` 절은 명제 2.6(a)보다 한 단계 어렵다. 왼쪽과 오른쪽이 _서로 다른_ 연산자의 최소
고정점이라 Scott 귀납법 하나로는 안 되고, 두 반복 사슬을 나란히 세워 단계별로 관계를
증명한 뒤 극한에 올린다.

# 별칭이 정리를 깨뜨린다
%%%
tag := "ch02-aliasing"
file := "ch02-aliasing"
number := false
%%%

단사 가정이 장식이 아님을 확인한다. 임시 변수를 거쳐 두 변수를 맞바꾸는 프로그램을
놓고 본다.

```anchor swap (module := Reynolds.Answers.Ch02.Substitution)
/-- 임시 변수 `t` 를 거쳐 `x` 와 `y` 를 맞바꾼다. -/
def swap : Comm String := ⟪ t := x; x := y; y := t ⟫ᶜ

/--
**맞바꾸기는 맞바꾼다.** `while` 이 없으므로 `Comm.eval` 이 정의 등식만으로 끝까지
계산되고, 결과 상태에서 `x` 와 `y` 를 읽으면 된다.
-/
@[exercise "§2.5 swap" 1]
theorem swap_ok (σ : State String) :
    ∃ τ, swap.eval σ = some τ ∧ τ "x" = σ "y" ∧ τ "y" = σ "x" := by
  refine ⟨_, rfl, ?_, ?_⟩ <;> simp [IntExp.eval, State.subst_def, Function.update]
```

여기에 `t`와 `y`를 같은 변수로 보내는 이름 바꾸기를 걸면 맞바꾸기가 망가진다.

```anchor alias (module := Reynolds.Answers.Ch02.Substitution)
/-- `t ↦ y` — 임시 변수를 `y` 와 겹치게 만드는 이름 바꾸기. `t` 와 `y` 가 같은 곳으로
가므로 단사가 아니다. -/
def aliasTY : Ren String := fun w => if w = "t" then "y" else w

/--
별칭이 생긴 맞바꾸기 `y := x; x := y; y := y` 는 맞바꾸지 못한다 —
`t` 자리에 들어온 `y` 가 첫 대입에서 덮어써져, **두 변수 모두 옛 `x` 값**이 된다.
-/
theorem swap_aliased_eval (σ : State String) :
    ∃ τ, (swap /ᶜ aliasTY).eval σ = some τ ∧ τ "x" = σ "x" ∧ τ "y" = σ "x" := by
  refine ⟨_, rfl, ?_, ?_⟩ <;>
    simp [aliasTY, IntExp.eval, IntExp.subst, Ren.toSubst, State.subst_def, Function.update]

/--
**단사 가정을 빼면 명제 2.7 은 거짓이다.**

증인: `swap` 에 `aliasTY` 를 걸고, `δ` 를 사이에 둔 일치를 만족하는 입력쌍에서 돌린다.
원래 쪽은 `x` 가 옛 `y` 값 `1` 이 되고, 별칭 쪽은 `x` 가 옛 `x` 값 `0` 그대로다.
`AgreeVia` 가 두 값을 같다고 주장하는 순간 `1 = 0` 이 나온다.

읽기만 있는 1장에서는 두 이름이 한 값을 가리켜도 아무 일이 없었다. 대입이 생기는
순간 이름의 수가 곧 저장 공간의 수가 되고, 이름을 합치는 치환은 공간을 합쳐 버린다.
-/
theorem substitution_needs_injective :
    ¬ (∀ (c : Comm String) (δ : Ren String) (σ σ' : State String),
        (∀ w ∈ c.fv, σ w = σ' (δ w)) →
        AgreeVia δ c.fv (c.eval σ) ((c /ᶜ δ).eval σ')) := by
  intro hclaim
  -- σ' 는 x = 0, y = 1. σ 는 같은 값에 t 만 1 — `δ t = y` 이므로 `σ t = σ' y` 여야 한다.
  have h := hclaim swap aliasTY
    ((State.const 0)["y" := (1 : Int)]["t" := (1 : Int)])
    ((State.const 0)["y" := (1 : Int)])
    (by
      intro w hw
      have hcases : w = "t" ∨ w = "x" ∨ w = "y" := by
        simpa [swap, Comm.fv, IntExp.fv, or_comm, or_assoc, or_left_comm] using hw
      rcases hcases with rfl | rfl | rfl <;> simp [aliasTY, State.const])
  obtain ⟨τ, hτ, hτx, -⟩ := swap_ok ((State.const 0)["y" := (1 : Int)]["t" := (1 : Int)])
  obtain ⟨τ', hτ', hτ'x, -⟩ := swap_aliased_eval ((State.const 0)["y" := (1 : Int)])
  rw [hτ, hτ'] at h
  have hx := (AgreeVia.some_some.mp h) "x" (by simp [swap, Comm.fv, IntExp.fv])
  -- τ "x" = τ' (aliasTY "x") = τ' "x" 인데, 왼쪽은 1 이고 오른쪽은 0 이다.
  rw [hτx, show aliasTY "x" = "x" from rfl, hτ'x] at hx
  simp [State.const] at hx
```

읽기만 하는 1장에서는 두 이름이 한 값을 가리켜도 아무 일이 없었다. 대입이 생기는 순간
_이름의 수가 곧 저장 공간의 수_가 되고, 이름을 합치는 치환은 공간을 합쳐 버린다.

# 지역 변수의 이름은 뜻이 아니다
%%%
tag := "ch02-newvar-rename"
file := "ch02-newvar-rename"
number := false
%%%

명제 2.7의 첫 수확이다. `newvar`의 결합자를 신선한 이름으로 바꿔도 명령의 뜻이 그대로다
(`Comm.newvar_rename`). 1장 명제 1.5(이름 바꾸기 정리)의 명령 판이고, "결합 변수는
이름이 아니라 자리"라는 원칙이 명령형 언어에서도 성립한다는 확인이다.

이름 바꾸기 `v ↦ vnew`는 단사다. 신선함이 `vnew`를 본문의 다른 자유 변수와 갈라놓기
때문이다. 그래서 명제 2.7이 적용되고 별칭 걱정 없이 결론을 얻는다.
