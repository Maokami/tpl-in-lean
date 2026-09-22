/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Answers.Ch02.Ex.ForRange

/-!
# 연습 2.10 — `dotwice` 의 디슈가링은 왜 유효한가

Reynolds 연습 2.10 에 대응한다. 앞의 연습들과 결이 전혀 다르다 — 명령 하나의 뜻이
아니라 **디슈가링 함수 자체가 잘 정의되는가** 를 묻는 메타 수준의 물음이다.

## 물음

`dotwice c` 를 "c 를 두 번 한다" 로 두고 이렇게 번역한다.

```
dotwice c   ⟹   c; c
```

Reynolds 의 지적: `c` 안에 `dotwice` 가 또 있으면 번역이 그것들을 **복제한다.**
`dotwice` 의 개수가 줄기는커녕 늘 수 있다. 그런데도 이 정의가 유효한가?

## Lean 에서는 종료 증명이 곧 답이다

답은 "무엇에 대해 재귀하는가" 다. 번역은 `dotwice` 의 개수가 아니라 **구문 나무**에
대해 재귀한다.

```
desugar (dotwice s) = seq (desugar s) (desugar s)
```

오른쪽의 `desugar` 는 둘 다 `s` — 원래 항의 **진부분항**이다. 복제는 **결과**에서
일어나지 출력이 다시 입력으로 들어가지 않는다. 그래서 구조적 재귀이고, Lean 은
`termination_by` 없이 그대로 받아 준다. **정의가 통과한다는 사실 자체가 답이다.**

바깥에서부터 고쳐 쓰는 방식이었다면 이야기가 달랐다. `dotwice` 개수는 실제로 늘 수
있어서(`dotwice_count_can_grow`) 측도가 되지 못한다.

## 그리고 번역이 뜻을 지킨다

잘 정의되는 것과 옳은 것은 다르다. `dotwice` 에 직접 뜻을 주고, 번역이 그 뜻을
보존함을 증명한다 — §2.6 에서 `for` 에 대해 한 것과 같은 일이다.

## 읽는 순서
`Ex/ForRange.lean` 다음. 2장 연습의 마지막이다.
-/

-- `#guard` 로 복제가 실제로 일어나는 것을 본다.
set_option linter.hashCommand false

@[expose] public section

namespace Reynolds.Answers.Ch02.Ex

open Reynolds Reynolds.Answers.Ch01 Reynolds.Answers.Ch02

universe u

variable {V : Type u} [DecidableEq V]

/-! ## 1. `dotwice` 가 있는 구문 -/

-- ANCHOR: SComm
/-- 2장의 명령에 `dotwice` 를 더한 구문. -/
inductive SComm (V : Type u) where
  /-- 대입. -/
  | assign : V → IntExp V → SComm V
  /-- 아무것도 하지 않는다. -/
  | skip
  /-- 순차 합성. -/
  | seq : SComm V → SComm V → SComm V
  /-- 조건. -/
  | ite : BoolExp V → SComm V → SComm V → SComm V
  /-- 반복. -/
  | wh : BoolExp V → SComm V → SComm V
  /-- 변수 선언. -/
  | newvar : V → IntExp V → SComm V → SComm V
  /-- **두 번 한다.** 이 절의 새 구문. -/
  | dotwice : SComm V → SComm V

/--
디슈가링. `dotwice s` 를 `desugar s; desugar s` 로 옮긴다.

**이 정의가 통과한다는 사실이 연습 2.10 의 답이다.** 재귀 호출이 둘 다 진부분항 `s` 에
일어나므로 구조적 재귀이고, Lean 이 `termination_by` 없이 받아 준다. 복제는 결과에서
일어나지 출력이 다시 입력으로 들어가지 않는다.
-/
def SComm.desugar : SComm V → Comm V
  | .assign v e   => .assign v e
  | .skip         => .skip
  | .seq s₀ s₁    => .seq s₀.desugar s₁.desugar
  | .ite b s₀ s₁  => .ite b s₀.desugar s₁.desugar
  | .wh b s       => .wh b s.desugar
  | .newvar v e s => .newvar v e s.desugar
  | .dotwice s    => .seq s.desugar s.desugar
-- ANCHOR_END: SComm

/-! ## 2. 개수는 측도가 되지 못한다

바깥에서부터 `dotwice c → c; c` 로 고쳐 쓴다면 무엇이 줄어드는가? `dotwice` 의 개수는
아니다 — 한 번 고쳐 쓰면 늘어날 수 있다. -/

-- ANCHOR: count
/-- 구문 나무에 든 `dotwice` 의 개수. -/
def SComm.dotwiceCount : SComm V → Nat
  | .assign _ _   => 0
  | .skip         => 0
  | .seq s₀ s₁    => s₀.dotwiceCount + s₁.dotwiceCount
  | .ite _ s₀ s₁  => s₀.dotwiceCount + s₁.dotwiceCount
  | .wh _ s       => s.dotwiceCount
  | .newvar _ _ s => s.dotwiceCount
  | .dotwice s    => s.dotwiceCount + 1

/-- 세 겹으로 쌓은 `dotwice`. -/
def tower : SComm String := .dotwice (.dotwice (.dotwice .skip))

/--
**`dotwice` 개수는 줄지 않는다.** 바깥 한 겹을 고쳐 쓰면 3 개가 4 개가 된다.

`dotwice t` 를 `t; t` 로 바꾸면 `t` 안의 `dotwice` 들이 통째로 복제된다. 그래서 이 수는
바깥에서부터 고쳐 쓰는 방식의 측도가 되지 못한다.

**구조적 재귀는 이 문제를 겪지 않는다.** 재귀가 입력 나무를 따라 내려가고, 복제는
출력에서만 일어나기 때문이다 — `SComm.desugar` 가 `termination_by` 없이 통과하는 것이
그 증거다.
-/
theorem dotwiceCount_can_grow :
    (SComm.seq (.dotwice (.dotwice .skip)) (.dotwice (.dotwice .skip)) : SComm String).dotwiceCount
      > tower.dotwiceCount := by
  decide
-- ANCHOR_END: count

-- 복제가 실제로 일어난다. 두 겹이면 `skip` 이 네 개로 퍼진다.
#guard (SComm.dotwice (.dotwice .skip) : SComm String).desugar
  == Comm.seq (.seq .skip .skip) (.seq .skip .skip)

/-! ## 3. 번역이 뜻을 지킨다

잘 정의되는 것과 옳은 것은 다르다. `dotwice` 에 직접 뜻을 주고 번역이 그것을 보존함을
확인한다. -/

-- ANCHOR: desugarEval
/--
`dotwice` 가 있는 구문의 뜻. `dotwice s` 만 새로운데, "한 번 돌고 또 한 번 돈다" 이므로
`bind` 두 번이다.
-/
noncomputable def SComm.eval : SComm V → State V → SigmaBot V
  | .assign v e   => fun σ => some (σ[v := ⟦e⟧ₑ σ])
  | .skip         => fun σ => some σ
  | .seq s₀ s₁    => fun σ => Option.bind (s₀.eval σ) s₁.eval
  | .ite b s₀ s₁  => fun σ => if ⟦b⟧ᵇ σ then s₀.eval σ else s₁.eval σ
  | .wh b s       => fix (whileF b s.eval) (whileF_monotone b s.eval)
  | .newvar v e s => fun σ => restore v σ (s.eval (σ[v := ⟦e⟧ₑ σ]))
  | .dotwice s    => fun σ => Option.bind (s.eval σ) s.eval

/--
**연습 2.10 — 디슈가링이 뜻을 지킨다.**

```
⟦desugar s⟧ = ⟦s⟧
```

구문에 대한 구조적 귀납이고, 절마다 그 생성자의 의미 방정식을 한 번 쓰는 계산이다.
`wh` 절만 `fix` 를 지나므로 본체의 뜻을 바꿔 끼우는 데 한 걸음이 더 든다 — §2.8 의
합성성(`Ctx.fill_congr`)에서 본 것과 같은 자리다.

`dotwice` 절이 이 연습의 요점이다. 번역이 만든 `desugar s; desugar s` 의 뜻이
`⟦s⟧ 한 번, 또 한 번` 과 같다는 것을, **하나의 귀납 가설을 두 번 써서** 얻는다 —
복제된 두 자리가 같은 부분항에서 왔기 때문이다.
-/
@[exercise "Ex 2.10" 2]
theorem SComm.desugar_eval : ∀ s : SComm V, s.desugar.eval = s.eval := by
  intro s
  induction s with
  | assign v e => rfl
  | «skip» => rfl
  | seq s₀ s₁ ih₀ ih₁ =>
      funext σ
      change Option.bind (s₀.desugar.eval σ) s₁.desugar.eval
          = Option.bind (s₀.eval σ) s₁.eval
      rw [ih₀, ih₁]
  | ite b s₀ s₁ ih₀ ih₁ =>
      funext σ
      change (if ⟦b⟧ᵇ σ then s₀.desugar.eval σ else s₁.desugar.eval σ)
          = (if ⟦b⟧ᵇ σ then s₀.eval σ else s₁.eval σ)
      rw [ih₀, ih₁]
  | wh b s ih =>
      change fix (whileF b s.desugar.eval) (whileF_monotone b s.desugar.eval)
          = fix (whileF b s.eval) (whileF_monotone b s.eval)
      rw [ih]
  | «newvar» v e s ih =>
      funext σ
      change restore v σ (s.desugar.eval (σ[v := ⟦e⟧ₑ σ]))
          = restore v σ (s.eval (σ[v := ⟦e⟧ₑ σ]))
      rw [ih]
  | dotwice s ih =>
      -- 복제된 두 자리가 같은 부분항에서 왔으므로 귀납 가설 하나를 두 번 쓴다.
      funext σ
      change Option.bind (s.desugar.eval σ) s.desugar.eval
          = Option.bind (s.eval σ) s.eval
      rw [ih]
-- ANCHOR_END: desugarEval

/-! ## 4. 2장 연습을 닫으며

열 문제를 다 옮겼다. 되돌아보면 `while` 하나가 장 전체를 끌고 갔다.

- 새 명령에 뜻을 주는 두 길과 그 둘이 같음 (2.1 · 2.2)
- 구체적인 반복의 닫힌 꼴과 반복 일반에 대한 등식 (2.3 · 2.5)
- 자유 변수가 언제 순서를 바꾸게 해 주는가, 별칭을 무엇이 막는가, 조건을 얼마나 약하게
  할 수 있는가 (2.6 · 2.7 · 2.8)
- 구문 설탕의 설계와 그 번역이 잘 정의되는 이유 (2.9 · 2.10)

그리고 2.4(연속성)는 §2.4 본문에 이미 들어 있었다 — 의미 정의의 전제였기 때문이다. -/

end Reynolds.Answers.Ch02.Ex
