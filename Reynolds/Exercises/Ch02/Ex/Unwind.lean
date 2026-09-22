/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Exercises.Ch02.Ex.Decr
-- `#guard`는 컴파일 시점에 계산한다 (AGENTS.md §10).
public meta import Reynolds.Exercises.Ch02.Interpreter
public meta import Reynolds.Answers.Ch02.Notation
public meta import Reynolds.Exercises.Ch02.Semantics
public meta import Reynolds.Prelude

/-!
# 연습 2.5 — 본체를 두 배로 늘려도 같다

Reynolds 연습 2.5 에 대응한다.

```
⟦while b do c⟧ = ⟦while b do (c; if b then c else skip)⟧
```

오른쪽은 한 바퀴에 본체를 **두 번** 돈다. 단, 두 번째는 조건이 아직 참일 때만이다 —
`if b then c else skip` 이 그 단서다. 그 단서가 없으면 거짓이다 (홀수 번 돌아야 하는
경우에 한 번 더 돌아 버린다).

## 왜 어려운가

양방향 `⊑` 인데 두 쪽의 성격이 전혀 다르다.

**쉬운 쪽 (`⊒`).** 늘린 반복의 뜻이 최소인데, 원래 반복의 뜻 `W` 가 늘린 반복의 풀기
방정식을 만족한다. `fix_least` 한 번으로 끝난다. 연습 2.2(c) 에서 한 것과 같은 모양이다.

**어려운 쪽 (`⊑`).** 같은 수를 쓰면 막힌다. `fix_least` 로 환원하면 "늘린 반복의 뜻이
한 바퀴 건너뛴 것보다 크지 않다" 를 보여야 하는데, 그것을 풀면 **증명하려던 것이 다시
나온다.** 순환이다.

## 순환을 끊는 법

근사열을 직접 따라간다. `W2 = ⨆ₙ Gⁿ(⊥)` 이므로, 각 근사 `Gⁿ(⊥)` 이 어떤 상계 아래에
있음을 `n` 에 대한 귀납으로 보이면 극한도 그 아래다.

상계로 쓸 함수를 하나 만든다.

```
U σ = if ⟦b⟧ᵇ σ then ⟦c⟧ σ >>= W2 else W2 σ
```

"조건이 참이면 본체를 **한 번만** 돌고 나머지는 늘린 반복에 맡긴다" 는 함수다.
`W2 ⊑ U` 를 보이면 어려운 쪽이 따라 나온다.

귀납이 돌아가는 이유는 보조 등식 하나다.

```
(if ⟦b⟧ᵇ σ then ⟦c⟧ σ else some σ) >>= U  =  W2 σ
```

늘린 본체를 한 번 훑은 뒤 `U` 로 가면 정확히 `W2` 다. 이것이 있으면 귀납 단계가
"귀납 가설 + `bind` 의 단조성" 으로 닫힌다.

**귀납 가설을 다른 상태에서 쓴다**는 것이 요점이다. `∀ σ` 로 묶어 두었기 때문에 가능하다 —
§2.5 의 명제 2.6 에서 진술을 일반화해야 했던 것과 같은 사정이다.

## 읽는 순서
`Ex/Decr.lean` 다음. §2.4 의 `fix_least` 와 `Chain.lub_le` 를 쓴다.
-/

-- 늘린 본체가 실제로 어떻게 도는지 `#guard` 로 본다.
set_option linter.hashCommand false

@[expose] public section

namespace Reynolds.Exercises.Ch02.Ex

open Reynolds Reynolds.Exercises.Ch01 Reynolds.Exercises.Ch02

universe u

variable {V : Type u} [DecidableEq V]

/-! ## 1. 두 배로 늘린 본체 -/

/--
`c; if b then c else skip` — 한 바퀴에 본체를 두 번 돈다.

두 번째 `c` 에 붙은 `if b then … else skip` 이 없으면 정리가 **거짓**이다. 홀수 번
돌아야 하는 경우에 한 번 더 돌아 버리기 때문이다. 아래 `#guard` 가 그 차이를 보여 준다.
-/
def dblBody (b : BoolExp V) (c : Comm V) : Comm V := .seq c (.ite b c .skip)

-- `while x > 0 do x := x-1` 은 3 에서 0 으로 간다.
#guard ((⟪ while x > 0 do x := x - 1 ⟫ᶜ).run 10 (State.const 3)).map (fun σ => σ "x")
  == some 0

-- 본체를 늘려도 같은 곳에 닿는다. 홀수(3)라서 마지막 바퀴는 `skip` 쪽으로 빠진다.
#guard ((Comm.wh (.cmp .gt (.var "x") (.num 0))
          (dblBody (.cmp .gt (.var "x") (.num 0))
            (.assign "x" (.bin .sub (.var "x") (.num 1))))).run 10
        (State.const 3)).map (fun σ => σ "x") == some 0

-- 단서를 뺀 `c; c` 라면 3 에서 -1 로 지나쳐 버린다. `if` 가 왜 필요한지가 여기 있다.
#guard ((Comm.wh (.cmp .gt (.var "x") (.num 0))
          (.seq (.assign "x" (.bin .sub (.var "x") (.num 1)))
                (.assign "x" (.bin .sub (.var "x") (.num 1))))).run 10
        (State.const 3)).map (fun σ => σ "x") == some (-1)

/-! ## 2. 두 반복이 같다 -/

/--
**연습 2.5 — 본체를 두 배로 늘려도 뜻이 같다.**

```
⟦while b do c⟧ = ⟦while b do (c; if b then c else skip)⟧
```

두 방향의 성격이 전혀 다르다.

- `⊒` (쉬운 쪽) — 원래 반복의 뜻 `W` 가 **늘린 반복의** 풀기 방정식을 만족한다.
  `fix_least` 한 번. 연습 2.2(c) 에서 한 것과 같다.
- `⊑` (어려운 쪽) — 같은 수가 안 통한다. `fix_least` 로 환원하면 증명하려던 것이 다시
  나와 순환에 빠진다.

어려운 쪽은 **근사열을 직접 따라간다.** 상계 `U` 를 세우고 `∀ n, Gⁿ(⊥) ⊑ U` 를 `n` 에
대해 귀납한 뒤 극한을 취한다. 귀납이 도는 이유는 보조 등식 `hD` 하나다 — 늘린 본체를
한 번 훑고 `U` 로 가면 정확히 `W2` 가 된다. 귀납 가설을 **다른 상태에서** 쓴다는 것이
요점이고, 진술을 `∀ σ` 로 묶어 둔 덕분에 가능하다.
-/
@[exercise "Ex 2.5" 3]
theorem while_eq_dblBody (b : BoolExp V) (c : Comm V) :
    (Comm.wh b c).eval = (Comm.wh b (dblBody b c)).eval := by
  -- 이 장에서 가장 어려운 연습이다. 두 방향의 성격이 전혀 다르다.
  -- 먼저 볼 것: 연습 2.2(c) (`repeatEval_eq_repeatSugar`) — 쉬운 쪽이 그것과 같은 모양이다.
  --
  -- 준비: `set s := c.eval`, `set W := (Comm.wh b c).eval`,
  --       `set W2 := (Comm.wh b (dblBody b c)).eval` 로 이름을 줄이고,
  --       두 반복의 한 바퀴 방정식을 `Comm.eval_isSemantics.2.2.2.2.1 _ _ σ` 로 꺼낸다.
  --       늘린 본체의 뒷부분 `h σ' = if ⟦b⟧ᵇ σ' then s σ' else some σ'` 도 이름을 준다
  --       (`(dblBody b c).eval σ = Option.bind (s σ) h` 는 `rfl` 이다).
  --
  -- 힌트 1 (`⊒`, 쉬운 쪽): `W` 가 **늘린** 반복의 풀기 방정식을 만족함을 보이면
  --         `fix_least` 가 끝낸다. `Option.bind_assoc` 로 두 번 훑는 것을 펴고,
  --         조건이 참인 갈래에서 `hW` 를 한 번 더 쓴다.
  --
  -- 힌트 2 (`⊑`, 어려운 쪽): 같은 수를 쓰면 **순환에 빠진다.** `fix_least` 로 환원하면
  --         증명하려던 것이 다시 나온다. 근사열을 직접 따라가야 한다.
  -- 힌트 3: 상계를 하나 만든다.
  --           `U σ = if ⟦b⟧ᵇ σ then Option.bind (s σ) W2 else W2 σ`
  --         "조건이 참이면 본체를 한 번만 돌고 나머지는 `W2` 에 맡긴다" 는 함수다.
  -- 힌트 4: 보조 등식 둘을 먼저 세운다.
  --           (C) `Option.bind ((dblBody b c).eval σ) W2 = Option.bind (s σ) U`
  --           (D) `Option.bind (h σ) U = W2 σ`
  --         둘 다 조건으로 갈래를 나누는 계산이고, (D) 가 귀납을 굴리는 연료다.
  -- 힌트 5: `∀ n, (whileF b ((dblBody b c).eval))^[n] ⊥ ≤ U` 를 `n` 에 대해 귀납한다.
  --         `Function.iterate_succ_apply'` 로 한 겹 벗기고, 귀납 가설을
  --         `Option.bind_le_bind` 로 밀어 넣은 뒤 (D) 로 닫는다.
  --         **귀납 가설을 다른 상태에서 쓴다**는 것이 요점이다.
  -- 힌트 6: 극한은 `Chain.lub_le` 로 올린다. 그러면 `W2 ≤ U` 이고,
  --         거기서 `W2` 가 원래 반복의 전고정점임이 나와 `fix_least` 가 끝낸다.
  sorry


/-! ## 3. 여기서 어디로 가나

`while` 자체에 대한 두 어려운 연습(2.3 과 2.5)이 끝났다. 2.3 은 구체적인 반복 하나의
값을 끝까지 계산했고, 2.5 는 반복 **일반**에 대한 등식을 최소성과 근사열로 얻었다.

다음은 자유 변수와 별칭 쪽이다 — 연습 2.6(순서 교환의 조건), 2.7(별칭에 안전한 계승
프로그램), 2.8(명제 2.7 의 조건 약화). §2.5 에서 만든 `FV`·`FA` 와 치환이 재료다. -/

end Reynolds.Exercises.Ch02.Ex
