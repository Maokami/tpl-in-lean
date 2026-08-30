#!/usr/bin/env python3
"""Answers 트리에서 Exercises 트리를 생성한다.

Answers 가 진리의 원천이고, Exercises 는 여기서 기계적으로 만든다.
손으로 두 트리를 맞추면 반드시 어긋나므로 생성기를 둔다.

하는 일은 셋이다.

1. 이름공간을 `Reynolds.Answers.Ch01` → `Reynolds.Exercises.Ch01` 로 바꾼다
2. `-- ANCHOR` 마커를 제거한다 (문서는 Answers 만 인용한다. AGENTS.md §3.1)
3. `BLANKS` 표에 적힌 증명을 `sorry` 와 힌트로 교체한다

## 어떤 정리를 비울지 고르는 규칙

`AGENTS.md` §1-9 의 **연습 독립성 원칙**: 비우는 정리들은 서로 의존하면 안 된다.
Lean 은 다른 모듈의 증명 항을 볼 수 없어서 "본인 sorry" 와 "선행 미완성" 을 구분할 수
없기 때문이다. 그래서 비우는 집합은 의존 순서에서 반사슬(antichain)이어야 한다.

예를 들어 `substitution_assert` 를 비우면 그것을 쓰는 `renaming_assert` 는 비우지 않는다.
`renaming_assert` 는 Exercises 에서도 완성된 채로 두고, 채점 대상에서 뺀다.

사용법:

    python3 scripts/gen-exercises.py          # 생성
    python3 scripts/gen-exercises.py --check  # Answers 와 어긋나면 실패 (CI용)
"""

from __future__ import annotations

import pathlib
import sys

# Exercises 로 복제하지 않고 Answers 쪽을 그대로 쓰는 모듈.
#
# `Notation.lean` 은 `declare_syntax_cat` 으로 **전역** 구문 범주를 만든다.
# 두 트리에 같은 범주가 생기면 루트 모듈에서 충돌한다:
#   environment already contains 'Lean.Parser.Category.reyA'
# 게다가 DSL 은 연습 대상이 아니라 인프라라서 복제할 이유도 없다.
# 매크로가 뱉는 이름(`IntExp.var` 등)은 한정되지 않아서, Exercises 이름공간 안에서
# 쓰면 Exercises 의 정의로 해석된다.
# `Ch02/Domain/Flat.lean` — `Option` 은 루트 타입이라 순서 인스턴스를 복제하면
# 같은 타입에 두 벌이 등록된다 (구문 범주가 전역인 것과 같은 사정).
SHARED = {"Ch01/Notation.lean", "Ch02/Notation.lean", "Ch02/Domain/Flat.lean"}

ROOT = pathlib.Path(__file__).resolve().parent.parent
ANSWERS = ROOT / "Reynolds" / "Answers"
EXERCISES = ROOT / "Reynolds" / "Exercises"

# (파일, 증명 시작 마커, 다음 선언 마커, 교체할 스텁)
#
# 시작 마커부터 다음 마커 직전까지를 스텁으로 갈아 끼운다.
# 마커는 파일 안에서 유일해야 한다.
BLANKS: list[tuple[str, str, str, str]] = [
    # ── §1.4 자유 변수와 일치 정리
    (
        "Ch01/FreeVars.lean",
        "theorem coincidence_intExp :",
        "/-! ## 단언의 자유 변수",
        """theorem coincidence_intExp :
    ∀ (e : IntExp V) (σ σ' : State V), (∀ w ∈ e.fv, σ w = σ' w) → ⟦e⟧ₑ σ = ⟦e⟧ₑ σ' := by
  -- 힌트: `intro e` 다음 `induction e with` 로 케이스를 나눈다.
  -- `bin` 케이스에서 `Finset` 합집합 소속을 어떻게 쪼갤지 생각해 볼 것.
  sorry

""",
    ),
    (
        "Ch01/FreeVars.lean",
        "theorem coincidence_assert :",
        "end Reynolds.Exercises.Ch01",
        """theorem coincidence_assert :
    ∀ (p : Assert V) (σ σ' : State V), (∀ w ∈ p.fv, σ w = σ' w) → (⟦p⟧ₐ σ ↔ ⟦p⟧ₐ σ') := by
  -- 먼저 볼 것: 바로 위 `coincidence_intExp` 의 완성 증명. 같은 모양이고 케이스만 늘어난다.
  -- 힌트 1: 진술이 `∀ (p) (σ σ')` 꼴인 것이 증명을 좌우한다.
  --         `σ σ'` 를 인자로 빼면 양화사 케이스에서 귀납 가설이 안 맞는다.
  -- 힌트 2: `quant` 케이스에서 귀납 가설을 `σ[v := n]`, `σ'[v := n]` 에 적용한다.
  -- 힌트 3: `State.subst_self` / `State.subst_of_ne` 가 `simp` 로 자동 적용된다.
  --         마무리는 `forall_congr'` 와 `exists_congr`.
  sorry

""",
    ),
    # ── §1.3 타당성과 추론
    (
        "Ch01/Validity.lean",
        "theorem Proof.sound {p : Assert V}",
        "/-! ## 4. 추론과 함의",
        """theorem Proof.sound {p : Assert V} : Proof p → Valid p := by
  -- 먼저 볼 것: `Proof` 의 정의. 생성자 하나가 규칙 하나이고, 케이스도 하나씩 대응한다.
  -- 힌트: `genAll` 케이스에서 "전제가 타당하다" 가 무엇을 주는지 보면 §4 의 논점이 보인다.
  sorry

""",
    ),
    (
        "Ch01/Validity.lean",
        "theorem valid_forall_of_valid (v : V)",
        "/--\n함의 쪽.",
        """theorem valid_forall_of_valid (v : V) {p : Assert V} (h : Valid p) :
    Valid (.quant .all v p) := by
  sorry

""",
    ),
    (
        "Ch01/Validity.lean",
        "theorem not_valid_imp_forall :",
        "/-! ## 5. 이 책이 다루지 않는 것",
        """theorem not_valid_imp_forall :
    ¬ Valid (.bin .imp (.cmp .gt (.var "x") (.num 0))
                       (.quant .all "x" (.cmp .gt (.var "x") (.num 0))) : Assert String) := by
  -- 힌트: 반례를 잡는다. `x ↦ 3` 인 상태에서 왼쪽은 참이고, 오른쪽은 0 을 넣으면 거짓이다.
  sorry

""",
    ),
    # ── §1.4 치환
    #
    # 비우는 넷은 서로 의존하지 않는다.
    #   1.2a, 1.2c            — 다른 정리를 쓰지 않는다
    #   1.2b-assert           — `subst_var_intExp`(완성본으로 제공)만 쓴다
    #   1.3-assert            — `substitution_intExp`, `coincidence_intExp`(제공)만 쓴다
    # `substitution_single` · `renaming_assert` · `valid_instAll` 은 1.3-assert 를 쓰므로
    # 완성된 채로 두고 채점 대상에서 뺐다.
    (
        "Ch01/Substitution.lean",
        "theorem subst_congr_intExp :",
        "omit [DecidableEq V] in",
        """theorem subst_congr_intExp :
    ∀ (e : IntExp V) (δ δ' : Subst V), (∀ w ∈ e.fv, δ w = δ' w) → e /ₑ δ = e /ₑ δ' := by
  -- 힌트: `coincidence_intExp` 과 모양이 같다. 상태 대신 치환 사상이 들어갔을 뿐이다.
  sorry

""",
    ),
    (
        "Ch01/Substitution.lean",
        "theorem fv_subst_intExp",
        "-- ANCHOR_END: prop12",
        """theorem fv_subst_intExp (e : IntExp V) (δ : Subst V) :
    (e /ₑ δ).fv = e.fv.biUnion fun w => (δ w).fv := by
  -- 힌트: `bin` 케이스에서 `∃` 가 `∨` 위로 분배되는 것을 손으로 보여야 한다.
  -- `ext w` 다음 `simp only [Finset.mem_union, Finset.mem_biUnion]` 로 시작해 볼 것.
  sorry

""",
    ),
    (
        "Ch01/Substitution.lean",
        "theorem subst_var_assert [HasFresh V]",
        "/-! ## 5. 명제 1.3",
        """theorem subst_var_assert [HasFresh V] (p : Assert V) : p /ₛ IntExp.var = p := by
  -- 먼저 볼 것: `subst_var_intExp` (완성본). 양화사 케이스만 새로 생각하면 된다.
  -- 힌트: 양화사 케이스가 전부다. 항등 치환에서는 `captureSet` 이 `p.fv.erase v` 로 줄고,
  -- `v` 는 거기 없으므로 `newBinder` 가 `v` 를 그대로 돌려준다.
  sorry

""",
    ),
    (
        "Ch01/Substitution.lean",
        "theorem substitution_assert [HasFresh V] :",
        "-- ANCHOR_END: substThm",
        """theorem substitution_assert [HasFresh V] :
    ∀ (p : Assert V) (δ : Subst V) (σ σ' : State V),
      (∀ w ∈ p.fv, σ w = ⟦δ w⟧ₑ σ') → (⟦p /ₛ δ⟧ₐ σ' ↔ ⟦p⟧ₐ σ) := by
  -- 먼저 볼 것: `substitution_intExp` (완성본) 과 `coincidence_assert` 의 양화사 케이스.
  -- 이 증명은 그 둘을 합친 모양이다.
  --
  -- 이 파일에서 가장 손이 많이 가는 증명이다. 양화사 케이스의 순서는 이렇다.
  --   1. `set vnew := newBinder p v δ`
  --   2. `∀ n` 아래에서 귀납 가설을 `σ[v := n]`, `σ'[vnew := n]`,
  --      `Function.update δ v (.var vnew)` 에 적용한다
  --   3. 그 전제를 확인할 때 `w = v` 와 `w ≠ v` 로 나눈다
  --   4. `w ≠ v` 쪽에서 `newBinder_notMem_fv` 와 `coincidence_intExp` 가 필요하다
  --   5. 마무리는 `forall_congr'` / `exists_congr`
  sorry

""",
    ),
    # ── 심화 A · 대수와 초기성
    (
        "Ch01/Depth/Algebra.lean",
        "theorem IntExp.initial {V : Type u}",
        "/-! ## 6. `eval` 과 `fv` 는 접기다",
        """theorem IntExp.initial {V : Type u} (A : IntExpAlg.{u, v} V) :
    ∃! h : IntExp V → A.Carrier, IsHom A h := by
  -- 먼저 볼 것: 바로 위 `IntExpAlg.fold_isHom`. 존재 쪽은 그것으로 끝난다.
  -- 힌트: 존재는 `A.fold` 이고 `A.fold_isHom` 이 이미 있다.
  -- 유일성은 `funext` 다음 `induction e with`.
  sorry

""",
    ),
    (
        "Ch01/Depth/Algebra.lean",
        "theorem eval_eq_fold {V : Type u}",
        "/-- `FV` 는 자유 변수 대수로의 접기다. -/",
        """theorem eval_eq_fold {V : Type u} (e : IntExp V) : ⟦e⟧ₑ = (evalAlg V).fold e := by
  -- 힌트: `e` 에 대한 구조적 귀납법. 각 케이스는 양쪽 정의를 펼치면 같아진다.
  sorry

""",
    ),
    # ── 심화 B · 시그니처 함자
    (
        "Ch01/Depth/SignatureFunctor.lean",
        "def IntExp.lambek (V : Type u)",
        "/-- `roll` 이 대수 연산임을 확인",
        """def IntExp.lambek (V : Type u) : IntExp V ≃ Sig V (IntExp V) where
  toFun := IntExp.unroll
  invFun := IntExp.roll
  left_inv e := by sorry
  right_inv s := by sorry

""",
    ),
    # ── 심화 A · 항 모나드
    (
        "Ch01/Depth/TermMonad.lean",
        "theorem subst_assoc_intExp (e : IntExp V)",
        "-- ANCHOR_END: monadLaws",
        """theorem subst_assoc_intExp (e : IntExp V) (δ δ' : Subst V) :
    (e /ₑ δ) /ₑ δ' = e /ₑ (fun w => (δ w) /ₑ δ') := by
  -- 힌트: `e` 에 대한 구조적 귀납법. `var` 케이스가 `rfl` 인 것이 좌단위 법칙이다.
  sorry

""",
    ),
# ── 연습 1.1 · 1.2 (전부 서로 독립이다)
    (
        "Ch01/Ex.lean", "theorem e11a_correct", "/-- 1.1(b)",
        """theorem e11a_correct (σ : State String) :
    (⟦e11a⟧ₐ σ ↔ ∃ n : Int, 0 < n ∧ n < 2) := by
  -- 힌트: `simp [e11a, Assert.eval, LogOp.denote, Cmp.denote, IntExp.eval]`
  sorry

""",
    ),
    (
        "Ch01/Ex.lean", "theorem e11b_correct", "/-- 1.1(c)",
        """theorem e11b_correct (σ : State String) :
    (⟦e11b⟧ₐ σ ↔ ∀ m n : Int, (0 < m ∧ m < 2) ∧ (0 < n ∧ n < 2) → m = n) := by
  sorry

""",
    ),
    (
        "Ch01/Ex.lean", "theorem e11c_correct", "/--\n1.1(d)",
        """theorem e11c_correct (σ : State String) :
    (⟦e11c⟧ₐ σ ↔ ∃ m n : Int, m ≠ n ∧ (0 < m ∧ m < 3) ∧ (0 < n ∧ n < 3)) := by
  sorry

""",
    ),
    (
        "Ch01/Ex.lean", "theorem e11d_correct", "/-! ## 연습 1.2",
        """theorem e11d_correct (σ : State String) :
    (⟦e11d⟧ₐ σ ↔ ∀ l m n : Int,
      (0 < l ∧ l < 3) ∧ (0 < m ∧ m < 3) ∧ (0 < n ∧ n < 3) →
        (l = m ∨ l = n ∨ m = n)) := by
  sorry

""",
    ),
    (
        "Ch01/Ex.lean", "theorem e12a_correct", "/-- 1.2(b)",
        """theorem e12a_correct (σ : State String) :
    (⟦e12a⟧ₐ σ ↔ σ "a" ∣ σ "b") := by
  -- 힌트: `dvd_def` 가 `a ∣ b ↔ ∃ c, b = a * c` 다. `IntOp.denote` 도 펼쳐야 한다.
  sorry

""",
    ),
    (
        "Ch01/Ex.lean", "theorem e12b_correct", "/--\n1.2(c)",
        """theorem e12b_correct (σ : State String) :
    (⟦e12b⟧ₐ σ ↔ (σ "a" ∣ σ "b" ∧ σ "a" ∣ σ "c")) := by
  sorry

""",
    ),
    (
        "Ch01/Ex.lean", "theorem e12c_correct", "/--\n1.2(d)",
        """theorem e12c_correct (σ : State String) :
    (⟦e12c⟧ₐ σ ↔
      ((σ "a" ∣ σ "b" ∧ σ "a" ∣ σ "c")
        ∧ ∀ d : Int, (d ∣ σ "b" ∧ d ∣ σ "c") → d ≤ σ "a")) := by
  sorry

""",
    ),
    (
        "Ch01/Ex.lean", "theorem e12d_correct", "/-! ## 연습 1.4",
        """theorem e12d_correct (σ : State String) :
    (⟦e12d⟧ₐ σ ↔
      (σ "p" > 1 ∧ ∀ d : Int, (d > 0 ∧ d ∣ σ "p") → (d = 1 ∨ d = σ "p"))) := by
  sorry

""",
    ),
    # ── 연습 1.3 (접두사 자유성은 완성본으로 주고 단사성만 비운다)
    (
        "Ch01/Realizations.lean", "theorem IntExp.toPrefix_injective",
        "/-! ## 접두 표기의 구문 세계",
        """theorem IntExp.toPrefix_injective : Function.Injective IntExp.toPrefix := by
  -- 먼저 볼 것: 바로 위 `toPrefix_prefixFree` (완성본).
  -- 힌트: 꼬리를 빈 열로 넣고 `simpa` 로 `++ []` 를 정리하면 된다.
  sorry

""",
    ),
    # ── 연습 1.5 · 1.6 합 식
    (
        "Ch01/Ex/Summation.lean",
        "theorem coincidence_sExp",
        "-- ANCHOR_END: coincidenceSExp",
        """theorem coincidence_sExp :
    ∀ (e : SExp V) (σ σ' : State V), (∀ w ∈ e.fv, σ w = σ' w) → ⟦e⟧ₛ σ = ⟦e⟧ₛ σ' := by
  -- 먼저 볼 것: `FreeVars.lean` 의 `coincidence_intExp`. 앞 네 케이스는 글자까지 같다.
  -- 힌트 1: `sum` 케이스에서 `e₀`, `e₁` 은 `σ`, `σ'` 에서 그대로 잰다.
  --         자유 변수가 통째로 `FV(Σ…)` 안에 있으므로 가설을 바로 쓴다.
  -- 힌트 2: 본체는 `Finset.sum_congr rfl` 로 항마다 나눈 뒤 `ih₂` 를 쓴다.
  -- 힌트 3: `w = v` 인지로 나눈다. 같으면 `State.subst_self`, 다르면 `State.subst_of_ne`.
  sorry

""",
    ),
    (
        "Ch01/Ex/Summation.lean",
        "theorem sum_empty",
        "/--\n**한 항 규칙.**",
        """theorem sum_empty (h : ⟦e₁⟧ₛ σ < ⟦e₀⟧ₛ σ) :
    ⟦SExp.sum v e₀ e₁ e₂⟧ₛ σ = 0 := by
  -- 힌트: `Finset.Icc_eq_empty` 가 `¬ a ≤ b → Finset.Icc a b = ∅` 다.
  sorry

""",
    ),
    (
        "Ch01/Ex/Summation.lean",
        "theorem sum_single",
        "/--\n**분리 규칙.**",
        """theorem sum_single (h : ⟦e₀⟧ₛ σ = ⟦e₁⟧ₛ σ) :
    ⟦SExp.sum v e₀ e₁ e₂⟧ₛ σ = ⟦e₂⟧ₛ (σ[v := ⟦e₀⟧ₛ σ]) := by
  -- 힌트: `h` 로 위끝을 아래끝으로 바꾸면 `Finset.Icc_self` 가 붙는다.
  sorry

""",
    ),
    (
        "Ch01/Ex/Summation.lean",
        "theorem sum_split",
        "/--\n**선형성.**",
        """theorem sum_split (h : ⟦e₀⟧ₛ σ ≤ ⟦e₁⟧ₛ σ + 1) :
    ⟦SExp.sum v e₀ (.bin .add e₁ (.num 1)) e₂⟧ₛ σ
      = ⟦SExp.sum v e₀ e₁ e₂⟧ₛ σ + ⟦e₂⟧ₛ (σ[v := ⟦e₁⟧ₛ σ + 1]) := by
  -- 힌트 1: `Finset.Icc a (b+1) = insert (b+1) (Finset.Icc a b)` 을 먼저 `have` 로 세운다.
  --         `ext k` 뒤 `Finset.mem_Icc`, `Finset.mem_insert` 로 풀면 `omega` 가 닫는다.
  -- 힌트 2: 그다음은 `Finset.sum_insert`. 그 가설도 `omega` 로 닫힌다.
  sorry

""",
    ),
    (
        "Ch01/Ex/Summation.lean",
        "theorem sum_add",
        "-- ANCHOR_END: sumRules",
        """theorem sum_add (e e' : SExp V) :
    ⟦SExp.sum v e₀ e₁ (.bin .add e e')⟧ₛ σ
      = ⟦SExp.sum v e₀ e₁ e⟧ₛ σ + ⟦SExp.sum v e₀ e₁ e'⟧ₛ σ := by
  -- 힌트: 정의를 편 뒤 `Finset.sum_add_distrib` 하나면 된다.
  sorry

""",
    ),
    (
        "Ch01/Ex/Summation.lean",
        "theorem isum_renaming_fails",
        "/-! ## 어려움 2",
        """theorem isum_renaming_fails :
    ∃ σ : State String,
      ⟦(ISExp.isum "i" (.num 1) : ISExp String)⟧ᵢ σ
        ≠ ⟦(ISExp.isum "j" (.num 1) : ISExp String)⟧ᵢ σ := by
  -- 힌트: `σ i = 1`, `σ j = 0` 인 상태를 `refine ⟨fun w => …, ?_⟩` 로 제시한다.
  --       그다음은 `simp [ISExp.eval]` 이 계산해 준다.
  sorry

""",
    ),
    # ── §2.2 표시적 의미론
    (
        "Ch02/Semantics.lean",
        "theorem boolExp_eval_iff",
        "-- ANCHOR_END: boolAgree",
        """theorem boolExp_eval_iff {V : Type u} [DecidableEq V] (b : BoolExp V) (σ : State V) :
    ⟦b.toAssert⟧ₐ σ ↔ ⟦b⟧ᵇ σ = true := by
  -- 먼저 볼 것: `Cmp.denoteBool_iff` 와 `LogOp.denoteBool_iff`. 둘 다 이 파일 앞쪽에 있다.
  -- 힌트 1: `b` 에 대한 구조적 귀납법. 양화사 절이 없으므로 다섯 가지다.
  -- 힌트 2: `bin` 절에서 귀납 가설의 방향이 보조정리와 반대다. `.symm` 이 필요하다.
  sorry

""",
    ),
    (
        "Ch02/Semantics.lean",
        "theorem liftBot_eq_bind",
        "/-- `Option.bind` 가 곧 `>>=` 다.",
        """theorem liftBot_eq_bind {V : Type u} (f : State V → SigmaBot V) (x : SigmaBot V) :
    liftBot f x = Option.bind x f := by
  -- 힌트: `x` 를 두 가지로 나누면 양변이 정의상 같아진다.
  sorry

""",
    ),
    (
        "Ch02/Semantics.lean",
        "theorem unwinding_not_unique",
        "-- ANCHOR_END: unwindingNotUnique",
        """theorem unwinding_not_unique :
    ∃ f g : State String → SigmaBot String, UnwindsDecr f ∧ UnwindsDecr g ∧ f ≠ g := by
  -- 먼저 볼 것: 바로 위의 `unwindsDecr_true` 와 `unwindsDecr_fake`. 둘 다 완성되어 있다.
  -- 힌트 1: 두 해를 그대로 제시하고, 다른 값을 내는 상태를 하나 짚으면 된다.
  -- 힌트 2: `x` 가 1 인 상태가 그러하다. 홀수라 반복이 끝나지 않는다.
  -- 힌트 3: `f ≠ g` 는 `intro h` 로 받아 `congrFun h σ` 로 한 점으로 줄인다.
  sorry

""",
    ),
    (
        "Ch02/Semantics.lean",
        "theorem unwinding_trivial",
        "/-! ## 5. 해를 비교할 순서가 필요하다",
        """theorem unwinding_trivial (f : State String → SigmaBot String) :
    ∀ σ, f σ = if ⟦(.tru : BoolExp String)⟧ᵇ σ then Option.bind (some σ : SigmaBot String) f
                else some σ := by
  -- 힌트: 조건이 언제나 참이고 본체가 상태를 바꾸지 않으므로
  --       우변이 좌변과 같아진다. 정의를 펼치기만 하면 된다.
  sorry

""",
    ),
    # ── 정의를 왜 이렇게 써야 하나
    (
        "Ch01/Design.lean",
        "theorem fvBad_breaks_coincidence",
        "/-! ## 2. 양화사에서 상태를 갱신하지 않으면",
        """theorem fvBad_breaks_coincidence :
    ∃ (p : Assert String) (σ σ' : State String),
      (∀ w ∈ p.fvBad, σ w = σ' w) ∧ ¬ (⟦p⟧ₐ σ ↔ ⟦p⟧ₐ σ') := by
  -- 증명보다 반례를 떠올리는 것이 이 연습이다.
  -- 힌트 1: `fvBad` 가 빠뜨리는 자리는 이항 논리 연산의 **오른쪽**이다.
  --         그 자리에만 변수를 두면 `fvBad` 가 빈 집합이 되어 전제가 공짜로 성립한다.
  -- 힌트 2: 두 상태는 `State.const` 로 만들면 된다.
  -- 힌트 3: 마무리는 `simp [Assert.eval, LogOp.denote, Cmp.denote, IntExp.eval, State.const]`.
  sorry

""",
    ),
    (
        "Ch01/Design.lean",
        "theorem evalBad_breaks_coincidence",
        "/-! ## 3. 치환에서 결합 변수를 그대로 두면",
        """theorem evalBad_breaks_coincidence :
    ∃ (p : Assert String) (σ σ' : State String),
      (∀ w ∈ p.fv, σ w = σ' w) ∧ ¬ (p.evalBad σ ↔ p.evalBad σ') := by
  -- 힌트 1: 이번에는 `fv` 가 옳으므로, 자유 변수가 **없는** 구를 잡아야 전제가 공짜다.
  -- 힌트 2: 그런데도 뜻이 상태에 달려야 한다. 묶인 변수를 본문에서 쓰면 된다.
  -- 힌트 3: `∀x. x = 0` 을 두 상태에서 재 보라.
  sorry

""",
    ),
    (
        "Ch01/Design.lean",
        "theorem substNaive_breaks_substitution",
        "/-! ## 4. 왜 동시 치환인가",
        """theorem substNaive_breaks_substitution :
    ∃ (p : Assert String) (δ : Subst String) (σ σ' : State String),
      (∀ w ∈ p.fv, σ w = ⟦δ w⟧ₑ σ') ∧ ¬ (⟦p.substNaive δ⟧ₐ σ' ↔ ⟦p⟧ₐ σ) := by
  -- 먼저 볼 것: 바로 위의 `#guard` 두 줄. 반례가 거기 이미 나와 있다.
  -- 힌트 1: 들어오는 식의 자유 변수가 결합 변수와 **같은 이름**이어야 포획이 일어난다.
  -- 힌트 2: 두 상태를 모두 `State.const 0` 으로 두면 전제가 `0 = 0` 이 된다.
  -- 힌트 3: 양변을 따로 `have` 로 세우고 마지막에 `hiff.mpr` 로 모순을 끌어내라.
  --         왼쪽은 `rintro ⟨n, hn⟩` 으로 열고, 오른쪽은 `refine ⟨1, ?_⟩` 로 증인을 준다.
  sorry

""",
    ),
    # ── §2.3 도메인과 연속 함수
    (
        "Ch02/Domain.lean",
        "theorem Continuous.monotone",
        "end ContinuousBasic",
        """theorem Continuous.monotone {f : α → β} (hf : Continuous f) : Monotone f := by
  -- 힌트 1: `x ⊑ y` 를 보이는 데 필요한 사슬은 `Chain.step hxy` 하나다 (`x, y, y, …`).
  -- 힌트 2: 그 사슬의 극한이 `y` 임을 먼저 세워라. 극한은 유일하므로
  --         `Chain.isLUB.unique` 로 보인다. `Chain.range_step` 이 훑는 값을 `{x, y}` 로 준다.
  -- 힌트 3: 연속성이 주는 `IsLUB` 의 **상계** 부분만 쓰면 끝난다.
  sorry

""",
    ),
    (
        "Ch02/Domain.lean",
        "theorem continuous_iff_le",
        "-- ANCHOR_END: prop21",
        """theorem continuous_iff_le [PartialOrder α] [PartialOrder β] [Predomain α] [Predomain β]
    {f : α → β} (hf : Monotone f) :
    Continuous f ↔ ∀ c : Chain α, f c.lub ≤ (c.map hf).lub := by
  -- 힌트 1: 두 방향 다 `Chain.range_map` 으로 상과 옮긴 사슬을 오간다.
  -- 힌트 2: (→) 극한은 유일하다. 같은 집합의 최소 상계 둘이면 같은 값이다.
  -- 힌트 3: (←) 상계 쪽은 `hf (c.le_lub n)` 한 줄이다. 최소 쪽에서 가정한 부등식을 쓴다.
  sorry

""",
    ),
    (
        "Ch02/Domain.lean",
        "theorem exists_monotone_not_continuous",
        "-- ANCHOR_END: notContinuous",
        """theorem exists_monotone_not_continuous :
    ∃ f : Set ℕ → Prop, Monotone f ∧ ¬ Continuous f := by
  -- 먼저 볼 것: 바로 위의 `initSegs` 와 `initSegs_lub`. 둘 다 완성되어 있다.
  -- 힌트 1: `f s = (s = Set.univ)` 를 쓴다. `Prop` 의 순서는 함의다.
  -- 힌트 2: 연속이라고 가정하고 `initSegs` 를 먹인 뒤, 상이 전부 거짓임을 보여라.
  --         그러면 `False` 도 상계이므로 최소 상계가 참일 수 없다.
  -- 힌트 3: `{k | k < n} = ℕ` 이면 `n < n` 이 된다.
  sorry

""",
    ),
    # ── §2.3 리프팅과 함수 공간
    (
        "Ch02/Domain/Lifting.lean",
        "theorem Monotone.continuous_of_lub_mem",
        "-- ANCHOR_END: monotoneContinuous",
        """theorem Monotone.continuous_of_lub_mem [PartialOrder α] [PartialOrder β] [Predomain α]
    {f : α → β} (hf : Monotone f)
    (hmem : ∀ c : Chain α, c.lub ∈ Set.range c.seq) : Continuous f := by
  -- 힌트 1: 상계 쪽은 단조성 그대로다. `rintro _ ⟨x, ⟨n, rfl⟩, rfl⟩` 로 상의 원소를 벗겨라.
  -- 힌트 2: 최소 쪽에서 `hmem c` 가 극한이 `c.seq N` 이라고 알려 준다.
  --         그러면 `f c.lub` 자체가 상의 원소이고, 상계 `b` 는 그 위에 있다.
  sorry

""",
    ),
    (
        "Ch02/Domain/Lifting.lean",
        "theorem liftBot_unique",
        "-- ANCHOR_END: prop24",
        """theorem liftBot_unique {V : Type u} {f : State V → SigmaBot V} {g : SigmaBot V → SigmaBot V}
    (hstrict : g none = none) (hext : ∀ σ, g (some σ) = f σ) : g = liftBot f := by
  -- 힌트: `funext x` 뒤 `cases x`. `Σ⊥` 에는 `⊥` 와 값밖에 없다.
  sorry

""",
    ),
    (
        "Ch02/Domain/FunctionSpace.lean",
        "theorem Continuous.comp",
        "-- ANCHOR_END: prop23",
        """theorem Continuous.comp [Predomain α] [Predomain β]
    {g : β → γ} {f : α → β} (hg : Continuous g) (hf : Continuous f) :
    Continuous (g ∘ f) := by
  -- 먼저 볼 것: 바로 위의 `Continuous.map_lub`. 극한의 유일성을 등식으로 바꿔 둔 것이다.
  -- 힌트 1: `hg (c.map hf.monotone)` 이 거의 답이다. 상을 `Chain.range_map` 과
  --         `Set.image_comp` 로 `(g ∘ f) '' …` 모양으로 접어라.
  -- 힌트 2: 남는 것은 `(g ∘ f) c.lub = g ((c.map _).lub)` 뿐이고, `hf.map_lub` 가 준다.
  sorry

""",
    ),
    (
        "Ch02/Domain/FunctionSpace.lean",
        "theorem lub_continuous",
        "-- ANCHOR_END: prop22",
        """theorem lub_continuous (c : Chain (Cont α β)) :
    Continuous ((Chain.toFuns c).lub) := by
  -- Reynolds 명제 2.2 의 극한 바꾸기다. `⨆ₙ⨆ᵢ = ⨆ᵢ⨆ₙ` 를 등식 없이
  -- `le_lub` / `lub_le` 만으로 오간다.
  -- 힌트 1: 먼저 점별 극한이 단조임을 `have` 로 세워라. 상계 쪽은 그 단조성 그대로다.
  -- 힌트 2: 최소 쪽은 극한을 두 번 벗긴다 — 바깥은 `Chain.lub_le fun n => ?_`,
  --         `(c.seq n).continuous.map_lub d` 로 안쪽 극한을 꺼낸 뒤 다시 `lub_le`.
  -- 힌트 3: 마지막 사슬 항은 `fₙ(dᵢ) ⊑ h(dᵢ) ⊑ b` 로 잇는다. `change` 로 목표 모양을
  --         맞춰야 `rw` 가 붙는 자리가 있다.
  sorry

""",
    ),
    # ── §2.4 최소 고정점 정리
    (
        "Ch02/Fixpoint.lean",
        "theorem fix_eq",
        "-- ANCHOR_END: fixEq",
        """theorem fix_eq {F : α → α} (hF : Continuous F) :
    F (fix F hF.monotone) = fix F hF.monotone := by
  -- 먼저 볼 것: 바로 위의 `isLUB_shifted`. 밀린 사슬의 극한도 `fix` 라는 사실이 완성되어 있다.
  -- 힌트 1: `hF (iterChain hF.monotone)` 이 `F(fix)` 를 "F 를 입힌 상" 의 극한으로 만든다.
  -- 힌트 2: 그 상이 밀린 사슬의 값들과 같음을 `ext` 로 보여라.
  --         양방향 모두 `Function.iterate_succ_apply'` 하나로 잇는다.
  -- 힌트 3: 극한은 유일하다 — `IsLUB.unique`.
  sorry

""",
    ),
    (
        "Ch02/Fixpoint.lean",
        "theorem fix_least",
        "-- ANCHOR_END: fixLeast",
        """theorem fix_least {F : α → α} (hF : Monotone F) {x : α} (hx : F x ≤ x) :
    fix F hF ≤ x := by
  -- 힌트 1: `lub_le` 로 "각 단계가 x 아래" 로 줄인 뒤 `n` 에 대한 귀납.
  -- 힌트 2: 걸음은 `Fⁿ⁺¹(⊥) = F(Fⁿ(⊥)) ⊑ F(x) ⊑ x`. `calc` 로 쓰면 그대로 읽힌다.
  sorry

""",
    ),
    (
        "Ch02/Fixpoint.lean",
        "theorem scott_induction",
        "-- ANCHOR_END: scott",
        """theorem scott_induction {F : α → α} (hF : Monotone F) {P : α → Prop}
    (hadm : ∀ c : Chain α, (∀ n, P (c.seq n)) → P c.lub)
    (hbot : P ⊥) (hstep : ∀ x, P x → P (F x)) : P (fix F hF) := by
  -- 힌트: 허용 가능성을 반복의 사슬에 적용하고, 각 단계는 `n` 에 대한 귀납으로.
  --       걸음에서 `Function.iterate_succ_apply'` 로 모양을 맞춘다.
  sorry

""",
    ),
]


def transform(text: str, blanks: list[tuple[str, str, str]]) -> str:
    """이름공간 치환 · ANCHOR 제거 · 증명 비우기."""
    # 장 번호를 하드코딩하지 않는다. 모듈 이름은 점(.)으로 쓰므로 슬래시 경로
    # (`Reynolds/Answers/…`, 산문에서 완성본을 가리킬 때 쓴다)는 건드리지 않는다.
    out = text.replace("Reynolds.Answers.", "Reynolds.Exercises.")
    # 공유 모듈은 Answers 쪽을 그대로 가리키게 되돌린다.
    for shared in SHARED:
        mod = "Reynolds.Exercises." + shared.removesuffix(".lean").replace("/", ".")
        out = out.replace(mod, mod.replace("Exercises", "Answers"))
    out = out.replace("완성본 (Answers)", "연습 (Exercises)")
    # ANCHOR 제거보다 **먼저** 증명을 비운다. 끝 마커로 `-- ANCHOR_END:` 를 쓰는 항목이 있다.
    for start, end, stub in blanks:
        try:
            a = out.index(start)
            b = out.index(end, a)
        except ValueError as exc:  # pragma: no cover - 마커가 어긋나면 즉시 알려야 한다
            raise SystemExit(f"마커를 찾지 못했다: {start!r} … {end!r}\n  {exc}") from exc
        out = out[:a] + stub + out[b:]
    return "\n".join(line for line in out.split("\n") if "-- ANCHOR" not in line)


def build() -> dict[pathlib.Path, str]:
    """생성 결과를 경로 → 내용으로 돌려준다."""
    per_file: dict[str, list[tuple[str, str, str]]] = {}
    for rel, start, end, stub in BLANKS:
        per_file.setdefault(rel, []).append((start, end, stub))

    result: dict[pathlib.Path, str] = {}
    for src in sorted(ANSWERS.rglob("*.lean")):
        rel = src.relative_to(ANSWERS)
        if str(rel) in SHARED:
            continue
        # ANCHOR 제거 뒤 마커 위치가 밀리므로, 파일별 blanks 를 그대로 넘긴다.
        result[EXERCISES / rel] = transform(src.read_text(), per_file.get(str(rel), []))
    return result


def main() -> int:
    check = "--check" in sys.argv
    generated = build()
    stale: list[pathlib.Path] = []
    for dst, content in generated.items():
        if check:
            if not dst.exists() or dst.read_text() != content:
                stale.append(dst)
        else:
            dst.parent.mkdir(parents=True, exist_ok=True)
            dst.write_text(content)

    # Answers 에서 사라진 파일이 Exercises 에 남아 있으면 알린다.
    for orphan in sorted(EXERCISES.rglob("*.lean")):
        if orphan not in generated:
            stale.append(orphan) if check else orphan.unlink()

    if check and stale:
        print("Exercises 트리가 Answers 와 어긋난다. `python3 scripts/gen-exercises.py` 를 돌려라:")
        for pth in stale:
            print(f"  {pth.relative_to(ROOT)}")
        return 1
    if not check:
        print(f"Exercises {len(generated)}개 파일 생성 완료")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
