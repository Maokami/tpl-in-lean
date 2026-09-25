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
        "-- ANCHOR_END: boolExp_eval_iff",
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
        "-- ANCHOR_END: unwinding_not_unique",
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
        "-- ANCHOR_END: continuous_iff_le",
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
        "-- ANCHOR_END: exists_monotone_not_continuous",
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
        "-- ANCHOR_END: Monotone.continuous_of_lub_mem",
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
        "-- ANCHOR_END: liftBot_unique",
        """theorem liftBot_unique {V : Type u} {f : State V → SigmaBot V} {g : SigmaBot V → SigmaBot V}
    (hstrict : g none = none) (hext : ∀ σ, g (some σ) = f σ) : g = liftBot f := by
  -- 힌트: `funext x` 뒤 `cases x`. `Σ⊥` 에는 `⊥` 와 값밖에 없다.
  sorry

""",
    ),
    (
        "Ch02/Domain/FunctionSpace.lean",
        "theorem Continuous.comp",
        "-- ANCHOR_END: Continuous.comp",
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
        "-- ANCHOR_END: lub_continuous",
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
        "-- ANCHOR_END: fix_eq",
        """theorem fix_eq {F : α → α} (hF : Continuous F) :
    F (fix F hF.monotone) = fix F hF.monotone := by
  -- 먼저 볼 것: 바로 위의 `isLUB_shifted`. 밀린 사슬의 극한도 `fix` 라는 사실이 완성되어 있다.
  -- 힌트 1: `hF (iterChain hF.monotone)`이 `F(fix)`를 "F를 입힌 상"의 극한으로 만든다.
  -- 힌트 2: 그 상이 밀린 사슬의 값들과 같음을 `ext`로 보여라.
  --         양방향 모두 `Function.iterate_succ_apply'` 하나로 잇는다.
  -- 힌트 3: 극한은 유일하다 — `IsLUB.unique`.
  sorry

""",
    ),
    (
        "Ch02/Fixpoint.lean",
        "theorem fix_least",
        "-- ANCHOR_END: fix_least",
        """theorem fix_least {F : α → α} (hF : Monotone F) {x : α} (hx : F x ≤ x) :
    fix F hF ≤ x := by
  -- 힌트 1: `lub_le`로 "각 단계가 x 아래"로 줄인 뒤 `n`에 대한 귀납.
  -- 힌트 2: 걸음은 `Fⁿ⁺¹(⊥) = F(Fⁿ(⊥)) ⊑ F(x) ⊑ x`. `calc`로 쓰면 그대로 읽힌다.
  sorry

""",
    ),
    (
        "Ch02/Fixpoint.lean",
        "theorem scott_induction",
        "-- ANCHOR_END: scott_induction",
        """theorem scott_induction {F : α → α} (hF : Monotone F) {P : α → Prop}
    (hadm : ∀ c : Chain α, (∀ n, P (c.seq n)) → P c.lub)
    (hbot : P ⊥) (hstep : ∀ x, P x → P (F x)) : P (fix F hF) := by
  -- 힌트: 허용 가능성을 반복의 사슬에 적용하고, 각 단계는 `n` 에 대한 귀납으로.
  --       걸음에서 `Function.iterate_succ_apply'` 로 모양을 맞춘다.
  sorry

""",
    ),
    (
        "Ch02/Eval.lean",
        "theorem whileF_continuous",
        "-- ANCHOR_END: whileF_continuous",
        """theorem whileF_continuous (b : BoolExp V) (s : State V → SigmaBot V) :
    Continuous (whileF b s) := by
  -- 먼저 볼 것: `Continuous`, `IsLUB`, `whileF_monotone`, `Chain.lub_apply`의 정의와 정리.
  -- 이 연습은 앞의 다른 연습 결과를 사용하지 않고 `Continuous` 정의에서 직접 증명한다.
  -- 힌트 1: 상계는 `c.le_lub`; 최소성은 상태 `σ`를 고정한 뒤 조건과 `s σ`로 나눈다.
  -- 힌트 2: `s σ = some τ`이면 `Chain.lub_le`로 각 `c.seq n τ`가 상계 아래임을 보인다.
  -- 힌트 3: 조건이 거짓이면 함수상의 0번째 항을 상계 가정에 넣는다.
  sorry

""",
    ),
    # ── §2.4 연료 해석기
    (
        "Ch02/Interpreter.lean",
        "theorem Comm.run_le_succ",
        "-- ANCHOR_END: Comm.run_le_succ",
        """theorem Comm.run_le_succ : ∀ (c : Comm V) (n : ℕ) (σ : State V),
    c.run n σ ≤ c.run (n + 1) σ := by
  -- 먼저 볼 것: 바로 위의 `Option.bind_le_bind`. `seq` 와 `wh` 절이 그것으로 돈다.
  -- 힌트 1: 명령에 대한 구조적 귀납. `skip` 과 `newvar` 는 DSL 이 키워드로 만들었으니
  --         분기 이름을 `«skip»`, `«newvar»` 로 써야 한다.
  -- 힌트 2: `run` 은 연료도 매칭하므로 자유 변수 연료로는 저절로 줄지 않는다.
  --         분기마다 `simp only [Comm.run]` 이나 `rw [Comm.run]` 으로 방정식을 펴라.
  -- 힌트 3: `wh` 절 안에서 연료에 대한 귀납을 겹친다. 0 은 `none ⊑ 무엇이든`.
  sorry

""",
    ),
    # ── §2.5 자유 변수
    (
        "Ch02/FreeVars.lean",
        "theorem Comm.fa_subset_fv",
        "-- ANCHOR_END: faSubset",
        """theorem Comm.fa_subset_fv : ∀ c : Comm V, c.fa ⊆ c.fv := by
  -- 힌트 1: 구조적 귀납. `skip` 과 `newvar` 분기는 `«skip»`, `«newvar»` 로 쓴다.
  -- 힌트 2: `Finset.union_subset`, `Finset.subset_union_left/right`,
  --         `Finset.erase_subset_erase` 를 `le_trans` 로 잇는다.
  sorry

""",
    ),
    (
        "Ch02/FreeVars.lean",
        "theorem AgreeOn.admissible",
        "-- ANCHOR_END: agreeAdmissible",
        """theorem AgreeOn.admissible (S : Finset V) (d : Chain (State V → SigmaBot V))
    {σ σ' : State V} (h : ∀ n, AgreeOn S (d.seq n σ) (d.seq n σ')) :
    AgreeOn S (d.lub σ) (d.lub σ') := by
  -- 먼저 볼 것: `Chain.flat_lub_mem_range` 와 `Chain.flat_stabilizes`. 둘 다 완성되어 있다.
  -- 힌트 1: `Chain.lub_apply` 로 점별 극한으로 바꾸고, 왼쪽 극한을 `rcases` 로 나눈다.
  -- 힌트 2: `⊥` 갈래 — 모든 단계가 `⊥` 였다는 것을 `le_lub` + `le_none_iff` 로 끌어내고,
  --         단계별 일치로 오른쪽도 전부 `⊥` 임을 보인다.
  -- 힌트 3: 상태 갈래 — 두 극한의 결정 시점 `k`, `k'` 를 얻고, `max k k'` 단계에서
  --         `flat_stabilizes` 로 두 극한값을 함께 읽는다.
  sorry

""",
    ),
    # ── §2.5 치환과 별칭
    (
        "Ch02/Substitution.lean",
        "theorem substitution_boolExp :",
        "-- ANCHOR_END: boolSubst",
        """theorem substitution_boolExp :
    ∀ (b : BoolExp V) (δ : Subst V) (σ σ' : State V),
      (∀ w ∈ b.fv, σ w = ⟦δ w⟧ₑ σ') → ⟦b /ᵇ δ⟧ᵇ σ' = ⟦b⟧ᵇ σ := by
  -- 먼저 볼 것: 1장 `substitution_intExp` 의 완성 증명. 절마다 그것을 이어 붙인다.
  -- 힌트: `cmp` 케이스에서 두 식에 각각 `substitution_intExp` 를 쓴다.
  --       나머지는 `not`/`bin` 의 귀납 가설이다.
  sorry

""",
    ),
    (
        "Ch02/Substitution.lean",
        "theorem Comm.subst_id",
        "-- ANCHOR_END: substId",
        """theorem Comm.subst_id [HasFresh V] : ∀ c : Comm V, c /ᶜ id = c := by
  -- 힌트 1: 구조적 귀납. `skip`, `newvar` 분기는 `«skip»`, `«newvar»` 로 쓴다.
  -- 힌트 2: `Ren.toSubst_id` 로 `id.toSubst = IntExp.var` 를 얻고,
  --         `subst_var_intExp` · `BoolExp.subst_var` 로 식·불 식을 처리한다.
  -- 힌트 3: `newvar` 케이스 — 피해야 할 집합이 `Finset.image_id` 로 `FV(c) \\ {v}` 가
  --         되어 `v` 가 안전하다. 새 결합자가 `v` 그대로임을 보이고,
  --         `Function.update id v v = id` 를 함수 외연성으로 확인한 뒤 귀납 가설을 쓴다.
  sorry

""",
    ),
    (
        "Ch02/Substitution.lean",
        "theorem swap_ok",
        "-- ANCHOR_END: swap",
        """theorem swap_ok (σ : State String) :
    ∃ τ, swap.eval σ = some τ ∧ τ "x" = σ "y" ∧ τ "y" = σ "x" := by
  -- 힌트: `while` 이 없으므로 `swap.eval σ` 는 정의 등식만으로 `some _` 까지 계산된다.
  --       첫 성분은 `rfl` 로 두고, 남는 두 등식을
  --       `simp [IntExp.eval, State.subst_def, Function.update]` 로 닫는다.
  sorry

""",
    ),
    # ── §2.6 for 명령과 결함
    (
        "Ch02/Sugar.lean",
        "theorem forV1_leaks :",
        "-- ANCHOR_END: forV1Leaks",
        """theorem forV1_leaks :
    ∃ (σ τ : State String),
      (forV1 "i" (.num 1) (.num 1) .skip).eval σ = some τ ∧ τ "i" ≠ σ "i" := by
  -- 먼저 볼 것: `Comm.run_sound` (연료 실행이 표시적 의미와 일치).
  -- 힌트 1: 증인은 `σ := State.const 0`. `for i := 1 to 1 do skip` 은 한 바퀴 돌고
  --         i 를 2 로 남긴다.
  -- 힌트 2: `run 2 (State.const 0) = some _` 를 `simp [forV1, forWhile, forBody, incr,
  --         Comm.run, BoolExp.eval, IntExp.eval, IntOp.denote, Cmp.denoteBool]` 로 계산하고,
  --         `Comm.run_sound` 로 옮긴 뒤 `τ "i" ≠ σ "i"` 를 `decide` 로 닫는다.
  --         (`run` 은 정의 등식으로만 풀린다 — `rfl` 로는 안 된다.)
  sorry

""",
    ),
    (
        "Ch02/Sugar.lean",
        "theorem forV2_diverges",
        "-- ANCHOR_END: forV2Diverges",
        """theorem forV2_diverges (v : V) (σ : State V) :
    (forV2 v (.num 1) (.var v) .skip).eval σ = none := by
  -- 먼저 볼 것: `Comm.run_complete` (표시적으로 종료하면 어떤 연료로 실행된다).
  -- 힌트 1: 안쪽 while 이 어떤 연료·상태에서도 `none` 임을 연료 귀납으로 보인다.
  --         조건 `v ≤ v` 는 언제나 참(`by_cases` 후 항상 참 쪽만 남는다).
  -- 힌트 2: 한 바퀴는 본체가 `some (σ'[v := σ' v + 1])` 을 내고 남은 루프로 넘어간다.
  --         `rw [forWhile, Comm.run]` 로 한 스텝 풀고 귀납 가설을 쓴다.
  -- 힌트 3: 표시적 의미가 `none` 임을 `Comm.run_complete` 의 대우로 얻고,
  --         `newvar` 의 복원이 `none` 을 통과시킨다 (`change` 로 펼친 뒤 `simp [restore]`).
  sorry

""",
    ),
    # ── §2.6 정확 반복
    (
        "Ch02/Sugar2.lean",
        "theorem forWhile_eq_fold",
        "-- ANCHOR_END: forWhileEqFold",
        """theorem forWhile_eq_fold (v w : V) (c : Comm V)
    (hv : v ∉ c.fa) (hw : w ∉ c.fa) (hvw : v ≠ w) :
    ∀ (m : Nat) (σ : State V), (σ w - σ v + 1).toNat = m →
      (forWhile v (.var w) c).eval σ = forFold v c m σ := by
  -- 먼저 볼 것: `Comm.eval_isSemantics` 의 `wh` 절과 `Comm.eval_agree_outside_fa` (명제 2.6(b)).
  -- 힌트 1: 보조 등식 셋을 `have` 로 깔아 두면 본 증명이 짧아진다. 셋 다 `rfl` 로 된다.
  --         (a) while 한 바퀴 펼치기 — `Comm.eval_isSemantics.2.2.2.2.1 _ _ σ`
  --         (b) 조건의 값 — `⟦cmp le (var v) (var w)⟧ᵇ σ = decide (σ v ≤ σ w)`
  --         (c) 본체 — `⟦forBody v c⟧ᶜ σ = Option.bind (⟦c⟧ᶜ σ) fun σ'' => some σ''[v := σ'' v + 1]`
  -- 힌트 2: `m` 에 대한 귀납. `σ` 는 `intro m` 뒤에 남겨 두어야 귀납 가설이 다음 상태에 쓰인다.
  -- 힌트 3: `if` 는 `if_pos`/`if_neg` 로 가른다. 조건이 `decide _ = true` 꼴이라
  --         `(by simp [hle])` / `(by simp [hgt])` 로 증거를 만든다. 두 부등식은 `omega`.
  -- 힌트 4: 한 바퀴 뒤 `σ'' v = σ v` 와 `σ'' w = σ w` 를 `eval_agree_outside_fa` 로 얻고,
  --         다음 상태의 측도가 `n` 임을 `State.subst_self` · `State.subst_of_ne` · `omega` 로 보인다.
  sorry

""",
    ),
    (
        "Ch02/Sugar2.lean",
        "theorem forV3_broken_by_assigning_control",
        "-- ANCHOR_END: broken",
        """theorem forV3_broken_by_assigning_control :
    "i" ∈ doublingBody.fa ∧
      ∃ τ, (forV3 "i" "hi" (.num 1) (.num 3) doublingBody).eval (State.const 0) = some τ
        ∧ τ "s" = 2 := by
  -- 힌트 1: 첫 성분은 `simp [doublingBody, Comm.fa]`.
  -- 힌트 2: 둘째 성분은 연료 8 로 실행한 뒤 `Comm.run_sound` 로 옮긴다.
  --         결과 상태를 손으로 적지 않으려면 `Option.map` 으로 `s` 만 뽑아
  --         `(run 8 _).map (fun σ => σ "s") = some 2` 를 `simp [...]` 로 계산하고,
  --         `Option.map_eq_some_iff` 로 상태를 되찾는다.
  -- 힌트 3: simp 인자에 `forV3, forWhile, forBody, incr, doublingBody, Comm.run, restore,`
  --         `BoolExp.eval, IntExp.eval, IntOp.denote, Cmp.denoteBool, State.const` 를 준다.
  sorry

""",
    ),
    # ── §2.7 산술 오류
    (
        "Ch02/ArithErrors.lean",
        "theorem AComm.eval_assign_overwrite",
        "-- ANCHOR_END: deadAssign",
        """theorem AComm.eval_assign_overwrite (A : ZeroDivision) (v : V) (d e : AExp V)
    (h : v ∉ e.fv) (σ : State V) :
    (AComm.seq (.assign v d) (.assign v e)).eval A σ = (AComm.assign v e).eval A σ := by
  -- 먼저 볼 것: 바로 위 `AExp.coincidence` (완성되어 있다).
  -- 힌트 1: `change` 로 양변을 상태 갱신까지 펼친다. `while` 이 없어 전함수라 `Option` 이 없다.
  -- 힌트 2: `e` 의 값이 `v` 를 덮어쓴 상태에서도 같음을 일치 정리로 보인다.
  --         `u ∈ e.fv` 이면 `u ≠ v` (가정 `h` 때문) 이므로 `State.subst_of_ne`.
  -- 힌트 3: 같은 자리에 두 번 대입한 것은 한 번 대입한 것과 같다.
  --         `simp [State.subst_def, Function.update_idem]`.
  sorry

""",
    ),
    (
        "Ch02/ArithErrors.lean",
        "theorem AExp.not_indep_div_zero",
        "-- ANCHOR_END: notIndep",
        """theorem AExp.not_indep_div_zero (v : V) : ¬ (AExp.div (.var v) (.num 0) : AExp V).Indep := by
  -- 힌트: `Indep` 은 "어떤 두 선택에서도 같다" 이므로, 다른 값을 내는 선택 둘을 들이대면 된다.
  --       `⟨fun _ => 0, fun _ => 0⟩` 과 `⟨fun _ => 1, fun _ => 0⟩`, 상태는 `State.const 0`.
  --       `simp [AExp.eval] at` 으로 `0 = 1` 을 끌어내면 끝난다.
  sorry

""",
    ),
    (
        "Ch02/ArithErrors.lean",
        "theorem AExp.eval_leanChoice",
        "-- ANCHOR_END: leanChoice",
        """theorem AExp.eval_leanChoice (e₀ e₁ : AExp V) (σ : State V) :
    (AExp.div e₀ e₁).eval .leanChoice σ
        = e₀.eval .leanChoice σ / e₁.eval .leanChoice σ
      ∧ (AExp.rem e₀ e₁).eval .leanChoice σ
        = e₀.eval .leanChoice σ % e₁.eval .leanChoice σ := by
  -- 힌트 1: 제수가 0 인지로 나눈다 (`by_cases h : e₁.eval (V := V) .leanChoice σ = 0`).
  -- 힌트 2: 0 이 아니면 선택이 아예 안 쓰인다 — `simp only [AExp.eval, if_neg h]`.
  -- 힌트 3: 0 이면 Lean 의 규약이 드러난다. `Int.ediv_zero` (`a / 0 = 0`) 와
  --         `Int.emod_zero` (`a % 0 = a`) 가 `ZeroDivision.leanChoice` 의 선택과 맞물린다.
  sorry

""",
    ),
    # ── §2.8 문맥과 완전 추상성
    (
        "Ch02/FullAbstraction.lean",
        "theorem Ctx.fill_congr",
        "-- ANCHOR_END: fillCongr",
        """theorem Ctx.fill_congr (C : Ctx V) {c c' : Comm V} (h : c.eval = c'.eval) :
    (C.fill c).eval = (C.fill c').eval := by
  -- 먼저 볼 것: 바로 위 `Comm.eval_wh_congr` (완성되어 있다). `wh` 절이 그것을 쓴다.
  -- 힌트 1: 문맥에 대한 구조적 귀납. `newvar` 분기는 `«newvar»` 로 쓴다.
  -- 힌트 2: `wh` 를 뺀 각 절은 `funext σ` 뒤에 `change` 로 그 생성자의 의미 방정식을
  --         펼치고 귀납 가설을 `rw` 하면 끝난다 (`Option.bind`, `if`, `restore`).
  -- 힌트 3: `wh` 절만 `fix` 를 지나므로 `Comm.eval_wh_congr` 가 필요하다.
  sorry

""",
    ),
    (
        "Ch02/FullAbstraction.lean",
        "theorem eval_diverge",
        "-- ANCHOR_END: diverge",
        """theorem eval_diverge (σ : State V) : (diverge : Comm V).eval σ = none := by
  -- 힌트 1: 이 반복의 함수 연산자는 항등 함수다 — `whileF tru ⟦skip⟧ w = w` 가 `rfl` 로 된다.
  -- 힌트 2: 그러면 `⊥` 가 전고정점이므로 `fix_least` 가 `⟦diverge⟧ ≤ ⊥` 를 준다.
  --         사슬을 펼칠 필요가 없다.
  -- 힌트 3: 함수 공간의 `≤` 는 점별이므로 그 부등식을 `σ` 에 적용한 뒤 `simpa`.
  sorry

""",
    ),
    (
        "Ch02/FullAbstraction.lean",
        "theorem obsEq_imp_eval_eq",
        "-- ANCHOR_END: obsComplete",
        """theorem obsEq_imp_eval_eq [Inhabited V] {c c' : Comm V} (h : ObsEq c c') : c.eval = c'.eval := by
  -- 힌트 1: 빈 문맥(`Ctx.hole`) 하나면 충분하다. `funext σ` 로 상태를 고정한다.
  -- 힌트 2: 두 결과를 `rcases h1 : c.eval σ with _ | τ` 로 네 갈래로 나눈다.
  -- 힌트 3: 한쪽만 발산하는 갈래는 아무 변수(`default`)에서 `none` 과 `some _` 로 갈린다.
  --         둘 다 종료하는 갈래는 모든 변수에서 값이 같으므로 `funext` 로 상태가 같다.
  sorry

""",
    ),
    # ── §2.8 관찰의 선택과 세 등식
    (
        "Ch02/FullAbstraction2.lean",
        "theorem incTwice_eq_incByTwo",
        "-- ANCHOR_END: obsEq1",
        """theorem incTwice_eq_incByTwo : incTwice.eval = incByTwo.eval := by
  -- 힌트 1: `while` 이 없으므로 `funext σ` 뒤에 `change` 로 양변을 상태 갱신까지 펼칠 수 있다.
  --         두 번째 대입이 읽는 `x` 는 이미 한 번 올라간 값이다.
  -- 힌트 2: `State.subst_self` 로 그 값을 읽고, 같은 자리 두 번 대입은
  --         `Function.update_idem` 으로 하나로 줄인다.
  -- 힌트 3: 남는 것은 `σ \"x\" + 1 + 1 = σ \"x\" + 2` 라는 산술이다.
  sorry

""",
    ),
    (
        "Ch02/FullAbstraction2.lean",
        "theorem countLoop_eval",
        "-- ANCHOR_END: loopEval",
        """theorem countLoop_eval (σ : State String) (h : σ \"x\" ≤ 100) :
    countLoop.eval σ = some (σ[\"x\" := (100 : Int)]) := by
  -- 먼저 볼 것: §2.6 의 `forWhile_eq_fold`. 측도에 대한 귀납이라는 뼈대가 같다.
  -- 힌트 1: `while` 한 바퀴를 펼치는 방정식을 `Comm.eval_isSemantics.2.2.2.2.1 _ _ τ` 로 꺼낸다.
  --         조건의 값 `⟦cmp lt (var \"x\") (num 100)⟧ᵇ τ = decide (τ \"x\" < 100)` 은 `rfl` 이다.
  -- 힌트 2: 남은 반복 횟수 `(100 - τ \"x\").toNat` 을 측도로 삼아 보조 명제를 세우고
  --         그 `Nat` 에 대해 귀납한다. `σ` 는 귀납 뒤에 `intro` 해야 가설이 다음 상태에 쓰인다.
  -- 힌트 3: 0 이면 `τ \"x\" = 100` (`omega`) 이라 조건이 거짓이고, `← heq` 로 되돌린 뒤
  --         `Function.update_eq_self` 가 끝낸다.
  -- 힌트 4: 아니면 한 바퀴 돌아 `x` 가 하나 늘고 측도가 하나 준다. 본체의 값은 `rfl` 로 얻고,
  --         `change` 로 `bind` 를 풀어 귀납 가설을 쓴 뒤 `Function.update_idem` 으로 마무리한다.
  sorry

""",
    ),
    (
        "Ch02/FullAbstraction2.lean",
        "theorem incThenDouble_eq_doubleThenInc",
        "-- ANCHOR_END: obsEq3",
        """theorem incThenDouble_eq_doubleThenInc : incThenDouble.eval = doubleThenInc.eval := by
  -- 힌트 1: `funext σ` 뒤 `change` 로 양변을 두 번의 상태 갱신까지 펼친다.
  -- 힌트 2: 한쪽이 읽는 변수를 다른 쪽이 쓰지 않으므로 `State.subst_of_ne` 로 읽기를 정리한다.
  --         문자열 부등식은 `by decide` 로 만든다.
  -- 힌트 3: 서로 다른 자리에 대한 갱신은 교환된다 — `Function.update_comm`.
  sorry

""",
    ),
    (
        "Ch02/FullAbstraction2.lean",
        "theorem alias_breaks_commutation",
        "-- ANCHOR_END: aliasBreak",
        """theorem alias_breaks_commutation :
    (incThenDouble /ᶜ aliasXY).eval (State.const 0)
      ≠ (doubleThenInc /ᶜ aliasXY).eval (State.const 0) := by
  -- 힌트 1: 등식을 가정한 뒤 양변에서 `z` 만 뽑아 본다 —
  --         `congrArg (fun o => o.map (fun τ => τ \"z\"))`.
  -- 힌트 2: `z := z+1; z := z×2` 는 0 에서 2 를, `z := z×2; z := z+1` 은 1 을 낸다.
  --         `simp` 인자에 `Comm.subst` 와 `Comm.eval` 을 함께 주어야 치환과 계산이 모두 풀린다.
  sorry

""",
    ),
    # ── 책 연습 2.1 · 2.2
    (
        "Ch02/Ex.lean",
        "theorem simulAssign_eval",
        "-- ANCHOR_END: simulAssign",
        """theorem simulAssign_eval (v\u2080 v\u2081 t : V) (e\u2080 e\u2081 : IntExp V)
    (ht : t \u2209 e\u2080.fv) (htv\u2080 : t \u2260 v\u2080) (htv\u2081 : t \u2260 v\u2081) (\u03c3 : State V) :
    (simulAssign v\u2080 v\u2081 t e\u2080 e\u2081).eval \u03c3
      = some ((\u03c3[v\u2080 := \u27e6e\u2080\u27e7\u2091 \u03c3])[v\u2081 := \u27e6e\u2081\u27e7\u2091 \u03c3]) := by
  -- \ud78c\ud2b8 1: `t` \ub97c \uae54\uc544\ub3c4 `e\u2080` \uc758 \uac12\uc740 \uadf8\ub300\ub85c\ub2e4 \u2014 1\uc7a5 `coincidence_intExp` \uacfc `t \u2209 FV(e\u2080)`.
  -- \ud78c\ud2b8 2: \ub2f4\uc544 \ub454 \uac12\uc740 `t \u2260 v\u2080` \ub355\ubd84\uc5d0 `v\u2080` \ub300\uc785\uc744 \uc9c0\ub098\ub3c4 \uadf8\ub300\ub85c\ub2e4
  --         (`State.subst_of_ne`, `State.subst_self`).
  -- \ud78c\ud2b8 3: `newvar` \uc640 `seq` \uc640 `assign` \uc758 \uc758\ubbf8 \ubc29\uc815\uc2dd\uc744 `Comm.eval_isSemantics` \uc5d0\uc11c \uafbc\ub0b8\ub2e4.
  -- \ud78c\ud2b8 4: \ub9c8\uc9c0\ub9c9\uc740 \ubcf5\uc6d0\uc774\ub2e4. `t` \uc5d0 \ub300\ud55c \uac31\uc2e0\uc744 `Function.update_comm` \uc73c\ub85c \uc55e\uc73c\ub85c
  --         \uc62e\uae34 \ub4a4 `Function.update_idem` \uacfc `Function.update_eq_self` \ub85c \uc0c1\uc1c4\ud55c\ub2e4.
  sorry

""",
    ),
    (
        "Ch02/Ex.lean",
        "theorem repeatEval_eq_repeatSugar",
        "-- ANCHOR_END: repeatEquiv",
        """theorem repeatEval_eq_repeatSugar (b : BoolExp V) (c : Comm V) :
    repeatEval b c = (repeatSugar b c).eval := by
  -- \uc774 \uc7a5\uc5d0\uc11c \uac00\uc7a5 \ubcfc \ub9cc\ud55c \uc5f0\uc2b5\uc774\ub2e4. \ucd5c\uc18c\uc131\uc744 \uc591\ucabd\uc5d0\uc11c \ud55c \ubc88\uc529 \uc4f4\ub2e4.
  -- \uba3c\uc800 \ubcfc \uac83: `fix_least` \uc640 `fix_eq`, \uadf8\ub9ac\uace0 \ubc14\ub85c \uc704 `repeatEval_unwind`.
  -- \ud78c\ud2b8 1: `le_antisymm` \uc73c\ub85c \ub450 \ubc29\ud5a5\uc744 \ub098\ub208\ub2e4.
  -- \ud78c\ud2b8 2: `\u2291` \u2014 \uc124\ud0d5 \ucabd \ud568\uc218\uac00 **`repeat` \uc758** \ud480\uae30 \ubc29\uc815\uc2dd\uc744 \ub9cc\uc871\ud568\uc744 \ubcf4\uc774\uba74
  --         `repeatF` \uc5d0 \ub300\ud55c `fix_least` \uac00 \uacf1\ubc14\ub85c \uc900\ub2e4.
  -- \ud78c\ud2b8 3: `\u2292` \u2014 \uc774\ubc88\uc5d0\ub294 `while` \ucabd \ucd5c\uc18c\uc131\uc744 \uc4f4\ub2e4. \ud6c4\ubcf4\ub294
  --         `fun \u03c3' => if \u27e6b\u27e7\u1d47 \u03c3' then some \u03c3' else repeatEval b c \u03c3'` \uc774\uace0,
  --         \uadf8\uac83\uc774 `whileF (\u00acb) \u27e6c\u27e7` \uc758 \uace0\uc815\uc810\uc784\uc744 \ubcf4\uc774\uba74 \ub41c\ub2e4.
  -- \ud78c\ud2b8 4: \uc591\ucabd \ubaa8\ub450 \uc870\uac74\uc774 \ucc38\uc778 \uac08\ub798\uc640 \uac70\uc9c3\uc778 \uac08\ub798\uc5d0\uc11c \ub450 \ubc29\uc815\uc2dd\uc774 \uc11c\ub85c\ub97c \uba54\uc6b4\ub2e4.
  --         `⟦¬b⟧ᵇ σ = !(⟦b⟧ᵇ σ)` \ub294 `rfl` \uc774\ub2e4.
  sorry

""",
    ),
    # ── 책 연습 2.3
    (
        "Ch02/Ex/Decr.lean",
        "theorem decrLoop_eval_of_halts",
        "-- ANCHOR_END: decrHalting",
        """theorem decrLoop_eval_of_halts :
    ∀ (σ : State String), decrHalts σ → decrLoop.eval σ = some (σ["x" := (0 : Int)]) := by
  -- 먼저 볼 것: 바로 위 `unwindsDecr_eval` (완성본) 과 §2.2 의 `decrHalts_step`,
  --            `decr_step`, `State.subst_subst`, `State.subst_eq_self`.
  -- 힌트 1: 측도는 `(σ "x" / 2).toNat` — 남은 바퀴 수다. 한 바퀴마다 `x` 가 2 씩 줄므로
  --         정확히 하나 준다. §2.8 의 `countLoop_eval` 과 같은 모양이다.
  -- 힌트 2: 그 `Nat` 에 대한 보조 명제를 `have` 로 세우고 귀납한다.
  --         `σ` 는 귀납 뒤에 `intro` 해야 가설이 다음 상태에 쓰인다.
  -- 힌트 3: 0 이면 `decrHalts σ` 와 측도로부터 `σ "x" = 0` 이 나온다 (`omega`).
  --         조건이 거짓이고 `State.subst_eq_self` 가 끝낸다.
  -- 힌트 4: 아니면 `σ "x" ≠ 0` 이므로 한 걸음 간다. `decrHalts` 가 한 걸음을 견딘다는
  --         `decrHalts_step` 이 귀납을 굴리는 연료다.
  sorry

""",
    ),
    # ── 책 연습 2.5
    (
        "Ch02/Ex/Unwind.lean",
        "theorem while_eq_dblBody",
        "-- ANCHOR_END: unwindTwice",
        """theorem while_eq_dblBody (b : BoolExp V) (c : Comm V) :
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

""",
    ),
    # ── 책 연습 2.6 · 2.7
    (
        "Ch02/Ex/Aliasing.lean",
        "theorem seq_comm",
        "-- ANCHOR_END: seqComm",
        """theorem seq_comm (c₀ c₁ : Comm V)
    (h₀ : ∀ w ∈ c₀.fv, w ∉ c₁.fa) (h₁ : ∀ w ∈ c₀.fa, w ∉ c₁.fv) :
    (Comm.seq c₀ c₁).eval = (Comm.seq c₁ c₀).eval := by
  -- 먼저 볼 것: §2.5 의 명제 2.6 **두 부분 모두** —
  --            `Comm.coincidence_general` (a) 와 `Comm.eval_agree_outside_fa` (b).
  -- 힌트 1: `funext σ` 뒤 `change` 로 양변을 `Option.bind` 로 펴고, 두 결과를 네 갈래로 나눈다.
  -- 힌트 2: 한쪽만 발산하는 갈래가 핵심이다. (b) 로 "다른 쪽을 지나도 내 자유 변수는
  --         그대로" 를 얻고, (a) 로 "그러므로 결과가 같다" 를 얻는다. `AgreeOn` 이
  --         `none` 과 `some` 을 가르므로 모순이 나온다.
  -- 힌트 3: 둘 다 끝나는 갈래는 `funext w` 로 변수마다 따진다. 세 경우다 —
  --         `w ∈ FA(c₀)`, `w ∈ FA(c₁)`, 둘 다 아님. 첫 둘은 `Comm.fa_subset_fv` 로
  --         `FV` 로 올린 뒤 (a) 를 쓰고, 마지막은 (b) 를 양쪽에 쓴다.
  sorry

""",
    ),
    (
        "Ch02/Ex/Aliasing.lean",
        "theorem fact_alias_safe_vs_naive",
        "-- ANCHOR_END: fact",
        """theorem fact_alias_safe_vs_naive :
    (∃ τ, (factSafe /ᶜ aliasToZ).eval (State.const 3) = some τ ∧ τ "z" = 6)
      ∧ (∃ τ, (factNaive /ᶜ aliasToZ).eval (State.const 3) = some τ ∧ τ "z" = 0) := by
  -- 먼저 볼 것: 바로 위 `factNaive_alias_eq` 와 `factSafe_alias_eq` (둘 다 `rfl` 로 완성되어 있다).
  -- 힌트 1: 그 둘로 치환을 손으로 쓴 프로그램으로 바꾼 뒤 계산한다.
  -- 힌트 2: `while` 이 있으므로 `run` 으로 계산하고 `Comm.run_sound` 로 옮긴다.
  --         안전한 판은 연료 4, 순진한 판은 연료 2 면 끝난다.
  -- 힌트 3: 결과 상태를 손으로 적지 않으려면 `Option.map` 으로 `z` 만 뽑아
  --         `(run n _).map (fun σ => σ "z") = some k` 를 `simp` 로 계산하고,
  --         `Option.map_eq_some_iff` 로 상태를 되찾는다.
  sorry

""",
    ),
    # ── 책 연습 2.8
    (
        "Ch02/Ex/SubstWeak.lean",
        "theorem Comm.substitution_weak",
        "-- ANCHOR_END: substWeak",
        """theorem Comm.substitution_weak [HasFresh V] :
    ∀ (c : Comm V) (δ : Ren V) (S : Finset V), c.fv ⊆ S →
      (∀ u ∈ c.fa, ∀ w ∈ S, δ u = δ w → u = w) →
      ∀ σ σ' : State V, (∀ w ∈ S, σ w = σ' (δ w)) →
      AgreeVia δ S (c.eval σ) ((c /ᶜ δ).eval σ') := by
  -- 먼저 볼 것: §2.5 의 `Comm.substitution_general` 을 곁에 두고 비교하며 쓴다.
  --            뼈대가 같고 **두 자리만** 다르다. 그리고 바로 위 `Comm.fa_subst_subset`.
  -- 힌트 1: `assign` 절 — 대입되는 `v` 가 `FA` 에 있으므로 약한 조건이 그대로 쓰인다.
  --         `hinj v (by simp [Comm.fa]) w hw` 의 방향에 주의한다 (`.symm` 이 두 번 필요하다).
  -- 힌트 2: `seq`·`ite`·`wh` 절은 조건을 부분 명령으로 좁혀 넘기기만 하면 된다.
  --         `FA(c₀) ⊆ FA(c₀; c₁)` 이고 `FA(while b c) = FA(c)` 다.
  -- 힌트 3: `newvar` 절의 `hinj'` — 결합자 `v` 쪽은 새 결합자 `vn` 의 신선함
  --         (`Comm.newBinder_ne`) 이 지켜 주고, 나머지는 바깥 조건을 `erase v` 로 좁혀 쓴다.
  -- 힌트 4: `newvar` 절의 `hfa'` 가 **이 연습의 핵심**이다. §2.5 의 증명은 여기서
  --         `(c /ᶜ δ).fa ⊆ (c /ᶜ δ).fv ⊆ (FV c).image δ` 로 올라가 버려 `FV` 위의
  --         단사성을 요구했다. 그 어림이 너무 거칠다 — `Comm.fa_subst_subset` 을 쓰면
  --         `FA` 위의 단사성만 있으면 된다.
  sorry

""",
    ),
    # ── 책 연습 2.9 · 2.10
    (
        "Ch02/Ex/ForRange.lean",
        "theorem forV4_eval_eq_forV3",
        "-- ANCHOR_END: forV4Eq",
        """theorem forV4_eval_eq_forV3 (v w : V) (e₀ e₁ : IntExp V) (c : Comm V)
    (hv : v ∉ c.fa) (hw : w ∉ c.fa) (hvw : v ≠ w) (hwe₀ : w ∉ e₀.fv) (σ : State V) :
    (forV4 v w e₀ e₁ c).eval σ = (forV3 v w e₀ e₁ c).eval σ := by
  -- 먼저 볼 것: 바로 위 보조정리 셋(`forWhileLt_eq_fold`, `forFold_succ_back`,
  --            `restore_bind_incr`)과 §2.6 의 `forV3_eq_fold`.
  -- 힌트 1: 오른쪽은 `forV3_eq_fold` 가 이미 푼다. 왼쪽의 `newvar` 두 겹을
  --         `Comm.eval_isSemantics.2.2.2.2.2` 로 펴고 `w ∉ FV(e₀)` 로 초기값을 맞춘다.
  -- 힌트 2: 안쪽 상태에서 `v` 는 `⟦e₀⟧σ`, `w` 는 `⟦e₁⟧σ` 다
  --         (`State.subst_self`, `State.subst_of_ne`). 조건이 `⟦e₀⟧σ ≤ ⟦e₁⟧σ` 로 읽힌다.
  -- 힌트 3: 구간이 차 있으면 보조정리 A 가 루프를 `(b-a).toNat` 번으로 세고,
  --         보조정리 B 가 판본 3 의 마지막 바퀴를 떼어 내어 모양을 맞춘다.
  --         `(b-a).toNat + 1 = (b-a+1).toNat` 은 `omega` 다.
  -- 힌트 4: 남는 차이는 **마지막 증가 하나**뿐이고 `restore_bind_incr` 이 그것을 지운다.
  -- 힌트 5: 구간이 비면 `(b-a+1).toNat = 0` 이라 양쪽 다 본문을 안 돈다.
  sorry

""",
    ),
    (
        "Ch02/Ex/DoTwice.lean",
        "theorem SComm.desugar_eval",
        "-- ANCHOR_END: desugarEval",
        """theorem SComm.desugar_eval : ∀ s : SComm V, s.desugar.eval = s.eval := by
  -- 힌트 1: 구문에 대한 구조적 귀납. `skip`·`newvar` 분기는 `«skip»`, `«newvar»` 로 쓴다.
  -- 힌트 2: 각 절은 `funext σ` 뒤 `change` 로 그 생성자의 의미 방정식을 펴고
  --         귀납 가설을 `rw` 하면 끝난다.
  -- 힌트 3: `wh` 절만 `fix` 를 지난다. 본체의 뜻을 바꿔 끼우는 것이고,
  --         §2.8 의 `Comm.eval_wh_congr` 와 같은 자리다 — `change` 뒤 `rw [ih]`.
  -- 힌트 4: `dotwice` 절이 요점이다. 복제된 두 자리가 **같은 부분항**에서 왔으므로
  --         귀납 가설 하나를 두 번 쓴다.
  sorry

""",
    ),
    # ── §3.1 명세의 뜻
    (
        "Ch03/Spec.lean",
        "theorem sat_admissible",
        "-- ANCHOR_END: satAdmissible",
        """theorem sat_admissible (Q : State V → Prop) (σ : State V) (d : Chain (State V → SigmaBot V))
    (h : ∀ n τ, d.seq n σ = some τ → Q τ) : ∀ τ, d.lub σ = some τ → Q τ := by
  -- 먼저 볼 것: §2.3 의 `Chain.flat_lub_mem_range` 와 `Chain.lub_apply`, 그리고 §2.5 의
  --            `AgreeOn.admissible` — 같은 논증인데 관계가 아니라 술어라 더 짧다.
  -- 힌트 1: `Chain.lub_apply` 로 `d.lub σ` 를 `Σ⊥` 사슬 `d.apply σ` 의 극한으로 바꾼다.
  -- 힌트 2: 평평한 사슬의 극한은 어느 항과 같다. 그 항 `k` 에서 가정 `h k` 가 `Q` 를 준다.
  sorry

""",
    ),
    (
        "Ch03/Spec.lean",
        "theorem TotalCorrect.toPartial",
        "-- ANCHOR_END: totalToPartial",
        """theorem TotalCorrect.toPartial {p q : Assert V} {c : Comm V} (h : ［p］c［q］) :
    ｛p｝c｛q｝ := by
  -- 힌트: 두 정의를 펼치면 (`intro σ hp τ hτ`) 전체 정확성이 준 `τ'` 와 가정의 `τ` 가
  --       같은 `some` 의 안이다. `Option.some.inj` 로 둘을 같게 만든다.
  sorry

""",
    ),
    (
        "Ch03/Spec.lean",
        "theorem totalCorrect_iff_partial_halts",
        "-- ANCHOR_END: haltsIff",
        """theorem totalCorrect_iff_partial_halts {p q : Assert V} {c : Comm V} :
    ［p］c［q］ ↔ ｛p｝c｛q｝ ∧ Halts p c := by
  -- 힌트 1: `→` 는 전체 정확성이 준 종료 상태로 두 성분을 각각 만든다. 종료 쪽은
  --         `simp [hτ]` 가 `isSome` 을 닫는다.
  -- 힌트 2: `←` 는 `Option.isSome_iff_exists` 로 종료 상태를 꺼낸 뒤 부분 정확성에 넣는다.
  sorry

""",
    ),
    # ── §3.2~3.6 건전성 — 규칙마다 하나
    (
        "Ch03/Soundness.lean",
        "theorem assign_sound",
        "-- ANCHOR_END: assignSound",
        """theorem assign_sound [HasFresh V] (q : Assert V) (v : V) (e : IntExp V) :
    ｛q /[v := e]｝(Comm.assign v e)｛q｝ := by
  -- 먼저 볼 것: §1.4 의 `substitution_single` (명제 1.4). 이 정리가 전부다.
  -- 힌트 1: `intro σ hp τ hτ` 뒤 `hτ` 는 정의상 `some (σ[v := ⟦e⟧ₑ σ]) = some τ` 다.
  --         `change` 로 드러내고 `Option.some.inj` 로 `τ` 를 없앤다.
  -- 힌트 2: 남는 목표가 `⟦q⟧ₐ (σ[v := ⟦e⟧ₑ σ])` 이고 가정이 `⟦q /[v := e]⟧ₐ σ` 다.
  sorry

""",
    ),
    (
        "Ch03/Soundness.lean",
        "theorem seq_sound",
        "-- ANCHOR_END: seqSound",
        """theorem seq_sound {p r q : Assert V} {c₀ c₁ : Comm V}
    (h₀ : ｛p｝c₀｛r｝) (h₁ : ｛r｝c₁｛q｝) : ｛p｝(Comm.seq c₀ c₁)｛q｝ := by
  -- 힌트 1: `⟦c₀ ; c₁⟧ᶜ σ` 는 정의상 `Option.bind (⟦c₀⟧ᶜ σ) ⟦c₁⟧ᶜ` 다 (`change … at hτ`).
  -- 힌트 2: `rcases h : ⟦c₀⟧ᶜ σ with _ | ρ` 로 나눈다. `none` 이면 `hτ` 가 모순이고,
  --         `some ρ` 면 `h₀` 가 `⟦r⟧ₐ ρ` 를, `h₁` 이 `⟦q⟧ₐ τ` 를 준다.
  sorry

""",
    ),
    (
        "Ch03/Soundness.lean",
        "theorem ite_sound",
        "-- ANCHOR_END: iteSound",
        """theorem ite_sound {p q : Assert V} {b : BoolExp V} {c₀ c₁ : Comm V}
    (h₀ : ｛p ⋀ b.toAssert｝c₀｛q｝) (h₁ : ｛p ⋀ .not b.toAssert｝c₁｛q｝) :
    ｛p｝(Comm.ite b c₀ c₁)｛q｝ := by
  -- 먼저 볼 것: §2.2 의 `boolExp_eval_iff`, 이 파일 위의 `Assert.eval_and` · `Assert.eval_not`.
  -- 힌트 1: `⟦if b then c₀ else c₁⟧ᶜ σ` 는 정의상 `if ⟦b⟧ᵇ σ then … else …` 다.
  -- 힌트 2: `by_cases hb : ⟦b⟧ᵇ σ = true` 로 나누고 `if_pos` / `if_neg` 로 가지를 고른다.
  -- 힌트 3: 각 가지의 사전조건 `p ⋀ …` 은 `hp` 와 `hb` 를 `boolExp_eval_iff` 로 합친 것이다.
  sorry

""",
    ),
    (
        "Ch03/Soundness.lean",
        "theorem wh_sound",
        "-- ANCHOR_END: whSound",
        """theorem wh_sound {i : Assert V} {b : BoolExp V} {c : Comm V}
    (hbody : ｛i ⋀ b.toAssert｝c｛i｝) : ｛i｝(Comm.wh b c)｛i ⋀ .not b.toAssert｝ := by
  -- 먼저 볼 것: §2.4 의 `scott_induction`, §3.1 의 `Sat.admissible` · `Sat.bot`,
  --            그리고 §2.5 의 `Comm.coincidence_general` — 같은 수법이다.
  -- 힌트 1: `⟦while b do c⟧ᶜ` 는 정의상 `fix (whileF b ⟦c⟧ᶜ) (whileF_monotone b ⟦c⟧ᶜ)` 다.
  --         목표를 `Sat ⟦i⟧ₐ (fix …) ⟦i ⋀ .not b.toAssert⟧ₐ` 로 `change` 한다.
  -- 힌트 2: `scott_induction (whileF_monotone b ⟦c⟧ᶜ) (P := fun w => Sat ⟦i⟧ₐ w ⟦…⟧ₐ)` 에
  --         세 의무를 준다 — 허용 가능(`Sat.admissible`), `⊥`(`Sat.bot`), 한 바퀴.
  -- 힌트 3: 한 바퀴에서 `whileF b ⟦c⟧ᶜ w σ` 를 `change` 로 펼치고, `⟦b⟧ᵇ σ = true` 로 나눈 뒤
  --         참이면 `rcases hc : ⟦c⟧ᶜ σ` — 본체가 끝난 상태에서 `hbody` 와 귀납 가설 `hw` 를 잇는다.
  sorry

""",
    ),
    (
        "Ch03/Soundness.lean",
        "theorem newvar_sound",
        "-- ANCHOR_END: newvarSound",
        """theorem newvar_sound {p q : Assert V} {v : V} {e : IntExp V} {c : Comm V}
    (hp : v ∉ p.fv) (hq : v ∉ q.fv) (he : v ∉ e.fv)
    (h : ｛p ⋀ .cmp .eq (.var v) e｝c｛q｝) : ｛p｝(Comm.newvar v e c)｛q｝ := by
  -- 먼저 볼 것: §1.4 의 `coincidence_assert` · `coincidence_intExp` (명제 1.1),
  --            `State.subst_self` · `State.subst_of_ne`.
  -- 힌트 1: `⟦newvar v := e in c⟧ᶜ σ` 는 정의상 `restore v σ (⟦c⟧ᶜ (σ[v := ⟦e⟧ₑ σ]))` 다.
  --         `rcases hc : ⟦c⟧ᶜ (σ[v := ⟦e⟧ₑ σ])` 로 나누고, `some ρ` 면
  --         `simp only [restore, Option.map_some, Option.some.injEq] at hτ` 로 `τ = ρ[v := σ v]`.
  -- 힌트 2: 안쪽 사전조건 두 조각 — `p` 는 `v` 를 안 보니 갱신해도 참(`hp`), `v = e` 는
  --         `State.subst_self` 와 `e` 가 `v` 를 안 본다는 것(`he`)으로.
  -- 힌트 3: 안쪽 결과 `⟦q⟧ₐ ρ` 에서 `v` 를 복원해도 `q` 는 `v` 를 안 본다(`hq`).
  sorry

""",
    ),
    # ── §3.3 대입 공리의 방향
    (
        "Ch03/Assign.lean",
        "theorem assign_forward_sound",
        "-- ANCHOR_END: assignForward",
        """theorem assign_forward_sound [HasFresh V] (p : Assert V) (v v₀ : V) (e : IntExp V)
    (h₀ : v₀ ∉ p.fv) (h₁ : v₀ ∉ e.fv) (h₂ : v₀ ≠ v) :
    ｛p｝(Comm.assign v e)｛floydPost p v v₀ e｝ := by
  -- 먼저 볼 것: `substitution_single` (명제 1.4) 와 식 판 `substitution_intExp`,
  --            `coincidence_assert` (명제 1.1), `Assert.eval_ex` · `Assert.eval_and` · `Assert.eval_eq`.
  -- 힌트 1: 대입 뒤 상태는 `σ[v := ⟦e⟧ₑ σ]` 다. `∃ v₀` 의 증인은 옛 값 `σ v` 다.
  -- 힌트 2: `p/v→v₀` 쪽 — `substitution_single` 로 뜻으로 옮기면 `p` 를 "`v` 에 옛 값을 도로
  --         넣은 상태" 에서 묻는다. 그 상태는 `p` 가 보는 변수들에서 `σ` 와 같다 (`h₀`, `h₂`).
  -- 힌트 3: `v = e/v→v₀` 쪽 — 왼쪽은 `State.subst_of_ne` · `State.subst_self` 로 `⟦e⟧ₑ σ`,
  --         오른쪽은 `substitution_intExp` 를 `σ` 와 새 상태 사이에 적용한다 (`h₁`, `h₂`).
  --         `w = v` 인지로 나눠 `Function.update_of_ne` · `IntExp.eval` 로 정리한다.
  sorry

""",
    ),
    (
        "Ch03/Assign.lean",
        "theorem floydPost_stronger",
        "-- ANCHOR_END: backwardOfForward",
        """theorem floydPost_stronger [HasFresh V] (q : Assert V) (v v₀ : V) (e : IntExp V)
    (h₀ : v₀ ∉ q.fv) (h₁ : v₀ ∉ e.fv) (h₂ : v₀ ≠ v) :
    Stronger (floydPost (q /[v := e] ) v v₀ e) q := by
  -- 먼저 볼 것: `assign_forward_sound` 의 힌트와 같은 도구들.
  -- 힌트 1: `Assert.eval_ex` 로 증인 `n` 을, `Assert.eval_and` 로 두 조각을 꺼낸다.
  -- 힌트 2: `v = e/v→v₀` 조각을 `IntExp.renameTo` 를 펼치고 `substitution_intExp` 로
  --         `τ v = ⟦e⟧ₑ (τ[v₀ := n][v := n])` 으로 읽는다.
  -- 힌트 3: `(q/v→e)/v→v₀` 조각에 `substitution_single` 을 두 번 쓰면 `q` 가
  --         `τ[v₀ := n][v := n][v := ⟦e⟧ₑ …]` 에서 참이고, 힌트 2 로 그 마지막 값이 `τ v` 다.
  -- 힌트 4: 그 상태는 `q` 가 보는 변수들에서 `τ` 와 같다 — `coincidence_assert` (`h₀`).
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
