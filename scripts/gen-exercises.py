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
SHARED = {"Ch01/Notation.lean"}

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
        "Ch01/Realizations.lean", "theorem IntExp.toPrefix_injective", "/-! ## 왜 이것이",
        """theorem IntExp.toPrefix_injective : Function.Injective IntExp.toPrefix := by
  -- 먼저 볼 것: 바로 위 `toPrefix_prefixFree` (완성본).
  -- 힌트: 꼬리를 빈 열로 넣고 `simpa` 로 `++ []` 를 정리하면 된다.
  sorry

""",
    ),
]


def transform(text: str, blanks: list[tuple[str, str, str]]) -> str:
    """이름공간 치환 · ANCHOR 제거 · 증명 비우기."""
    out = text.replace("Reynolds.Answers.Ch01", "Reynolds.Exercises.Ch01")
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
