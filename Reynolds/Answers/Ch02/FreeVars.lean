/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Answers.Ch02.Interpreter
public import Reynolds.Answers.Ch01.FreeVars

/-!
# §2.5 자유 변수 (1) — 두 종류의 자유 변수와 명제 2.6

Reynolds §2.5 전반부에 대응한다. 치환과 별칭(aliasing)은 다음 파일이다.

## 자유 변수가 둘로 갈라진다

1장에서 자유 변수는 하나의 집합이었다. 명령형 언어에서는 변수를 **읽는** 일과 **쓰는**
일이 다르고, 그래서 집합이 둘이 된다.

- `FV(c)` — 명령이 읽거나 쓰는 변수 전부
- `FA(c)` — 명령이 **대입하는**(assign) 변수. `FA(c) ⊆ FV(c)`

구분이 값을 하는 자리가 명제 2.6(b)다. `c` 를 실행해도 `FA(c)` 밖의 변수는 그대로다 —
"이 명령은 그 변수를 안 건드린다" 를 문장으로 만들려면 읽기와 쓰기를 갈라야 한다.
§2.6 의 `for` 제약(제어 변수에 대입하지 말 것)도 `FA` 로 쓴다.

## 명제 2.6 — 일치 정리가 복잡해지는 이유

1장의 일치 정리는 "자유 변수 위에서 같으면 뜻이 같다" 한 줄이었다. 여기서는 비종료 때문에
결과가 `Σ⊥` 라서, "같다" 를 두 경우로 나눠 말해야 한다 — 둘 다 `⊥` 이거나, 둘 다 상태이고
그 상태들이 다시 자유 변수 위에서 같다. 그 관계가 `AgreeOn` 이다.

증명에는 두 가지 새 도구가 든다.

- **진술 강화.** `FV(c)` 위에서의 일치만으로는 `seq` 케이스가 돌지 않는다.
  `c₀` 를 지난 상태들은 `FV(c₀)` 위에서만 일치한다고 알게 되는데, `c₁` 은
  `FV(c₁) \ FV(c₀)` 의 변수도 읽기 때문이다. 진술을 "임의의 `S ⊇ FV(c)` 위에서" 로
  올리면 그 간극이 사라진다. 1장 §1.4 에서 상태를 `∀` 로 묶어야 했던 것과 같은 종류의
  일반화이고, 이번에는 집합을 묶는다.
- **Scott 귀납법.** `while` 케이스는 `fix` 에 대한 주장이므로 성질이 극한을 통과해야
  한다. `AgreeOn` 이 허용 가능하다는 것은 `Σ⊥` 의 평평함에서 나온다 — 두 극한이 각각
  어느 단계에서 이미 결정되어 있으므로, 극한끼리의 주장이 한 단계끼리의 주장으로 내려온다.

## 읽는 순서
`Interpreter.lean` → 이 파일 → `Substitution.lean` (치환과 별칭)
-/

@[expose] public section

namespace Reynolds.Answers.Ch02

open Reynolds Reynolds.Answers.Ch01

universe u

variable {V : Type u} [DecidableEq V]

/-! ## 1. 불 식의 자유 변수

단언에서 양화사를 뺐으므로 결합자가 없고, 나오는 변수를 모으면 끝난다.
일치 정리도 1장의 정수 식 판을 그대로 잇는다. -/

/-- `FV(b)` — 불 식의 자유 변수. 결합자가 없어 `erase` 가 나오지 않는다. -/
def BoolExp.fv : BoolExp V → Finset V
  | .tru | .fls   => ∅
  | .cmp _ e₀ e₁  => e₀.fv ∪ e₁.fv
  | .not b        => b.fv
  | .bin _ b₀ b₁  => b₀.fv ∪ b₁.fv

/-- 불 식 판 일치 정리. 정수 식 판(1장 명제 1.1)을 절마다 이어 붙인다. -/
theorem BoolExp.fv_coincidence :
    ∀ (b : BoolExp V) (σ σ' : State V), (∀ w ∈ b.fv, σ w = σ' w) → ⟦b⟧ᵇ σ = ⟦b⟧ᵇ σ' := by
  intro b
  induction b with
  | tru => intro _ _ _; rfl
  | fls => intro _ _ _; rfl
  | cmp c e₀ e₁ =>
      intro σ σ' h
      have h₀ := coincidence_intExp e₀ σ σ' fun w hw => h w (by simp [BoolExp.fv, hw])
      have h₁ := coincidence_intExp e₁ σ σ' fun w hw => h w (by simp [BoolExp.fv, hw])
      simp [BoolExp.eval, h₀, h₁]
  | not b ih => intro σ σ' h; simp [BoolExp.eval, ih σ σ' h]
  | bin op b₀ b₁ ih₀ ih₁ =>
      intro σ σ' h
      have h₀ := ih₀ σ σ' fun w hw => h w (by simp [BoolExp.fv, hw])
      have h₁ := ih₁ σ σ' fun w hw => h w (by simp [BoolExp.fv, hw])
      simp [BoolExp.eval, h₀, h₁]

/-! ## 2. 명령의 자유 변수 — 읽는 것과 쓰는 것 -/

-- ANCHOR: fvFa
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
-- ANCHOR_END: fvFa

-- ANCHOR: faSubset
/--
**쓰는 변수는 읽거나 쓰는 변수다.** `FA(c) ⊆ FV(c)`.

절마다 확인하는 계산이다. `newvar` 절에서 `erase` 끼리의 포함이 필요하다.
-/
@[exercise "§2.5 fa-subset" 1]
theorem Comm.fa_subset_fv : ∀ c : Comm V, c.fa ⊆ c.fv := by
  intro c
  induction c with
  | assign v e => simp [Comm.fa, Comm.fv]
  | «skip» => simp [Comm.fa, Comm.fv]
  | seq c₀ c₁ ih₀ ih₁ =>
      exact Finset.union_subset_union ih₀ ih₁
  | ite b c₀ c₁ ih₀ ih₁ =>
      refine Finset.union_subset ?_ ?_
      · exact le_trans ih₀
          (le_trans Finset.subset_union_right Finset.subset_union_left)
      · exact le_trans ih₁ Finset.subset_union_right
  | wh b c ih =>
      exact le_trans ih Finset.subset_union_right
  | «newvar» v e c ih =>
      exact le_trans (Finset.erase_subset_erase v ih) Finset.subset_union_right
-- ANCHOR_END: faSubset

/-! ## 3. `AgreeOn` — 비종료가 있는 "같다"

`Σ⊥` 값 둘이 집합 `S` 위에서 일치한다는 관계다. 둘 다 `⊥` 이거나,
둘 다 상태이고 `S` 의 모든 변수에서 같은 값을 갖거나. 하나만 `⊥` 인 경우는 거짓이다. -/

-- ANCHOR: agreeOn
/-- `S` 위에서의 일치. 명제 2.6 의 결론을 담는 관계다. -/
def AgreeOn (S : Finset V) : SigmaBot V → SigmaBot V → Prop
  | none,   none    => True
  | some τ, some τ' => ∀ w ∈ S, τ w = τ' w
  | _,      _       => False
-- ANCHOR_END: agreeOn

omit [DecidableEq V] in
@[simp] theorem AgreeOn.none_none {S : Finset V} : AgreeOn S none none := trivial

omit [DecidableEq V] in
@[simp] theorem AgreeOn.some_some {S : Finset V} {τ τ' : State V} :
    AgreeOn S (some τ) (some τ') ↔ ∀ w ∈ S, τ w = τ' w := Iff.rfl

omit [DecidableEq V] in
@[simp] theorem AgreeOn.none_some {S : Finset V} {τ : State V} :
    ¬ AgreeOn S none (some τ) := fun h => h

omit [DecidableEq V] in
@[simp] theorem AgreeOn.some_none {S : Finset V} {τ : State V} :
    ¬ AgreeOn S (some τ) none := fun h => h

/-! ## 4. `AgreeOn` 은 허용 가능하다

`while` 케이스의 Scott 귀납법이 요구하는 것이다. 두 함수 사슬을 같은 상태쌍에서 보면
`Σ⊥` 사슬 둘이 나오는데, 평평함 때문에 각 극한은 어느 단계에서 이미 결정되어 있다.
두 결정 시점보다 뒤의 공통 단계 하나를 잡으면, 극한끼리의 일치가 그 단계에서의 일치로
내려온다. -/

-- ANCHOR: agreeAdmissible
omit [DecidableEq V] in
/--
**`AgreeOn` 은 극한을 통과한다.**

극한이 `⊥` 인 쪽은 모든 단계가 `⊥` 였다는 뜻이고, 단계별 일치가 반대쪽도 전부 `⊥` 로
만든다. 극한이 상태인 쪽은 어느 단계 `k` 가 이미 그 상태다 — 평평한 사슬은 멈추므로
(`Chain.flat_stabilizes`) 그 뒤 어느 단계에서 봐도 같은 상태이고, 반대쪽 결정 시점과의
최댓값에서 두 극한을 함께 읽으면 된다.

허용 가능성이 공짜가 아니라던 `Fixpoint.lean` 의 경고와 나란히 두고 볼 것 —
이 성질이 통과하는 이유는 순전히 `Σ⊥` 가 평평해서다.
-/
@[exercise "§2.5 agree-admissible" 2]
theorem AgreeOn.admissible (S : Finset V) (d : Chain (State V → SigmaBot V))
    {σ σ' : State V} (h : ∀ n, AgreeOn S (d.seq n σ) (d.seq n σ')) :
    AgreeOn S (d.lub σ) (d.lub σ') := by
  rw [Chain.lub_apply, Chain.lub_apply]
  rcases hσ : (d.apply σ).lub with _ | τ
  · -- 왼쪽 극한이 `⊥` — 왼쪽 사슬이 전부 `⊥` 였고, 일치가 오른쪽도 전부 `⊥` 로 만든다.
    have hall : ∀ n, d.seq n σ' = none := by
      intro n
      have hn := (d.apply σ).le_lub n
      rw [hσ] at hn
      simp only [Option.le_none_iff, Chain.apply_seq] at hn
      have := h n
      rw [hn] at this
      rcases hn' : d.seq n σ' with _ | τ'
      · rfl
      · rw [hn'] at this; exact absurd this (by simp)
    have : (d.apply σ').lub ≤ none :=
      (d.apply σ').lub_le fun n => by rw [Chain.apply_seq, hall n]
    simp only [Option.le_none_iff] at this
    rw [this]
    simp
  · -- 왼쪽 극한이 상태 — 결정 시점 둘의 최댓값에서 두 극한을 함께 읽는다.
    obtain ⟨k, hk⟩ := (d.apply σ).flat_lub_mem_range
    rw [hσ] at hk
    rcases hσ' : (d.apply σ').lub with _ | τ'
    · -- 오른쪽만 `⊥` 일 수는 없다. 단계 `k` 에서 왼쪽이 이미 상태인데,
      -- 오른쪽 사슬이 전부 `⊥` 면 단계 `k` 의 일치가 거짓이 된다.
      have hk' : d.seq k σ' = none := by
        have hn := (d.apply σ').le_lub k
        rw [hσ'] at hn
        simpa using hn
      have := h k
      rw [show d.seq k σ = some τ from hk, hk'] at this
      exact absurd this (by simp)
    · obtain ⟨k', hk'⟩ := (d.apply σ').flat_lub_mem_range
      rw [hσ'] at hk'
      -- 공통 단계 `m` 에서는 양쪽 다 극한값이다.
      have hm : d.seq (max k k') σ = some τ :=
        Chain.flat_stabilizes (c := d.apply σ) hk (max k k') (le_max_left _ _)
      have hm' : d.seq (max k k') σ' = some τ' :=
        Chain.flat_stabilizes (c := d.apply σ') hk' (max k k') (le_max_right _ _)
      have := h (max k k')
      rw [hm, hm'] at this
      exact this
-- ANCHOR_END: agreeAdmissible

/-! ## 5. 명제 2.6

두 부분이다. (a) 입력이 일치하면 출력이 일치한다. (b) `FA(c)` 밖의 변수는 변하지 않는다.

(a) 는 `FV(c)` 가 아니라 **임의의 `S ⊇ FV(c)`** 로 강화해서 증명한다. 파일 첫머리에
적었듯 `seq` 케이스가 그 강화를 요구한다 — 무엇이 막히는지 보려면 `S := c.fv` 로
고정하고 `seq` 절을 직접 시도해 보라. `c₀` 의 귀납 가설이 주는 일치가 `FV(c₀)` 위뿐이라
`c₁` 이 읽는 나머지 변수를 잇지 못한다. -/

/-- 상태 갱신은 일치를 보존한다. (a) 의 `assign` 절과 `newvar` 절이 쓴다. -/
theorem agree_update {S : Finset V} {σ σ' : State V} (h : ∀ w ∈ S, σ w = σ' w)
    (v : V) (n : Int) : ∀ w ∈ insert v S, σ[v := n] w = σ'[v := n] w := by
  intro w hw
  by_cases hwv : w = v
  · subst hwv; simp
  · have : w ∈ S := by
      rcases Finset.mem_insert.mp hw with h' | h'
      · exact absurd h' hwv
      · exact h'
    simp [hwv, h w this]

-- ANCHOR: prop26a
/--
**명제 2.6(a), 강화판** — `S ⊇ FV(c)` 위에서 일치하는 두 상태에서 `c` 를 돌리면,
결과도 `S` 위에서 일치한다 (둘 다 `⊥` 이거나, 둘 다 상태로).

채점 연습이 아니다. 증명이 1장의 일치 정리(명제 1.1)와 Scott 귀납법 위에 서 있고,
둘 다 이미 연습이라 비우면 비운 것끼리 의존한다 (연습 독립성 원칙). 대신 `while` 절이
Scott 귀납법과 `AgreeOn.admissible` 이 실제로 맞물리는 자리이니 완성본으로 읽어 두면
연습 2.5 와 2.6 에서 그대로 쓴다.
-/
theorem Comm.coincidence_general :
    ∀ (c : Comm V) (S : Finset V), c.fv ⊆ S →
      ∀ σ σ' : State V, (∀ w ∈ S, σ w = σ' w) → AgreeOn S (c.eval σ) (c.eval σ') := by
  intro c
  induction c with
  | assign v e =>
      intro S hS σ σ' h
      change AgreeOn S (some _) (some _)
      have he : ⟦e⟧ₑ σ = ⟦e⟧ₑ σ' :=
        coincidence_intExp e σ σ' fun w hw =>
          h w (hS (by simp [Comm.fv, hw]))
      rw [AgreeOn.some_some, he]
      intro w hw
      exact agree_update h v (⟦e⟧ₑ σ') w (Finset.mem_insert_of_mem hw)
  | «skip» =>
      intro S _ σ σ' h
      exact h
  | seq c₀ c₁ ih₀ ih₁ =>
      intro S hS σ σ' h
      have hS₀ : c₀.fv ⊆ S := le_trans Finset.subset_union_left hS
      have hS₁ : c₁.fv ⊆ S := le_trans Finset.subset_union_right hS
      change AgreeOn S (Option.bind (c₀.eval σ) c₁.eval) (Option.bind (c₀.eval σ') c₁.eval)
      have h₀ := ih₀ S hS₀ σ σ' h
      rcases h₀₁ : c₀.eval σ with _ | τ <;> rcases h₀₂ : c₀.eval σ' with _ | τ'
      · simp
      · rw [h₀₁, h₀₂] at h₀; exact absurd h₀ (by simp)
      · rw [h₀₁, h₀₂] at h₀; exact absurd h₀ (by simp)
      · rw [h₀₁, h₀₂] at h₀
        exact ih₁ S hS₁ τ τ' h₀
  | ite b c₀ c₁ ih₀ ih₁ =>
      intro S hS σ σ' h
      have hb : ⟦b⟧ᵇ σ = ⟦b⟧ᵇ σ' :=
        BoolExp.fv_coincidence b σ σ' fun w hw =>
          h w (hS (by simp [Comm.fv, hw]))
      change AgreeOn S (if ⟦b⟧ᵇ σ then _ else _) (if ⟦b⟧ᵇ σ' then _ else _)
      rw [← hb]
      by_cases hbσ : ⟦b⟧ᵇ σ
      · simp only [if_pos hbσ]
        exact ih₀ S (le_trans (le_trans Finset.subset_union_left
          Finset.subset_union_right) (by simpa [Comm.fv, Finset.union_assoc] using hS)) σ σ' h
      · simp only [if_neg hbσ]
        exact ih₁ S (le_trans Finset.subset_union_right hS) σ σ' h
  | wh b c ihc =>
      intro S hS σ σ' h
      have hSb : b.fv ⊆ S := le_trans Finset.subset_union_left hS
      have hSc : c.fv ⊆ S := le_trans Finset.subset_union_right hS
      -- Scott 귀납법. 성질: 일치하는 입력쌍을 일치하는 출력쌍으로 보낸다.
      have key := scott_induction (whileF_monotone b c.eval)
        (P := fun w => ∀ σ σ' : State V,
          (∀ v ∈ S, σ v = σ' v) → AgreeOn S (w σ) (w σ'))
        (fun d hd σ σ' hσσ' => AgreeOn.admissible S d fun n => hd n σ σ' hσσ')
        (fun _ _ _ => AgreeOn.none_none)
        (fun w hw σ σ' hσσ' => by
          have hb : ⟦b⟧ᵇ σ = ⟦b⟧ᵇ σ' :=
            BoolExp.fv_coincidence b σ σ' fun v hv => hσσ' v (hSb hv)
          change AgreeOn S (if ⟦b⟧ᵇ σ then _ else _) (if ⟦b⟧ᵇ σ' then _ else _)
          rw [← hb]
          by_cases hbσ : ⟦b⟧ᵇ σ
          · simp only [if_pos hbσ]
            have hbody := ihc S hSc σ σ' hσσ'
            rcases h₁ : c.eval σ with _ | τ <;> rcases h₂ : c.eval σ' with _ | τ'
            · simp
            · rw [h₁, h₂] at hbody; exact absurd hbody (by simp)
            · rw [h₁, h₂] at hbody; exact absurd hbody (by simp)
            · rw [h₁, h₂] at hbody
              exact hw τ τ' hbody
          · simp only [if_neg hbσ]
            exact hσσ')
      exact key σ σ' h
  | «newvar» v e c ih =>
      intro S hS σ σ' h
      have he : ⟦e⟧ₑ σ = ⟦e⟧ₑ σ' :=
        coincidence_intExp e σ σ' fun w hw =>
          h w (hS (by simp [Comm.fv, hw]))
      change AgreeOn S (restore v σ (c.eval (σ[v := ⟦e⟧ₑ σ])))
                       (restore v σ' (c.eval (σ'[v := ⟦e⟧ₑ σ'])))
      -- 안쪽은 `S ∪ {v}` 위에서 돌린다. 갱신된 두 상태가 거기서 일치한다.
      have hin : c.fv ⊆ insert v S := by
        intro w hw
        by_cases hwv : w = v
        · subst hwv; exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem
            (hS (by simp [Comm.fv, Finset.mem_erase, hwv, hw]))
      have hupd : ∀ w ∈ insert v S, σ[v := ⟦e⟧ₑ σ] w = σ'[v := ⟦e⟧ₑ σ'] w := by
        rw [he]; exact agree_update h v (⟦e⟧ₑ σ')
      have hinner := ih (insert v S) hin _ _ hupd
      rcases h₁ : c.eval (σ[v := ⟦e⟧ₑ σ]) with _ | τ
        <;> rcases h₂ : c.eval (σ'[v := ⟦e⟧ₑ σ']) with _ | τ'
      · simp [restore]
      · rw [h₁, h₂] at hinner; exact absurd hinner (by simp)
      · rw [h₁, h₂] at hinner; exact absurd hinner (by simp)
      · rw [h₁, h₂] at hinner
        simp only [restore, Option.map_some]
        rw [AgreeOn.some_some]
        intro w hw
        by_cases hwv : w = v
        · subst hwv; simp [h _ hw]
        · simp only [State.subst_of_ne _ _ _ _ hwv]
          exact hinner w (Finset.mem_insert_of_mem hw)
-- ANCHOR_END: prop26a

/-- **명제 2.6(a), Reynolds 의 진술** — `FV(c)` 위에서 일치하면 결과도 일치한다. -/
theorem Comm.coincidence (c : Comm V) (σ σ' : State V)
    (h : ∀ w ∈ c.fv, σ w = σ' w) : AgreeOn c.fv (c.eval σ) (c.eval σ') :=
  Comm.coincidence_general c c.fv (le_refl _) σ σ' h

-- ANCHOR: prop26b
/--
**명제 2.6(b)** — 명령은 `FA(c)` 밖의 변수를 건드리지 않는다.

`c` 가 끝났다면, 대입 목록에 없는 변수의 값은 입력 그대로다.
`while` 절은 (a) 와 같은 모양의 Scott 귀납법인데 성질이 더 단순하다 —
사슬 하나만 보면 되고, 극한이 상태면 어느 단계가 이미 그 상태라는 것으로 끝난다.
-/
theorem Comm.eval_agree_outside_fa :
    ∀ (c : Comm V) (σ τ : State V), c.eval σ = some τ →
      ∀ w, w ∉ c.fa → τ w = σ w := by
  intro c
  induction c with
  | assign v e =>
      intro σ τ h w hw
      have : τ = σ[v := ⟦e⟧ₑ σ] := by
        have : some (σ[v := ⟦e⟧ₑ σ]) = some τ := h
        exact (Option.some.injEq _ _ ▸ this).symm
      subst this
      have hwv : w ≠ v := by simpa [Comm.fa] using hw
      simp [hwv]
  | «skip» =>
      intro σ τ h w _
      have : σ = τ := by
        have : some σ = some τ := h
        exact Option.some.injEq _ _ ▸ this
      rw [← this]
  | seq c₀ c₁ ih₀ ih₁ =>
      intro σ τ h w hw
      change Option.bind (c₀.eval σ) c₁.eval = some τ at h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨τ₀, h₀, h₁⟩ := h
      have hw₀ : w ∉ c₀.fa := fun hmem => hw (by simp [Comm.fa, hmem])
      have hw₁ : w ∉ c₁.fa := fun hmem => hw (by simp [Comm.fa, hmem])
      rw [ih₁ τ₀ τ h₁ w hw₁, ih₀ σ τ₀ h₀ w hw₀]
  | ite b c₀ c₁ ih₀ ih₁ =>
      intro σ τ h w hw
      change (if ⟦b⟧ᵇ σ then c₀.eval σ else c₁.eval σ) = some τ at h
      have hw₀ : w ∉ c₀.fa := fun hmem => hw (by simp [Comm.fa, hmem])
      have hw₁ : w ∉ c₁.fa := fun hmem => hw (by simp [Comm.fa, hmem])
      by_cases hb : ⟦b⟧ᵇ σ
      · rw [if_pos hb] at h; exact ih₀ σ τ h w hw₀
      · rw [if_neg hb] at h; exact ih₁ σ τ h w hw₁
  | wh b c ihc =>
      intro σ τ heval w hw
      have hwc : w ∉ c.fa := by simpa [Comm.fa] using hw
      have key := scott_induction (whileF_monotone b c.eval)
        (P := fun w' => ∀ σ τ : State V, w' σ = some τ → τ w = σ w)
        (fun d hd σ τ hlub => by
          -- 극한이 상태면 어느 단계가 이미 그 상태다.
          rw [Chain.lub_apply] at hlub
          obtain ⟨k, hk⟩ := (d.apply σ).flat_lub_mem_range
          rw [hlub] at hk
          exact hd k σ τ hk)
        (fun σ τ h => by simp at h)
        (fun w' hw' σ τ h => by
          change (if ⟦b⟧ᵇ σ then Option.bind (c.eval σ) w' else some σ) = some τ at h
          by_cases hb : ⟦b⟧ᵇ σ
          · rw [if_pos hb, Option.bind_eq_some_iff] at h
            obtain ⟨τ₀, h₀, h₁⟩ := h
            rw [hw' τ₀ τ h₁, ihc σ τ₀ h₀ w hwc]
          · rw [if_neg hb] at h
            have : σ = τ := Option.some.injEq _ _ ▸ h
            rw [← this])
      exact key σ τ heval
  | «newvar» v e c ih =>
      intro σ τ h w hw
      change restore v σ (c.eval (σ[v := ⟦e⟧ₑ σ])) = some τ at h
      rcases hc : c.eval (σ[v := ⟦e⟧ₑ σ]) with _ | τ₀
      · rw [hc] at h; simp [restore] at h
      · rw [hc] at h
        simp only [restore, Option.map_some, Option.some.injEq] at h
        subst h
        by_cases hwv : w = v
        · subst hwv; simp
        · simp only [State.subst_of_ne _ _ _ _ hwv]
          have hwfa : w ∉ c.fa := by
            intro hmem
            exact hw (by simp [Comm.fa, Finset.mem_erase, hwv, hmem])
          rw [ih _ _ hc w hwfa]
          simp [hwv]
-- ANCHOR_END: prop26b

/-! ## 6. 여기서 어디로 가나

읽기와 쓰기가 갈라졌고, 그 구분 위에서 일치 정리가 다시 섰다. (b) 가 특히 다음 파일의
재료다 — "이 명령은 그 변수를 안 건드린다" 가 문장이 되었으므로, 이제 **건드리면 안 되는
변수를 건드리게 만드는 치환** 이 무엇을 깨뜨리는지 물을 수 있다. 그것이 별칭(aliasing)이고,
명령의 치환 정리가 1장과 달리 조건부로만 성립하는 이유다. -/

end Reynolds.Answers.Ch02
