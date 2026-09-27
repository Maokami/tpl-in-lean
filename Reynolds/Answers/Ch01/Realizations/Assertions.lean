/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Answers.Ch01.Realizations

/-!
# 연습 1.3 — 단언의 접두 구문 세계 (Reynolds p. 22)

책이 가리키는 식 (1.1)(p. 4)은 정수 식과 단언의 생성자를 모두 포함한다.
`Realizations.lean`의 정수 식 토큰 열에 이어 단언의 토큰 열을 정의한다.
비교에는 정수 식 둘, 논리 연결에는 단언 둘, 양화에는 변수 토큰과 단언 하나가 온다.

토큰 열의 치역만 구로 인정하여 인자가 모자란 목록을 배제한다.
이 파일의 접두사 자유성은 다음 파일의 생성자 단사성 연습에 주는 완성 자료다.
책의 문자열 대신 구별되는 토큰을 쓰는 선택은 `Realizations.lean`과 같다.

읽는 순서: `Realizations.lean` → 이 파일 → `Constructors.lean`.
-/

@[expose] public section

namespace Reynolds.Answers.Ch01

/-- Reynolds 연습 1.3(p. 22). 식 (1.1)(p. 4)의 단언을 괄호 없는 접두 토큰 열로 나타낸다. -/
def Assert.toPrefix : Assert String → List Tok
  | .tru => [.truth true]
  | .fls => [.truth false]
  | .cmp c e f => .cmp c :: (e.toPrefix ++ f.toPrefix)
  | .not p => .assertNot :: p.toPrefix
  | .bin op p q => .log op :: (p.toPrefix ++ q.toPrefix)
  | .quant q v p => .quant q :: .var v :: p.toPrefix

/--
연습 1.3(p. 22)의 보조 자료. 단언의 접두 표기는 뒤에 붙인 토큰 열과 구별된다.
비교 절에서는 정수 식의 접두사 자유성을 두 번 쓰고, 나머지는 단언의 귀납 가설을 쓴다.
-/
theorem Assert.toPrefix_prefixFree :
    ∀ (p q : Assert String) (r s : List Tok),
      p.toPrefix ++ r = q.toPrefix ++ s → p = q ∧ r = s := by
  intro p
  induction p with
  | tru =>
      intro q r s h
      cases q with
      | tru => simpa [Assert.toPrefix] using h
      | fls | cmp _ _ _ | not _ | bin _ _ _ | quant _ _ _ => simp [Assert.toPrefix] at h
  | fls =>
      intro q r s h
      cases q with
      | fls => simpa [Assert.toPrefix] using h
      | tru | cmp _ _ _ | not _ | bin _ _ _ | quant _ _ _ => simp [Assert.toPrefix] at h
  | cmp c e f =>
      intro q r s h
      cases q with
      | cmp c' e' f' =>
          simp only [Assert.toPrefix, List.cons_append, List.append_assoc] at h
          injection h with hc ht
          injection hc with hcc
          subst c'
          obtain ⟨he, hr⟩ := IntExp.toPrefix_prefixFree e e' _ _ ht
          obtain ⟨hf, hs⟩ := IntExp.toPrefix_prefixFree f f' _ _ hr
          exact ⟨by rw [he, hf], hs⟩
      | tru | fls | not _ | bin _ _ _ | quant _ _ _ => simp [Assert.toPrefix] at h
  | not p ih =>
      intro q r s h
      cases q with
      | not q =>
          simp only [Assert.toPrefix, List.cons_append] at h
          injection h with _ ht
          obtain ⟨hp, hr⟩ := ih q r s ht
          exact ⟨by rw [hp], hr⟩
      | tru | fls | cmp _ _ _ | bin _ _ _ | quant _ _ _ => simp [Assert.toPrefix] at h
  | bin op p q ihp ihq =>
      intro a r s h
      cases a with
      | bin op' p' q' =>
          simp only [Assert.toPrefix, List.cons_append, List.append_assoc] at h
          injection h with hop ht
          injection hop with hopp
          subst op'
          obtain ⟨hp, hr⟩ := ihp p' _ _ ht
          obtain ⟨hq, hs⟩ := ihq q' _ _ hr
          exact ⟨by rw [hp, hq], hs⟩
      | tru | fls | cmp _ _ _ | not _ | quant _ _ _ => simp [Assert.toPrefix] at h
  | quant k v p ih =>
      intro q r s h
      cases q with
      | quant k' v' q =>
          simp only [Assert.toPrefix, List.cons_append] at h
          injection h with hk ht
          injection hk with hkk
          injection ht with hv hp
          injection hv with hvv
          obtain ⟨hq, hr⟩ := ih q r s hp
          exact ⟨by rw [hkk, hvv, hq], hr⟩
      | tru | fls | cmp _ _ _ | not _ | bin _ _ _ => simp [Assert.toPrefix] at h

/-- 연습 1.3(p. 22)의 보조 자료. 서로 다른 단언은 서로 다른 접두 토큰 열을 만든다. -/
theorem Assert.toPrefix_injective : Function.Injective Assert.toPrefix := by
  intro p q h
  exact (Assert.toPrefix_prefixFree p q [] [] (by simpa using h)).1

/-- Reynolds 연습 1.3(p. 22)의 단언 구문 세계. 실제 단언을 표현하는 토큰 열만 포함한다. -/
def AssertPrefixPhrase := {xs : List Tok // ∃ p : Assert String, p.toPrefix = xs}

namespace AssertPrefixPhrase

/-- 식 (1.1)(p. 4)의 참 생성자. -/
def tru : AssertPrefixPhrase := ⟨[.truth true], ⟨.tru, rfl⟩⟩

/-- 식 (1.1)(p. 4)의 거짓 생성자. -/
def fls : AssertPrefixPhrase := ⟨[.truth false], ⟨.fls, rfl⟩⟩

/-- 식 (1.1)(p. 4)의 비교 생성자. 두 정수 식 구를 단언 구로 보낸다. -/
def cmp (c : Cmp) (x y : PrefixPhrase) : AssertPrefixPhrase := by
  refine ⟨.cmp c :: (x.val ++ y.val), ?_⟩
  obtain ⟨e, he⟩ := x.property
  obtain ⟨f, hf⟩ := y.property
  exact ⟨.cmp c e f, by rw [Assert.toPrefix, he, hf]⟩

/-- 식 (1.1)(p. 4)의 단언 부정 생성자. -/
def not (x : AssertPrefixPhrase) : AssertPrefixPhrase := by
  refine ⟨.assertNot :: x.val, ?_⟩
  obtain ⟨p, hp⟩ := x.property
  exact ⟨.not p, by rw [Assert.toPrefix, hp]⟩

/-- 식 (1.1)(p. 4)의 이항 논리 생성자. -/
def bin (op : LogOp) (x y : AssertPrefixPhrase) : AssertPrefixPhrase := by
  refine ⟨.log op :: (x.val ++ y.val), ?_⟩
  obtain ⟨p, hp⟩ := x.property
  obtain ⟨q, hq⟩ := y.property
  exact ⟨.bin op p q, by rw [Assert.toPrefix, hp, hq]⟩

/-- 식 (1.1)(p. 4)의 양화 생성자. 변수 이름도 구문의 일부로 보존한다. -/
def quant (k : Quant) (v : String) (x : AssertPrefixPhrase) : AssertPrefixPhrase := by
  refine ⟨.quant k :: .var v :: x.val, ?_⟩
  obtain ⟨p, hp⟩ := x.property
  exact ⟨.quant k v p, by rw [Assert.toPrefix, hp]⟩

end AssertPrefixPhrase

/-- 연습 1.3(p. 22)의 단언을 그 접두 구로 보낸다. -/
def Assert.toPrefixPhrase (p : Assert String) : AssertPrefixPhrase :=
  ⟨p.toPrefix, ⟨p, rfl⟩⟩

/-- 연습 1.3(p. 22)의 단언 구문 세계에는 누락이나 쓰레기 구가 없다. -/
theorem Assert.toPrefixPhrase_bijective : Function.Bijective Assert.toPrefixPhrase := by
  constructor
  · intro p q h
    exact Assert.toPrefix_injective (congrArg Subtype.val h)
  · rintro ⟨xs, p, hp⟩
    exact ⟨p, Subtype.ext hp⟩

end Reynolds.Answers.Ch01
