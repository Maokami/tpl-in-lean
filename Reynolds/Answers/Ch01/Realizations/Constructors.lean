/-
Copyright (c) 2026 tpl-in-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: tpl-in-lean contributors
-/
module

public import Reynolds.Answers.Ch01.Realizations.Assertions

/-!
# 연습 1.3 — 접두 구 생성자의 단사성 (Reynolds p. 22)

식 (1.1)(p. 4)의 생성자마다, 결과가 같으면 인자도 같음을 보인다.
예를 들어 이항 생성자는 두 구의 목록을 이어 붙인다. 일반 목록에서는 연결 위치를
복원할 수 없지만, 실제 구의 접두사 자유성은 첫 인자가 끝나는 위치를 유일하게 정한다.

**책과의 차이**: 책은 구의 세계와 생성자도 직접 설계하라고 한다.
여기서는 앞 두 파일에 그 설계를 완성 자료로 주고, 모든 생성자의 단사성을 증명한다.
상수·변수 계열은 매개변수까지 구별하는 더 강한 단사성을 보인다.
논리 상수는 인자가 없으므로 정의역을 `Unit`으로 쓴다.

읽는 순서: `Realizations.lean` → `Assertions.lean` → 이 파일.
-/

@[expose] public section

namespace Reynolds.Answers.Ch01

/-- Reynolds 연습 1.3(p. 22). 식 (1.1)의 각 접두 구 생성자가 인자를 보존한다는 명세. -/
structure PrefixConstructorsInjective : Prop where
  /-- 정수 상수는 그 정수 값을 보존한다. -/
  num : Function.Injective PrefixPhrase.num
  /-- 변수는 그 이름을 보존한다. -/
  var : Function.Injective PrefixPhrase.var
  /-- 산술 부정은 인자 구를 보존한다. -/
  neg : Function.Injective PrefixPhrase.neg
  /-- 고정된 산술 연산자는 두 인자 구를 보존한다. -/
  intBin : ∀ op, Function.Injective (fun p : PrefixPhrase × PrefixPhrase =>
    PrefixPhrase.bin op p.1 p.2)
  /-- 인자가 없는 참 생성자. -/
  tru : Function.Injective (fun _ : Unit => AssertPrefixPhrase.tru)
  /-- 인자가 없는 거짓 생성자. -/
  fls : Function.Injective (fun _ : Unit => AssertPrefixPhrase.fls)
  /-- 고정된 비교 연산자는 두 정수 식 구를 보존한다. -/
  cmp : ∀ c, Function.Injective (fun p : PrefixPhrase × PrefixPhrase =>
    AssertPrefixPhrase.cmp c p.1 p.2)
  /-- 논리 부정은 인자 단언 구를 보존한다. -/
  not : Function.Injective AssertPrefixPhrase.not
  /-- 고정된 논리 연결자는 두 단언 구를 보존한다. -/
  logBin : ∀ op, Function.Injective (fun p : AssertPrefixPhrase × AssertPrefixPhrase =>
    AssertPrefixPhrase.bin op p.1 p.2)
  /-- 고정된 양화자는 변수 이름과 단언 구를 보존한다. -/
  quant : ∀ k, Function.Injective (fun p : String × AssertPrefixPhrase =>
    AssertPrefixPhrase.quant k p.1 p.2)

/-- Reynolds 연습 1.3(p. 22). 주어진 접두 구 세계의 모든 생성자가 단사임을 증명한다. -/
@[exercise "Ex 1.3" 3]
theorem prefixConstructors_injective : PrefixConstructorsInjective := by
  constructor
  · intro a b h
    simpa [PrefixPhrase.num] using congrArg Subtype.val h
  · intro a b h
    simpa [PrefixPhrase.var] using congrArg Subtype.val h
  · intro a b h
    apply Subtype.ext
    simpa [PrefixPhrase.neg] using congrArg Subtype.val h
  · intro op
    rintro ⟨⟨_, e, rfl⟩, ⟨_, f, rfl⟩⟩ ⟨⟨_, e', rfl⟩, ⟨_, f', rfl⟩⟩ h
    have ht : e.toPrefix ++ f.toPrefix = e'.toPrefix ++ f'.toPrefix := by
      simpa [PrefixPhrase.bin] using congrArg Subtype.val h
    obtain ⟨he, hf⟩ := IntExp.toPrefix_prefixFree e e' _ _ ht
    apply Prod.ext
    · exact Subtype.ext (congrArg IntExp.toPrefix he)
    · exact Subtype.ext hf
  · intro a b _
    exact Subsingleton.elim a b
  · intro a b _
    exact Subsingleton.elim a b
  · intro c
    rintro ⟨⟨_, e, rfl⟩, ⟨_, f, rfl⟩⟩ ⟨⟨_, e', rfl⟩, ⟨_, f', rfl⟩⟩ h
    have ht : e.toPrefix ++ f.toPrefix = e'.toPrefix ++ f'.toPrefix := by
      simpa [AssertPrefixPhrase.cmp] using congrArg Subtype.val h
    obtain ⟨he, hf⟩ := IntExp.toPrefix_prefixFree e e' _ _ ht
    apply Prod.ext
    · exact Subtype.ext (congrArg IntExp.toPrefix he)
    · exact Subtype.ext hf
  · intro a b h
    apply Subtype.ext
    simpa [AssertPrefixPhrase.not] using congrArg Subtype.val h
  · intro op
    rintro ⟨⟨_, p, rfl⟩, ⟨_, q, rfl⟩⟩ ⟨⟨_, p', rfl⟩, ⟨_, q', rfl⟩⟩ h
    have ht : p.toPrefix ++ q.toPrefix = p'.toPrefix ++ q'.toPrefix := by
      simpa [AssertPrefixPhrase.bin] using congrArg Subtype.val h
    obtain ⟨hp, hq⟩ := Assert.toPrefix_prefixFree p p' _ _ ht
    apply Prod.ext
    · exact Subtype.ext (congrArg Assert.toPrefix hp)
    · exact Subtype.ext hq
  · intro k a b h
    have ht := congrArg Subtype.val h
    simp only [AssertPrefixPhrase.quant, List.cons.injEq, Tok.var.injEq, true_and] at ht
    exact Prod.ext ht.1 (Subtype.ext ht.2)

end Reynolds.Answers.Ch01
