# 연습 푸는 법

`Reynolds/Exercises/` 의 `sorry` 를 채울 때 읽는 문서다.
Lean 자체 입문서가 아니라, **이 저장소에서 반복해 나오는 패턴**을 모아 둔 것이다.

Lean 이 처음이면 [Functional Programming in Lean](https://lean-lang.org/functional_programming_in_lean/)
과 [Theorem Proving in Lean](https://lean-lang.org/theorem_proving_in_lean4/) 을 먼저 훑어라.
여기서는 그 지식을 가정한다.

---

## 시작하기

1. VS Code 에서 `Reynolds/Exercises/Ch01/…` 를 연다
2. `sorry` 에 커서를 놓는다
3. 오른쪽 패널의 목표(goal)를 읽는다 — 가로선 위가 가진 것, 아래가 보여야 할 것
4. 한 줄씩 쓰고 목표가 어떻게 바뀌는지 본다

목표 패널이 안 보이면 아무것도 못 한다. 그것부터 띄워라.

확인:

```bash
lake exe grade --chapter 1
```

---

## 이 저장소가 반복하는 패턴 넷

### 1. 구조적 귀납법과 `∀` 일반화

가장 자주 나오고, 가장 자주 막히는 자리다.

`FreeVars.lean` 의 일치 정리를 보면 진술이 이렇게 생겼다.

```lean
∀ (p : Assert V) (σ σ' : State V), (∀ w ∈ p.fv, σ w = σ' w) → (⟦p⟧ₐ σ ↔ ⟦p⟧ₐ σ')
```

`σ σ'` 를 `theorem` 의 인자로 빼지 않고 `∀` 안에 둔 것이 핵심이다.
인자로 빼면 귀납 가설이 **그 특정 상태에만** 붙는다. 그런데 `∀v. p` 케이스에서는
귀납 가설을 `σ`, `σ'` 가 아니라 `σ[v := n]`, `σ'[v := n]` 에 써야 한다.

증명은 이렇게 시작한다.

```lean
  intro p
  induction p with
  | tru | fls => intro _ _ _; rfl
  | quant q v p ih =>
      intro σ σ' h
      -- 여기서 `ih` 를 갱신된 상태에 적용한다
```

**막혔을 때 자문할 것**: 귀납 가설이 지금 필요한 형태로 되어 있나?
아니면 진술을 더 일반화해야 하나?

이 패턴은 1장에서만 여섯 번 나온다. 한 번 익히면 나머지가 따라온다.

### 2. 상태 갱신

`σ[v := n]` 은 CSlib 의 표기이고 타입클래스 프로젝션이라 그냥은 안 풀린다.
`Prelude.lean` 에 `@[simp]` 보조정리 둘을 놓아 두었다.

```lean
State.subst_self  : σ[v := n] v = n
State.subst_of_ne : w ≠ v → σ[v := n] w = σ w
```

둘 다 `simp` 세트에 있으므로, `w = v` 인지 아닌지만 갈라 주면 된다.

```lean
  by_cases hwv : w = v
  · subst hwv; simp          -- 덮어쓴 자리
  · simp [hwv, ...]          -- 그 밖
```

### 3. `Finset` 소속 쪼개기

자유 변수는 `Finset` 이라 소속 증명을 자주 옮겨야 한다. 쓰는 것은 셋뿐이다.

| 상황 | 보조정리 |
|---|---|
| `w ∈ s ∪ t` 를 만들거나 쪼갠다 | `Finset.mem_union` |
| `w ∈ s.erase v` ↔ `w ≠ v ∧ w ∈ s` | `Finset.mem_erase` |
| `w ∈ s.biUnion f` ↔ `∃ a ∈ s, w ∈ f a` | `Finset.mem_biUnion` |

대부분은 `simp [IntExp.fv, hw]` 정도로 끝난다. 안 끝나면 위 셋을 명시한다.

`∃` 가 `∨` 위로 분배되는 자리(명제 1.2c 의 `bin` 케이스)는 `simp` 도 `tauto` 도 못 한다.
`constructor` 로 나누고 `rintro` 로 벗겨야 한다.

### 4. 정의를 펼치는 `simp` 목록

의미론이 걸린 목표는 대개 양쪽 정의를 펼치면 같아진다. 자주 쓰는 조합이다.

```lean
simp [Assert.eval, LogOp.denote, Cmp.denote, IntExp.eval]
simp [Assert.subst, IntExp.subst]
simp [Assert.fv, IntExp.fv]
```

무엇을 펼쳐야 할지는 목표에 뭐가 남아 있는지를 보면 안다.
`IntOp.mul.denote` 가 보이면 `IntOp.denote` 를 넣는다.

---

## 막혔을 때 순서

1. **목표를 소리 내어 읽는다.** 무엇을 보여야 하는지 한국어로 말할 수 있나?
2. `exact?` — 라이브러리에 이미 있는 정리인지 찾는다
3. `apply?` — 목표를 한 걸음 줄여 줄 정리를 찾는다
4. `simp?` — `simp` 가 무엇을 썼는지 보고 `simp only [...]` 로 좁힌다
5. `#check @foo` — 쓰려는 정리의 정확한 모양을 확인한다
6. **같은 모양의 완성 증명을 찾는다.** `Reynolds/Answers/` 의 대응 파일을 열어라.
   1장의 증명은 서로 닮았다. 정수 식 판이 완성되어 있고 단언 판이 연습인 경우가 많다.
7. 그래도 안 되면 `sorry` 를 남기고 PR 본문의 "막혔던 곳" 에 적는다.
   막힌 지점을 기록하는 것이 이 스터디에서 가장 재사용성 높은 정보다.

---

## 자주 만나는 오류 메시지

| 메시지 | 뜻 | 조치 |
|---|---|---|
| `Invalid \`meta\` definition …; consider adding \`public meta import X\`` | `#guard`/`#eval` 은 컴파일 시점에 계산한다 | 시키는 대로 `public meta import` 를 추가 |
| `failed to synthesize Decidable (⟦p⟧ₐ σ)` | 이 명제에 쓸 결정 절차를 Lean이 찾지 못했다 | 정의를 풀어 증명하려면 `simp`를 쓰고, 계산하려면 해당 명제의 `Decidable` 인스턴스가 있는지 확인한다 |
| `simp made no progress` | 펼칠 정의가 목록에 없다 | 목표에 남은 이름을 `simp [...]` 에 넣는다 |
| `motive is not type correct` | 의존 타입이 얽힌 `rw` | `simp only [...]` 나 `subst` 를 쓴다 |
| `declaration uses 'sorry'` | 아직 안 채웠다 | 경고이지 오류가 아니다. 연습 중에는 정상 |
| `failed to compile definition … 'noncomputable'` | 계산 불가능한 인스턴스가 딸려 왔다 | 정의를 고치기 전에 어떤 인스턴스인지 먼저 읽어라. `Ex/Summation.lean` 첫머리에 같은 사례가 있다 |

모듈 시스템 오류는 대개 고치는 법을 직접 알려 준다. 끝까지 읽어라.

---

## 하지 말 것

- **`native_decide`** — 커널 밖에서 참을 만들어 낸다. 채점기가 불합격 처리한다.
- **새 `axiom` 선언** — 마찬가지다.
- **진술을 약하게 고쳐서 통과시키기** — 통과해도 배운 것이 없다.
  정말 진술이 틀렸다고 생각하면 그렇게 적고 PR 로 올려라.
- **`Reynolds/Exercises/` 를 직접 고치기** — 그 트리는 `scripts/gen-exercises.py` 가 생성한다.
  힌트를 고치고 싶으면 그 스크립트의 `BLANKS` 표를 고쳐라.

---

## 심화 연습은 어떻게 다른가

`심화 A…` / `심화 B…` 로 표시된 것들은 책을 따라가는 데 필요하지 않다.
건너뛰어도 1장은 완결된다. 다만 A 는 범주론 어휘 없이도 읽히게 썼으니
`Depth/Algebra.lean` 정도는 한 번 훑어 보길 권한다.

무엇이 어디에 있고 왜 그 자리에 있는지는 [`depth-track.md`](./depth-track.md).
