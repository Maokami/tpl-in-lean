#!/usr/bin/env python3
"""문서에 손으로 적은 연습 개수가 실제와 맞는지 검사한다.

`@[exercise "id" stars]` 애트리뷰트가 진리의 원천이고, 문서의 숫자는 그 사본이다.
사본은 원본이 바뀌어도 아무 소리를 내지 않는다. 1장 문서가 28 이라고 적어 둔 동안
실제 개수는 31 이었고, 사람이 표를 더해 볼 때까지 CI는 전부 초록이었다.

## 문서가 지켜야 하는 틀

개수를 적을 때는 문장과 표를 짝으로 쓴다. 검사기는 이 틀만 읽는다.

    3장에는 채점되는 연습이 10 개 있다.

    | 갈래 | 개수 | 어디에 |
    |---|---|---|
    | 본문 명제 | 6 | `Semantics.lean`, `FixedPoint.lean` |
    | 심화 트랙 | 4 | `Depth/` |

- 문장의 두 숫자는 장 번호와 그 장의 총 개수다. 장 번호가 문장 안에 있으므로
  파일 이름과 무관하게 어느 문서에든 쓸 수 있다.
- 표의 `어디에` 칸은 `Reynolds/Answers/ChNN/` 기준 상대 경로를 백틱으로 적는다.
  `Depth/` 처럼 슬래시로 끝내면 그 디렉터리 아래 전부를 가리킨다.
- 표의 행은 그 장의 연습 파일을 빠짐없이, 겹치지 않게 나눈다.
- 코드 울타리(```) 안은 건너뛴다. 규약을 예시로 적은 문서까지 검사 대상이 되면 곤란하다.

## 검사 항목

1. 행에 적힌 개수가 그 행이 가리키는 파일들의 실제 태그 수와 같은가
2. 행들이 그 장의 연습 파일을 빠짐없이 덮고, 두 행이 같은 파일을 가리키지 않는가
3. 행의 합과 문장의 총계와 실제 총계가 셋 다 같은가
4. 연습이 있는 장의 Verso 문서(`manual/Manual/ChNN.lean`)에 이 블록이 있는가
5. (`--grade`) 소스를 세어 얻은 총계가 `lake exe grade` 의 레지스트리와 같은가

4번이 이 검사의 값을 정한다. 틀을 안 쓰면 검사도 없는 것이라, 장 문서가 있으면 블록을
요구한다. 5번은 빌드가 필요해서 기본값이 아니다. 소스에 `@[exercise]` 를 달아 놓고
루트 모듈 `Reynolds.lean` 에 import 를 빠뜨려 레지스트리에 안 올라온 경우가 여기서 걸린다.

숫자가 틀리면 고쳐 쓸 블록의 뼈대를 같이 찍는다. 갈래 이름만 채우면 된다.

사용법:

    python3 scripts/check-doc-counts.py           # 문서만 검사 (빌드 불필요)
    python3 scripts/check-doc-counts.py --grade   # 레지스트리와 총계 대조까지 (CI용)
"""

from __future__ import annotations

import argparse
import json
import pathlib
import re
import subprocess

ROOT = pathlib.Path(__file__).resolve().parent.parent
ANSWERS = ROOT / "Reynolds" / "Answers"

# 개수 블록의 두 조각.
TOTAL_RE = re.compile(r"(\d+)\s*장에는\s*채점되는\s*연습이\s*(\d+)\s*개\s*있다")
HEADER_RE = re.compile(r"^\|\s*갈래\s*\|\s*개수\s*\|\s*어디에\s*\|\s*$")

FENCE_RE = re.compile(r"^\s*```")
RULE_RE = re.compile(r"^\|[-:|\s]*\|\s*$")
EXERCISE_RE = re.compile(r'@\[exercise\s+"')
CODE_SPAN_RE = re.compile(r"`([^`]+)`")
CHAPTER_DIR_RE = re.compile(r"^Ch(\d+)$")
CHAPTER_DECL_RE = re.compile(r"\.Ch(\d+)\.")

# 개수를 적을 만한 문서. 산문이 있는 곳은 전부 훑는다.
DOC_GLOBS = ["*.md", "docs/**/*.md", "manual/Manual/**/*.lean"]


# ── 진리의 원천 ────────────────────────────────────────────────────────────────


def tag_counts() -> dict[int, dict[str, int]]:
    """`Reynolds/Answers/**` 를 훑어 장별·파일별 `@[exercise]` 개수를 센다.

    파일별 개수를 소스에서 직접 세는 이유는 `lake exe grade --json` 이 알려주지 못하기
    때문이다. 연습 선언은 파일 이름이 아니라 장 이름공간(`Reynolds.Answers.Ch01`)에
    들어 있어서, 선언 이름만 봐서는 어느 파일에서 왔는지 알 수 없다.
    """
    counts: dict[int, dict[str, int]] = {}
    for src in sorted(ANSWERS.rglob("*.lean")):
        rel = src.relative_to(ANSWERS)
        chapter = CHAPTER_DIR_RE.match(rel.parts[0])
        if chapter is None:
            continue
        found = len(EXERCISE_RE.findall(src.read_text()))
        if found:
            counts.setdefault(int(chapter.group(1)), {})["/".join(rel.parts[1:])] = found
    return counts


def grade_totals() -> dict[int, int]:
    """`lake exe grade` 가 보는 레지스트리의 장별 개수."""
    proc = subprocess.run(
        ["lake", "exe", "grade", "--answers", "--json"],
        cwd=ROOT,
        capture_output=True,
        text=True,
    )
    # 종료 코드는 보지 않는다. `--answers` 는 미완성 연습이 있으면 1 을 돌려주는데,
    # 그건 `lake exe grade --answers` 단계가 볼 일이고 여기서 필요한 것은 개수뿐이다.
    start = proc.stdout.find("{")
    if start < 0:
        raise SystemExit(
            "`lake exe grade --answers --json` 에서 JSON 을 못 받았다. `lake build` 를 먼저 돌려라.\n"
            + (proc.stderr or proc.stdout).strip()
        )
    totals: dict[int, int] = {}
    for item in json.loads(proc.stdout[start:])["items"]:
        chapter = CHAPTER_DECL_RE.search(item["decl"])
        if chapter:
            key = int(chapter.group(1))
            totals[key] = totals.get(key, 0) + 1
    return totals


# ── 문서 읽기 ─────────────────────────────────────────────────────────────────


class Row:
    """개수 표의 한 행: 갈래 이름, 적힌 개수, 백틱으로 적은 경로들."""

    def __init__(self, line: int, label: str, count: int, specs: list[str]) -> None:
        self.line = line
        self.label = label
        self.count = count
        self.specs = specs


class Block:
    """총계 문장 하나와 그 뒤에 붙은 표 하나. 표가 없으면 `rows` 가 빈다."""

    def __init__(self, doc: pathlib.Path, line: int, chapter: int, total: int) -> None:
        self.doc = doc
        self.line = line
        self.chapter = chapter
        self.total = total
        self.rows: list[Row] = []

    def at(self, line: int | None = None) -> str:
        return f"{self.doc.relative_to(ROOT)}:{line or self.line}"


def fence_mask(lines: list[str]) -> list[bool]:
    """줄마다 "코드 울타리 밖인가"를 표시한다."""
    mask: list[bool] = []
    inside = False
    for line in lines:
        if FENCE_RE.match(line):
            inside = not inside
            mask.append(False)
        else:
            mask.append(not inside)
    return mask


def read_table(lines: list[str], mask: list[bool], header: int) -> tuple[list[Row], int]:
    """머리글 줄 번호를 받아 행 목록과 표가 끝난 자리를 돌려준다."""
    rows: list[Row] = []
    i = header + 1
    if i < len(lines) and RULE_RE.match(lines[i].strip()):  # `|---|---|---|`
        i += 1
    while i < len(lines) and mask[i] and lines[i].lstrip().startswith("|"):
        cells = [c.strip() for c in lines[i].strip().strip("|").split("|")]
        if len(cells) == 3 and cells[1].isdigit():
            rows.append(Row(i + 1, cells[0], int(cells[1]), CODE_SPAN_RE.findall(cells[2])))
        i += 1
    return rows, i


def parse_doc(path: pathlib.Path) -> tuple[list[Block], list[int]]:
    """문서 하나에서 개수 블록과, 총계 문장 없이 떠 있는 표의 줄 번호를 뽑는다."""
    lines = path.read_text().split("\n")
    mask = fence_mask(lines)

    blocks: list[Block] = []
    for i, line in enumerate(lines):
        found = TOTAL_RE.search(line) if mask[i] else None
        if found:
            blocks.append(Block(path, i + 1, int(found.group(1)), int(found.group(2))))

    # 표는 자기 앞의 가장 가까운 총계 문장에 붙인다. 붙일 문장이 없으면 고아 표다.
    orphans: list[int] = []
    i = 0
    while i < len(lines):
        if mask[i] and HEADER_RE.match(lines[i]):
            rows, end = read_table(lines, mask, i)
            owner = next((b for b in reversed(blocks) if b.line <= i + 1 and not b.rows), None)
            if owner is None:
                orphans.append(i + 1)
            else:
                owner.rows = rows
            i = end
        else:
            i += 1
    return blocks, orphans


def docs() -> list[pathlib.Path]:
    """검사할 문서 목록."""
    found: list[pathlib.Path] = []
    for pattern in DOC_GLOBS:
        found.extend(sorted(ROOT.glob(pattern)))
    return found


# ── 검사 ──────────────────────────────────────────────────────────────────────


def resolve(spec: str, files: dict[str, int]) -> list[str]:
    """`어디에` 칸의 경로 하나를 실제 파일 목록으로 바꾼다."""
    if spec.endswith("/"):
        return sorted(f for f in files if f.startswith(spec))
    return sorted(f for f in files if f == spec)


def suggest(chapter: int, files: dict[str, int]) -> str:
    """고쳐 쓸 블록의 뼈대. 숫자는 여기서 주고 갈래 이름은 사람이 붙인다."""
    out = [f"{chapter}장에는 채점되는 연습이 {sum(files.values())} 개 있다.", ""]
    out += ["| 갈래 | 개수 | 어디에 |", "|---|---|---|"]
    out += [f"| (갈래 이름) | {n} | `{f}` |" for f, n in sorted(files.items())]
    return "\n".join("      " + line for line in out)


def check_block(block: Block, truth: dict[int, dict[str, int]]) -> list[str]:
    """블록 하나를 진리의 원천과 대조한다."""
    files = truth.get(block.chapter)
    if files is None:
        return [f"  ✖ {block.at()} : {block.chapter}장에는 `@[exercise]` 가 하나도 없다."]

    bad: list[str] = []
    actual = sum(files.values())
    if block.total != actual:
        bad.append(f"  ✖ {block.at()} : {block.chapter}장 총계 — 문서 {block.total}, 실제 {actual}")
    if not block.rows:
        return bad + [
            f"  ✖ {block.at()} : 총계 문장 뒤에 개수 표가 없다.\n{suggest(block.chapter, files)}"
        ]

    # 행마다 개수를 대조하면서, 어느 파일이 어느 행에 덮였는지도 같이 모은다.
    covered: dict[str, list[str]] = {}
    row_sum = 0
    for row in block.rows:
        row_sum += row.count
        picked: list[str] = []
        if not row.specs:
            bad.append(
                f"  ✖ {block.at(row.line)} : `{row.label}` — `어디에` 칸에 백틱 경로가 없다."
                " 어느 파일을 센 것인지 적어야 대조할 수 있다."
            )
        for spec in row.specs:
            hit = resolve(spec, files)
            if not hit:
                on_disk = (ANSWERS / f"Ch{block.chapter:02d}" / spec.rstrip("/")).exists()
                bad.append(
                    f"  ✖ {block.at(row.line)} : `{spec}` —"
                    f" {'연습이 하나도 없다' if on_disk else '그런 파일이 없다'}"
                    f" (`Reynolds/Answers/Ch{block.chapter:02d}/` 기준)"
                )
            picked.extend(hit)
        for f in picked:
            covered.setdefault(f, []).append(row.label)
        real = sum(files[f] for f in picked)
        if picked and row.count != real:
            bad.append(
                f"  ✖ {block.at(row.line)} : `{row.label}` — 문서 {row.count}, 실제 {real}"
                f" ({', '.join(picked)})"
            )

    if row_sum != block.total:
        bad.append(f"  ✖ {block.at()} : 표의 합 {row_sum}, 문장의 총계 {block.total}")
    for f, labels in sorted(covered.items()):
        if len(labels) > 1:
            bad.append(
                f"  ✖ {block.at()} : `{f}` — 여러 행이 가리킨다 ({', '.join(labels)})."
                " 그만큼 겹쳐 세어진다."
            )
    for f in sorted(set(files) - set(covered)):
        bad.append(
            f"  ✖ {block.at()} : `{f}` (연습 {files[f]} 개) 가 어느 행에도 없다."
            " 행을 더하거나 기존 행의 경로에 넣어라."
        )
    return bad


def main() -> int:
    parser = argparse.ArgumentParser(description="문서의 연습 개수와 실제 `@[exercise]` 를 대조한다")
    parser.add_argument(
        "--grade", action="store_true", help="`lake exe grade` 레지스트리와 총계까지 대조한다"
    )
    args = parser.parse_args()

    truth = tag_counts()
    fail = 0

    print("== 1. 문서에 적힌 개수 ==")
    blocks: list[Block] = []
    bad: list[str] = []
    for doc in docs():
        found, orphans = parse_doc(doc)
        blocks.extend(found)
        bad += [
            f"  ✖ {doc.relative_to(ROOT)}:{line} : 총계 문장 없이 개수 표만 있다."
            " 표 앞에 `N장에는 채점되는 연습이 X 개 있다` 를 둔다."
            for line in orphans
        ]
    for block in blocks:
        bad += check_block(block, truth)
    if bad:
        print("\n".join(bad))
        fail = 1
    else:
        print(f"  ✔ 이상 없음 (블록 {len(blocks)} 개)")

    print("== 2. 장 문서에 개수 블록이 있는가 ==")
    bad = []
    for chapter, files in sorted(truth.items()):
        doc = ROOT / "manual" / "Manual" / f"Ch{chapter:02d}.lean"
        if doc.exists() and not any(b.doc == doc and b.chapter == chapter for b in blocks):
            bad.append(
                f"  ✖ {doc.relative_to(ROOT)} : {chapter}장에 연습이 {sum(files.values())} 개 있는데"
                f" 개수 블록이 없다.\n{suggest(chapter, files)}"
            )
    if bad:
        print("\n".join(bad))
        fail = 1
    else:
        print("  ✔ 이상 없음")

    if args.grade:
        print("== 3. 레지스트리와 총계 대조 ==")
        registry = grade_totals()
        source = {c: sum(f.values()) for c, f in truth.items()}
        bad = [
            f"  ✖ {chapter}장 — 소스 {source.get(chapter, 0)} 개,"
            f" 레지스트리 {registry.get(chapter, 0)} 개."
            " 루트 모듈 `Reynolds.lean` 의 import 를 확인해라."
            for chapter in sorted(set(registry) | set(source))
            if registry.get(chapter, 0) != source.get(chapter, 0)
        ]
        if bad:
            print("\n".join(bad))
            fail = 1
        else:
            print(f"  ✔ 일치 ({sum(source.values())} 개)")

    return fail


if __name__ == "__main__":
    raise SystemExit(main())
