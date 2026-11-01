"""Render the sponsor's upstream packet (ADR-020, SPEC-020-A — stages 3+5).

A packet is everything the human sponsor needs to take one lemma to mathlib
honestly and efficiently — and nothing the sponsor is required to write from
scratch except the parts mathlib policy reserves for humans:

- `docs/upstream/<id>.md`: statement, the proposed mathlib-ready contribution
  block, dedup-at-HEAD evidence, provenance dossier, a paste-ready *factual*
  AI-disclosure block, and sponsor instructions with the rewrite-in-own-words
  boundary stated explicitly (LLM-written PR/Zulip narrative is against
  mathlib policy; the lemma itself, disclosed, is not).
- `docs/upstream/<id>.patch`: a `git apply`-able new-file diff against a
  mathlib checkout. The path `Mathlib/Unsorry/<Camel>.lean` is a deliberate
  placeholder — placement is a Zulip question, and the standalone file is
  exactly what `verify_head.sh` kernel-checks at HEAD.

Mechanical by design: structured facts only, no model access — CI can run it
nightly (SPEC-020-A automatic initiation).

Usage:
  python3 -m tools.upstream.packet --goal <id> [--root <repo>]
      [--dedup <report.json>] [--sponsor <name>] [--outdir docs/upstream]
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path
from typing import List

from tools.lean_sig import camel_name
from tools.sourcing.targets_board import _backlog_fields
from tools.upstream.dedup_head import _index_name

_TOPLEVEL_RE = re.compile(r"^(theorem|def|opaque|/--|/-!|@\[)")
_IMPORT_RE = re.compile(r"^import\s+(\S+)")


def _module_text(root: Path, goal: str) -> str:
    return _module_path(root, goal).read_text(encoding="utf-8")


def _module_path(root: Path, goal: str) -> Path:
    rel = Path("library") / "Unsorry" / f"{camel_name(goal)}.lean"
    active = root / rel
    if active.is_file():
        return active
    packages = root / "packages"
    if packages.is_dir():
        for archive in sorted(packages.glob("unsorry-archive-*")):
            candidate = archive / rel
            if candidate.is_file():
                return candidate
    raise FileNotFoundError(rel.as_posix())


def _module_label(root: Path, goal: str) -> str:
    return _module_path(root, goal).relative_to(root).as_posix()


def _theorem_block(module_text: str, name: str) -> str:
    """The theorem's own lines: from `theorem <name>` to the next top-level
    declaration (our generated modules may carry lint-scope helpers before or
    after it — none of that belongs in a mathlib contribution)."""
    lines = module_text.splitlines()
    start = None
    for i, line in enumerate(lines):
        if line.startswith(f"theorem {name}"):
            start = i
            break
    if start is None:
        raise ValueError(f"theorem {name} not found in module")
    end = len(lines)
    for j in range(start + 1, len(lines)):
        if _TOPLEVEL_RE.match(lines[j]):
            end = j
            break
    return "\n".join(lines[start:end]).rstrip() + "\n"


def _imports(module_text: str) -> tuple[List[str], List[str]]:
    """(mathlib_imports, unsorry_imports) — internal lint plumbing dropped."""
    mathlib: List[str] = []
    unsorry: List[str] = []
    for line in module_text.splitlines():
        m = _IMPORT_RE.match(line)
        if not m:
            continue
        mod = m.group(1)
        if mod.startswith("Unsorry."):
            unsorry.append(mod)
        elif mod.startswith("Mathlib"):
            mathlib.append(mod)
        # Lean.Linter.* is our --wfail workaround plumbing — never upstreamed.
    return mathlib, unsorry


def _contribution(root: Path, goal: str, sponsor: str) -> str:
    """The mathlib-ready file content: human-author header, imports, theorem."""
    name = _index_name(root, goal)
    text = _module_text(root, goal)
    mathlib_imports, _ = _imports(text)
    header = (
        "/-\n"
        f"Copyright (c) 2026 {sponsor}. All rights reserved.\n"
        "Released under Apache 2.0 license as described in the file LICENSE.\n"
        f"Authors: {sponsor}\n"
        "-/\n"
    )
    imports = "\n".join(f"import {m}" for m in mathlib_imports)
    return f"{header}{imports}\n\n{_theorem_block(text, name)}"


def render_patch(root: Path, goal: str, sponsor: str) -> str:
    content = _contribution(root, goal, sponsor)
    lines = content.splitlines()
    target = f"Mathlib/Unsorry/{camel_name(goal)}.lean"
    body = "\n".join(f"+{ln}" for ln in lines)
    return (
        f"--- /dev/null\n"
        f"+++ b/{target}\n"
        f"@@ -0,0 +1,{len(lines)} @@\n"
        f"{body}\n"
    )


def render_packet(root: Path, goal: str, dedup: dict, sponsor: str) -> str:
    name = _index_name(root, goal)
    statement = (root / "goals" / f"{goal}.lean").read_text(encoding="utf-8").strip()
    module_text = _module_text(root, goal)
    _, unsorry_deps = _imports(module_text)
    fields = _backlog_fields(root, goal)
    blocked = dedup.get("verdict") != "no-local-match"
    status = "blocked-possible-duplicate" if blocked else "packet-ready"

    dep_section = ""
    if unsorry_deps:
        deps = "\n".join(f"- `{d}`" for d in unsorry_deps)
        dep_section = (
            "\n## Dependencies on sibling lemmas\n\n"
            "The proof imports unsorry library modules that mathlib does not have —\n"
            "the sponsor must **bundle or inline** them (or upstream the dependency\n"
            "first):\n\n"
            f"{deps}\n"
        )

    matches = dedup.get("local_matches") or []
    match_lines = "\n".join(
        f"- `{m['file']}`: `{m['line']}` (pattern `{m['pattern']}`)" for m in matches
    ) or "- none"

    provenance_rows = "\n".join(
        f"| {k} | {v} |" for k, v in fields.items()
    ) or "| — | — |"

    return f"""# Upstream packet: `{goal}`

Status: {status} · generated mechanically (ADR-020 / SPEC-020-A) · sponsor: {sponsor}

## The statement (as proved here)

```lean
{statement}
```

Kernel-verified on `main`: `{_module_label(root, goal)}` (theorem `{name}`),
through Gate A (build `--wfail`, axiom audit against the standard whitelist, leanchecker
kernel replay, regenerated ADR-011 binding obligation).

## Proposed contribution

The `git apply`-able new-file diff is at [`{goal}.patch`]({goal}.patch). The target path
`Mathlib/Unsorry/{camel_name(goal)}.lean` is a **placeholder** — file placement and the
final name are Zulip questions, not ours to decide. Content:

```lean
{_contribution(root, goal, sponsor).rstrip()}
```
{dep_section}
## Dedup at mathlib HEAD

- mathlib revision scanned: `{dedup.get("mathlib_rev", "unknown")}`
- patterns: {", ".join(f"`{p}`" for p in dedup.get("patterns", [])) or "—"}
- verdict: **{dedup.get("verdict", "unknown")}**
- matches:
{match_lines}

A name-grep is a pre-filter, not a proof of absence; the kernel build at HEAD
(`tools/upstream/verify_head.sh`) is the strong evidence and its result belongs in the
PR conversation.

## Provenance dossier

| Field | Value |
|---|---|
{provenance_rows}

Proof produced by an autonomous Claude agent swarm (model policy ADR-013/ADR-015:
`fable`, progressive effort), merged with no human review through two CI gates
(ADR-006 soundness, Gate B hygiene). Full machine history: the goal's PR trail in
this repository.

## AI disclosure (paste-ready facts)

> The Lean proof in this PR was produced by an autonomous LLM agent
> (Anthropic Claude, model `fable`) operating in the `unsorry` proof swarm
> (github.com/agenticsnz/unsorry), and was machine-verified there by kernel
> replay, an axiom audit against the standard whitelist (`propext`,
> `Classical.choice`, `Quot.sound`), and a CI-regenerated statement-binding
> obligation. I have read and understood the proof in full and can justify
> each step without AI assistance. Label: `LLM-generated`.

## For the sponsor

1. Read the proof until you can justify every step **without AI assistance** —
   mathlib reviewers will expect exactly that.
2. **Zulip first**, in your own words: is the lemma wanted, where does it live,
   what should it be called? The PR-description narrative and every review reply
   likewise **must be rewritten in your own words** — mathlib policy forbids
   LLM-written conversation; only the lemma itself (disclosed) and the factual
   disclosure block above may be pasted.
3. **Raise the draft PR with one command** once you've done 1–2 — from the
   unsorry repo root:
   ```
   python3 -m tools.upstream.raise_pr --goal {goal} --fork <your-github-user> --understood
   ```
   It clones mathlib master, applies the patch to a fresh branch, pushes to
   your fork, and opens a **draft** PR pre-filled with the factual disclosure
   and a placeholder where your narrative goes. (`--understood` is your
   attestation that you've read the proof; `--dry-run` shows the plan first.)
   The machine never marks it ready and never writes a review reply.
4. Write your narrative in the draft, apply the `LLM-generated` label, then
   **you** flip draft → ready. Expect the linter to want golfing (binder
   names, line length) — that editing is yours. See [docs/upstreaming.md](../upstreaming.md).
5. Record the outcome on the targets board (`in-discussion → pr-open →
   merged | declined`). **Declined is a valid, recorded result.**
"""


def main(argv: List[str] | None = None) -> int:
    parser = argparse.ArgumentParser(prog="tools.upstream.packet")
    parser.add_argument("--goal", required=True)
    parser.add_argument("--root", type=Path, default=Path("."))
    parser.add_argument("--dedup", type=Path, help="dedup_head JSON report")
    parser.add_argument("--sponsor", default="Chris Barlow")
    parser.add_argument("--outdir", type=Path, default=Path("docs/upstream"))
    args = parser.parse_args(argv)

    dedup = (
        json.loads(args.dedup.read_text(encoding="utf-8"))
        if args.dedup
        else {"verdict": "not-run", "mathlib_rev": "unknown", "patterns": [],
              "local_matches": []}
    )
    outdir = args.root / args.outdir if not args.outdir.is_absolute() else args.outdir
    outdir.mkdir(parents=True, exist_ok=True)
    (outdir / f"{args.goal}.md").write_text(
        render_packet(args.root, args.goal, dedup, args.sponsor),
        encoding="utf-8",
        newline="\n",
    )
    (outdir / f"{args.goal}.patch").write_text(
        render_patch(args.root, args.goal, args.sponsor),
        encoding="utf-8",
        newline="\n",
    )
    print(f"packet: {outdir / args.goal}.md (+ .patch)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
