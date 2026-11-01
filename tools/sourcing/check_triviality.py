"""Triviality probe (backlog sourcing, ADR-035 / SPEC-035-A).

A target only belongs in the backlog if it is **non-trivial** — not closable by
one-shot automation, and not already in mathlib (under *any* name). The absence
check (`check_absence.py`) greps mathlib for the theorem *name*; it cannot see a
lemma stated under a different name, nor a statement a single tactic discharges.
This tool closes that gap.

It builds a probe module that states the goal's closed type (the same
`∀`-quantified statement the ADR-011 binding gate asserts) under `import Mathlib`
and tries a fixed battery of closing tactics:

    theorem <name>_triviality_probe : <foralltype> := by
      first | rfl | trivial | decide | norm_num | omega | simp | simp_all | aesop | ring | linarith | tauto

If any tactic closes it, the statement is one-shot-trivial — and because the
whole library is in scope, `simp`/`aesop` will also find a *renamed duplicate*,
so the probe is simultaneously a semantic complement to the name-grep absence
check. The probe reuses `tools.lean_sig` (`foralltype`/`open_lines`/
`theorem_name`) so it elaborates exactly the goal-as-stated.

Verdict trichotomy (a probe that fails to elaborate is NOT evidence of
non-triviality):
  * ``trivial``     — the battery closed it. Reject. Exit 1.
  * ``non-trivial`` — it elaborated, nothing closed it. Admit-eligible. Exit 0.
  * ``probe-error`` — the statement failed to elaborate (import/open gap, unknown
                      identifier). Tooling issue, surfaced loudly. Exit 2.

An allowlist (intentional trivial fixtures) and a per-goal backlog override
(`- **Nontrivial-override:** …`) downgrade a ``trivial`` verdict to
``allowlisted`` / ``override`` (admit). Like absence, a triviality claim is
rev-dated — a mathlib bump can turn a target into a near-duplicate, which is
correct, not a bug.

Usage:
  python3 -m tools.sourcing.check_triviality goals/<id>.lean [--per-tactic] \\
      [--root <repo>] [--timeout <s>] [--json]
  python3 -m tools.sourcing.check_triviality --all [--root <repo>] [--json]

Exit: 0 = non-trivial (admit-eligible) · 1 = trivial · 2 = probe-error/usage.
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Callable

from tools.lean_sig import foralltype, open_lines, theorem_name
from tools.sourcing.check_absence import manifest_rev

Runner = Callable[..., "subprocess.CompletedProcess[str]"]

#: The fixed, ordered triviality battery (cheapest/most-decisive first, then the
#: simp family, then aesop — the strongest renamed-duplicate finder — then
#: algebra/order/propositional). `native_decide` is deliberately excluded: it is
#: forbidden in `library/` and is platform-nondeterministic.
TACTIC_BATTERY: tuple[str, ...] = (
    "rfl", "trivial", "decide", "norm_num", "omega",
    "simp", "simp_all", "aesop", "ring", "linarith", "tauto",
)

PROBE_SUFFIX = "_triviality_probe"
ALLOWLIST = Path(__file__).with_name("triviality_allowlist.txt")

#: stderr/stdout signatures of a *statement* that failed to elaborate (vs. a
#: tactic that merely failed to close an elaborated goal). Order-independent.
_ELAB_ERROR_RE = re.compile(
    r"unknown identifier|unknown constant|unknown tactic|unexpected token"
    r"|unexpected identifier|function expected|unknown package|unknown namespace"
    r"|invalid field|expected type must be known|failed to synthesize",
)

#: `decide` (in the battery `first | … | decide | …`) cannot synthesize a
#: `Decidable` instance for a ∀ over an infinite type — that is the *tactic's*
#: limitation, not a statement elaboration error, so its "failed to synthesize …
#: Decidable …" message must NOT be read as a probe-error (it falsely tripped the
#: `failed to synthesize` branch above — #410 follow-up). Stripped before the
#: elab-error check. A genuine statement typeclass gap (e.g. "failed to synthesize
#: instance\n  Inv ℕ") still matches and is surfaced.
_DECIDE_NOISE_RE = re.compile(r"failed to synthesize\s*\n?\s*Decidable\b[^\n]*")


def probe_module(goal_text: str, battery: tuple[str, ...] = TACTIC_BATTERY,
                 tactic: str | None = None) -> str:
    """The probe Lean source: the ADR-011 binding shape with the proof term
    replaced by a tactic block. `tactic` runs a single tactic (``--per-tactic``);
    otherwise the whole battery under `first | …`."""
    name = theorem_name(goal_text)
    ftype = foralltype(goal_text)
    opens = "".join(f"{o}\n" for o in open_lines(goal_text))
    body = tactic if tactic is not None else "first | " + " | ".join(battery)
    return (
        "import Mathlib\n\n"
        f"{opens}"
        "set_option linter.unusedVariables false in\n"
        f"theorem {name}{PROBE_SUFFIX} : {ftype} := by\n"
        f"  {body}\n"
    )


def classify(returncode: int, output: str) -> str:
    """Map a build result to the verdict trichotomy. A statement that fails to
    elaborate (elaboration-error signature) is ``probe-error``, never
    ``non-trivial``; any other non-zero exit is ``non-trivial`` (the statement
    elaborated — at sourcing it already type-checked — but no tactic closed it)."""
    if returncode == 0:
        return "trivial"
    cleaned = _DECIDE_NOISE_RE.sub("", output)
    if _ELAB_ERROR_RE.search(cleaned):
        return "probe-error"
    return "non-trivial"


def _run_probe(module: str, *, runner: Runner, root: Path, timeout: float) -> tuple[int, str]:
    with tempfile.TemporaryDirectory() as tmp:
        probe_file = Path(tmp) / "TrivialityProbe.lean"
        probe_file.write_text(module, encoding="utf-8", newline="\n")
        try:
            result = runner(
                ("lake", "env", "lean", str(probe_file)),
                cwd=str(root), capture_output=True, text=True, timeout=timeout,
            )
        except subprocess.TimeoutExpired:
            # A tactic looped past the wall clock — conservatively non-trivial
            # (it did not close), never a spurious reject.
            return 1, "triviality probe timed out (treated as non-trivial)"
        return result.returncode, (result.stdout or "") + (result.stderr or "")


def allowlisted(goal_id: str, allowlist: Path = ALLOWLIST) -> bool:
    """True if `goal_id` is on the intentional-trivial-fixture allowlist (ids one
    per line; ``#`` comments and blank lines ignored)."""
    if not allowlist.is_file():
        return False
    for line in allowlist.read_text(encoding="utf-8").splitlines():
        entry = line.split("#", 1)[0].strip()
        if entry == goal_id:
            return True
    return False


def override_reason(goal_id: str, root: Path) -> str | None:
    """The reason from a ``- **Nontrivial-override:** <reason>`` line in
    ``backlog/<id>.md``, or None. (Gate B does not validate backlog md, so this
    advisory field adds no schema churn.)"""
    backlog = root / "backlog" / f"{goal_id}.md"
    if not backlog.is_file():
        return None
    m = re.search(r"^- \*\*Nontrivial-override:\*\*\s*(.+)$",
                  backlog.read_text(encoding="utf-8"), re.MULTILINE)
    return m.group(1).strip() if m else None


def probe(goal_lean: Path, *, battery: tuple[str, ...] = TACTIC_BATTERY,
          runner: Runner | None = None, root: Path | None = None,
          timeout: float = 180.0, per_tactic: bool = False,
          allowlist: Path = ALLOWLIST) -> dict:
    """Probe one goal. Returns a JSON-able verdict dict. Pure orchestration —
    `runner` is injectable so tests never touch lake (resolved at call time so a
    monkeypatched `subprocess.run` is honoured)."""
    runner = runner or subprocess.run
    root = root or Path.cwd()
    goal_id = goal_lean.stem
    text = goal_lean.read_text(encoding="utf-8")
    result: dict = {
        "goal": goal_id,
        "mathlib_rev": manifest_rev(root),
        "battery": list(battery),
        "closed_by": None,
        "stderr_excerpt": "",
    }

    if per_tactic:
        verdict = "non-trivial"
        last_output = ""
        for tac in battery:
            rc, output = _run_probe(probe_module(text, battery, tactic=tac),
                                    runner=runner, root=root, timeout=timeout)
            last_output = output
            if rc == 0:
                verdict, result["closed_by"] = "trivial", tac
                break
            if classify(rc, output) == "probe-error":
                verdict = "probe-error"
                break
        result["stderr_excerpt"] = last_output[-600:]
    else:
        rc, output = _run_probe(probe_module(text, battery),
                                runner=runner, root=root, timeout=timeout)
        verdict = classify(rc, output)
        result["stderr_excerpt"] = output[-600:]

    # Downgrade a trivial verdict via allowlist / per-goal override (admit).
    if verdict == "trivial":
        if allowlisted(goal_id, allowlist):
            verdict = "allowlisted"
        else:
            reason = override_reason(goal_id, root)
            if reason:
                verdict, result["override_reason"] = "override", reason
    result["verdict"] = verdict
    return result


#: verdict → process exit code. Non-trivial/allowlisted/override admit (0);
#: trivial rejects (1); probe-error surfaces (2).
_EXIT = {"non-trivial": 0, "allowlisted": 0, "override": 0, "trivial": 1, "probe-error": 2}


def _goal_files(root: Path) -> list[Path]:
    return sorted((root / "goals").glob("*.lean"))


def audit(root: Path, *, runner: Runner | None = None, timeout: float = 180.0) -> list[dict]:
    """Report-only probe of every goal, in two passes for a tractable wall-clock
    (#411). Pass 1 is the fast combined ``first | …`` probe — one build per goal.
    Pass 2 re-probes only the goals that came back ``trivial`` with
    ``--per-tactic``, to recover which tactic closed them (``closed_by``). That is
    ~1 build/goal plus a re-probe for the trivial handful, instead of ~11/goal
    (which timed the retro-audit out at 90 min over ~100 goals). Never mutates
    anything."""
    runner = runner or subprocess.run
    reports = []
    for goal in _goal_files(root):
        report = probe(goal, runner=runner, root=root, timeout=timeout)
        if report["verdict"] == "trivial":
            # rc==0 on the combined battery ⇒ some tactic closes it; re-probe
            # per-tactic to name it. (Allowlisted/override are already admitted —
            # no re-probe; probe-error/non-trivial never closed.)
            report = probe(goal, runner=runner, root=root, timeout=timeout,
                           per_tactic=True)
        reports.append(report)
    return reports


def render_audit(reports: list[dict], mathlib_rev: str | None) -> tuple[str, str]:
    """(markdown, json) for the report-only retro-audit over all goals (#387 PR2).
    A ``trivial`` verdict flags a proved-but-one-shot goal for human review — it is
    never deleted (ADR-035)."""
    order = ["trivial", "probe-error", "allowlisted", "override", "non-trivial"]
    by_verdict: dict[str, list[dict]] = {v: [] for v in order}
    for report in reports:
        by_verdict.setdefault(report["verdict"], []).append(report)
    counts = {v: len(by_verdict.get(v, [])) for v in order}
    lines = [
        "# Triviality retro-audit (ADR-035, report-only)",
        "",
        f"Probed **{len(reports)}** goals against the one-shot tactic battery at "
        f"mathlib `{mathlib_rev or '?'}`. **Report-only** — nothing is deleted; a "
        "`trivial` verdict means a single battery tactic closes the statement (so it "
        "is one-shot-provable or already in mathlib under another name) and is flagged "
        "for human review (ADR-035).",
        "",
        "| verdict | count |",
        "|---|---|",
        *[f"| {v} | {counts[v]} |" for v in order],
        "",
    ]
    flagged = sorted(by_verdict.get("trivial", []), key=lambda r: r["goal"])
    if flagged:
        lines += ["## Flagged trivial (review)", "", "| goal | closed by |", "|---|---|"]
        lines += [f"| `{r['goal']}` | {('`' + r['closed_by'] + '`') if r['closed_by'] else '—'} |"
                  for r in flagged]
    else:
        lines.append("**No proved-but-trivial goals — the library is clean.** ✅")
    errs = sorted(by_verdict.get("probe-error", []), key=lambda r: r["goal"])
    if errs:
        lines += ["", "## Probe errors (statement did not elaborate — tooling/import gap)", ""]
        lines += [f"- `{r['goal']}`" for r in errs]
    lines.append("")
    payload = json.dumps(
        {"mathlib_rev": mathlib_rev, "counts": counts, "reports": reports},
        indent=2, sort_keys=True) + "\n"
    return "\n".join(lines), payload


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("goal", nargs="?", help="goals/<id>.lean to probe")
    parser.add_argument("--all", action="store_true",
                        help="audit every goal under <root>/goals (report-only)")
    parser.add_argument("--per-tactic", action="store_true",
                        help="run each tactic separately and report which closed it")
    parser.add_argument("--root", type=Path, default=Path.cwd())
    parser.add_argument("--timeout", type=float, default=180.0)
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--write", action="store_true",
                        help="with --all: write docs/triviality-audit.{md,json} (#387 PR2)")
    args = parser.parse_args(argv)

    if args.all:
        reports = audit(args.root, timeout=args.timeout)
        trivial = [r for r in reports if r["verdict"] == "trivial"]
        if args.write:
            md, payload = render_audit(reports, manifest_rev(args.root))
            (args.root / "docs" / "triviality-audit.md").write_text(md, encoding="utf-8")
            (args.root / "docs" / "triviality-audit.json").write_text(payload, encoding="utf-8")
            print(f"wrote docs/triviality-audit.{{md,json}} — "
                  f"{len(trivial)} trivial / {len(reports)} goals")
        elif args.json:
            print(json.dumps({"reports": reports, "trivial_count": len(trivial)}, indent=2))
        else:
            for r in trivial:
                print(f"TRIVIAL  {r['goal']:48s} closed_by={r['closed_by']}")
            print(f"\n{len(trivial)} trivial / {len(reports)} goals "
                  f"(mathlib {manifest_rev(args.root) or '?'})")
        return 0  # audit is report-only; never fails the caller

    if not args.goal:
        parser.error("a goals/<id>.lean is required (or --all)")
    report = probe(Path(args.goal), root=args.root, timeout=args.timeout,
                   per_tactic=args.per_tactic)
    if args.json:
        print(json.dumps(report, indent=2))
    else:
        line = f"{report['verdict'].upper()}  {report['goal']}"
        if report["closed_by"]:
            line += f"  (closed by {report['closed_by']})"
        print(line)
        if report["verdict"] == "probe-error":
            print(report["stderr_excerpt"], file=sys.stderr)
    return _EXIT[report["verdict"]]


if __name__ == "__main__":
    raise SystemExit(main())
