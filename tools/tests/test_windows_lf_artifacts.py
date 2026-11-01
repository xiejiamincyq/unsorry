"""Windows newline hygiene: generated repo text artifacts must be LF-only.

Python's text mode translates ``\\n`` to ``os.linesep`` unless the writer asks for
``newline="\\n"``. On Windows that silently turns generated ``.lean``/``.aisp``
records (and the ``lean-toolchain`` / ``lakefile.toml`` glue) into CRLF: the
agent loop's extracted module no longer byte-matches the provider's fenced
output, an AISP rewrite churns every line, and ``elan`` reads a toolchain pin it
never declared. Each writer below therefore has to emit LF on every platform, so
the assertion is on the raw bytes (a CR-free read through ``read_text`` would
hide exactly the bug under test).

POSIX passes trivially; this is the Windows regression guard.
"""
from __future__ import annotations

from pathlib import Path

from tools.intake.verifier_context import scaffold
from tools.seedkit._artifact import write_artifacts
from tools.sourcing.gen_triples import write_triple


def _assert_lf_only(path: Path) -> None:
    data = path.read_bytes()
    assert b"\r" not in data, f"{path} contains a CR byte (CRLF translation leaked): {data[:200]!r}"


def test_gen_triple_writes_are_lf_only(tmp_path):
    paths = write_triple(
        tmp_path,
        "nat-succ-pos",
        date="2026-06-16",
        lean_sig="(n : Nat) : 0 < n + 1",
        statement="The successor of any natural number is positive.",
        source="#400 Identity Engine (ADR-043) — order family.",
        reference="Not a named mathlib lemma in this form.",
        absence="no-local-match (grep of pinned mathlib rev abc123, 2026-06-16).",
        triviality="machine-checked non-trivial (battery v1, rev abc123, 2026-06-16).",
        difficulty=3,
        decomposition="omega after Nat.succ_pos; verify with lake env lean.",
    )
    assert [p.name for p in paths] == ["nat-succ-pos.lean", "nat-succ-pos.aisp", "nat-succ-pos.md"]
    for p in paths:
        _assert_lf_only(p)


def test_seedkit_artifacts_are_lf_only(tmp_path, monkeypatch):
    monkeypatch.chdir(tmp_path)
    line = write_artifacts(
        gid="nat-succ-pos",
        name="nat_succ_pos",
        goal_lean=(
            "import Mathlib\n\n"
            "theorem nat_succ_pos (n : Nat) : 0 < n + 1 := by\n  sorry\n"
        ),
        proof=(
            "import Mathlib\n\n"
            "theorem nat_succ_pos (n : Nat) : 0 < n + 1 := by\n  omega\n"
        ),
        summary="The successor of any natural number is positive.",
        source="#400 Identity Engine (ADR-043) — order family.",
        reference="Not a named mathlib lemma in this form.",
        difficulty=3,
        delta="0.60",
        model="omega",
        solver="solver-x",
    )
    assert line.split("|")[0] == "nat-succ-pos"
    for rel in (
        "goals/nat-succ-pos.lean",
        "goals/nat-succ-pos.aisp",
        "backlog/nat-succ-pos.md",
        "library/Unsorry/NatSuccPos.lean",
    ):
        _assert_lf_only(tmp_path / rel)
    (index_path,) = list((tmp_path / "library" / "index").iterdir())
    _assert_lf_only(index_path)


def test_verifier_context_glue_is_lf_only(tmp_path):
    manifest_src = tmp_path / "lake-manifest.json"
    manifest_src.write_text("{}\n", encoding="utf-8")
    vctx = scaffold(
        tmp_path,
        "suite-x",
        toolchain="leanprover/lean4:v4.30.0",
        mathlib="0123456789abcdef",
        manifest_src=manifest_src,
    )
    # A CRLF lean-toolchain is a broken pin for elan; both are generated glue.
    _assert_lf_only(vctx / "lean-toolchain")
    _assert_lf_only(vctx / "lakefile.toml")
