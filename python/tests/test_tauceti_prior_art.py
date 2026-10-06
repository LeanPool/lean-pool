"""Regression coverage for honest Tau Ceti novelty evidence."""

import json
import subprocess
from types import SimpleNamespace

import pytest

from lean_pool import tauceti_prior_art
from lean_pool.prior_art import Claim

ADO = "TauCeti/RepresentationTheory/Lie/Ado/CharacteristicZero.lean"


def _tree(paths: list[str], *, truncated: bool = False) -> str:
    """Build a GitHub inventory response without contacting GitHub."""
    return json.dumps(
        {
            "sha": "tree-object-not-a-commit",
            "truncated": truncated,
            "tree": [{"path": path, "type": "blob"} for path in paths],
        }
    )


def test_ado_candidate_beats_generic_lie_modules() -> None:
    """A distinctive theorem name finds its source among generic words."""
    paths = [ADO, "TauCeti/AdicSpace/SheafForEveryPresentation.lean"] + [
        f"TauCeti/Algebra/Lie/Basic{i}.lean" for i in range(10)
    ]
    claim = Claim("Ado.adoCharZero", "Every Lie algebra has a faithful representation")
    assert tauceti_prior_art.candidates(claim, paths)[0] == ADO


def test_evidence_fetches_sources_at_inventory_revision() -> None:
    """A moving main branch cannot mix candidates and later source text."""
    calls = []

    def run_gh(*args):
        calls.append(args)
        if "commits/main" in args[1]:
            return "fixed-commit\n"
        if "git/trees" in args[1]:
            return _tree([ADO])
        return "theorem Ado.adoCharZero : True := trivial"

    section = tauceti_prior_art.gather([Claim("Ado.adoCharZero", "")], run_gh)
    assert "Ado.adoCharZero : True" in section
    assert "git/trees/fixed-commit?" in calls[1][1]
    assert "?ref=fixed-commit" in calls[2][1]
    assert "blob/fixed-commit/" in section
    assert "untrusted" in section
    assert "not a complete semantic search" in section


def test_truncated_inventory_is_unchecked() -> None:
    """A partial GitHub tree must not be mistaken for a complete search."""
    section = tauceti_prior_art.gather(
        [Claim("Ado.adoCharZero", "")],
        lambda *args: (
            "fixed-commit"
            if "commits/main" in args[1]
            else _tree([ADO], truncated=True)
        ),
    )
    assert "Not searched" in section
    assert "unchecked" in section
    assert "### " + ADO not in section


def test_inventory_failure_degrades_without_failing_review() -> None:
    """GitHub outages leave explicit uncertainty rather than empty prior art."""

    def run_gh(*args):
        raise subprocess.CalledProcessError(1, "gh")

    section = tauceti_prior_art.gather([Claim("Ado.adoCharZero", "")], run_gh)
    assert "unchecked" in section


def test_failed_source_fetch_and_missing_match_remain_unverifiable() -> None:
    """Neither a failed fetch nor lexical silence proves novelty."""

    def run_gh(*args):
        if "commits/main" in args[1]:
            return "fixed-commit"
        if "git/trees" in args[1]:
            return _tree([ADO])
        raise subprocess.CalledProcessError(1, "gh")

    section = tauceti_prior_art.gather(
        [Claim("Ado.adoCharZero", ""), Claim("Unrelated.xyz", "")], run_gh
    )
    assert "Source fetch failed; statement unchecked" in section
    assert "no lexical candidates" in section
    assert "say unverifiable" in section


def test_long_source_preserves_head_and_tail_with_omission_notice() -> None:
    """A long module's endpoint theorem remains visible within the budget."""
    source = "HEAD" + "x" * 20_000 + "TAIL"
    section = tauceti_prior_art._source(ADO, "commit", lambda *args: source)
    assert "HEAD" in section and "TAIL" in section
    assert "Middle of source omitted" in section
    assert len(section) < tauceti_prior_art.SOURCE_CHARACTERS + 500


def test_no_headlines_do_not_call_github() -> None:
    """Deletion-only PRs need no Tau Ceti source lookup."""

    def run_gh(*args):
        raise AssertionError("No GitHub calls expected")

    assert "No new headline" in tauceti_prior_art.gather([], run_gh)


def test_project_review_receives_tauceti_even_without_mathlib_key(
    monkeypatch, tmp_path
) -> None:
    """Mathlib credentials do not gate the independent Tau Ceti comparison."""
    from lean_pool import review

    registry = tmp_path / "LeanPool" / "projects.yml"
    registry.parent.mkdir()
    registry.write_text("projects: []\n")
    monkeypatch.setattr(review, "REPO_ROOT", tmp_path)
    monkeypatch.setattr(
        review,
        "fetch_file_at",
        lambda *args: (
            "projects:\n- slug: ado\n  main_results:\n"
            "  - declaration: Ado.adoCharZero\n"
        ),
    )
    monkeypatch.delenv("LEANEXPLORE_API_KEY", raising=False)
    monkeypatch.setattr(
        review,
        "run_gh",
        lambda *args: (
            "fixed-commit"
            if "commits/main" in args[1]
            else _tree([ADO])
            if "git/trees" in args[1]
            else "theorem TauCeti.adoCharZero : True := trivial"
        ),
    )
    section = review.gather_prior_art("project", "head", "o/r")
    assert "LEANEXPLORE_API_KEY is not set" in section
    assert "TauCeti.adoCharZero : True" in section


def test_pinned_worker_compares_against_pr_base(monkeypatch) -> None:
    """Projects merged after the engine pin must not become new PR claims."""
    from lean_pool import review

    base = """projects:
  - slug: accepted
    title: Accepted project
    main_results:
      - declaration: acceptedTheorem
"""
    head = (
        base
        + """  - slug: new
    title: New project
    main_results:
      - declaration: newTheorem
"""
    )
    fetched = []

    def fetch(path, ref, repository):
        fetched.append(ref)
        return head if ref == "head" else base

    claims_seen = []
    monkeypatch.setattr(review, "fetch_file_at", fetch)
    monkeypatch.setattr(review.prior_art, "search_mathlib", lambda claims: ({}, None))
    monkeypatch.setattr(
        review.tauceti_prior_art,
        "gather",
        lambda claims, run_gh: claims_seen.extend(claims) or "TauCeti evidence",
    )
    section = review.gather_prior_art("project", "head", "o/r", base_sha="base")
    assert fetched == ["head", "base"]
    assert [claim.declaration for claim in claims_seen] == ["newTheorem"]
    assert "accepted: Accepted project" in section


@pytest.mark.parametrize("base_sha", ["base", ""])
def test_unreadable_pr_base_is_unchecked(monkeypatch, base_sha) -> None:
    """A failed base lookup must not use the pinned registry as a fallback."""
    from lean_pool import review

    monkeypatch.setattr(
        review,
        "fetch_file_at",
        lambda path, ref, repository: "projects: []" if ref == "head" else "",
    )
    monkeypatch.setattr(
        review.prior_art, "search_mathlib", lambda claims: pytest.fail("must skip")
    )
    section = review.gather_prior_art("project", "head", "o/r", base_sha=base_sha)
    assert "could not be read at base" in section
    assert "did not run" in section
    assert "Tau Ceti prior art is unchecked" in section


@pytest.mark.parametrize("base_available", [True, False])
def test_standalone_reviewer_supplies_pr_base(monkeypatch, base_available) -> None:
    """A CLI review must use the PR baseline even with an older engine checkout."""
    from lean_pool import review

    fetched = []
    result = SimpleNamespace(truncation=None, model="model", effort=None)

    def gather(kind, head, repository, *, base_sha):
        fetched.append((kind, head, repository, base_sha))
        return "TauCeti evidence"

    def rubrics(**kwargs):
        assert kwargs["prior_art_section"] == "TauCeti evidence"
        return [SimpleNamespace(result=result)]

    def run_gh(*args):
        assert args[-1] == ".base.sha"
        if not base_available:
            raise subprocess.CalledProcessError(1, "gh")
        return "base\n"

    monkeypatch.setenv("PR_NUMBER", "7")
    monkeypatch.setenv("REVIEW_HEAD_SHA", "head")
    monkeypatch.delenv("REVIEW_EVIDENCE_PATH", raising=False)
    for name, value in {
        "resolve_repo_full_name": lambda: "o/r",
        "fetch_pr_files": lambda *args: [("LeanPool/New/Basic.lean", "added")],
        "fetch_head_sha": lambda *args: "head",
        "fetch_diff": lambda *args: "diff",
        "fetch_pr_context": lambda *args: review.PullRequestContext("title", ""),
        "run_gh": run_gh,
        "gather_prior_art": gather,
        "run_project_rubrics": rubrics,
        "aggregate_verdict": lambda *args: "approve",
        "render_rubric_comment": lambda *args, **kwargs: "comment",
        "post_comment": lambda *args, **kwargs: None,
    }.items():
        monkeypatch.setattr(review, name, value)
    assert review.main() == 0
    assert fetched == [("project", "head", "o/r", "base" if base_available else "")]
