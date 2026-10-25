"""Tests for deterministic repository quality checks."""

from __future__ import annotations

import json
import subprocess
from pathlib import Path
from unittest.mock import patch

import pytest

from lean_pool.quality import (
    _audit_axioms,
    _parse_axiom_output,
    _parse_declarations,
    _parse_option_audit_output,
    _project_card,
    _strip_lean_comments,
    _write_project_card,
    run_checks,
)

HEADER = """/-
Copyright (c) 2026 Test Author. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Test Author
-/
"""


def _write_minimal_repo(root: Path, basic_body: str = 'def hello := "world"\n') -> None:
    """Create the smallest LeanPool tree accepted by static checks."""
    (root / "LeanPool").mkdir()
    (root / "LeanPool.lean").write_text("import LeanPool.Basic\n")
    (root / "LeanPool" / "Basic.lean").write_text(f"{HEADER}\n{basic_body}")
    (root / "LeanPool" / "projects.yml").write_text("projects: []\n")
    (root / "lakefile.toml").write_text(
        'name = "lean-pool"\nversion = "0.1.0"\ndefaultTargets = ["LeanPool"]\n'
    )


def _write_project_yaml(root: Path, projects: list[dict[str, str | None]]) -> None:
    """Write a `projects.yml` containing the given project entries.

    Each entry uses an `arxiv` source and the `[test]` tag set by default. A
    `github_repo` is emitted unless the entry maps `github_repo` to `None`.
    """
    lines = ["projects:"]
    for project in projects:
        source_lines = [
            "    source:",
            f'      arxiv: "{project.get("arxiv", "1234.5678")}"',
        ]
        github_repo = project.get("github_repo", "test-owner/test-repo")
        if github_repo is not None:
            source_lines.append(f"      github_repo: {github_repo}")
        lines.extend(
            [
                f"  - slug: {project['slug']}",
                f"    title: {project.get('title', 'Test Project')}",
                f"    summary: {project.get('summary', 'A test project.')}",
                f"    branch: {project.get('branch', 'test mathematics')}",
                f"    entry_module: {project['entry_module']}",
                "    authors: [Test Author]",
                *source_lines,
                f"    license: {project.get('license', 'Apache-2.0')}",
                f"    status: {project.get('status', 'verified')}",
                f"    provenance: {project.get('provenance', 'human')}",
                "    main_declarations: [hello]",
                "    main_results:",
                "      - declaration: hello",
                "        informal: A test result.",
                "    tags: [test]",
                "    msc: ['00A35']",
            ]
        )
    (root / "LeanPool" / "projects.yml").write_text("\n".join(lines) + "\n")


def test_strip_lean_comments_preserves_code_not_comments() -> None:
    """Forbidden tokens in comments and strings are ignored."""
    stripped = _strip_lean_comments(
        "-- set_option maxHeartbeats 0\n"
        'def label := "sorry"\n'
        "/- admit -/\n"
        "def safe := 1\n"
    )

    assert "set_option" not in stripped
    assert "sorry" not in stripped
    assert "admit" not in stripped
    assert "def safe := 1" in stripped


@pytest.mark.parametrize(
    ("text", "expected"),
    [
        ("α /- outer /- sorry -/ end -/ β", "α " + " " * 27 + " β"),
        ('"a\\"sorry" def safe := 1', " " * 10 + " def safe := 1"),
        ('"a\\\\"sorry', " " * 5 + "sorry"),
        ('"α\nβ"\ndef safe := 1', "  \n  \ndef safe := 1"),
        ("-- sorry\r\ndef safe := 1", " " * 9 + "\ndef safe := 1"),
        ("/- α\n/- nested -/", " " * 4 + "\n" + " " * 12),
        ('"unfinished\\', " " * 12),
        ("def safe := 1 -- sorry", "def safe := 1 " + " " * 8),
    ],
)
def test_strip_comments_preserves_offsets_with_nested_and_escaped_tokens(
    text: str, expected: str
) -> None:
    """Nested comments, escapes, and unfinished tokens retain diagnostic locations."""
    assert _strip_lean_comments(text) == expected
    assert len(expected) == len(text)


def test_minimal_repo_passes_static_quality_checks(tmp_path: Path) -> None:
    """A compliant minimal repo passes without invoking Lean."""
    _write_minimal_repo(tmp_path)

    assert run_checks(tmp_path, skip_lean_axioms=True) == []


def test_nested_project_requires_top_level_entry(tmp_path: Path) -> None:
    """A nested entry fails without its wrapper and passes once it is supplied."""
    _write_minimal_repo(tmp_path, basic_body="")
    project = tmp_path / "LeanPool" / "MyProj"
    project.mkdir()
    (project / "Internal.lean").write_text(
        f"{HEADER}\n{_project_card(_PROJECT_FIXTURE)}\ndef hello := 1\n"
    )
    (tmp_path / "LeanPool.lean").write_text(
        "import LeanPool.Basic\nimport LeanPool.MyProj.Internal\n"
    )
    _write_project_yaml(
        tmp_path, [{"slug": "p", "entry_module": "LeanPool.MyProj.Internal"}]
    )
    entry = tmp_path / "LeanPool" / "MyProj.lean"
    errors = run_checks(tmp_path, skip_lean_axioms=True, skip_project_declarations=True)

    assert any(
        error.path == entry and "missing top-level project entry" in error.message
        for error in errors
    )

    entry.write_text(HEADER)
    (tmp_path / "LeanPool.lean").write_text(
        "import LeanPool.Basic\nimport LeanPool.MyProj\n"
        "import LeanPool.MyProj.Internal\n"
    )
    errors = run_checks(tmp_path, skip_lean_axioms=True, skip_project_declarations=True)

    assert any(
        error.path == entry and "not reachable" in error.message for error in errors
    )

    entry.write_text(f"{HEADER}\nimport LeanPool.MyProj.Internal\n")
    errors = run_checks(tmp_path, skip_lean_axioms=True, skip_project_declarations=True)

    assert errors == []


def test_nested_project_wrapper_allows_transitive_imports(tmp_path: Path) -> None:
    """A wrapper can export its registered entry through an intermediate module."""
    _write_minimal_repo(tmp_path, basic_body="")
    project = tmp_path / "LeanPool" / "MyProj"
    project.mkdir()
    (project / "Internal.lean").write_text(
        f"{HEADER}\n{_project_card(_PROJECT_FIXTURE)}\ndef hello := 1\n"
    )
    (project / "Bridge.lean").write_text(f"{HEADER}\nimport LeanPool.MyProj.Internal\n")
    (tmp_path / "LeanPool" / "MyProj.lean").write_text(
        f"{HEADER}\nimport LeanPool.MyProj.Bridge\n"
    )
    (tmp_path / "LeanPool.lean").write_text(
        "import LeanPool.Basic\nimport LeanPool.MyProj\n"
        "import LeanPool.MyProj.Internal\n"
    )
    _write_project_yaml(
        tmp_path, [{"slug": "p", "entry_module": "LeanPool.MyProj.Internal"}]
    )

    errors = run_checks(tmp_path, skip_lean_axioms=True, skip_project_declarations=True)

    assert errors == []


def test_quality_check_rejects_set_option(tmp_path: Path) -> None:
    """Lean files may not override options locally."""
    _write_minimal_repo(tmp_path, "set_option maxHeartbeats 0\n\ndef hello := 1\n")

    errors = run_checks(tmp_path, skip_lean_axioms=True)

    assert any("set_option is forbidden" in error.message for error in errors)


def test_quality_check_rejects_programmatic_option_manipulation(
    tmp_path: Path,
) -> None:
    """The PR #278 bypass — `withOptions` in an elaborator — is rejected."""
    _write_minimal_repo(
        tmp_path,
        "elab_rules : command\n"
        "  | `(lrat_semantic) => do\n"
        "      Command.liftTermElabM do\n"
        "        withOptions (fun options => options.set `maxRecDepth"
        " (100000 : Nat)) do\n"
        "          pure ()\n"
        "\n"
        "def hello := 1\n",
    )

    errors = run_checks(tmp_path, skip_lean_axioms=True)

    assert any(
        "programmatic option manipulation is forbidden" in error.message
        for error in errors
    )
    assert any(
        "gated option name in code is forbidden" in error.message for error in errors
    )


def test_quality_check_rejects_gated_option_name_in_code(tmp_path: Path) -> None:
    """Receiver-variable spellings like `opts.set` cannot slip through."""
    _write_minimal_repo(
        tmp_path,
        "def tweak (opts : Lean.Options) : Lean.Options :=\n"
        "  opts.set `maxHeartbeats 400000\n"
        "\n"
        "def hello := 1\n",
    )

    errors = run_checks(tmp_path, skip_lean_axioms=True)

    assert any(
        "gated option name in code is forbidden" in error.message for error in errors
    )


def test_quality_check_rejects_linter_option_name_in_code(tmp_path: Path) -> None:
    """Backtick-quoted linter option names are programmatic waiver material."""
    _write_minimal_repo(
        tmp_path,
        "def waiver := `linter.unusedVariables\n\ndef hello := 1\n",
    )

    errors = run_checks(tmp_path, skip_lean_axioms=True)

    assert any(
        "gated option name in code is forbidden" in error.message for error in errors
    )


def test_quality_check_allows_option_names_in_comments_and_identifiers(
    tmp_path: Path,
) -> None:
    """Option talk in comments and names like `maxRecDepth_bound` are fine."""
    _write_minimal_repo(
        tmp_path,
        "-- a large `decide`; upstream increases `maxHeartbeats` to avoid timeouts\n"
        "/- `withOptions` and `set_option maxRecDepth` are banned here. -/\n"
        "theorem maxRecDepth_bound : 1 = 1 := rfl\n"
        "\n"
        "def hello := 1\n",
    )

    errors = run_checks(tmp_path, skip_lean_axioms=True)

    assert not any(
        "programmatic option manipulation" in error.message for error in errors
    )
    assert not any("gated option name" in error.message for error in errors)


def test_parse_option_audit_output_reports_findings(tmp_path: Path) -> None:
    """Environment-audit findings map to the module's file with the detail."""
    stdout = (
        "LEANPOOL_OPTION_AUDIT|LeanPool.Evil.Lrat|Evil.elabRule|references "
        "forbidden option-manipulating constants: "
        "Lean.MonadWithOptions.withOptions; embeds forbidden gated option "
        'name "maxRecDepth"\n'
        "LEANPOOL_OPTION_AUDIT_COMPLETE\n"
    )

    errors = _parse_option_audit_output(tmp_path, stdout, "")

    assert len(errors) == 1
    assert errors[0].path == tmp_path / "LeanPool" / "Evil" / "Lrat.lean"
    assert (
        "Evil.elabRule references forbidden option-manipulating constants"
        in errors[0].message
    )


def test_parse_option_audit_output_accepts_clean_run(tmp_path: Path) -> None:
    """A completed audit with no findings yields no errors."""
    assert not _parse_option_audit_output(
        tmp_path, "LEANPOOL_OPTION_AUDIT_COMPLETE\n", ""
    )


def test_parse_option_audit_output_fails_closed_without_marker(tmp_path: Path) -> None:
    """A crashed or non-compiling audit must fail the run, not pass silently."""
    errors = _parse_option_audit_output(tmp_path, "", "error: script broke\nmore")

    assert len(errors) == 1
    assert "option-manipulation audit did not complete" in errors[0].message
    assert "error: script broke" in errors[0].message


def test_quality_check_rejects_nolint_attribute(tmp_path: Path) -> None:
    """Lean files may not waive linters with `@[nolint ...]`."""
    _write_minimal_repo(
        tmp_path,
        "@[nolint unusedArguments]\ndef hello (_n : Nat) := 1\n",
    )

    errors = run_checks(tmp_path, skip_lean_axioms=True)

    assert any("nolint waiver is forbidden" in error.message for error in errors)


def test_quality_check_rejects_nolint_command(tmp_path: Path) -> None:
    """Lean files may not waive linters with `attribute [nolint ...]`."""
    _write_minimal_repo(
        tmp_path,
        "def hello := 1\nattribute [nolint docBlame] hello\n",
    )

    errors = run_checks(tmp_path, skip_lean_axioms=True)

    assert any("nolint waiver is forbidden" in error.message for error in errors)


def test_quality_check_rejects_style_linter_allowlist_entry(tmp_path: Path) -> None:
    """The style-linter allowlist file may not carry active entries."""
    _write_minimal_repo(tmp_path)
    (tmp_path / "scripts").mkdir()
    (tmp_path / "scripts" / "nolints-style.txt").write_text(
        "-- comments are fine\nLeanPool/Basic.lean:12\n"
    )

    errors = run_checks(tmp_path, skip_lean_axioms=True)

    assert any("style linter waiver is forbidden" in error.message for error in errors)


def test_quality_check_rejects_unreachable_lean_file(tmp_path: Path) -> None:
    """Every Lean file under LeanPool must be imported by LeanPool.lean."""
    _write_minimal_repo(tmp_path)
    (tmp_path / "LeanPool" / "Extra.lean").write_text(f"{HEADER}\ndef extra := 1\n")

    errors = run_checks(tmp_path, skip_lean_axioms=True)

    assert any("not reachable" in error.message for error in errors)


def test_quality_check_requires_direct_project_entry_import(tmp_path: Path) -> None:
    """Transitive reachability does not replace a root import for each project."""
    _write_minimal_repo(tmp_path, "def baseHello := 1\n")
    wrapper = tmp_path / "LeanPool" / "Wrapper"
    wrapper.mkdir()
    (tmp_path / "LeanPool.lean").write_text(
        "import LeanPool.Basic\nimport LeanPool.Wrapper.Internal\n"
    )
    (wrapper / "Internal.lean").write_text(f"{HEADER}\nimport LeanPool.MyProj\n")
    card = _project_card(_PROJECT_FIXTURE)
    (tmp_path / "LeanPool" / "MyProj.lean").write_text(
        f"{HEADER}\n\n{card}\n\ndef hello := 1\n"
    )
    _write_project_yaml(tmp_path, [{"slug": "p", "entry_module": "LeanPool.MyProj"}])

    errors = run_checks(tmp_path, skip_lean_axioms=True)

    assert not any("not reachable" in error.message for error in errors)
    assert any(
        "project entry module LeanPool.MyProj is not imported by LeanPool.lean"
        in error.message
        for error in errors
    )


def test_quality_check_rejects_missing_project_metadata(tmp_path: Path) -> None:
    """Project metadata is required even before there are projects."""
    _write_minimal_repo(tmp_path)
    (tmp_path / "LeanPool" / "projects.yml").unlink()

    errors = run_checks(tmp_path, skip_lean_axioms=True)

    assert any("missing LeanPool/projects.yml" in error.message for error in errors)


def test_quality_check_rejects_top_level_project_missing_from_metadata(
    tmp_path: Path,
) -> None:
    """Every direct `LeanPool.Foo` project module must be registered."""
    _write_minimal_repo(tmp_path)
    (tmp_path / "LeanPool.lean").write_text(
        "import LeanPool.Basic\nimport LeanPool.MyProj\n"
    )
    (tmp_path / "LeanPool" / "MyProj.lean").write_text(
        f"{HEADER}\nimport LeanPool.Basic\n\ndef project_decl := hello\n"
    )

    errors = run_checks(tmp_path, skip_lean_axioms=True)

    assert any("LeanPool.MyProj missing from projects.yml" in e.message for e in errors)


def test_quality_check_allows_extra_documented_main_results(tmp_path: Path) -> None:
    """`main_results` may document more results than the compact card list."""
    _write_minimal_repo(tmp_path)
    (tmp_path / "LeanPool.lean").write_text(
        "import LeanPool.Basic\nimport LeanPool.MyProj\n"
    )
    card = _project_card(_PROJECT_FIXTURE)
    (tmp_path / "LeanPool" / "MyProj.lean").write_text(
        f"{HEADER}\nimport LeanPool.Basic\n\n{card}\n"
        "def hello : Nat := 1\n"
        "def extra : Nat := 2\n"
    )
    _write_project_yaml(tmp_path, [{"slug": "p", "entry_module": "LeanPool.MyProj"}])
    projects = tmp_path / "LeanPool" / "projects.yml"
    projects.write_text(
        projects.read_text().replace(
            "    tags: [test]\n",
            "      - declaration: extra\n"
            "        informal: Another documented result.\n"
            "    tags: [test]\n",
        )
    )

    errors = run_checks(tmp_path, skip_lean_axioms=True)

    assert not any(
        "main_results missing main declarations" in e.message for e in errors
    )


def test_quality_check_finds_prefixed_declarations(tmp_path: Path) -> None:
    """The axiom audit declaration parser handles common Lean prefixes."""
    _write_minimal_repo(
        tmp_path,
        "@[simp] theorem decorated_identity (n : Nat) : n = n := rfl\n",
    )

    declarations = _parse_declarations(tmp_path)

    assert any(declaration.name == "decorated_identity" for declaration in declarations)


def test_quality_check_parses_declaration_with_prime_suffix(tmp_path: Path) -> None:
    r"""Trailing primes must survive declaration parsing.

    Regression: the original regex used `\b` after `[A-Za-z_][A-Za-z0-9_'.]*`,
    but `\b` does not treat `'` as a word character, so `lemma foo'` was
    parsed as `foo` and the subsequent `#print axioms` audit failed with
    `unknown constant`.
    """
    _write_minimal_repo(tmp_path, "theorem foo' (n : Nat) : n = n := rfl\n")

    declarations = _parse_declarations(tmp_path)

    assert any(declaration.name == "foo'" for declaration in declarations)
    assert not any(declaration.name == "foo" for declaration in declarations)


def test_quality_check_parses_unicode_declaration_name(tmp_path: Path) -> None:
    """Unicode in declaration names (subscripts, Greek) must not be truncated.

    Regression: an ASCII-only `[A-Za-z0-9_'.]` name pattern parsed `c₀_pos`
    as `c`, so the `#print axioms` audit then failed with `unknown constant`.
    """
    _write_minimal_repo(tmp_path, "theorem c₀_pos (n : Nat) : n = n := rfl\n")

    declarations = _parse_declarations(tmp_path)

    assert any(declaration.name == "c₀_pos" for declaration in declarations)
    assert not any(declaration.name == "c" for declaration in declarations)


def test_quality_check_strips_root_escape_from_declaration_name(tmp_path: Path) -> None:
    """`theorem _root_.Foo.bar` is recorded as `Foo.bar`, not the escaped form.

    Regression: the escape prefix was kept, so the audit emitted
    `#print axioms _root_._root_.Foo.bar` and failed.
    """
    _write_minimal_repo(
        tmp_path,
        "namespace Ns\ntheorem _root_.Foo.bar : True := trivial\nend Ns\n",
    )

    names = {declaration.name for declaration in _parse_declarations(tmp_path)}

    assert "Foo.bar" in names
    assert "_root_.Foo.bar" not in names
    assert "Ns.Foo.bar" not in names


def test_quality_check_section_inside_namespace_keeps_namespace(
    tmp_path: Path,
) -> None:
    """A `section ... end` nested in a `namespace` must not pop the namespace.

    Regression: `end <section>` popped the enclosing namespace, so every
    declaration after the first nested section was recorded unqualified and the
    `#print axioms` audit then failed with `unknown constant`.
    """
    _write_minimal_repo(
        tmp_path,
        "namespace Ns\n"
        "section A\n"
        "theorem before : True := trivial\n"
        "end A\n"
        "section B\n"
        "theorem after : True := trivial\n"
        "end B\n"
        "end Ns\n",
    )

    names = {declaration.name for declaration in _parse_declarations(tmp_path)}

    assert "Ns.before" in names
    assert "Ns.after" in names
    assert "before" not in names
    assert "after" not in names


@pytest.mark.parametrize(
    "header",
    [
        f"{expose}{public}{noncomputable}{meta}section"
        for expose in ("", "@[expose] ")
        for public in ("", "public ")
        for noncomputable in ("", "noncomputable ")
        for meta in ("", "meta ")
    ],
)
@pytest.mark.parametrize("label", ["", "LocalSection"])
def test_quality_check_modified_section_keeps_namespace(
    tmp_path: Path, header: str, label: str
) -> None:
    """Every Lean section-header combination must balance its closing end."""
    suffix = f" {label}" if label else ""
    _write_minimal_repo(
        tmp_path,
        "namespace Ns\n"
        f"{header}{suffix}\n"
        "theorem before : True := trivial\n"
        "namespace Inner\n"
        "theorem nested : True := trivial\n"
        "end Inner\n"
        f"end{suffix}\n"
        "theorem after : True := trivial\n"
        "end Ns\n"
        "theorem outside : True := trivial\n",
    )

    names = [declaration.name for declaration in _parse_declarations(tmp_path)]

    assert names == ["Ns.before", "Ns.Inner.nested", "Ns.after", "outside"]


@pytest.mark.parametrize("opening", ["namespace A.B", "namespace A\nnamespace B"])
@pytest.mark.parametrize("closing", ["end A.B", "end B\nend A"])
def test_quality_check_dotted_namespace_scopes(
    tmp_path: Path, opening: str, closing: str
) -> None:
    """Dotted opens and ends represent one scope per name component."""
    _write_minimal_repo(
        tmp_path,
        "namespace Outer\n"
        f"{opening}\n"
        "theorem nested : True := trivial\n"
        f"{closing}\n"
        "theorem after : True := trivial\n"
        "end Outer\n"
        "theorem outside : True := trivial\n",
    )

    names = [declaration.name for declaration in _parse_declarations(tmp_path)]

    assert names == ["Outer.A.B.nested", "Outer.after", "outside"]


def test_quality_check_partial_namespace_end_and_dotted_section(tmp_path: Path) -> None:
    """Ending one component preserves the rest; dotted section names also balance."""
    _write_minimal_repo(
        tmp_path,
        "namespace A.B\n"
        "end B\n"
        "section Local.Inner\n"
        "theorem inside : True := trivial\n"
        "end Inner\n"
        "theorem middle : True := trivial\n"
        "end Local\n"
        "theorem after : True := trivial\n"
        "end A\n"
        "theorem outside : True := trivial\n",
    )

    names = [declaration.name for declaration in _parse_declarations(tmp_path)]

    assert names == ["A.inside", "A.middle", "A.after", "outside"]


def test_quality_check_dotted_name_inside_namespace_is_qualified(
    tmp_path: Path,
) -> None:
    """`theorem Foo.bar` inside `namespace Ns` is recorded as `Ns.Foo.bar`.

    Regression: dotted declaration names skipped namespace qualification, so the
    audit emitted `#print axioms _root_.Foo.bar` (the unqualified name) and
    failed even though the real declaration is `Ns.Foo.bar`.
    """
    _write_minimal_repo(
        tmp_path,
        "namespace Ns\ntheorem Foo.bar : True := trivial\nend Ns\n",
    )

    names = {declaration.name for declaration in _parse_declarations(tmp_path)}

    assert "Ns.Foo.bar" in names
    assert "Foo.bar" not in names


def test_quality_check_rejects_oversized_file(tmp_path: Path) -> None:
    """Files over the 10000-line cap fail; there is no waiver."""
    _write_minimal_repo(tmp_path)
    body = "def x := 0\n" * 10001
    (tmp_path / "LeanPool" / "Basic.lean").write_text(f"{HEADER}\n{body}")

    errors = run_checks(tmp_path, skip_lean_axioms=True)

    assert any("limit is 10000" in error.message for error in errors)


def test_quality_check_does_not_honor_size_marker(tmp_path: Path) -> None:
    """The old `-- size-limit-ok:` waiver is gone: the marker has no effect."""
    _write_minimal_repo(tmp_path)
    body = "-- size-limit-ok: should be ignored\n" + "def x := 0\n" * 10001
    (tmp_path / "LeanPool" / "Basic.lean").write_text(f"{HEADER}\n{body}")

    errors = run_checks(tmp_path, skip_lean_axioms=True)

    assert any("limit is 10000" in error.message for error in errors)


_PROJECT_FIXTURE = {
    "slug": "p",
    "title": "Test Project",
    "summary": "A test project.",
    "branch": "test mathematics",
    "entry_module": "LeanPool.MyProj",
    "authors": ["Test Author"],
    "source": {"arxiv": "1234.5678"},
    "license": "Apache-2.0",
    "status": "verified",
    "provenance": "human",
    "main_declarations": ["hello"],
    "main_results": [{"declaration": "hello", "informal": "A test result."}],
    "tags": ["test"],
    "msc": ["00A35"],
}


def test_write_project_card_inserts_card_after_imports(tmp_path: Path) -> None:
    """The card writer must place the card after imports, not before them.

    Regression: the previous implementation inserted the card right after
    the copyright header — Lean then rejected the file with "invalid
    'import' command, it must be used in the beginning of the file" because
    the imports came after a non-import block.
    """
    entry = tmp_path / "MyProj.lean"
    entry.write_text(
        f"{HEADER}\nimport Mathlib.Tactic\nimport Mathlib.Data.Nat.Basic\n\n"
        "def hello : Nat := 1\n"
    )
    _write_project_card(entry, _project_card(_PROJECT_FIXTURE))
    text = entry.read_text()
    header_end = text.find("-/") + 2
    body = text[header_end:].lstrip("\n")
    assert body.startswith("import "), (
        "imports must come immediately after the copyright header; got:\n" + body[:200]
    )
    assert "/-!\n# Test Project" in text
    assert text.index("import ") < text.index("/-!\n# Test Project"), (
        "the project card must come AFTER the import block"
    )


def test_write_project_card_replaces_existing_card(tmp_path: Path) -> None:
    """Running the writer again with a changed source must not double the card.

    Regression: the previous implementation only stripped a card sitting
    immediately after the copyright header. A card living in the canonical
    post-imports location was left alone, so a writer run after a source
    edit produced two cards in the same file.
    """
    entry = tmp_path / "MyProj.lean"
    initial = _project_card(_PROJECT_FIXTURE)
    entry.write_text(
        f"{HEADER}\nimport Mathlib.Tactic\n\n{initial}\n\ndef hello : Nat := 1\n"
    )
    updated_fixture = {**_PROJECT_FIXTURE, "source": {"doi": "10.0/x.y"}}
    _write_project_card(entry, _project_card(updated_fixture))
    text = entry.read_text()
    assert text.count("/-!\n# Test Project") == 1, (
        "there should be exactly one project card; got:\n" + text
    )
    assert "Source: doi:10.0/x.y" in text
    assert "Source: arxiv:1234.5678" not in text


def test_project_card_lists_all_source_identifiers() -> None:
    """A project with several source keys renders them all, in arxiv/doi/url order."""
    project = {**_PROJECT_FIXTURE, "source": {"doi": "10.0/x.y", "arxiv": "1234.5678"}}
    assert "Source: arxiv:1234.5678, doi:10.0/x.y" in _project_card(project)


def test_write_project_card_moves_misplaced_card(tmp_path: Path) -> None:
    """A file written by the old buggy writer (card before imports) is repaired.

    Regression: when bumping/repairing files left by the previous writer,
    the current writer must produce a Lean-valid file (imports first) even
    when it finds the card in the wrong place.
    """
    entry = tmp_path / "MyProj.lean"
    card = _project_card(_PROJECT_FIXTURE)
    # buggy old layout: card BEFORE imports (Lean rejects this)
    entry.write_text(
        f"{HEADER}\n{card}\n\nimport Mathlib.Tactic\n\ndef hello : Nat := 1\n"
    )
    _write_project_card(entry, _project_card(_PROJECT_FIXTURE))
    text = entry.read_text()
    assert text.index("import Mathlib.Tactic") < text.index("/-!\n# Test Project"), (
        "after rewriting, imports must precede the project card; got:\n" + text
    )
    assert text.count("/-!\n# Test Project") == 1


def test_quality_check_accepts_project_card_after_imports(tmp_path: Path) -> None:
    """Regression test for e161b8c: project card may follow imports.

    Mathlib convention places imports between the file header and the module
    docstring. The earlier check required the docstring at byte offset 0 of the
    body and rejected this layout.
    """
    _write_minimal_repo(tmp_path)
    (tmp_path / "LeanPool.lean").write_text(
        "import LeanPool.Basic\nimport LeanPool.MyProj\n"
    )
    card = _project_card(_PROJECT_FIXTURE)
    (tmp_path / "LeanPool" / "MyProj.lean").write_text(
        f"{HEADER}\nimport LeanPool.Basic\n\n{card}\ndef hello : Nat := 1\n"
    )
    _write_project_yaml(tmp_path, [{"slug": "p", "entry_module": "LeanPool.MyProj"}])

    errors = run_checks(tmp_path, skip_lean_axioms=True)

    # The project-card position check must accept this layout. (lake env lean
    # for the declarations check fails in the test sandbox; that's unrelated.)
    assert not any("project card for p is out of date" in e.message for e in errors)


def test_quality_check_falls_back_when_lake_missing(tmp_path: Path) -> None:
    """A missing `lake` binary yields a single advisory error, not a crash.

    The python_ci job runs without a Lean toolchain, so the subprocess
    that invokes ``lake env lean`` raises ``FileNotFoundError``. The
    quality module must catch that and emit a clear "skipped" message
    rather than aborting the whole run.
    """
    _write_minimal_repo(tmp_path)
    (tmp_path / "LeanPool.lean").write_text(
        "import LeanPool.Basic\nimport LeanPool.MyProj\n"
    )
    card = _project_card(_PROJECT_FIXTURE)
    (tmp_path / "LeanPool" / "MyProj.lean").write_text(
        f"{HEADER}\nimport LeanPool.Basic\n\n{card}\ndef hello : Nat := 1\n"
    )
    _write_project_yaml(tmp_path, [{"slug": "p", "entry_module": "LeanPool.MyProj"}])

    with patch(
        "lean_pool.quality.subprocess.run",
        side_effect=FileNotFoundError("[Errno 2] No such file or directory: 'lake'"),
    ):
        errors = run_checks(tmp_path)

    messages = [error.message for error in errors]
    assert any("`lake` not found" in message for message in messages)


def test_quality_check_rejects_non_verified_status(tmp_path: Path) -> None:
    """Only `status: verified` projects may merge; `draft` is not accepted."""
    _write_minimal_repo(tmp_path)
    _write_project_yaml(
        tmp_path,
        [{"slug": "p", "entry_module": "LeanPool.Basic", "status": "draft"}],
    )

    errors = run_checks(tmp_path, skip_lean_axioms=True)

    assert any("invalid status" in error.message for error in errors)


def test_quality_check_requires_license(tmp_path: Path) -> None:
    """Every project entry must declare a `license` field."""
    _write_minimal_repo(tmp_path)
    _write_project_yaml(tmp_path, [{"slug": "p", "entry_module": "LeanPool.Basic"}])
    projects = tmp_path / "LeanPool" / "projects.yml"
    projects.write_text(projects.read_text().replace("    license: Apache-2.0\n", ""))

    errors = run_checks(tmp_path, skip_lean_axioms=True)

    assert any(
        "missing fields" in error.message and "license" in error.message
        for error in errors
    )


def test_quality_check_rejects_non_permissive_license(tmp_path: Path) -> None:
    """Only permissive SPDX licenses (Apache-2.0 or MIT) are accepted."""
    _write_minimal_repo(tmp_path)
    _write_project_yaml(
        tmp_path,
        [{"slug": "p", "entry_module": "LeanPool.Basic", "license": "GPL-3.0"}],
    )

    errors = run_checks(tmp_path, skip_lean_axioms=True)

    assert any("invalid license" in error.message for error in errors)


def test_quality_check_requires_provenance(tmp_path: Path) -> None:
    """Every project entry must declare a `provenance` field."""
    _write_minimal_repo(tmp_path)
    _write_project_yaml(tmp_path, [{"slug": "p", "entry_module": "LeanPool.Basic"}])
    projects = tmp_path / "LeanPool" / "projects.yml"
    projects.write_text(projects.read_text().replace("    provenance: human\n", ""))

    errors = run_checks(tmp_path, skip_lean_axioms=True)

    assert any(
        "missing fields" in error.message and "provenance" in error.message
        for error in errors
    )


def test_quality_check_rejects_invalid_provenance(tmp_path: Path) -> None:
    """Provenance must be one of `human`, `AI`, or `mix`."""
    _write_minimal_repo(tmp_path)
    _write_project_yaml(
        tmp_path,
        [{"slug": "p", "entry_module": "LeanPool.Basic", "provenance": "robot"}],
    )

    errors = run_checks(tmp_path, skip_lean_axioms=True)

    assert any("invalid provenance" in error.message for error in errors)


def _axiom_output(
    declarations: list[dict],
    modules: list[str] | None = None,
) -> str:
    """Encode the environment audit's line-oriented JSON protocol."""
    modules = modules if modules is not None else ["LeanPool.Basic"]
    complete = {
        "kind": "complete",
        "modules": modules,
        "declarations": len(declarations),
    }
    return "".join(
        "LEANPOOL_AXIOM_AUDIT|" + json.dumps(record) + "\n"
        for record in [*declarations, complete]
    )


def _axiom_record(name: str = "foo", axioms: list[str] | None = None) -> dict:
    """Construct a declaration record with a compiler-provided source location."""
    return {
        "kind": "declaration",
        "module": "LeanPool.Basic",
        "name": name,
        "line": 12,
        "axioms": axioms if axioms is not None else [],
    }


@pytest.mark.parametrize("name", ["foo", "Ns.foo'", "Ns.odd name|with punctuation"])
@pytest.mark.parametrize("axioms", [[], ["propext", "Classical.choice", "Quot.sound"]])
def test_axiom_audit_accepts_allowed_results(
    tmp_path: Path, name: str, axioms: list[str]
) -> None:
    """JSON records need no Lean-name or pretty-printer parsing."""
    output = _axiom_output([_axiom_record(name, axioms)])
    assert _parse_axiom_output(tmp_path, ["LeanPool.Basic"], output) == []


def test_axiom_audit_accepts_empty_module(tmp_path: Path) -> None:
    """An explicitly completed module with no public declarations is valid."""
    assert _parse_axiom_output(tmp_path, ["LeanPool.Basic"], _axiom_output([])) == []


@pytest.mark.parametrize(
    "output",
    [
        "",
        "LEANPOOL_AXIOM_AUDIT|{broken JSON\n",
        "LEANPOOL_AXIOM_AUDIT|[]\n",
        _axiom_output([_axiom_record()]).splitlines()[0] + "\n",
        _axiom_output([]).replace('"declarations": 0', '"declarations": 1'),
        _axiom_output([], ["LeanPool.Other"]),
        _axiom_output([_axiom_record(), _axiom_record()]),
        _axiom_output([{**_axiom_record(), "module": "Mathlib.Other"}]),
        _axiom_output([{**_axiom_record(), "line": -1}]),
        _axiom_output([{**_axiom_record(), "axioms": "sorryAx"}]),
        _axiom_output([{**_axiom_record(), "axioms": [None]}]),
    ],
)
def test_axiom_audit_rejects_incomplete_or_invalid_output(
    tmp_path: Path, output: str
) -> None:
    """Malformed, partial, duplicate, or out-of-scope results fail closed."""
    errors = _parse_axiom_output(tmp_path, ["LeanPool.Basic"], output)
    assert errors
    assert "did not complete" in errors[0].message


def test_axiom_audit_rejects_nonzero_exit_with_completion(tmp_path: Path) -> None:
    """A completion marker cannot conceal a subprocess failure."""
    errors = _parse_axiom_output(
        tmp_path, ["LeanPool.Basic"], _axiom_output([]), "import failed", 1
    )
    assert len(errors) == 1
    assert "import failed" in errors[0].message


def test_axiom_audit_uses_environment_not_source_parser(tmp_path: Path) -> None:
    """Only module names are passed to Lean; source declaration parsing is unused."""
    with (
        patch("lean_pool.quality._declarations_in", side_effect=AssertionError),
        patch(
            "lean_pool.quality.subprocess.run",
            return_value=subprocess.CompletedProcess(
                [], 0, _axiom_output([_axiom_record()]), ""
            ),
        ) as run,
    ):
        assert _audit_axioms(tmp_path, ["LeanPool.Basic"]) == []
    command = run.call_args.args[0]
    assert command[:4] == ["lake", "env", "lean", "--run"]
    assert json.loads(run.call_args.kwargs["input"]) == ["LeanPool.Basic"]
    assert len(command) == 5
    assert not Path(command[4]).exists()


def test_axiom_audit_missing_lake_fails_closed(tmp_path: Path) -> None:
    """A missing toolchain is an audit failure, not an implicit pass."""
    with patch("lean_pool.quality.subprocess.run", side_effect=FileNotFoundError):
        errors = _audit_axioms(tmp_path, ["LeanPool.Basic"])
    assert len(errors) == 1
    assert "failed" in errors[0].message


def test_quality_check_rejects_duplicate_slug(tmp_path: Path) -> None:
    """Two projects sharing a slug must be rejected."""
    _write_minimal_repo(tmp_path)
    _write_project_yaml(
        tmp_path,
        [
            {"slug": "p", "entry_module": "LeanPool.Basic"},
            {"slug": "p", "entry_module": "LeanPool.Other"},
        ],
    )

    errors = run_checks(tmp_path, skip_lean_axioms=True)

    assert any(
        "duplicate `slug`" in error.message and "'p'" in error.message
        for error in errors
    )


def test_quality_check_rejects_duplicate_entry_module(tmp_path: Path) -> None:
    """Two projects sharing an entry_module must be rejected."""
    _write_minimal_repo(tmp_path)
    _write_project_yaml(
        tmp_path,
        [
            {"slug": "a", "entry_module": "LeanPool.Basic"},
            {"slug": "b", "entry_module": "LeanPool.Basic"},
        ],
    )

    errors = run_checks(tmp_path, skip_lean_axioms=True)

    assert any("duplicate `entry_module`" in error.message for error in errors)


def test_quality_check_rejects_out_of_order_header(tmp_path: Path) -> None:
    """The Copyright/License/Authors lines must appear in the documented order."""
    _write_minimal_repo(tmp_path)
    out_of_order = (
        "/-\n"
        "Authors: Test Author\n"
        "Copyright (c) 2026 Test Author. All rights reserved.\n"
        "Released under Apache 2.0 license as described in the file LICENSE.\n"
        "-/\n"
    )
    (tmp_path / "LeanPool" / "Basic.lean").write_text(
        f"{out_of_order}\ndef hello := 1\n"
    )

    errors = run_checks(tmp_path, skip_lean_axioms=True)

    assert any("malformed file header" in error.message for error in errors)


def test_quality_check_rejects_adhoc_metadata_in_header(tmp_path: Path) -> None:
    """Source/MSC/Tags/Status belong in projects.yml, not in file headers."""
    _write_minimal_repo(tmp_path)
    bad_header = (
        "/-\n"
        "Copyright (c) 2026 Test Author. All rights reserved.\n"
        "Released under Apache 2.0 license as described in the file LICENSE.\n"
        "Authors: Test Author\n"
        "Source: arxiv:1234.5678\n"
        "-/\n"
    )
    (tmp_path / "LeanPool" / "Basic.lean").write_text(f"{bad_header}\ndef hello := 1\n")

    errors = run_checks(tmp_path, skip_lean_axioms=True)

    assert any("malformed file header" in error.message for error in errors)


def test_quality_check_rejects_extra_axiom_status(tmp_path: Path) -> None:
    """`extra-axiom` status was previously valid; only `verified` is now accepted."""
    _write_minimal_repo(tmp_path)
    _write_project_yaml(
        tmp_path,
        [{"slug": "p", "entry_module": "LeanPool.Basic", "status": "extra-axiom"}],
    )

    errors = run_checks(tmp_path, skip_lean_axioms=True)

    assert any("invalid status" in error.message for error in errors)


def test_quality_check_rejects_source_without_github_repo(tmp_path: Path) -> None:
    """Every project source must name its upstream GitHub repo.

    Without `source.github_repo` the partial-port audit silently skips the
    project, so the quality check has to reject the omission instead.
    """
    _write_minimal_repo(tmp_path)
    _write_project_yaml(
        tmp_path,
        [{"slug": "p", "entry_module": "LeanPool.Basic", "github_repo": None}],
    )

    errors = run_checks(tmp_path, skip_lean_axioms=True)

    assert any("github_repo" in error.message for error in errors)


def test_quality_check_rejects_malformed_github_repo(tmp_path: Path) -> None:
    """A `github_repo` that is not an `owner/name` slug is rejected too.

    The partial-port audit's repo regex would reject the value and skip the
    project, so the quality check must reject the same shapes.
    """
    _write_minimal_repo(tmp_path)
    _write_project_yaml(
        tmp_path,
        [{"slug": "p", "entry_module": "LeanPool.Basic", "github_repo": "not-a-slug"}],
    )

    errors = run_checks(tmp_path, skip_lean_axioms=True)

    assert any("github_repo" in error.message for error in errors)


@pytest.mark.parametrize("proof", ["sorry", "by sorry", "by admit", "⟨sorry, trivial⟩"])
def test_quality_check_rejects_unproved_terms(tmp_path: Path, proof: str) -> None:
    """Completed projects reject proof holes in every source form."""
    _write_minimal_repo(tmp_path, f"theorem unfinished : True := {proof}\n")
    errors = run_checks(tmp_path, skip_lean_axioms=True)
    assert any(
        error.message in {"sorry is forbidden", "admit is forbidden"}
        for error in errors
    )


def test_axiom_audit_rejects_sorry_axiom(tmp_path: Path) -> None:
    """A compiled proof hole fails even when textual checks cannot see it."""
    errors = _parse_axiom_output(
        tmp_path,
        ["LeanPool.Basic"],
        _axiom_output([_axiom_record("unfinished", ["propext", "sorryAx"])]),
    )
    assert len(errors) == 1
    assert "unallowlisted axioms: sorryAx" in errors[0].message
    assert errors[0].path == tmp_path / "LeanPool/Basic.lean"
    assert errors[0].line == 12


@pytest.mark.parametrize("name", ["unfinished", "unfinished.eq_def"])
def test_environment_audit_rejects_proof_holes(tmp_path: Path, name: str) -> None:
    """Generated companions cannot hide a compiled proof hole."""
    errors = _parse_option_audit_output(
        tmp_path,
        f"LEANPOOL_OPTION_AUDIT|LeanPool.Basic|{name}|references "
        "forbidden axiom-injecting constants: sorryAx\n"
        "LEANPOOL_OPTION_AUDIT_COMPLETE\n",
        "",
    )
    assert len(errors) == 1
    assert "sorryAx" in errors[0].message


@pytest.mark.parametrize("extra", [[], ["sorryAx"], ["customAxiom"]])
def test_axiom_audit_reads_axiom_arrays(tmp_path: Path, extra: list[str]) -> None:
    """Structured axiom arrays preserve both safe and forbidden findings."""
    errors = _parse_axiom_output(
        tmp_path,
        ["LeanPool.Basic"],
        _axiom_output(
            [
                _axiom_record(
                    "Widget.long_theorem_name",
                    ["propext", "Classical.choice", "Quot.sound", *extra],
                )
            ]
        ),
    )
    assert bool(errors) == bool(extra)
    if extra:
        assert extra[0] in errors[0].message
