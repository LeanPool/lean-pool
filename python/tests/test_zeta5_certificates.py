"""Check exact and constrained rendering of the Zeta5 certificate archive."""

import hashlib
import importlib.util
import json
import shutil
from pathlib import Path, PureWindowsPath

import pytest

SCRIPT = Path(__file__).parents[2] / "scripts/zeta5-certificates/regenerate.py"
SPECIFICATION = importlib.util.spec_from_file_location("zeta5_regenerate", SCRIPT)
assert SPECIFICATION is not None and SPECIFICATION.loader is not None
GENERATOR = importlib.util.module_from_spec(SPECIFICATION)
SPECIFICATION.loader.exec_module(GENERATOR)


def test_exact_large_rational_and_name() -> None:
    """Preserve huge rational numerators, signs, names, and Unicode byte for byte."""
    template = (
        "lemma U_{{integer}} : (-( {{integer}} / {{integer}} : ℝ)) ≤ x := by\n"
        "  exact h\n"
    )
    numerator = "123456789012345678901234567890123456789"
    result = GENERATOR.render(template, ["12", numerator, "200000000000000000000"])
    assert (
        result
        == f"lemma U_12 : (-( {numerator} / 200000000000000000000 : ℝ)) ≤ x := by\n"
        "  exact h\n"
    )


@pytest.mark.parametrize("parameters", [[], ["1", "2"], ["1e100"], ["0; run"]])
def test_reject_invalid_parameters(parameters: list[str]) -> None:
    """Reject malformed or incomplete certificate data before rendering."""
    with pytest.raises(ValueError):
        GENERATOR.render("{{integer}}", parameters)


@pytest.mark.parametrize("path", ["../bad.lean", "/bad.lean", "LeanPool/Other/A.lean"])
def test_reject_output_outside_project(path: str) -> None:
    """Keep accidental manifest edits from writing unrelated files."""
    with pytest.raises(ValueError):
        GENERATOR.certificate_path(path)


def test_complete_archive(tmp_path: Path) -> None:
    """Regenerate every output and independently check its pinned hash."""
    archive = SCRIPT.parent / "archive"
    GENERATOR.verify_archive(archive)
    assert GENERATOR.regenerate(archive, tmp_path / "generated", False) == 118
    assert GENERATOR.regenerate(archive, tmp_path / "generated", True) == 118
    manifest = json.loads((archive / "manifest.json").read_text(encoding="utf-8"))
    first = tmp_path / "generated" / next(iter(manifest["files"]))
    first.write_text(
        first.read_text(encoding="utf-8") + "-- damaged\n", encoding="utf-8"
    )
    with pytest.raises(ValueError, match="Certificates differ"):
        GENERATOR.regenerate(archive, tmp_path / "generated", True)


def test_reject_reused_or_symlinked_destination(tmp_path: Path) -> None:
    """Protect pre-existing output trees and symlink targets from writes."""
    outside = tmp_path / "outside"
    outside.mkdir()
    sentinel = outside / "sentinel"
    sentinel.write_text("preserve me")
    symlink = tmp_path / "link"
    symlink.symlink_to(outside, target_is_directory=True)
    for destination in (outside, symlink):
        with pytest.raises(FileExistsError):
            GENERATOR.regenerate(SCRIPT.parent / "archive", destination, False)
    assert sentinel.read_text(encoding="utf-8") == "preserve me"
    assert list(outside.iterdir()) == [sentinel]


def test_failed_later_record_creates_nothing(tmp_path: Path) -> None:
    """Create no output when a later template is absent."""
    archive = tmp_path / "archive"
    shutil.copytree(SCRIPT.parent / "archive", archive)
    manifest = json.loads((archive / "manifest.json").read_text(encoding="utf-8"))
    last = list(manifest["files"].values())[-1]
    records = archive / "records" / last["records"]
    records.write_text('[["999", []]]')
    output = tmp_path / "generated"
    with pytest.raises(FileNotFoundError):
        GENERATOR.regenerate(archive, output, False)
    assert not output.exists()
    assert list(tmp_path.glob(".zeta5-certificates-*")) == []


def test_destination_created_during_render_is_preserved(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """Do not replace a destination created after the operation starts."""
    output = tmp_path / "generated"

    def competing_creation(archive: Path) -> dict[Path, bytes]:
        output.mkdir()
        return {Path("LeanPool/Zeta5Irrational/A.lean"): b"test"}

    monkeypatch.setattr(GENERATOR, "_render_modules", competing_creation)
    with pytest.raises(FileExistsError):
        GENERATOR.regenerate(SCRIPT.parent / "archive", output, False)
    assert output.is_dir()
    assert list(output.iterdir()) == []


def test_nested_output_and_write_failure_cleanup(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """Support new parents and clean up output if writing fails."""
    relative = Path("LeanPool/Zeta5Irrational/A.lean")
    monkeypatch.setattr(GENERATOR, "_render_modules", lambda _: {relative: b"test"})
    output = tmp_path / "new" / "parents" / "generated"
    assert GENERATOR.regenerate(SCRIPT.parent / "archive", output, False) == 1
    assert (output / relative).read_bytes() == b"test"

    def fail_write(path: Path, content: bytes) -> None:
        raise OSError("disk full")

    monkeypatch.setattr(Path, "write_bytes", fail_write)
    failed_output = tmp_path / "failed"
    with pytest.raises(OSError, match="disk full"):
        GENERATOR.regenerate(SCRIPT.parent / "archive", failed_output, False)
    assert not failed_output.exists()


def test_archive_manifest_uses_portable_paths(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """Look up POSIX manifest keys even when rendering uses Windows paths."""
    content = b"certificate"
    path = PureWindowsPath("LeanPool/Zeta5Irrational/Table/U00.lean")
    manifest = {
        "files": {path.as_posix(): {"sha256": hashlib.sha256(content).hexdigest()}}
    }
    (tmp_path / "manifest.json").write_text(json.dumps(manifest), encoding="utf-8")
    monkeypatch.setattr(GENERATOR, "_render_modules", lambda _: {path: content})
    GENERATOR.verify_archive(tmp_path)
