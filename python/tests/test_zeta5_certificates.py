"""Check exact and constrained rendering of the Zeta5 certificate archive."""

import importlib.util
import json
from pathlib import Path

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
    assert GENERATOR.regenerate(archive, tmp_path, False) == 118
    assert GENERATOR.regenerate(archive, tmp_path, True) == 118
    manifest = json.loads((archive / "manifest.json").read_text())
    first = tmp_path / next(iter(manifest["files"]))
    first.write_text(first.read_text() + "-- damaged\n")
    with pytest.raises(ValueError, match="Certificates differ"):
        GENERATOR.regenerate(archive, tmp_path, True)
