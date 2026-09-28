"""Check certificate reproduction input validation and cover completeness."""

import importlib
import json
from pathlib import Path

import pytest

from lean_pool.sofa_certificates.__main__ import (
    digest,
    prepare_source,
    read_sources,
    validate_leaves,
    validate_witnesses,
    verify_outputs,
)

FIXTURES = Path(__file__).parent / "fixtures/sofa_certificates"


@pytest.mark.parametrize(
    "leaves",
    [
        {},
        {"0": 0},
        {"": 1, "0": 0},
        {"4": 0},
        {"0": 1, "1": 0, "2": 0, "3": 0},
        {"00": -1, "01": -1, "02": -1, "03": -1, "1": 0, "2": 0, "3": 0},
    ],
)
def test_reject_incomplete_or_overlapping_trees(leaves: dict[str, int]) -> None:
    """A witness cannot omit quadrants, overlap leaves or falsify its depth."""
    with pytest.raises(ValueError):
        validate_leaves(leaves, 1)


def test_all_recorded_witnesses_cover_their_roots() -> None:
    """Every actual input tree satisfies the cover structure invariants."""
    validate_witnesses()


def test_archive_checksum_precedes_archive_parsing(tmp_path: Path) -> None:
    """Unpinned bytes are rejected without interpreting the archive."""
    archive = tmp_path / "bad.tar.gz"
    archive.write_bytes(b"not a tar archive")
    with pytest.raises(ValueError, match="SHA-256 mismatch"):
        read_sources(archive)


def test_reproduction_rejects_missing_or_extra_modules(tmp_path: Path) -> None:
    """The output check requires the complete exact module set."""
    (tmp_path / "Unexpected.lean").write_text("theorem unwanted : True := trivial\n")
    with pytest.raises(ValueError, match="Unexpected.lean"):
        verify_outputs(tmp_path)


def test_reproduction_rejects_nested_extra_module(tmp_path: Path) -> None:
    """Matching top-level digests cannot hide an additional nested certificate."""
    folder = tmp_path / "certificates"
    folder.mkdir()
    content = b"theorem valid : True := trivial\n"
    (folder / "Expected.lean").write_bytes(content)
    manifest = tmp_path / "manifest.json"
    manifest.write_text(json.dumps({"Expected.lean": digest(content)}))
    assert verify_outputs(folder, manifest) == {"Expected.lean": digest(content)}
    (folder / "nested").mkdir()
    (folder / "nested/Unexpected.lean").write_bytes(content)
    with pytest.raises(ValueError, match="Unexpected directory.*nested"):
        verify_outputs(folder, manifest)


def test_real_subtree_passes_ordered_transformation_stages(tmp_path: Path) -> None:
    """A pinned production subtree must reproduce its reviewed intermediate source."""
    folder = tmp_path / "pool/LeanPool/MovingSofa/GerverSofa/KernelOnly/PartE"
    folder.mkdir(parents=True)
    source = folder / "E24KC6R4Subtree_e91aff9c114b660b.lean"
    source.write_bytes((FIXTURES / "subtree.input.txt").read_bytes())
    for name in [
        "split_proofs",
        "share_cells",
        "normalize",
        "rename",
        "module_names",
        "wrap",
    ]:
        stage = importlib.import_module(f"lean_pool.sofa_certificates.stages.{name}")
        stage.run(tmp_path)
    result = folder / "E24KC6R4SubtreeE91aff9c114b660b.lean"
    assert not source.exists()
    assert result.read_text() == (FIXTURES / "subtree.expected.txt").read_text()


def test_visibility_and_attribution_preserve_upstream_body() -> None:
    """Only owned imports are prefixed; existing attribution and proofs survive."""
    source = (
        "import GerverSofa.Core\nimport Mathlib.Data.Real.Basic\n"
        "/- Original attribution. -/\ntheorem example : True := trivial\n"
    )
    prepared = prepare_source(source)
    assert "public import LeanPool.MovingSofa.GerverSofa.Core\n" in prepared
    assert "public import Mathlib.Data.Real.Basic\n" in prepared
    assert prepared.endswith(
        "\n@[expose] public section\n"
        "/- Original attribution. -/\ntheorem example : True := trivial\n"
    )
