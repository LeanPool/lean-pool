"""Exercise independent project cards, historical reads, and rejected corruption."""

import subprocess
from pathlib import Path

import pytest
import yaml

from lean_pool.registry import combine, load_document, read_revision


def test_directory_and_legacy_have_identical_cards(tmp_path: Path) -> None:
    """Migration changes storage only, preserving unknown and nested metadata."""
    path = tmp_path / "projects.yml"
    cards = [{"slug": "b", "source": {"url": "https://example.org"}}, {"slug": "a"}]
    path.write_text(yaml.safe_dump({"projects": cards}))
    before = load_document(path)
    path.unlink()
    directory = tmp_path / "projects"
    directory.mkdir()
    for card in cards:
        (directory / f"{card['slug']}.yaml").write_text(yaml.safe_dump(card))
    assert load_document(path) == {
        "projects": sorted(before["projects"], key=lambda c: c["slug"])
    }
    assert load_document(directory) == load_document(path)


@pytest.mark.parametrize(
    "cards",
    [
        {},
        {"a.yaml": "[]"},
        {"a.yaml": "slug: b"},
        {"a.yaml": "slug: a\nslug: a\n"},
        {"a.yml": "slug: a"},
        {"../a.yaml": "slug: a"},
    ],
)
def test_invalid_cards_fail_closed(cards: dict[str, str]) -> None:
    """Empty registries and malformed identities cannot silently hide projects."""
    with pytest.raises(ValueError):
        combine(cards)


def test_mixed_layout_and_nested_directory_rejected(tmp_path: Path) -> None:
    """Ambiguous migrations and ignored nested cards must fail validation."""
    directory = tmp_path / "projects"
    directory.mkdir()
    (directory / "a.yaml").write_text("slug: a\n")
    legacy = tmp_path / "projects.yml"
    legacy.write_text("projects: []")
    with pytest.raises(ValueError, match="both"):
        load_document(directory)
    legacy.unlink()
    (directory / "nested").mkdir()
    with pytest.raises(ValueError, match="ordinary"):
        load_document(directory)


def test_git_reads_each_layout_without_checkout(tmp_path: Path) -> None:
    """Old PR comparisons retain their original cards after the local migration."""

    def git(*args: str) -> str:
        return subprocess.check_output(["git", *args], cwd=tmp_path, text=True).strip()

    git("init")
    git("config", "user.email", "test@example.org")
    git("config", "user.name", "Test")
    pool = tmp_path / "LeanPool"
    pool.mkdir()
    legacy = pool / "projects.yml"
    legacy.write_text("projects:\n  - slug: a\n")
    git("add", ".")
    git("commit", "-m", "old registry")
    before = git("rev-parse", "HEAD")
    legacy.unlink()
    (pool / "projects").mkdir()
    (pool / "projects/a.yaml").write_text("slug: a\n")
    git("add", ".")
    git("commit", "-m", "new registry")
    assert read_revision(tmp_path, before) == read_revision(tmp_path, "HEAD")


def test_registry_symlinks_rejected_locally_and_in_git(tmp_path: Path) -> None:
    """Card contents cannot come from outside the tracked project registry."""
    directory = tmp_path / "LeanPool/projects"
    directory.mkdir(parents=True)
    target = tmp_path / "outside.yaml"
    target.write_text("slug: a\n")
    (directory / "a.yaml").symlink_to(target)
    with pytest.raises(ValueError, match="ordinary"):
        load_document(directory)
    for arguments in [
        ["init"],
        ["config", "user.email", "test@example.org"],
        ["config", "user.name", "Test"],
        ["add", "."],
        ["commit", "-m", "invalid registry"],
    ]:
        subprocess.run(
            ["git", *arguments], cwd=tmp_path, check=True, capture_output=True
        )
    with pytest.raises(ValueError, match="file type"):
        read_revision(tmp_path, "HEAD")
    (directory / "a.yaml").unlink()
    directory.rmdir()
    directory.symlink_to(tmp_path, target_is_directory=True)
    with pytest.raises(ValueError, match="symbolic link"):
        load_document(directory)
