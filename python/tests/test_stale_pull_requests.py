"""Tests for the age-based stale pull request policy."""

from datetime import UTC, datetime, timedelta

from lean_pool.stale_pull_requests import PullRequest, decide

NOW = datetime(2026, 11, 14, 12, tzinfo=UTC)


def _pull_request(age_days: float, *labels: str) -> PullRequest:
    return PullRequest(
        number=1,
        created_at=NOW - timedelta(days=age_days),
        labels=frozenset(labels),
    )


def test_young_pull_requests_are_left_alone() -> None:
    """PRs younger than a week get no label."""
    assert decide(_pull_request(6.9), None, NOW) is None


def test_week_old_pull_requests_are_labelled() -> None:
    """Any unlabelled PR at least a week old is labelled."""
    assert decide(_pull_request(7), None, NOW) == "label"
    assert decide(_pull_request(30), None, NOW) == "label"


def test_labelled_pull_requests_close_at_three_weeks() -> None:
    """A labelled PR closes once it is 21 days old."""
    labelled = NOW - timedelta(days=14)
    assert decide(_pull_request(20.9, "stale"), labelled, NOW) is None
    assert decide(_pull_request(21, "stale"), labelled, NOW) == "close"


def test_old_pull_requests_get_a_week_of_warning() -> None:
    """A PR that was already past 21 days when labelled is not closed at once."""
    assert decide(_pull_request(40, "stale"), NOW - timedelta(days=6), NOW) is None
    assert decide(_pull_request(40, "stale"), NOW - timedelta(days=7), NOW) == "close"


def test_pinned_pull_requests_are_exempt() -> None:
    """The pinned label exempts a PR from the policy."""
    assert decide(_pull_request(40, "pinned"), None, NOW) is None
    assert decide(_pull_request(40, "pinned", "stale"), None, NOW) is None


def test_missing_label_history_never_closes_a_pull_request() -> None:
    """A stale label without its timestamp cannot establish seven days of warning."""
    assert decide(_pull_request(40, "stale"), None, NOW) is None
