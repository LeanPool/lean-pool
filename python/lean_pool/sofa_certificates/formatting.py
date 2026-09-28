"""Wrap the pinned certificate grammar without splitting inline tactic blocks."""

import re
import textwrap


def wrap_source(source: str) -> str:
    """Apply the import's deterministic 100-column source layout."""
    lines = []
    comment_depth = 0
    for line in source.splitlines():
        stripped = line.lstrip()
        indent = len(line) - len(stripped)
        is_comment = comment_depth > 0 or stripped.startswith(("--", "/-"))
        comment_depth += line.count("/-") - line.count("-/")
        if len(line) <= 100:
            lines.append(line)
            continue
        if is_comment:
            prefix = " " * indent + ("-- " if stripped.startswith("--") else "")
            value = stripped[3:] if stripped.startswith("-- ") else stripped
            lines.extend(
                textwrap.wrap(
                    value,
                    width=100,
                    initial_indent=prefix,
                    subsequent_indent=prefix,
                    break_long_words=False,
                    break_on_hyphens=False,
                )
            )
            continue
        protected = []
        for m in re.finditer("\\(by[^\\n]*?\\)", line):
            if len(m[0]) < 75:
                protected.append((m.start(), m.end()))
        spaces = [
            m.start()
            for m in re.finditer(" +", line)
            if m.start() > indent
            and (not any((a < m.start() < b for a, b in protected)))
        ]
        remaining = line
        offset = 0
        continuation = " " * (indent + 2)
        while len(remaining) > 100:
            possible = [
                pos - offset
                for pos in spaces
                if offset < pos and 0 < pos - offset <= 98
            ]
            if not possible:
                break
            cut = max(possible)
            lines.append(remaining[:cut].rstrip())
            skip = cut
            while skip < len(remaining) and remaining[skip] == " ":
                skip += 1
            remaining = continuation + remaining[skip:]
            offset += skip - len(continuation)
        lines.append(remaining)
    return "\n".join(lines) + "\n"
