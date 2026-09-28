"""Normalize."""

import logging
import re

logger = logging.getLogger(__name__)


def run(workspace):
    """Run this transformation inside the fresh reproduction workspace."""
    root = workspace
    pool = root / "pool"

    def comment_end(text, start):
        depth = 1
        index = start + 2
        while depth:
            if text[index : index + 2] == "/-":
                depth += 1
                index += 2
            elif text[index : index + 2] == "-/":
                depth -= 1
                index += 2
            else:
                index += 1
        return index

    changes = []
    for path in sorted((pool / "LeanPool/MovingSofa").rglob("*.lean")):
        original = path.read_text()
        text = original
        if "GerverSofa" in path.parts:
            text = text.replace(
                "Released under MIT license as described in the file LICENSE.",
                "Released under Apache 2.0 license as described in the file LICENSE.",
                1,
            )
        text, options = re.subn(
            ("(?m)^\\s*set_option (?:maxRecDepth|maxHeartbeats) \\d+(?: in)?\\s*\\n"),
            "",
            text,
        )
        text, diagnostics = re.subn(
            "(?m)^#eval[^\\n]*(?:\\n[ \\t]+[^\\n]*)*\\n", "", text
        )
        marker = "@[expose] public section"
        if marker in text:
            position = text.index(marker)
            following = text[position + len(marker) :]
            doc = following.find("/-!")
            if doc >= 0:
                before = following[:doc]
                only_setup = all(
                    not line.strip()
                    or re.match(
                        "^(?:namespace |open |noncomputable section|section(?: |$)|--)",
                        line.strip(),
                    )
                    for line in before.splitlines()
                )
                if only_setup:
                    start = position + len(marker) + doc
                    end = comment_end(text, start)
                    documentation = text[start:end]
                    text = (
                        text[:position]
                        + documentation
                        + "\n\n"
                        + marker
                        + text[position + len(marker) : start]
                        + text[end:]
                    )
            if not re.search("/-!", text[: text.index(marker)]):
                parts = (
                    path.relative_to(pool / "LeanPool/MovingSofa").with_suffix("").parts
                )
                title = " / ".join(
                    re.sub("(?<=[a-z])(?=[A-Z])", " ", part) for part in parts
                )
                text = text.replace(marker, "/-!\n# " + title + "\n-/\n\n" + marker, 1)
        text = re.sub("\\n{3,}", "\n\n", text)
        if text != original:
            changes.append(
                {
                    "file": str(path.relative_to(pool)),
                    "options_removed": options,
                    "diagnostics_removed": diagnostics,
                }
            )
            path.write_text(text)
    logger.info("%s", "Normalized source")
