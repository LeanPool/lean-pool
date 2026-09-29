"""Split proofs."""

import hashlib
import json
import logging
import re
import textwrap

logger = logging.getLogger(__name__)


def closing_parenthesis(source: str, start: int) -> int:
    """Find the balanced end of a generated parenthesized expression."""
    depth = 0
    for index in range(start, len(source)):
        if source[index] == "(":
            depth += 1
        elif source[index] == ")":
            depth -= 1
            if depth == 0:
                return index
    raise ValueError("Unbalanced generated expression")


def split_body(body: str, prefix: str, helpers: list[str]) -> str:
    """Factor closed child-cover subproofs, keeping their exact statement."""
    position = 0
    while True:
        start = body.find("(by\n", position)
        if start < 0:
            return body
        end = closing_parenthesis(body, start)
        inner = textwrap.dedent(body[start + 4 : end]).strip()
        match = re.match(
            "exact adaptiveCoverCheck_succ_of_children (\\d+) (\\()", inner
        )
        if not match or inner.count("\n") < 35:
            position = end + 1
            continue
        cell_start = match.end() - 1
        cell_end = closing_parenthesis(inner, cell_start)
        cell = inner[cell_start : cell_end + 1]
        depth = int(match.group(1)) + 1
        name = prefix + "_subtree_" + hashlib.sha256(inner.encode()).hexdigest()[:12]
        inner = split_body(inner, prefix, helpers)
        helper = (
            f"theorem {name} :\n"
            f"    adaptiveCoverCheck {depth} {cell} = true := by\n"
            + textwrap.indent(inner, "  ")
            + "\n\n"
        )
        helpers.append(helper)
        body = body[:start] + name + body[end + 1 :]
        position = start + len(name)


def transform(path):
    """Split only closed adaptive-cover proofs exceeding the size threshold."""
    source = path.read_text()
    pattern = re.compile(
        "(?m)^theorem (\\w+) :\\n\\s+adaptiveCoverCheck (\\d+) "
        "([^\\n]+) = true := by\\n"
    )
    matches = list(pattern.finditer(source))
    if not matches:
        return (source, 0)
    replacements = []
    helper_count = 0
    for index, match in enumerate(matches):
        end = matches[index + 1].start() if index + 1 < len(matches) else len(source)
        trailing = source[match.end() : end]
        boundary = re.search("(?m)^(?:set_option|end |theorem )", trailing)
        if boundary:
            end = match.end() + boundary.start()
        body = source[match.end() : end].rstrip()
        if body.count("\n") < 150:
            continue
        helpers = []
        transformed = split_body(body, match.group(1), helpers)
        if helpers:
            prefix = "".join(helpers) + source[match.start() : match.end()]
            replacements.append((match.start(), end, prefix + transformed + "\n\n"))
            helper_count += len(helpers)
    for start, end, replacement in reversed(replacements):
        source = source[:start] + replacement + source[end:]
    return (source, helper_count)


def run(workspace):
    """Run this transformation inside the fresh reproduction workspace."""
    root = workspace
    project = root / "pool/LeanPool/MovingSofa/GerverSofa/KernelOnly/PartE"

    results = []
    for path in sorted(project.glob("E24KC*.lean")):
        transformed, count = transform(path)
        if count:
            results.append(
                {
                    "file": str(path.relative_to(root / "pool")),
                    "helpers": count,
                    "before_lines": len(path.read_text().splitlines()),
                    "after_lines": len(transformed.splitlines()),
                }
            )
            path.write_text(transformed)
    (root / "certificate-split-applied.json").write_text(json.dumps(results, indent=2))
    logger.info(
        "%s",
        json.dumps(
            {
                "applied": True,
                "files": len(results),
                "helpers": sum(x["helpers"] for x in results),
            }
        ),
    )
