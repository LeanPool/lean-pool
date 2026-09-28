"""Expand."""

import collections
import hashlib
import json
import logging
import re

logger = logging.getLogger(__name__)


def run(workspace):
    """Run this transformation inside the fresh reproduction workspace."""
    r = workspace
    items = json.loads((r / "cover-expansion-candidates.json").read_text())
    leaves = collections.defaultdict(dict)
    for line in (r / "cover-bulk-discovery.jsonl").read_text().splitlines():
        i, path, depth, reason = line.split("|")
        assert reason == "rejected"
        leaves[int(i)][path] = int(depth)
    assert len(leaves) == len(items)
    pat = re.compile(
        "(?m)^theorem (\\w+) :\\s*adaptiveCoverCheck (\\d+) (["
        "^:=]+?) = true := by\\n  decide \\+kernel\\b"
    )
    byname = {x["name"]: x for x in items}
    changes = []
    for file in sorted({x["file"] for x in items}):
        p = r / file
        s = p.read_text()
        new_nodes = 0

        def replace(match):
            nonlocal new_nodes
            item = byname[match[1]]
            terminal = leaves[item["id"]]
            if len(terminal) == 1:
                return match[0]
            assert int(match[2]) == item["depth"]
            assert " ".join(match[3].split()) == " ".join(item["cell"].split())
            paths = {""}
            for path in terminal:
                for i in range(1, len(path) + 1):
                    paths.add(path[:i])
            for path in paths - terminal.keys():
                assert all(path + str(j) in paths for j in range(4))
            ns = (
                "CoverCertificate"
                + hashlib.sha256(item["name"].encode()).hexdigest()[:10]
            )
            root = " ".join(item["cell"].split())
            lines = [
                f"namespace {ns}",
                "",
                "private abbrev cellRoot : AngleCell :=",
                "  " + root,
            ]

            def cell(path):
                return "cell" + (path or "Root")

            def proof(path):
                return "checked" + (path or "Root")

            for path in sorted(paths, key=lambda x: (len(x), x)):
                if path:
                    lines.extend(
                        [
                            "",
                            f"private abbrev {cell(path)} : AngleCell :=",
                            "  "
                            + ["childLL", "childLH", "childHL", "childHH"][
                                int(path[-1])
                            ]
                            + " "
                            + cell(path[:-1]),
                        ]
                    )
            for path in sorted(paths, key=lambda x: (-len(x), x)):
                depth = item["depth"] - len(path)
                lines.extend(
                    [
                        "",
                        f"private theorem {proof(path)} : "
                        f"adaptiveCoverCheck {depth} {cell(path)} = true := by",
                    ]
                )
                if path in terminal:
                    assert depth == terminal[path]
                    lines.append(
                        f"  exact adaptiveCoverCheck_true_of_rejected {depth} "
                        f"{cell(path)} (by decide +kernel)"
                    )
                else:
                    lines.extend(
                        [
                            f"  exact adaptiveCoverCheck_succ_of_children "
                            f"{depth - 1} {cell(path)}",
                            "    " + " ".join(proof(path + str(j)) for j in range(4)),
                        ]
                    )
            lines.extend(
                [
                    "",
                    f"end {ns}",
                    "",
                    match[0].removesuffix("  decide +kernel")
                    + "  exact "
                    + ns
                    + ".checkedRoot",
                ]
            )
            new_nodes += len(paths)
            return "\n".join(lines)

        t = pat.sub(replace, s)
        if t != s:
            changes.append(
                {
                    "file": file,
                    "nodes": new_nodes,
                    "lines_before": len(s.splitlines()),
                    "lines_after": len(t.splitlines()),
                }
            )
            p.write_text(t)
    (r / "cover-expansion-changes.json").write_text(json.dumps(changes, indent=2))
    logger.info(
        "%s",
        {
            "files": len(changes),
            "nodes": sum(x["nodes"] for x in changes),
            "added_lines": sum(x["lines_after"] - x["lines_before"] for x in changes),
            "largest_file": max((x["lines_after"] for x in changes), default=0),
        },
    )
