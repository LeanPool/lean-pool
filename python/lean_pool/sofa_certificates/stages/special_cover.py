"""Special cover."""

import re


def run(workspace):
    """Run this transformation inside the fresh reproduction workspace."""
    r = workspace
    t = r
    p = t / (
        "pool/LeanPool/MovingSofa/GerverSofa/KernelOnly/Par"
        "tE/E24KC4BatchPhiAboveF9C1LLRLRL0011.lean"
    )
    original = p.read_text()
    match = re.search(
        "theorem (\\w+) :\\n\\s+adaptiveCoverCheck 9 (.+) = true := by", original
    )
    leaves = {
        a: (int(b), c)
        for a, b, c in re.findall(
            "^COVER\\|([^|]*)\\|(\\d+)\\|(\\w+)$",
            (r / "cover-special-discovery.txt").read_text(),
            re.M,
        )
    }
    assert all((c == "rejected" for _, c in leaves.values()))
    paths = {""}
    for path in leaves:
        for i in range(1, len(path) + 1):
            paths.add(path[:i])
    lines = [
        "namespace CoverPhiAbove1101100",
        "",
        f"abbrev coverCell : AngleCell := {match[2]}",
    ]
    for path in sorted(paths, key=lambda s: (len(s), s)):
        if path:
            lines.append(
                "abbrev coverCell"
                + path
                + " : AngleCell := "
                + ["childLL", "childLH", "childHL", "childHH"][int(path[-1])]
                + " coverCell"
                + path[:-1]
            )
    lines.extend(
        [""]
        + original[original.index("namespace CertificateCells") : match.start()]
        .rstrip()
        .splitlines()
    )
    for path in sorted(paths, key=lambda s: (-len(s), s)):
        depth = 9 - len(path)
        cell = "coverCell" + path
        name = "checked" + (path or "Root")
        lines.append(
            f"\ntheorem {name} : adaptiveCoverCheck {depth} {cell} = true := by"
        )
        if path in leaves:
            lines.append(
                f"  exact adaptiveCoverCheck_true_of_rejected {depth} "
                f"{cell} (by decide +kernel)"
            )
        else:
            lines.append(
                f"  exact adaptiveCoverCheck_succ_of_children {depth - 1} {cell}\n    "
                + " ".join("checked" + path + str(j) for j in range(4))
            )
    lines.extend(
        [
            "",
            "end CoverPhiAbove1101100",
            "",
            f"theorem {match[1]} :\n    adaptiveCoverCheck 9 {match[2]} = true :=\n"
            "      CoverPhiAbove1101100.checkedRoot",
            "",
            "end PartE",
            "end GerverSofa",
        ]
    )
    result = (
        original.split("namespace CertificateCells", 1)[0] + "\n".join(lines) + "\n"
    )
    p.write_text(result)
