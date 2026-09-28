"""Public root."""

import re


def run(workspace):
    """Run this transformation inside the fresh reproduction workspace."""
    p = workspace / (
        "pool/LeanPool/MovingSofa/GerverSofa/KernelOnly/Par"
        "tE/Certificates/Batch002.lean"
    )
    s = p.read_text()
    s = re.sub(
        "abbrev coverCell : AngleCell :=[^\\n]*",
        (
            "abbrev coverCell : AngleCell :=\n  (childLL (chil"
            "dLL (childLH (childLH (childLL (childLH (childLH ("
            "e24PhiAboveRoot))))))))"
        ),
        s,
    )
    s = re.sub(
        (
            "(theorem e24KC2PhiAboveLeaf1101100 :\\n    adaptive"
            "CoverCheck 9 )[^\\n]+?( = true :=)"
        ),
        "\\1CoverPhiAbove1101100.coverCell\\2",
        s,
    )
    p.write_text(s)
