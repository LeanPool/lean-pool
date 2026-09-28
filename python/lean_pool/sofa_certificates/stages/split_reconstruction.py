"""Split reconstruction."""

import logging
import re

logger = logging.getLogger(__name__)


def run(workspace):
    """Run this transformation inside the fresh reproduction workspace."""
    r = workspace
    base = r / "pool/LeanPool/MovingSofa/GerverSofa/KernelOnly/PartE"
    p = base / "E24KC6ThetaAboveReconstruct.lean"
    s = p.read_text()
    positions = [m.start() for m in re.finditer("(?m)^theorem ", s)]
    first = positions[0]
    header = s[: s.index("namespace GerverSofa")]
    prefix = s[:first]
    suffix = "\nend PartE\nend GerverSofa\n"
    body = s[first : s.rindex("\nend PartE")]
    blocks = re.split("(?m)(?=^theorem )", body)
    blocks = [b for b in blocks if b.strip()]
    groups = []
    group = []
    size = prefix.count("\n")
    for block in blocks:
        if size + block.count("\n") > 5500 and group:
            groups.append("".join(group))
            group = []
            size = 0
        group.append(block)
        size += block.count("\n")
    groups.append("".join(group))
    assert len(groups) == 3
    folder = base / "ThetaAbove"
    folder.mkdir(exist_ok=True)
    (folder / "ReconstructionBase.lean").write_text(prefix + groups[0] + suffix)
    start = header.split("public import ", 1)[0]

    def next_header(module, title):
        return (
            start
            + "public import "
            + module
            + "\n\n/-!\n# "
            + title
            + (
                "\n-/\n\n@[expose] public section\n\nnoncomputable secti"
                "on\n\nnamespace GerverSofa\nnamespace PartE\n\nopen Cer"
                "tificateCells1a75b359b5\n\n"
            )
        )

    (folder / "ReconstructionMiddle.lean").write_text(
        next_header(
            (
                "LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Th"
                "etaAbove.ReconstructionBase"
            ),
            "Intermediate reconstruction of the upper theta cover",
        )
        + groups[1]
        + suffix
    )
    p.write_text(
        next_header(
            (
                "LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Th"
                "etaAbove.ReconstructionMiddle"
            ),
            "Reconstruction of the upper theta cover",
        )
        + groups[2]
        + suffix
    )
    logger.info(
        "%s %s %s",
        "Split reconstruction into",
        [g.count("\n") for g in groups],
        "proof lines with unchanged declarations.",
    )
