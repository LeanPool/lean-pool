"""Route closed rejection proofs through the equal sign-based evaluator."""

import json
import logging
import re

from lean_pool.sofa_certificates.stages.split_proofs import closing_parenthesis

logger = logging.getLogger(__name__)

REJECTION_FACT = re.compile(
    r"(?m)(^\s*have h : [^:]*?\.rejected = true := by\s*\n\s*)decide \+kernel"
)
REJECTION_CALL = re.compile(r"adaptiveCoverCheck_true_of_rejected\s+\d+\s+")
INLINE_DECISION = re.compile(r"\s+\(by (?P<tactic>decide \+kernel)\)")
ORIGINAL_IMPORT = (
    "public import LeanPool.MovingSofa.GerverSofa.KernelOnly.Core.Bundle005"
)
FAST_IMPORT = (
    "public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.FastRejection"
)


def inline_decisions(source: str) -> tuple[str, int]:
    """Replace only the decision supplied as the rejection call's proof argument."""
    replacements = []
    for call in REJECTION_CALL.finditer(source):
        start = call.end()
        if source[start : start + 1] == "(":
            end = closing_parenthesis(source, start) + 1
        else:
            cell = re.match(r"[A-Za-z_][A-Za-z_0-9.]*", source[start:])
            if cell is None:
                continue
            end = start + cell.end()
        decision = INLINE_DECISION.match(source, end)
        if decision:
            replacements.append(decision.span("tactic"))
    for start, end in reversed(replacements):
        source = source[:start] + "sofa_reject" + source[end:]
    return source, len(replacements)


def transform(source: str) -> tuple[str, int]:
    """Change rejection decisions and their import, preserving all statements."""
    transformed, facts = REJECTION_FACT.subn(r"\1sofa_reject", source)
    transformed, inline = inline_decisions(transformed)
    count = facts + inline
    if count:
        if ORIGINAL_IMPORT not in transformed:
            raise ValueError("A rejection certificate lacks its evaluator import")
        transformed = transformed.replace(ORIGINAL_IMPORT, FAST_IMPORT)
    return transformed, count


def run(workspace):
    """Apply the proof transformation after checking the historical bundle digests."""
    project = (
        workspace / "pool/LeanPool/MovingSofa/GerverSofa/KernelOnly/PartE/Certificates"
    )
    records = []
    for path in sorted(project.glob("*.lean")):
        transformed, count = transform(path.read_text())
        if count:
            path.write_text(transformed)
            records.append({"file": path.name, "rejections": count})
    (workspace / "fast-rejection-applied.json").write_text(
        json.dumps(records, indent=2) + "\n"
    )
    logger.info(
        "Fast evaluator: %s proofs across %s modules",
        sum(record["rejections"] for record in records),
        len(records),
    )
