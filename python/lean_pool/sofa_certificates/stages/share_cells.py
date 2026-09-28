"""Share cells."""

import hashlib
import json
import logging
import re

logger = logging.getLogger(__name__)


def run(workspace):
    """Run this transformation inside the fresh reproduction workspace."""
    root = workspace
    project = root / "pool/LeanPool/MovingSofa/GerverSofa/KernelOnly/PartE"
    stride = 4
    pattern = re.compile("\\((childLL|childLH|childHL|childHH) ([A-Za-z0-9_]+)\\)")
    digits = {"childLL": "0", "childLH": "1", "childHL": "2", "childHH": "3"}
    results = []
    for path in sorted(project.glob("E24KC*.lean")):
        original = path.read_text()
        text = original
        parents = {
            f"e24{a}{b}Root": (a[0].lower() + a[1:] + b, "")
            for a in ["Phi", "Theta"]
            for b in ["Below", "Above"]
        }
        definitions = {}
        expansions = {}
        namespace = (
            "CertificateCells" + hashlib.sha256(path.name.encode()).hexdigest()[:10]
        )
        while True:
            count = 0

            def replace(match):
                nonlocal count
                operation, parent = match.groups()
                if parent not in parents:
                    return match.group(0)
                region, branch = parents[parent]
                branch += digits[operation]
                name = region + "Cell" + branch
                value = operation + " " + parent
                if name in definitions:
                    assert definitions[name] == value
                else:
                    definitions[name] = value
                    parents[name] = (region, branch)
                    expansions[name] = match.group(0)
                count += 1
                return name

            text = pattern.sub(replace, text)
            if not count:
                break
        if not definitions:
            continue
        identifier = re.compile("\\b[A-Za-z][A-Za-z0-9_]*\\b")
        fully_expanded = {}
        for name, expression in expansions.items():
            fully_expanded[name] = identifier.sub(
                lambda m: fully_expanded.get(m[0], m[0]), expression
            )
        expanded = identifier.sub(lambda m: fully_expanded.get(m[0], m[0]), text)
        assert expanded == original, path
        kept = {name for name in definitions if len(parents[name][1]) % stride == 0}
        declarations = "\n".join(
            (
                "abbrev " + name + " : AngleCell :=\n  " + value
                for name, value in definitions.items()
                if name in kept
            )
        )
        pruned = {}
        for name, expression in expansions.items():
            if name not in kept:
                pruned[name] = identifier.sub(
                    lambda m: pruned.get(m[0], m[0]), expression
                )
        text = identifier.sub(lambda m: pruned.get(m[0], m[0]), text)
        declarations = identifier.sub(lambda m: pruned.get(m[0], m[0]), declarations)
        if not kept:
            assert text == original
            continue
        identifier = re.compile("\\b[A-Za-z][A-Za-z0-9_]*\\b")
        fully_expanded = {}
        for name, expression in expansions.items():
            fully_expanded[name] = identifier.sub(
                lambda m: fully_expanded.get(m[0], m[0]), expression
            )
        expanded = identifier.sub(lambda m: fully_expanded.get(m[0], m[0]), text)
        assert expanded == original, path
        shared = (
            f"namespace {namespace}\n\n"
            "-- Base-four digits encode LL, LH, HL, HH "
            "subdivisions of the named root.\n"
            + declarations
            + f"\n\nend {namespace}\n\nopen {namespace}\n\n"
        )
        first = re.search("(?m)^(?:set_option|theorem) ", text)
        assert first
        text = text[: first.start()] + shared + text[first.start() :]
        results.append(
            {
                "file": str(path.relative_to(root / "pool")),
                "cells": len(kept),
                "original_characters": len(original),
                "shared_characters": len(text),
                "expansion_verified": True,
            }
        )
        path.write_text(text)
    (root / "cell-sharing-applied.json").write_text(json.dumps(results, indent=2))
    logger.info(
        "%s",
        json.dumps(
            {
                "applied": True,
                "stride": stride,
                "files": len(results),
                "cells": sum(x["cells"] for x in results),
                "before_characters": sum(x["original_characters"] for x in results),
                "after_characters": sum(x["shared_characters"] for x in results),
            }
        ),
    )
