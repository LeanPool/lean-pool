"""Repair roots."""

import collections
import json
import logging
import re

logger = logging.getLogger(__name__)


def run(workspace):
    """Run this transformation inside the fresh reproduction workspace."""
    r = workspace
    root = r / "pool/LeanPool/MovingSofa/GerverSofa/KernelOnly/PartE/Certificates"
    public = re.compile(
        "(?m)^abbrev (\\w+) : AngleCell :=([^\\n]*(?:\\n[ \\t]+[^\\n]*)*)"
    )
    private = re.compile(
        "(?m)^private abbrev (\\w+) : AngleCell :=([^\\n]*(?:\\n[ \\t]+[^\\n]*)*)"
    )
    definitions = collections.defaultdict(list)
    for p in root.glob("*.lean"):
        for m in public.finditer(p.read_text()):
            definitions[m[1]].append(m[2])

    def tokens(s):
        return re.findall("\\w+", s)

    cache = {}
    active = set()

    def expand_name(name):
        if name in cache:
            return cache[name]
        assert name not in active, name
        active.add(name)
        values = []
        for body in definitions[name]:
            value = []
            for token in tokens(body):
                value.extend(expand_name(token) if token in definitions else [token])
            values.append(value)
        assert all(value == values[0] for value in values), name
        active.remove(name)
        cache[name] = values[0]
        return values[0]

    for name in definitions:
        expand_name(name)

    def expression(parts):
        assert parts[-1] in [
            "e24PhiBelowRoot",
            "e24PhiAboveRoot",
            "e24ThetaBelowRoot",
            "e24ThetaAboveRoot",
        ], parts
        assert all(
            x in ["childLL", "childLH", "childHL", "childHH"] for x in parts[:-1]
        ), parts
        value = parts[-1]
        for operation in reversed(parts[:-1]):
            value = f"{operation} ({value})"
        return "(" + value + ")"

    changes = []
    for p in root.glob("*.lean"):
        s = p.read_text()
        count = [0]

        def replace(m):
            old = m[2]
            new = re.sub(
                "\\b\\w+\\b",
                lambda t: expression(cache[t[0]]) if t[0] in cache else t[0],
                old,
            )
            if new == old:
                return m[0]
            old_expanded = []
            for token in tokens(old):
                old_expanded.extend(cache.get(token, [token]))
            assert old_expanded == tokens(new), (p, m[1])
            count[0] += 1
            return "private abbrev " + m[1] + " : AngleCell :=" + new

        s = private.sub(replace, s)
        if count[0]:
            p.write_text(s)
            changes.append(
                {"file": str(p.relative_to(r / "pool")), "roots_expanded": count[0]}
            )
    (r / "hoisted-cell-repairs.json").write_text(json.dumps(changes, indent=2))
    logger.info(
        "%s %s %s %s %s",
        "Expanded",
        sum(x["roots_expanded"] for x in changes),
        "hoisted roots in",
        len(changes),
        "files; all unary subdivision expressions checked equal",
    )
