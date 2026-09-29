"""Consolidate."""

import json
import re
from pathlib import Path

from lean_pool import quality


def scoped_lines(text):
    """Track the namespace enclosing each line of pinned Lean source."""
    stack = []
    stripped = quality._strip_lean_comments(text).splitlines()
    for line_no, line in enumerate(stripped):
        yield (
            line_no,
            ".".join((name for kind, name in stack if kind == "namespace")),
        )
        line = re.sub("^\\s*@\\[[^\\]]+\\]\\s*", "", line).strip()
        start = re.match(
            (
                "(?:(?:public|private|noncomputable) )?(namespace|s"
                "ection)(?:\\s+([^\\s]+))?"
            ),
            line,
        )
        if start:
            stack.append((start[1], start[2] or ""))
        elif re.match("end(?:\\s|$)", line):
            assert stack, (line_no, line)
            stack.pop()
    return stack


def fragment(m, sources, import_re, generated, private_maps):
    """Preserve one module body and hoist its private cell abbreviations."""
    s = sources[m]
    for a, b in private_maps.get(m, {}).items():
        s = re.sub("(?<![\\w\\'])" + re.escape(a) + "(?![\\w\\'])", b, s)
    s = import_re.sub("", s)
    s = re.sub("(?m)^module\\s*\\n", "", s, 1)
    header_end = s.index("-/") + 2
    s = s[header_end:].strip() + "\n"
    hoisted = []
    if m in generated:
        namespaces = dict(scoped_lines(s))
        lines = s.splitlines(keepends=True)
        offsets = [0]
        for line in lines:
            offsets.append(offsets[-1] + len(line))
        edits = []
        for match in re.finditer(
            (
                "(?m)^private abbrev \\w+\\s*:\\s*AngleCell\\s*:=.*(?:\\"
                "n(?:[ \\t].*|\\s*))*(?=\\n\\S|\\Z)"
            ),
            s,
        ):
            row = s[: match.start()].count("\n")
            ns = namespaces[row]
            assert ns.startswith("GerverSofa.PartE"), (m, ns)
            hoisted.append(
                "namespace " + ns + "\n\n" + match[0].rstrip() + "\n\nend " + ns + "\n"
            )
            edits.append((match.start(), match.end()))
        for a, b in reversed(edits):
            s = s[:a] + s[b:]
    count = 0
    for line in quality._strip_lean_comments(s).splitlines():
        line = re.sub("^\\s*@\\[[^\\]]+\\]\\s*", "", line).strip()
        if re.match(
            ("(?:(?:public|private|noncomputable) )?(?:namespace|section)(?:\\s|$)"),
            line,
        ):
            count += 1
        elif re.match("end(?:\\s|$)", line):
            count -= 1
    assert count >= 0, (m, count)
    body = "section\n\n" + s.rstrip() + "\n" + "\nend\n" * (count + 1)
    return ("\n".join(hoisted), body)


def materialize(ms, sources, import_re, fragments, header):
    """Combine ordered fragments with their external imports and attribution."""
    imps = sorted({d for m in ms for d in import_re.findall(sources[m]) if d not in ms})
    return (
        header
        + "\n"
        + "".join("public import " + d + "\n" for d in imps)
        + "\n/-!\n# Gerver sofa dependency batch\n\n"
        + "\n".join(
            "* `" + m.removeprefix("LeanPool.MovingSofa.GerverSofa.") + "`." for m in ms
        )
        + "\n-/\n\n@[expose] public section\n\nnoncomputable section\n\n"
        + "\n".join(fragments[m][0] for m in ms if fragments[m][0])
        + "\n"
        + "\n".join(fragments[m][1] for m in ms)
    )


def rewrite(s, mapping, import_re):
    """Relocate and deduplicate imports using the recorded module assignment."""
    seen = set()

    def replace(match):
        mod = mapping.get(match[1], match[1])
        if mod in seen:
            return ""
        seen.add(mod)
        return "public import " + mod

    return import_re.sub(replace, s)


def docs(match):
    """Explain the exact root and subdivision path of each public alias."""
    name = match[1]
    m = re.fullmatch("(phi|theta)(Below|Above)Cell([0-3]+)", name)
    if m:
        doc = (
            f"Subcell `{m[3]}` of the {m[1]}-{m[2].lower()} root; "
            "digits 0–3 mean LL, LH, HL, HH."
        )
    elif name == "coverCell":
        doc = (
            "The root angle cell for the expanded adaptive-cove"
            "r certificate below `phiAboveCell1101`."
        )
    else:
        m = re.fullmatch("coverCell([0-3]+)", name)
        assert m, name
        doc = (
            f"Cached adaptive-cover cell {m[1]}; "
            "its parent subdivisions specify the exact interval."
        )
    return "/-- " + doc + " -/\n" + match[0]


def run(workspace):
    """Run this transformation inside the fresh reproduction workspace."""
    r = workspace
    pool = r / "pool"
    assignment = json.loads((r / "batch-assignment.json").read_text())
    selected = {m for b in assignment for m in b["sources"]}
    sources = {
        m: (pool / Path(*m.split(".")).with_suffix(".lean")).read_text()
        for m in selected
    }
    generated = selected
    private_maps = {}
    import_re = re.compile("(?m)^(?:public )?import ([\\w.]+)\\s*$")

    fragments = {
        m: fragment(m, sources, import_re, generated, private_maps) for m in selected
    }
    header = (
        "/-\nCopyright (c) 2026 Dawid Trela. All rights rese"
        "rved.\nReleased under Apache 2.0 license as describ"
        "ed in the file LICENSE.\nAuthors: Dawid Trela\n-/\nmo"
        "dule\n"
    )

    mapping = json.loads((r / "module-consolidation-map.json").read_text())

    output = pool / "LeanPool/MovingSofa/GerverSofa/KernelOnly/PartE/Certificates"
    output.mkdir(parents=True)
    for batch in assignment:
        text = rewrite(
            materialize(batch["sources"], sources, import_re, fragments, header),
            mapping,
            import_re,
        )
        text, n = re.subn("end (\\S+)\\n\\nnamespace \\1\\n", "", text)

        text = re.sub("(?m)^abbrev (\\w+) : AngleCell :=", docs, text)
        (output / (batch["module"].split(".")[-1] + ".lean")).write_text(text)
    (r / "module-renames.json").write_text(json.dumps(mapping))
