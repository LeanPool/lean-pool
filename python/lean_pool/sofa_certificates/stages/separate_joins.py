"""Separate joins."""

import json
import logging
import re

from lean_pool import quality

logger = logging.getLogger(__name__)


def pieces(path):
    """Locate original module fragments by balanced visibility sections."""
    text = path.read_text()
    lines = text.splitlines(keepends=True)
    stripped = quality._strip_lean_comments(text).splitlines()
    assert len(lines) == len(stripped)
    header_start = text.index("/-!")
    header_end = text.index("-/", header_start)
    names = re.findall("^\\* `([^`]+)`\\.", text[header_start:header_end], re.M)
    depth = 0
    start = None
    spans = []
    for i, line in enumerate(stripped):
        line = re.sub("^\\s*@\\[[^\\]]+\\]\\s*", "", line).strip()
        opening = re.match(
            "(?:(?:public|private|noncomputable) )?(namespace|section)(?:\\s|$)",
            line,
        )
        if opening:
            if line == "section" and depth == 2:
                assert start is None
                start = i
            depth += 1
        elif re.match("end(?:\\s|$)", line):
            depth -= 1
            if start is not None and depth == 2:
                spans.append((start, i + 1))
                start = None
    assert start is None and depth == 2, (path, start, depth)
    assert len(names) == len(spans), (path, len(names), len(spans))
    return (text, lines, names, spans)


def run(workspace):
    """Run this transformation inside the fresh reproduction workspace."""
    r = workspace
    pool = r / "pool"
    root = pool / "LeanPool/MovingSofa/GerverSofa/KernelOnly/PartE/Certificates"

    moved = []
    retained = {}
    sources = {}
    for i in range(35, 45):
        p = root / f"Batch{i:03d}.lean"
        text, lines, names, spans = pieces(p)
        sources[p] = text
        keep = []
        for name, (a, b) in zip(names, spans):
            body = "".join(lines[a:b])
            assembly = ".Join" in name or name.endswith("Reconstruct")
            if assembly:
                plain = quality._strip_lean_comments(body)
                assert "CoverCertificate" not in plain, (p, name)
                assert not re.search("^private ", plain, re.M), (p, name)
                moved.append(
                    {
                        "original": name,
                        "from": p.stem,
                        "body": body,
                        "code_lines": quality._non_comment_code_lines(body),
                    }
                )
            else:
                keep.append(name)
        retained[p.stem] = keep
    report = {
        "moved_fragments": len(moved),
        "moved_code_lines": sum(x["code_lines"] for x in moved),
        "moves": [{k: v for k, v in x.items() if k != "body"} for x in moved],
        "retained_fragments": {k: len(v) for k, v in retained.items()},
    }
    (r / "certificate-join-separation-proposal.json").write_text(
        json.dumps(report, indent=2)
    )
    (r / "certificate-join-fragments.json").write_text(json.dumps(moved, indent=2))
    logger.info("%s", {k: v for k, v in report.items() if k != "moves"})
    module = (
        "LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Certificates.Reconstruction"
    )
    new_path = root / "Reconstruction.lean"
    assert not new_path.exists()
    all_paths = sorted(root.glob("*.lean"))
    before_names = sorted(x.name for x in quality._declarations_in(all_paths))
    changed = {}
    for p, text in sources.items():
        _, lines, names, spans = pieces(p)
        for name, (a, b) in reversed(list(zip(names, spans))):
            if name not in retained[p.stem]:
                lines[a:b] = []
        new = "".join(lines)
        new = re.sub(
            "^public import .*Certificates\\.Batch\\d+\\n", "", new, flags=re.M
        )
        new = re.sub(
            "^\\* `([^`]+)`\\.\\n",
            lambda m: m[0] if m[1] in retained[p.stem] else "",
            new,
            flags=re.M,
        )
        changed[p] = new
    header = (root / "Batch035.lean").read_text().split("-/", 1)[0] + "-/\nmodule\n\n"
    imports = [
        "LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Semantics.Batch001",
        "LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Semantics.Batch002",
    ] + [
        f"LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Certificates.Batch{i:03d}"
        for i in range(1, 45)
    ]
    new = (
        header
        + "".join("public import " + m + "\n" for m in imports)
        + (
            "\n/-!\n# Combining adaptive-cover certificates\n\nThe "
            "numerical leaf checks are imported separately so t"
            "hat they can compile in parallel.\nThis module comb"
            "ines them using the adaptive-cover soundness lemma"
            "s.\n\n"
        )
        + "".join("* `" + x["original"] + "`.\n" for x in moved)
        + "-/\n\n@[expose] public section\n\nnoncomputable section\n\n"
        + "".join(x["body"] + "\n" for x in moved)
    )
    changed[new_path] = new
    p = root / "Batch045.lean"
    text = p.read_text()
    text = re.sub("^public import .*\\n", "", text, flags=re.M)
    text = text.replace("module\n", "module\n\npublic import " + module + "\n", 1)
    changed[p] = text
    for p, text in changed.items():
        assert quality._non_comment_code_lines(text) <= 10000, (p, "file size")
        lines = text.splitlines()
        starts = quality._declaration_starts(quality._strip_lean_comments(text))
        for i, (line, _) in enumerate(starts):
            end = starts[i + 1][0] if i + 1 < len(starts) else len(lines) + 1
            block = lines[line - 1 : end - 1]
            start = next((j for j, s in enumerate(block) if ":=" in s), None)
            if start is not None:
                assert (
                    quality._non_comment_code_lines("\n".join(block[start:])) <= 200
                ), (p, line, "proof size")
    for p, text in changed.items():
        p.write_text(text)
    after_names = sorted(
        x.name for x in quality._declarations_in(sorted(root.glob("*.lean")))
    )
    audit = {
        "before": len(before_names),
        "after": len(after_names),
        "missing": sorted(set(before_names) - set(after_names)),
        "added": sorted(set(after_names) - set(before_names)),
    }
    (r / "certificate-join-public-name-audit.json").write_text(
        json.dumps(audit, indent=2)
    )
    assert before_names == after_names, audit
    renames = json.loads((r / "module-renames.json").read_text())
    for fragment in moved:
        old = "LeanPool.MovingSofa.GerverSofa." + fragment["original"]
        assert old in renames, old
        renames[old] = module
    (r / "module-renames.json").write_text(json.dumps(renames, indent=2))
    logger.info(
        "%s %s %s %s",
        "Applied:",
        audit,
        "new reconstruction code lines",
        quality._non_comment_code_lines(new),
    )
    assembly = root / "Reconstruction.lean"
    moved = json.loads((r / "certificate-join-fragments.json").read_text())
    before = sorted(
        x.name for x in quality._declarations_in(sorted(root.glob("*.lean")))
    )
    extra = []
    while True:
        assembly_text = assembly.read_text()
        names = {
            x.name.rsplit(".", 1)[-1]
            for x in quality._declarations_in([assembly])
            if x.kind in ["theorem", "lemma"]
        }
        found = []
        for i in range(35, 45):
            p = root / f"Batch{i:03d}.lean"
            text, lines, identities, spans = pieces(p)
            for identity, (a, b) in zip(identities, spans):
                body = "".join(lines[a:b])
                tokens = set(
                    re.findall("\\b\\w+\\b", quality._strip_lean_comments(body))
                )
                dependencies = sorted(tokens & names)
                if dependencies:
                    assert "CoverCertificate" not in quality._strip_lean_comments(
                        body
                    ), (p, identity)
                    found.append((p, text, lines, identity, a, b, body, dependencies))
        if not found:
            break
        seen = set()
        for p, text, lines, identity, a, b, body, dependencies in found:
            if p in seen:
                continue
            seen.add(p)
            del lines[a:b]
            text = "".join(lines).replace("* `" + identity + "`.\n", "", 1)
            p.write_text(text.rstrip() + "\n")
            assembly_text = assembly.read_text()
            end = assembly_text.index("-/", assembly_text.index("/-!"))
            assembly_text = (
                assembly_text[:end] + "* `" + identity + "`.\n" + assembly_text[end:]
            )
            assembly.write_text(assembly_text.rstrip() + "\n\n" + body.rstrip() + "\n")
            entry = {
                "original": identity,
                "from": p.stem,
                "body": body,
                "code_lines": quality._non_comment_code_lines(body),
            }
            moved.append(entry)
            extra.append({"original": identity, "dependencies": dependencies})
            renames = json.loads((r / "module-renames.json").read_text())
            key = "LeanPool.MovingSofa.GerverSofa." + identity
            assert key in renames
            renames[key] = (
                "LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Ce"
                "rtificates.Reconstruction"
            )
            (r / "module-renames.json").write_text(json.dumps(renames, indent=2))
    after = sorted(
        x.name for x in quality._declarations_in(sorted(root.glob("*.lean")))
    )
    assert before == after
    assert quality._non_comment_code_lines(assembly.read_text()) < 10000
    (r / "certificate-join-fragments.json").write_text(json.dumps(moved, indent=2))
    (r / "certificate-join-extra-fragments.json").write_text(
        json.dumps(extra, indent=2)
    )
    logger.info(
        "%s",
        {
            "extra_fragments": extra,
            "total_moved": len(moved),
            "public_names": len(after),
            "assembly_code_lines": quality._non_comment_code_lines(
                assembly.read_text()
            ),
        },
    )
