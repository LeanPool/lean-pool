"""Wrap roots."""

import json

from lean_pool.sofa_certificates.formatting import wrap_source


def run(workspace):
    """Run this transformation inside the fresh reproduction workspace."""
    for p in [
        workspace / "pool" / x["file"]
        for x in json.loads((workspace / "hoisted-cell-repairs.json").read_text())
    ]:
        s = p.read_text()
        t = s
        t = wrap_source(t)
        if t != s:
            p.write_text(t)
