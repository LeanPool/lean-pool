/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.S4ConstantGain

/-!
# An explicit improvement to the planar distinct-distance bound in general position

Source: doi:10.5281/zenodo.23680960, url:https://github.com/mysticflounder/distinct-distances-general-position
Authors: Adam McKenna
Status: verified
Main declarations: `Esgk.numDistances_gt_one_third_add_kappa_image_gap`
Tags: discrete-geometry, distinct-distances, computational-certificates, farkas-lemma
MSC: 52C10, 51K05, 68V20
-/

/-!
## Upstream sources and certificate data

The proof is ported from Adam McKenna's Apache-2.0 release at commit
`091530ea585b132a0c893910a9a367a00660659a` of
<https://github.com/mysticflounder/distinct-distances-general-position>.
The planar predicates come from `mysticflounder/lean-formalizations` at
`dd46c17a2a034d7bfa0df02e7f77834d35592864`; that file credits their earlier
Apache-2.0 formal-conjectures definitions. The mathematical source is the
accompanying paper, DOI 10.5281/zenodo.23680960. Historical `docs/results/` labels
in the upstream comments refer to working notes absent from the public release.

Most source lines encode certificate data, rather than generated proof terms.
The public release includes the raw rational certificate and a Python verifier:
`certificate/constant-gain-1-40-K160-c60.json.gz` and
`verifier/verify_constant_gain_1_40.py`. Its uncompressed JSON has SHA-256
`0ce1bc6d77306573a2eccad01b75168a5faa6d6a058b91c8dcbbd0d1ce6e979a`.
The original exporter named in the data comments is absent from that release.
The preserved Lean strings are self-contained: the elaborators construct ordinary
`Nat`, `Int`, `Rat` and project-owned tree terms, and `decide +kernel` checks every
certificate. Their soundness follows from the general checker and geometric row
lemmas. Neither the exporter nor the Python verifier enters the trusted proof.
-/
