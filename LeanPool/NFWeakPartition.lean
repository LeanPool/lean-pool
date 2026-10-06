/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NFStandard.NotWPP

/-!
# New Foundations refutes the Weak Partition Principle

Source: url:https://github.com/elliotglazer/nf-not-wpp/tree/fa58a7a895a73422042e167391c78e9149979913
Authors: Elliot Glazer, NFNotWPP contributors, Jesse Michael Han, Floris van Doorn, Ian Klatzco
Status: verified
Main declarations: `NFChoice.Foundation.NFStandard.NF_proves_not_WPP`
Tags: new-foundations, weak-partition-principle, first-order-logic
MSC: 03E70, 03B35
-/

/-!
## Maintenance and reproduction

The checked certificates are ordinary Lean source and require no generator to build.
They are preserved from upstream commit `fa58a7a895a73422042e167391c78e9149979913`;
the import commits record the namespace changes, pruning, grouping, and proof repairs.
Every certificate is checked again by Lean at the pool's pinned toolchain and Mathlib.

Upstream documents CPython 3.12 commands `translation/reproduce_c18.py build/c18-replay`
and `translation/reproduce_wpp_fv_split.py`. They reproduce the final C18 translator
chunk and its finite-variable support packaging. They are not a generator for this
entire ported dependency closure. The historical translation archive is retained at
the pinned upstream URL rather than imported as executable tooling here. Future
upgrades must validate the retained source, including its generated certificates;
the acquisition PR records clean build times and declaration profiles.

Four general proof layers have no external declaration callers in the current
endpoint. They are retained as reusable infrastructure: `NFStandard.StratificationNormalize`
normalizes arbitrary finite integer type assignments, `NFCompactLeafGate` establishes
compact axiom validity in arbitrary models of the literal finite theory, and
`PartialTotalizationBridgeDev002` proves compatibility of partial and total lowering.
`FocusedFVPaths` supplies generic free-variable embeddings through binding and complement.
The partial/total lowering layer is exposed as `NFChoice.DirectNominalPrf.Nominal.Totalization`.
The focused-variable lemmas are exposed as `NFChoice.DefinitionLeaves.AlphaFocusedFV`.
-/

/-!
## Finite-presentation attribution

The compatibility name `HailperinNF` denotes the eleven-sentence Metamath
Hailperin-derived presentation, including its added singleton axiom `axSn`.
Metamath credits that addition to SF on 12 January 2015 and identifies it as
absent from Hailperin's original presentation: <https://us.metamath.org/nfeuni/ax-sn.html>.
Both advertised equivalences concern this explicitly defined augmented presentation.
-/
