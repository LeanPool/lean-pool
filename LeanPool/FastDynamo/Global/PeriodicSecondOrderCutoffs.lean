/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Global.ParametrixExplicitCutoffDerivatives
public import LeanPool.FastDynamo.Analysis.TransverseVecCutoffMultiplier
public import LeanPool.FastDynamo.Analysis.TransverseVecMultiplierAlgebra
public import LeanPool.FastDynamo.Analysis.TransverseVecMultipliers
public import LeanPool.FastDynamo.Global.LocalizedSummandAlgebra

/-!
# Periodic second-order cut-off multipliers

`PeriodicSecondOrderCutoff` bundles a periodic scalar cut-off (value, two first derivatives and
transverse Laplacian in quotient-level `L∞`) with a bounded multiplication map on the transverse
`H²` graph `TransverseC3H2` and its product rules: the embedding of the product is the
pointwise product, the first-order Leibniz rule, and the Laplacian product rule.  No commutator
identity or norm estimate is part of the structure.

Its instances are the Schwartz periodizations of `Global/TorusSchwartzPeriodicCutoff.lean`
(through `Analysis/TransverseSmoothH2CutoffMultiplier.lean`), and
`Global/HorizontalCutoffMultiplier.lean` descends it to the two-component fibre.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace PeriodicSecondOrderCutoffs

open ParametrixExplicitCutoff
open LocalizedSummandAlgebra
open TransverseVecMultiplierAlgebra

/-! ## The second-order multiplier interface -/

/-- A periodic scalar cutoff together with the `H²` multiplication
map and its first- and second-order product rules.

The value, gradient, and Laplacian live in quotient-level `L∞`.  No
commutator identity or norm estimate is included in this structure. -/
abbrev PeriodicSecondOrderCutoff := ParametrixCutoffs.TransverseVecSecondOrderCutoff (Fin 3)

end PeriodicSecondOrderCutoffs

end

end FastDynamo
