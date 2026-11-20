/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Global.ParametrixExplicitCutoffDerivatives
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
structure PeriodicSecondOrderCutoff where
  /-- Quotient-level scalar value of the cutoff. -/
  value : TransverseScalarLInf
  /-- The two quotient-level first derivatives of the cutoff. -/
  gradient : Fin 2 → TransverseScalarLInf
  /-- Quotient-level transverse Laplacian of the cutoff. -/
  laplacian : TransverseScalarLInf
  /-- Bounded multiplication by the cutoff on the transverse `H²` graph. -/
  domainMul : TransverseC3H2 →L[ℂ] TransverseC3H2
  embedding_domainMul : ∀ b,
    transverseH2Embedding (domainMul b) =
      scalarVectorMulTransverse value (transverseH2Embedding b)
  deriv_domainMul : ∀ j b,
    transverseDerivFromH2 j (domainMul b) =
      scalarVectorMulTransverse (gradient j) (transverseH2Embedding b) +
        scalarVectorMulTransverse value (transverseDerivFromH2 j b)
  laplacian_domainMul : ∀ b,
    transverseLaplacianFromH2 (domainMul b) =
      scalarVectorMulTransverse value (transverseLaplacianFromH2 b) +
        (2 : ℂ) • (∑ j : Fin 2,
          scalarVectorMulTransverse (gradient j)
            (transverseDerivFromH2 j b)) +
        scalarVectorMulTransverse laplacian (transverseH2Embedding b)

end PeriodicSecondOrderCutoffs

end

end FastDynamo
