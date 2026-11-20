/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Analysis.TransverseWeightedLeibniz

/-!
# Second-order periodic cut-off multipliers at an arbitrary fibre

The commutator calculus of `eq:explicit-error` (proof of `lem:parametrix-error`)
needs the cut-offs of `eq:parametrix-cutoff-bounds` not as plane profiles but
as bounded multipliers of the periodic `H²` Fourier graph.

The interface below is generic in the fibre type `ι`: the value, the two first derivatives and
the Laplacian live in quotient-level `L∞`, the multiplier is a bounded map of the transverse
`H²` graph at the fibre `ι`, and the two Leibniz rules relate them.  Neither a commutator
identity nor a norm estimate is part of the structure, and no cell, radius or spectral
parameter occurs; it is the fibre-generic form of
`FastDynamo.PeriodicSecondOrderCutoffs.PeriodicSecondOrderCutoff`, whose fibre is
hard-wired to `ℂ³`, whereas the paper works at `ℂ²`.

The declarations live in the namespace `ParametrixCutoffs`, shared with
`Global/ParametrixCutoffs.lean`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory

namespace ParametrixCutoffs

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A periodic scalar cut-off together with the `H²` multiplication map at the fibre `ι`
and its first- and second-order product rules. -/
structure TransverseVecSecondOrderCutoff (ι : Type*) [Fintype ι] [DecidableEq ι] where
  /-- Quotient-level scalar value of the cut-off. -/
  value : TransverseScalarLInf
  /-- The two quotient-level first derivatives of the cut-off. -/
  gradient : Fin 2 → TransverseScalarLInf
  /-- Quotient-level transverse Laplacian of the cut-off. -/
  laplacian : TransverseScalarLInf
  /-- Bounded multiplication by the cut-off on the transverse `H²` graph at the fibre `ι`. -/
  domainMul : TransverseVecH2 ι →L[ℂ] TransverseVecH2 ι
  /-- The multiplier is multiplication by `value` on the underlying physical field. -/
  embedding_domainMul : ∀ b, transverseH2Embedding (domainMul b) =
    scalarVectorMulTransverseVec ι value (transverseH2Embedding b)
  /-- First-order Leibniz rule `∂_j(χb) = (∂_jχ)b + χ∂_jb`. -/
  deriv_domainMul : ∀ j b, transverseVecDerivFromH2 ι j (domainMul b) =
    scalarVectorMulTransverseVec ι (gradient j) (transverseH2Embedding b) +
      scalarVectorMulTransverseVec ι value (transverseVecDerivFromH2 ι j b)
  /-- Second-order Leibniz rule `Δ(χb) = χΔb + 2Σ_j(∂_jχ)(∂_jb) + (Δχ)b`. -/
  laplacian_domainMul : ∀ b, transverseVecLaplacianFromH2 ι (domainMul b) =
    scalarVectorMulTransverseVec ι value (transverseVecLaplacianFromH2 ι b) +
      (2 : ℂ) • (∑ j : Fin 2, scalarVectorMulTransverseVec ι (gradient j)
        (transverseVecDerivFromH2 ι j b)) +
      scalarVectorMulTransverseVec ι laplacian (transverseH2Embedding b)

/-- Multiplication by the cut-off on the ambient transverse `L²` space at the fibre `ι`. -/
def TransverseVecSecondOrderCutoff.stateMul (chi : TransverseVecSecondOrderCutoff ι) :
    TransverseVecL2 ι →L[ℂ] TransverseVecL2 ι :=
  scalarVectorMulTransverseVec ι chi.value

/-- The domain multiplier and the state multiplier agree through the `H²` embedding: this is
`embedding_domainMul` read as an identity of bounded maps. -/
theorem TransverseVecSecondOrderCutoff.embedding_comp_domainMul
    (chi : TransverseVecSecondOrderCutoff ι) :
    (transverseH2Embedding (ι := ι)).comp chi.domainMul =
      chi.stateMul.comp (transverseH2Embedding (ι := ι)) := by
  apply ContinuousLinearMap.ext
  intro b
  exact chi.embedding_domainMul b

end ParametrixCutoffs

end

end FastDynamo
