/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Operator.RieszSpectralMomentCalculus
public import LeanPool.FastDynamo.Operator.RieszEigenvalueLocalization

/-!
# Spectral calculus for the corrected Riesz projection

This file connects the generic contour calculus to the finite-dimensional
eigenmode extraction interface.  For a nonnegative circle radius, the first
spectral moment automatically preserves the Riesz range.  Thus idempotence,
finite rank, and nonvanishing are the only data needed to construct
`FiniteInvariantRieszData`.  The generic Cauchy localization theorem then
places every eigenvalue of the restricted moment strictly inside the circle.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open Complex Metric Set

namespace CorrectedRieszProjectionEigenmode

universe u v

variable {X : Type u} {D : Type v}
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup D] [NormedSpace ℂ D] [CompleteSpace D]
  {A : DomainOperator X D} {center : ℂ} {radius : ℝ}

omit [CompleteSpace D] in
/-- The first spectral moment canonically preserves the Riesz range. -/
theorem spectralMomentPreservesRieszRange_of_nonnegative_radius
    (h : HasResolventOn A (sphere center radius))
    (hRadius : 0 ≤ radius) :
    SpectralMomentPreservesRieszRange h := by
  intro x hx
  exact h.rieszSpectralMoment_mem_rieszProjection_range hRadius hx

omit [CompleteSpace D] in
/-- Construct the complete finite invariant Riesz package from idempotence,
finite-dimensionality, and nonvanishing.  Spectral-moment invariance is a
theorem of the contour calculus, not an additional input. -/
theorem finiteInvariantRieszDataOfFiniteProjection
    (h : HasResolventOn A (sphere center radius))
    (hRadius : 0 ≤ radius)
    (hIdempotent : IsIdempotentElem h.rieszProjection)
    (hFinite : FiniteDimensional ℂ h.rieszProjection.toLinearMap.range)
    (hNe : h.rieszProjection ≠ 0) :
    FiniteInvariantRieszData h where
  idempotent := hIdempotent
  range_finiteDimensional := hFinite
  projection_ne_zero := hNe
  spectralMoment_invariant :=
    spectralMomentPreservesRieszRange_of_nonnegative_radius h hRadius

/-- A nonzero finite-dimensional Riesz projection produces a domain
eigenpair whose eigenvalue lies strictly inside its contour. -/
theorem exists_domain_eigenpair_mem_ball_of_finite_projection
    (h : HasResolventOn A (sphere center radius))
    (hRadius : 0 ≤ radius)
    (hIdempotent : IsIdempotentElem h.rieszProjection)
    (hFinite : FiniteDimensional ℂ h.rieszProjection.toLinearMap.range)
    (hNe : h.rieszProjection ≠ 0) :
    ∃ eigenvalue : ℂ, ∃ eigenvector : D,
      eigenvalue ∈ ball center radius ∧
        A.IsEigenpair eigenvalue eigenvector := by
  let data := finiteInvariantRieszDataOfFiniteProjection h hRadius
    hIdempotent hFinite hNe
  exact exists_domain_eigenpair_mem_ball h data hRadius
    (rieszRangeSpectrumInsideCircle_of_nonnegative_radius h data hRadius)

end CorrectedRieszProjectionEigenmode

end

end FastDynamo
