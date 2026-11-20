/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Operator.RieszDomainCalculus
public import LeanPool.FastDynamo.Operator.Product
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

/-!
# Extracting an eigenmode from a corrected Riesz projection

The corrected parametrix produces a nonzero finite-dimensional Riesz range.
`RieszDomainCalculus` already gives a canonical lift of that range into the
bundled operator domain and identifies the operator action on the lift with
the first resolvent moment.  This file performs the remaining
finite-dimensional linear algebra.

There are two spectral-calculus inputs, kept abstract here so that this file
needs no circle-integral API of its own:

* the first resolvent moment preserves the Riesz range; and
* eigenvalues of its restriction lie inside the isolating circle.

They are exposed as named predicates below.  Given the first, nonzero finite
rank already produces an actual nonzero domain eigenpair.  Given the second,
the eigenvalue lies inside the circle (`exists_domain_eigenpair_mem_ball`).

Both predicates are theorems of the contour calculus, proved in
`Global/CorrectedRieszProjectionSpectralCalculus.lean`, which packages the extraction as
`exists_domain_eigenpair_mem_ball_of_finite_projection`.
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

/-! ## The exact invariant finite-dimensional interface -/

/-- The first resolvent moment maps the algebraic Riesz range into itself.
This is the precise invariance statement needed to restrict the moment to a
finite-dimensional endomorphism. -/
def SpectralMomentPreservesRieszRange
    (h : HasResolventOn A (sphere center radius)) : Prop :=
  ∀ x : X, x ∈ h.rieszProjection.toLinearMap.range →
    h.rieszSpectralMoment x ∈ h.rieszProjection.toLinearMap.range

/-- Restriction of the first resolvent moment to the Riesz range. -/
def rieszRangeSpectralMoment
    (h : HasResolventOn A (sphere center radius))
    (hinvariant : SpectralMomentPreservesRieszRange h) :
    Module.End ℂ h.rieszProjection.toLinearMap.range where
  toFun x := ⟨h.rieszSpectralMoment x, hinvariant x x.property⟩
  map_add' x y := by
    apply Subtype.ext
    exact h.rieszSpectralMoment.map_add x y
  map_smul' a x := by
    apply Subtype.ext
    exact h.rieszSpectralMoment.map_smul a x

omit [CompleteSpace X] [CompleteSpace D] in
/-- The restriction of the first resolvent moment to the Riesz range acts, in the ambient space,
by the unrestricted moment `h.rieszSpectralMoment`. -/
@[simp] theorem rieszRangeSpectralMoment_coe
    (h : HasResolventOn A (sphere center radius))
    (hinvariant : SpectralMomentPreservesRieszRange h)
    (x : h.rieszProjection.toLinearMap.range) :
    ((rieszRangeSpectralMoment h hinvariant x :
      h.rieszProjection.toLinearMap.range) : X) =
      h.rieszSpectralMoment x :=
  rfl

/-- Finite-rank and invariance data supplied by the corrected contour
calculus.  Idempotence is included because the canonical domain lift of a
vector `x` in the range has ambient value `P x`, which equals `x` precisely
for an idempotent contour operator. -/
structure FiniteInvariantRieszData
    (h : HasResolventOn A (sphere center radius)) : Prop where
  /-- The contour operator is a projection. -/
  idempotent : IsIdempotentElem h.rieszProjection
  /-- Its algebraic range is finite-dimensional. -/
  range_finiteDimensional :
    FiniteDimensional ℂ h.rieszProjection.toLinearMap.range
  /-- The corrected projection is nonzero. -/
  projection_ne_zero : h.rieszProjection ≠ 0
  /-- The first resolvent moment preserves the corrected range. -/
  spectralMoment_invariant : SpectralMomentPreservesRieszRange h

namespace FiniteInvariantRieszData

variable {h : HasResolventOn A (sphere center radius)}

omit [CompleteSpace X] [CompleteSpace D] in
/-- The corrected Riesz range is nontrivial. -/
theorem range_ne_bot
    (data : FiniteInvariantRieszData h) :
    h.rieszProjection.toLinearMap.range ≠ ⊥ := by
  have hlinear : h.rieszProjection.toLinearMap ≠ 0 := by
    intro hzero
    apply data.projection_ne_zero
    exact ContinuousLinearMap.coe_injective (by simpa using hzero)
  intro hrange
  exact hlinear (LinearMap.range_eq_bot.mp hrange)

omit [CompleteSpace X] [CompleteSpace D] in
/-- The restriction of the first resolvent moment has an eigenvalue because
it acts on a nontrivial finite-dimensional complex vector space. -/
theorem exists_range_eigenvalue
    (data : FiniteInvariantRieszData h) :
    ∃ eigenvalue : ℂ,
      Module.End.HasEigenvalue
        (rieszRangeSpectralMoment h data.spectralMoment_invariant)
        eigenvalue := by
  let _ : FiniteDimensional ℂ h.rieszProjection.toLinearMap.range :=
    data.range_finiteDimensional
  let _ : Nontrivial h.rieszProjection.toLinearMap.range :=
    Submodule.nontrivial_iff_ne_bot.mpr data.range_ne_bot
  exact Module.End.exists_eigenvalue
    (rieszRangeSpectralMoment h data.spectralMoment_invariant)

/-- Every eigenvector of the restricted first moment lifts canonically to an
eigenvector in the bundled operator domain. -/
theorem isEigenpair_domainRieszProjection_of_hasEigenvector
    (data : FiniteInvariantRieszData h)
    (hRadius : 0 ≤ radius) {eigenvalue : ℂ}
    {x : h.rieszProjection.toLinearMap.range}
    (hx : Module.End.HasEigenvector
      (rieszRangeSpectralMoment h data.spectralMoment_invariant)
      eigenvalue x) :
    A.IsEigenpair eigenvalue (h.domainRieszProjection (x : X)) := by
  have hPx : h.rieszProjection (x : X) = x := by
    exact (LinearMap.IsIdempotentElem.mem_range_iff
      (ContinuousLinearMap.IsIdempotentElem.toLinearMap data.idempotent)).mp
      x.property
  have hembedding :
      A.embedding (h.domainRieszProjection (x : X)) = x := by
    rw [h.embedding_domainRieszProjection_apply hRadius, hPx]
  have hmoment :
      A.op (h.domainRieszProjection (x : X)) =
        h.rieszSpectralMoment (x : X) := by
    exact DFunLike.congr_fun
      (h.op_comp_domainRieszProjection hRadius) (x : X)
  have heigenRange := hx.apply_eq_smul
  have heigenAmbient :
      h.rieszSpectralMoment (x : X) = eigenvalue • (x : X) := by
    exact congrArg Subtype.val heigenRange
  constructor
  · rw [hembedding]
    intro hxzero
    apply hx.2
    exact Subtype.ext hxzero
  · rw [hmoment, heigenAmbient, hembedding]

end FiniteInvariantRieszData

/-! ## Spectral location and the isolating contour -/

/-- The spectral-mapping input in its minimal finite-dimensional
form: every eigenvalue of the restricted first resolvent moment lies inside
the isolating circle. -/
def RieszRangeSpectrumInsideCircle
    (h : HasResolventOn A (sphere center radius))
    (data : FiniteInvariantRieszData h) : Prop :=
  ∀ eigenvalue : ℂ,
    Module.End.HasEigenvalue
        (rieszRangeSpectralMoment h data.spectralMoment_invariant)
        eigenvalue →
      eigenvalue ∈ ball center radius

/-- With the finite-dimensional spectral-mapping input, the extracted domain
eigenvalue lies strictly inside the isolating circle. -/
theorem exists_domain_eigenpair_mem_ball
    (h : HasResolventOn A (sphere center radius))
    (data : FiniteInvariantRieszData h) (hRadius : 0 ≤ radius)
    (hinside : RieszRangeSpectrumInsideCircle h data) :
    ∃ eigenvalue : ℂ, ∃ eigenvector : D,
      eigenvalue ∈ ball center radius ∧
        A.IsEigenpair eigenvalue eigenvector := by
  obtain ⟨eigenvalue, heigenvalue⟩ := data.exists_range_eigenvalue
  obtain ⟨x, hx⟩ := heigenvalue.exists_hasEigenvector
  exact ⟨eigenvalue, h.domainRieszProjection (x : X),
    hinside eigenvalue heigenvalue,
    data.isEigenpair_domainRieszProjection_of_hasEigenvector hRadius hx⟩

end CorrectedRieszProjectionEigenmode

end

end FastDynamo
