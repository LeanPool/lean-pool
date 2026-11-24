/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.CoordinateDensityTwo
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.RestrictedMassEnvelopeMonotone

/-!
# Low-dimensional determinant form of a regular-patch density

The restricted mass is defined through the genuine exterior-power density of
the current pulled back to a regular parameter patch.  In complex dimensions
zero and one the verified finite-dimensional exterior/determinant identities
therefore rewrite that *actual* patch density as the normalized determinant
coefficient, with no comparison-of-measures assumption.

The dimension-two counterpart additionally needs the standard `(1,1)`
certificate off the pole set; it is recorded below in the form needed by a
future chartwise Bedford--Taylor comparison.  These statements do not claim
that the resulting parameter measure is already the ambient global measure:
the remaining input is the full-dimensional chart/pushforward compatibility.
-/

@[expose] public section

noncomputable section

namespace SGPT.Foundations.Analysis.Pending.FullSpaceLowDimDensity

open FirstPass FirstPass.PositiveClasses FirstPass.NumericalRestrictedVolumeScaffold
  FirstPass.NumericalRestrictedVolume FirstPass.AdmissibleCurrentFormPositivity
  FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending.RestrictedMassEnvelopeMonotone

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {omega : KahlerBackground n M} {alpha : RealBottChern n M}
  {V : ClosedIrreducibleAnalyticSubvariety n M} {epsilon : PositiveError}

private theorem actualTopPowerDensity_eq_normalizedTopPowerDensity_of_dim_eq_zero
    {k : ℕ} (hk : k = 0) (A : CoordinateRealTwoForm k) :
    actualTopPowerDensity A = normalizedTopPowerDensity A := by
  subst k
  exact actualTopPowerDensity_eq_normalizedTopPowerDensity_zero A

private theorem actualTopPowerDensity_eq_normalizedTopPowerDensity_of_dim_eq_one
    {k : ℕ} (hk : k = 1) (A : CoordinateRealTwoForm k) :
    actualTopPowerDensity A = normalizedTopPowerDensity A := by
  subst k
  exact actualTopPowerDensity_eq_normalizedTopPowerDensity_one A

private theorem actualTopPowerDensity_eq_normalizedTopPowerDensity_of_dim_eq_two
    {k : ℕ} (hk : k = 2) (A : CoordinateRealTwoForm k) (hA : IsOneOne A) :
    actualTopPowerDensity A = normalizedTopPowerDensity A := by
  subst k
  exact actualTopPowerDensity_eq_normalizedTopPowerDensity_two A hA

/-- In parameter dimension zero, the density used in `acTopMass` is exactly
the normalized determinant coefficient of the pulled-back current form. -/
theorem patchDensity_eq_normalizedTopPowerDensity_of_dim_eq_zero
    (p : AdmissibleRestrictedCurrentPresentation omega alpha V epsilon)
    (P : RegularPatch V) (w : ComplexModel V.dim) (hV : V.dim = 0) :
    patchDensity p P w =
      normalizedTopPowerDensity
        ((coordinateCurrentForm p (complexChartAt (n := n) P.center)
          (P.coordinateParametrization w)).compContinuousLinearMap
          (fderiv ℝ P.coordinateParametrization w)) := by
  unfold patchDensity
  exact actualTopPowerDensity_eq_normalizedTopPowerDensity_of_dim_eq_zero hV _

/-- In parameter dimension one, the density used in `acTopMass` is exactly
the normalized determinant coefficient of the pulled-back current form.  No
positivity premise is needed in this dimension. -/
theorem patchDensity_eq_normalizedTopPowerDensity_of_dim_eq_one
    (p : AdmissibleRestrictedCurrentPresentation omega alpha V epsilon)
    (P : RegularPatch V) (w : ComplexModel V.dim) (hV : V.dim = 1) :
    patchDensity p P w =
      normalizedTopPowerDensity
        ((coordinateCurrentForm p (complexChartAt (n := n) P.center)
          (P.coordinateParametrization w)).compContinuousLinearMap
          (fderiv ℝ P.coordinateParametrization w)) := by
  unfold patchDensity
  exact actualTopPowerDensity_eq_normalizedTopPowerDensity_of_dim_eq_one hV _

/-- In parameter dimension two, the verified exterior/determinant identity
applies on the regular, pole-free locus.  The `(1,1)` certificate is obtained
from the admissible current and complex linearity of the regular-patch
differential; it is not an additional analytic assumption. -/
theorem patchDensity_eq_normalizedTopPowerDensity_of_dim_eq_two
    (p : AdmissibleRestrictedCurrentPresentation omega alpha V epsilon)
    (P : RegularPatch V) (w : ComplexModel V.dim) (hV : V.dim = 2)
    (hw : w ∈ P.parameterDomain)
    (hpole : (complexChartAt (n := n) P.center).val.symm
      (P.coordinateParametrization w) ∉ poleSet p.potential) :
    patchDensity p P w =
      normalizedTopPowerDensity
        ((coordinateCurrentForm p (complexChartAt (n := n) P.center)
          (P.coordinateParametrization w)).compContinuousLinearMap
          (fderiv ℝ P.coordinateParametrization w)) := by
  let e := complexChartAt (n := n) P.center
  have hz : P.coordinateParametrization w ∈ e.val.target :=
    P.source_subset (P.flattening.mapsTo_invFun hw)
  have hL := RegularPatchDerivative.fderiv_coordinateParametrization_I_smul P hw
  obtain ⟨hA, -⟩ := coordinateCurrentForm_isOneOne_and_semipositive p e hz hpole
  have hpull : IsOneOne
      ((coordinateCurrentForm p e (P.coordinateParametrization w)).compContinuousLinearMap
        (fderiv ℝ P.coordinateParametrization w)) :=
    isOneOne_compContinuousLinearMap hA _ hL
  unfold patchDensity
  change actualTopPowerDensity
      ((coordinateCurrentForm p e (P.coordinateParametrization w)).compContinuousLinearMap
        (fderiv ℝ P.coordinateParametrization w)) =
    normalizedTopPowerDensity
      ((coordinateCurrentForm p e (P.coordinateParametrization w)).compContinuousLinearMap
        (fderiv ℝ P.coordinateParametrization w))
  exact actualTopPowerDensity_eq_normalizedTopPowerDensity_of_dim_eq_two hV _ hpull

end SGPT.Foundations.Analysis.Pending.FullSpaceLowDimDensity
