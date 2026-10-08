/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.HilbertMinimization
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Corrector.C1WeightedLeastSquaresCore

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Linear least-squares coordinates in a coercive Hilbert energy

For an injective finite-dimensional trial map, coercive Hilbert minimization
selects a unique residual.  Pulling its correction back through the trial map
gives a linear parameter selector.
-/

namespace HCPolySupport
namespace HighContrast
namespace Root

noncomputable section

variable {E H : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- A closed-subspace package for a closed linear range. -/
@[expose]
public noncomputable def closedLinearRange
    (T : E →ₗ[ℝ] H) (hclosed : IsClosed (LinearMap.range T : Set H)) :
    ClosedSubmodule ℝ H :=
  ⟨LinearMap.range T, hclosed⟩

/-- The coefficient-weighted least-squares slope selector.  The correction
of the affine Hilbert minimizer lies in the trial range; injectivity of the
trial map identifies that correction with a unique parameter. -/
@[expose]
noncomputable def weightedLeastSquaresSlopeMap
    (T : E →ₗ[ℝ] H) (hT : Function.Injective T)
    (hclosed : IsClosed (LinearMap.range T : Set H))
    (B : H →L[ℝ] H →L[ℝ] ℝ) (hB : IsCoercive B)
    (J : E →L[ℝ] H) : E →ₗ[ℝ] E :=
  -((LinearEquiv.ofInjective T hT).symm.toLinearMap.comp
    ((correctionMap (closedLinearRange T hclosed) B hB).toLinearMap.comp
      J.toLinearMap))

/-- The selected trial field is exactly the correction of the affine Hilbert
minimizer. -/
theorem trialMap_weightedLeastSquaresSlopeMap
    (T : E →ₗ[ℝ] H) (hT : Function.Injective T)
    (hclosed : IsClosed (LinearMap.range T : Set H))
    (B : H →L[ℝ] H →L[ℝ] ℝ) (hB : IsCoercive B)
    (J : E →L[ℝ] H) (e : E) :
    T (weightedLeastSquaresSlopeMap T hT hclosed B hB J e) =
      -(correctionMap (closedLinearRange T hclosed) B hB (J e) : H) := by
  change T (-((LinearEquiv.ofInjective T hT).symm
    (correctionMap (closedLinearRange T hclosed) B hB (J e)))) = _
  rw [map_neg]
  congr 1
  exact congrArg Subtype.val
    ((LinearEquiv.ofInjective T hT).apply_symm_apply
      (correctionMap (closedLinearRange T hclosed) B hB (J e)))

/-- The residual defined by the slope selector is the affine Hilbert
minimizer. -/
theorem residual_weightedLeastSquaresSlopeMap
    (T : E →ₗ[ℝ] H) (hT : Function.Injective T)
    (hclosed : IsClosed (LinearMap.range T : Set H))
    (B : H →L[ℝ] H →L[ℝ] ℝ) (hB : IsCoercive B)
    (J : E →L[ℝ] H) (e : E) :
    J e - T (weightedLeastSquaresSlopeMap T hT hclosed B hB J e) =
      affineMinimizerMap (closedLinearRange T hclosed) B hB (J e) := by
  rw [trialMap_weightedLeastSquaresSlopeMap T hT hclosed B hB J e,
    affineMinimizerMap_apply]
  abel

/-- The selected residual minimizes the coercive quadratic energy among all
trial slopes. -/
theorem quadraticEnergy_residual_weightedLeastSquaresSlopeMap_le
    (T : E →ₗ[ℝ] H) (hT : Function.Injective T)
    (hclosed : IsClosed (LinearMap.range T : Set H))
    {B : H →L[ℝ] H →L[ℝ] ℝ} (hB : IsCoercive B)
    (hBsymm : ∀ x y : H, B x y = B y x)
    (J : E →L[ℝ] H) (e b : E) :
    quadraticEnergy B
        (J e - T (weightedLeastSquaresSlopeMap T hT hclosed B hB J e)) ≤
      quadraticEnergy B (J e - T b) := by
  rw [residual_weightedLeastSquaresSlopeMap T hT hclosed B hB J e]
  apply affineMinimizerMap_minimizes_quadraticEnergy
    (closedLinearRange T hclosed) hB hBsymm
  change J e - T b - J e ∈ LinearMap.range T
  refine ⟨-b, ?_⟩
  rw [map_neg]
  abel

/-- The selected slope is the unique slope whose residual has no larger
energy than the canonical least-squares residual. -/
theorem eq_weightedLeastSquaresSlopeMap_of_quadraticEnergy_le
    (T : E →ₗ[ℝ] H) (hT : Function.Injective T)
    (hclosed : IsClosed (LinearMap.range T : Set H))
    {B : H →L[ℝ] H →L[ℝ] ℝ} (hB : IsCoercive B)
    (hBsymm : ∀ x y : H, B x y = B y x)
    (J : E →L[ℝ] H) (e b : E)
    (hle : quadraticEnergy B (J e - T b) ≤
      quadraticEnergy B
        (J e - T (weightedLeastSquaresSlopeMap T hT hclosed B hB J e))) :
    b = weightedLeastSquaresSlopeMap T hT hclosed B hB J e := by
  have hres := residual_weightedLeastSquaresSlopeMap
    T hT hclosed B hB J e
  have hmem : J e - T b - J e ∈
      closedLinearRange T hclosed := by
    change J e - T b - J e ∈ LinearMap.range T
    refine ⟨-b, ?_⟩
    rw [map_neg]
    abel
  have heq := eq_affineMinimizerMap_of_quadraticEnergy_le
    (closedLinearRange T hclosed) hB hBsymm (J e) (J e - T b)
      hmem (by simpa only [hres] using hle)
  rw [← hres] at heq
  have htrial : T b =
      T (weightedLeastSquaresSlopeMap T hT hclosed B hB J e) := by
    exact sub_right_injective heq
  exact hT htrial

end

end Root
end HighContrast
end HCPolySupport
