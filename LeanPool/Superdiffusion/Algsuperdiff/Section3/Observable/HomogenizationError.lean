/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section24.UnitCubeMultiscale.HomogenizationError.UnitCubeHomogenizationErrorCharacterization
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Observable.Comparator

/-!
# HomogenizationError

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Section 3 homogenization-error observable

This file defines the precise Section 3 specialization

`mathcal E_{s,infinity,2}(square_m; a, sigma Id)`

for an actual coefficient restriction `a` on `square_m` and a strictly
positive scalar comparator `sigma`.  The coefficient is pulled back by
`x ↦ 3^m x` to the unit cube and then fed to the already frozen, fully
characterized unit-cube homogenization error.  Thus the definition uses the
paper's spatial exponent `p = infinity`, aggregation exponent `q = 2`, and
the literal `sigma Id` gauge.  There is no free error family or fallback.

## References

* ABK26, definition `d.mathcal.E`, (2.28).
* ABK26, definition `d.mathcalS.def`, Section 3.1.
-/

namespace Algsuperdiff.Section3.Observable

open HCPolySupport HCPolySupport.Book.Ch02

noncomputable section

/-- The exact Section 3 error
`mathcal E_{s,infinity,2}(square_m; a, sigma Id)`. -/
noncomputable def homogenizationErrorAtScale {d : ℕ}
    (m : ℤ) (s : ℝ) (a : CoeffOn (cubeDomain (originCube d m)))
    (sigma : PositiveScalar) : ℝ :=
  Algsuperdiff.Frozen.Section24.unitCubeHomogenizationError
    s .infinity (.finite 2) (unitRescaledCoeffOn m a)
    (isotropicComparatorMatrix sigma)

/-- Characterization by the manuscript's literal
`mathcal E_{s,infinity,2}` on `square_m`.  The equality also certifies that the
scalar gauge is `sigma Id`, with no bare-diffusivity substitution. -/
theorem homogenizationErrorAtScale_characterization {d : ℕ}
    (m : ℤ) (s : ℝ) (a : CoeffOn (cubeDomain (originCube d m)))
    (sigma : PositiveScalar) (F : TriadicCoeffFamily d)
    (hF : CoeffOn.AEEq (F.coeffOn (originCube d m)) a) :
    homogenizationErrorAtScale m s a sigma =
      HomogenizationErrorOnCube (originCube d m) s .infinity (.finite 2) F
        (isotropicComparatorMatrix sigma) := by
  let B := TriadicCoeffFamily.dilate (-m) F
  calc
    homogenizationErrorAtScale m s a sigma =
        HomogenizationErrorOnCube (originCube d 0) s .infinity (.finite 2) B
          (isotropicComparatorMatrix sigma) := by
      exact
        Algsuperdiff.Frozen.Section24.unitCubeHomogenizationError_characterization
          s .infinity (.finite 2) (unitRescaledCoeffOn m a)
          (isotropicComparatorMatrix sigma) B
          (dilatedFamily_root_aeeq_unitRescaledCoeffOn m a F hF)
    _ = HomogenizationErrorOnCube (originCube d m) s .infinity (.finite 2) F
          (isotropicComparatorMatrix sigma) := by
      simpa [B, dilateOriginCube_neg_scale] using
        (HomogenizationErrorOnCube_dilate
          (TriadicCoeffFamily.isDilation_dilate (-m) F) (originCube d m)
          s .infinity (.finite 2) (isotropicComparatorMatrix sigma))

/-- The Section 3 homogenization error is nonnegative.  This follows directly from
the finite-`q` `Real.rpow` branch of CoarseGraining's literal definition. -/
theorem homogenizationErrorAtScale_nonneg {d : ℕ}
    (m : ℤ) {s : ℝ} (hs : 0 < s)
    (a : CoeffOn (cubeDomain (originCube d m)))
    (sigma : PositiveScalar) :
    0 ≤ homogenizationErrorAtScale m s a sigma := by
  let a0 := unitRescaledCoeffOn m a
  let F := Classical.choose
    (Algsuperdiff.Section24.UnitCubeMultiscale.exists_compatibleTriadicCoeffFamily a0)
  have hF : CoeffOn.AEEq (F.coeffOn (originCube d 0)) a0 :=
    Classical.choose_spec
      (Algsuperdiff.Section24.UnitCubeMultiscale.exists_compatibleTriadicCoeffFamily a0)
  rw [homogenizationErrorAtScale,
    Algsuperdiff.Frozen.Section24.unitCubeHomogenizationError_characterization
      s .infinity (.finite 2) a0 (isotropicComparatorMatrix sigma) F hF]
  unfold Book.Ch02.HomogenizationErrorOnCube Book.Ch02.HomogenizationError
    Book.Ch02.HomogenizationErrorFinite
  refine Real.rpow_nonneg (tsum_nonneg fun l => mul_nonneg ?_ ?_) _
  · simpa [geometricWeight_eq_old] using
      (HCPolySupport.geometricWeight_nonneg (s := s) (q := 2) l
        (by positivity : 0 ≤ s * (2 : ℝ)))
  · exact Real.rpow_nonneg
      (scaleResponseAtScale_infinity_nonneg (originCube d 0)
        (sub_le_self _ (by exact_mod_cast Nat.zero_le l)) F
        (isotropicComparatorMatrix sigma)) _

end

end Algsuperdiff.Section3.Observable
