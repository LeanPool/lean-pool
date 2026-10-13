/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.HomogBridge.NormalizedLoading
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Observable.CutoffHomogenizationErrorRepresentative
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Observable.CutoffResponseJ
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.ErrorComparison.Monotonicity

/-!
# ResponseCommonDomination

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Simultaneous directional response domination

The Section 3.5 response is evaluated from one measurable representative of
the entire coarse block matrix.  On the common physical event, every unit
direction is bounded by the square of the observation-cube homogenization
error formed from that same representative.  The coefficient cutoff scale
and observation scale remain separate.
-/

namespace Algsuperdiff.Section3.Provider.Homogenization

open MeasureTheory
open _root_.HCPolySupport _root_.HCPolySupport.Book

noncomputable section

/-- On one probability-one event, the observation-cube homogenization error
dominates the actual cutoff response simultaneously in every unit direction.
The comparator is the genuine running diffusivity at the coefficient cutoff
scale. -/
theorem ae_forall_cutoffResponseJ_le_observationHomogenizationError_sq
    {d : ℕ} (M : ABKModel d) (cubeScale coefficientScale : ℤ)
    {s : ℝ} (hs : 0 < s) :
    letI : NeZero d :=
      ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩
    ∀ᵐ omega ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ∀ e : Vec d, Ch02.vecNorm e = 1 →
        Observable.cutoffResponseJ M cubeScale coefficientScale e omega ≤
          Observable.cutoffHomogenizationErrorRepresentative M coefficientScale
            cubeScale hs (Annealed.sigmaBar M coefficientScale) omega ^ 2 := by
  let : NeZero d :=
    ⟨Nat.ne_of_gt (lt_of_lt_of_le (by omega) M.shellPrefix.dimension)⟩
  let sigma := Annealed.sigmaBar M coefficientScale
  let Q := originCube d cubeScale
  let F := fun omega : Cutoff.CutoffSample d =>
    Cutoff.coefficientCutoffTriadicCoeffFamily M coefficientScale omega
  filter_upwards
    [Observable.ae_forall_cutoffResponseJ_eq_literal M cubeScale coefficientScale,
      Observable.cutoffHomogenizationErrorRaw_ae_eq_representative M
        coefficientScale cubeScale hs sigma] with omega hresponse herror
  intro e he
  have hbook :
      Ch02.responseJ (Ch02.cubeDomain Q) ((F omega).coeffOn Q)
          (Observable.inverseSqrtLoad sigma e) (Observable.sqrtLoad sigma e) =
        Observable.cutoffResponseJ M cubeScale coefficientScale e omega := by
    rw [HCPolySupport.Internal.Ch02.book_responseJ_eq_ResponseJ]
    simp only [Q, F, Cutoff.coefficientCutoffTriadicCoeffFamily,
      Cutoff.coefficientCutoffCoeffOn_toCoeffField]
    change ResponseJ (openCubeSet (originCube d cubeScale))
      (Observable.inverseSqrtLoad sigma e) (Observable.sqrtLoad sigma e)
        (Cutoff.coefficientCutoff M.nu coefficientScale omega).toFun =
      Observable.cutoffResponseJ M cubeScale coefficientScale e omega
    rw [← HCPolySupport.responseJ_cubeSet_eq_openCubeSet_of_triadicCube]
    simpa only [sigma] using (hresponse e).symm
  have hresponse_le :
      Observable.cutoffResponseJ M cubeScale coefficientScale e omega ≤
        Ch02.normalizedBlockResponseMax Q (F omega)
          (Observable.isotropicComparatorMatrix sigma) := by
    rw [← hbook]
    simpa only [Observable.inverseSqrtLoad, Observable.sqrtLoad,
      Observable.isotropicComparatorMatrix, scalarMatrix] using
      Algsuperdiff.Section24.Sensitivity.Provider.HomogBridge.responseJ_scalarLoading_le_normalizedBlockResponseMax
          (F omega) Q sigma.property he
  have hhalf :=
    Algsuperdiff.Section3.Provider.ErrorComparison.rpow_half_normalizedBlockResponseMax_le_homogenizationErrorOnCube_infinity_finite
        Q (F omega) (Observable.isotropicComparatorMatrix sigma) hs
          (by norm_num : (1 : ℝ) ≤ 2)
  have hmax_nonneg :
      0 ≤ Ch02.normalizedBlockResponseMax Q (F omega)
        (Observable.isotropicComparatorMatrix sigma) :=
    Ch02.normalizedBlockResponseMax_nonneg Q (F omega)
      (Observable.isotropicComparatorMatrix sigma)
  have hmax_le_error_sq :
      Ch02.normalizedBlockResponseMax Q (F omega)
          (Observable.isotropicComparatorMatrix sigma) ≤
        (Ch02.HomogenizationErrorOnCube Q s .infinity (.finite 2) (F omega)
          (Observable.isotropicComparatorMatrix sigma)) ^ 2 := by
    have hsquared :
        (Real.rpow
          (Ch02.normalizedBlockResponseMax Q (F omega)
            (Observable.isotropicComparatorMatrix sigma)) (1 / 2 : ℝ)) ^ 2 ≤
          (Ch02.HomogenizationErrorOnCube Q s .infinity (.finite 2) (F omega)
            (Observable.isotropicComparatorMatrix sigma)) ^ 2 :=
      pow_le_pow_left₀ (Real.rpow_nonneg hmax_nonneg (1 / 2 : ℝ)) hhalf 2
    have hhalf_sq :
        (Real.rpow
          (Ch02.normalizedBlockResponseMax Q (F omega)
            (Observable.isotropicComparatorMatrix sigma)) (1 / 2 : ℝ)) ^ 2 =
          Ch02.normalizedBlockResponseMax Q (F omega)
            (Observable.isotropicComparatorMatrix sigma) := by
      calc
        (Real.rpow
          (Ch02.normalizedBlockResponseMax Q (F omega)
            (Observable.isotropicComparatorMatrix sigma)) (1 / 2 : ℝ)) ^ 2 =
            Real.rpow
              (Real.rpow
                (Ch02.normalizedBlockResponseMax Q (F omega)
                  (Observable.isotropicComparatorMatrix sigma)) (1 / 2 : ℝ))
              (2 : ℝ) := (Real.rpow_natCast _ 2).symm
        _ = Real.rpow
              (Ch02.normalizedBlockResponseMax Q (F omega)
                (Observable.isotropicComparatorMatrix sigma)) ((1 / 2 : ℝ) * 2) :=
          (Real.rpow_mul hmax_nonneg (1 / 2 : ℝ) 2).symm
        _ = Ch02.normalizedBlockResponseMax Q (F omega)
              (Observable.isotropicComparatorMatrix sigma) := by norm_num
    rw [hhalf_sq] at hsquared
    exact hsquared
  calc
    Observable.cutoffResponseJ M cubeScale coefficientScale e omega ≤
        Ch02.normalizedBlockResponseMax Q (F omega)
          (Observable.isotropicComparatorMatrix sigma) := hresponse_le
    _ ≤ (Ch02.HomogenizationErrorOnCube Q s .infinity (.finite 2) (F omega)
          (Observable.isotropicComparatorMatrix sigma)) ^ 2 := hmax_le_error_sq
    _ = Observable.cutoffHomogenizationErrorRaw M coefficientScale cubeScale s
          sigma omega ^ 2 := by
      rw [Observable.cutoffHomogenizationErrorRaw_characterization]
    _ = Observable.cutoffHomogenizationErrorRepresentative M coefficientScale
          cubeScale hs sigma omega ^ 2 := by rw [herror]

end

end Algsuperdiff.Section3.Provider.Homogenization
