/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Analytic.DualNormJunk
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorOriginCubeFields
public import LeanPool.HighContrastHomogenization.Support.Ambient.CoefficientFieldHilbert
public import LeanPool.HighContrastHomogenization.Support.PDE.EnergyIdentities

/-!
# High-contrast homogenization: Provider.Regularity.CorrectorClassEnergy

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Symmetric energy of a local corrector class

The normalized symmetric energy is defined directly on the local Hilbert
`L²` class.  Raw-field characterizations are stated only after a caller
supplies a representative and its `L²` witness.
-/

open scoped ENNReal

namespace HCPolySupport
namespace HighContrast

noncomputable section

open MeasureTheory

private theorem ennreal_rpow_half_sq (x : ℝ≥0∞) :
    (x ^ (1 / 2 : ℝ)) ^ 2 = x := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

private theorem volumeAverage_eq_setAverage {d : ℕ}
    (U : Set (Vec d)) (f : Vec d → ℝ) :
    volumeAverage U f = ⨍ x in U, f x ∂volume := by
  simpa only [volumeAverage, smul_eq_mul, measureReal_def] using
    (MeasureTheory.setAverage_eq volume f U).symm

private theorem coefficientEnergyDensity_ae_nonneg {d : ℕ}
    {U : Set (Vec d)} {b : CoeffField d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam U b) (f : Vec d → Vec d) :
    0 ≤ᵐ[volumeMeasureOn U] coefficientEnergyDensity b f := by
  filter_upwards
      [ae_restrict_mem (measurableSet_of_isEllipticFieldOn hEll)] with x hx
  exact coefficientEnergyDensity_nonneg_of_isEllipticFieldOn hEll f x hx

/-! ## Generic quotient-carrier energy -/

/-- The volume-normalized symmetric coefficient energy of a local Hilbert
vector `L²` class. -/
@[expose]
noncomputable def normalizedLocalSymmetricEnergy {d : ℕ}
    {U : Set (Vec d)} {b : CoeffField d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam U b)
    (F : HilbertVectorL2 U) : ℝ :=
  (volume U).toReal⁻¹ *
    inner ℝ (hilbertSymmCoeffOperator hEll F) F

/-- On an explicitly supplied raw representative, the quotient-class energy
is the literal normalized coefficient-energy average. -/
theorem normalizedLocalSymmetricEnergy_eq_volumeAverage {d : ℕ}
    {U : Set (Vec d)} {b : CoeffField d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam U b)
    {f : Vec d → Vec d} (hf : MemVectorL2 U f) :
    normalizedLocalSymmetricEnergy hEll
        (toHilbertVectorL2OfVecField hf) =
      volumeAverage U (coefficientEnergyDensity b f) := by
  unfold normalizedLocalSymmetricEnergy volumeAverage
  rw [hilbertSymmCoeffOperator_toHilbertVectorL2OfVecField hEll hf]
  rw [inner_toHilbertVectorL2OfVecField_eq_integral]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [] with x
  exact vecDot_comm _ _

/-- The real class energy is exactly the square of the weighted
gradient norm after conversion to `ℝ≥0∞`. -/
theorem ofReal_normalizedLocalSymmetricEnergy_eq_weightedGradNorm_sq
    {d : ℕ} {U : Set (Vec d)} {b : CoeffField d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam U b)
    {f : Vec d → Vec d} (hf : MemVectorL2 U f) :
    ENNReal.ofReal
        (normalizedLocalSymmetricEnergy hEll
          (toHilbertVectorL2OfVecField hf)) =
      weightedGradNorm b U f ^ 2 := by
  rw [normalizedLocalSymmetricEnergy_eq_volumeAverage hEll hf]
  have hint : IntegrableOn (coefficientEnergyDensity b f) U :=
    integrableOn_coefficientEnergyDensity_of_isEllipticFieldOn hEll hf
  have hnonneg :
      0 ≤ᵐ[volumeMeasureOn U] coefficientEnergyDensity b f :=
    coefficientEnergyDensity_ae_nonneg hEll f
  rw [volumeAverage_eq_setAverage]
  rw [MeasureTheory.ofReal_setAverage hint hnonneg]
  unfold weightedGradNorm eVolumeAverage
  rw [ennreal_rpow_half_sq]
  rfl

/-- The normalized symmetric energy is nonnegative on every quotient class. -/
theorem normalizedLocalSymmetricEnergy_nonneg {d : ℕ}
    {U : Set (Vec d)} {b : CoeffField d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam U b)
    (F : HilbertVectorL2 U) :
    0 ≤ normalizedLocalSymmetricEnergy hEll F := by
  let fL2 : VectorL2 U := hilbertVectorL2ToVectorL2 (U := U) F
  let f : Vec d → Vec d := fun x ↦ fL2 x
  let hf : MemVectorL2 U f := MeasureTheory.Lp.memLp fL2
  have hclass : toHilbertVectorL2OfVecField hf = F := by
    calc
      toHilbertVectorL2OfVecField hf =
          vectorL2ToHilbertVectorL2 (U := U) (toVectorL2 hf) := by
        exact (vectorL2ToHilbertVectorL2_toVectorL2 hf).symm
      _ = vectorL2ToHilbertVectorL2 (U := U) fL2 := by
        apply congrArg (vectorL2ToHilbertVectorL2 (U := U))
        change hf.toLp (fun x => fL2 x) = fL2
        exact MeasureTheory.Lp.toLp_coeFn fL2 hf
      _ = F :=
        vectorL2ToHilbertVectorL2_hilbertVectorL2ToVectorL2 F
  rw [← hclass, normalizedLocalSymmetricEnergy_eq_volumeAverage hEll hf]
  unfold volumeAverage
  exact mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg)
    (integral_nonneg_of_ae (coefficientEnergyDensity_ae_nonneg hEll f))

/-- The quotient-class symmetric energy is continuous. -/
theorem continuous_normalizedLocalSymmetricEnergy {d : ℕ}
    {U : Set (Vec d)} {b : CoeffField d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam U b) :
    Continuous fun F : HilbertVectorL2 U ↦
      normalizedLocalSymmetricEnergy hEll F := by
  unfold normalizedLocalSymmetricEnergy
  refine continuous_const.mul ?_
  exact continuous_inner.comp
    ((hilbertSymmCoeffOperator hEll).continuous.prodMk continuous_id)

/-! ## Scalar-identity corrector specialization -/

end

end HighContrast
end HCPolySupport
