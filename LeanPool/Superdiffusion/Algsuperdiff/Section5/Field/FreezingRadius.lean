/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Field.HolderEstimate
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Freezing.LocalContrast
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.Decay.Geometry

/-!
# FreezingRadius

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# A polynomial quantitative freezing radius for the stream coefficient

The subcritical Hölder modulus gives an explicit point-dependent ball on
which subtracting the skew value at the centre and normalizing by `nu`
produces a coefficient within `delta` of the identity.  The radius is exactly
a positive sample-dependent constant times `(1 + |x|) ^ (-2 / gamma)`.
-/

namespace Algsuperdiff.Section5.Field

open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3
open Algsuperdiff.StochasticProcess.Common.Regularity.Ported
open Algsuperdiff.StochasticProcess.Common.Regularity.Freezing
open HCPolySupport
open HCPolySupport.Book.Ch02
open MeasureTheory

noncomputable section

variable {d : ℕ} {gamma : ℝ}

/-- The scalar-plus-stream coefficient. -/
def streamCoefficient (nu : ℝ) (omega : FullSample d gamma) : CoeffField d :=
  fun x ↦ nu • (1 : Mat d) + streamField omega x

/-- The scalar-plus-stream coefficient is continuous. -/
theorem continuous_streamCoefficient (nu : ℝ) (omega : FullSample d gamma) :
    Continuous (streamCoefficient nu omega) :=
  continuous_const.add (continuous_streamField omega)

/-- The symmetric part of the scalar-plus-stream coefficient is `nu I`. -/
theorem symmPart_streamCoefficient (nu : ℝ) (omega : FullSample d gamma)
    (x : Vec d) :
    symmPart (streamCoefficient nu omega x) = nu • (1 : Mat d) :=
  symmPart_nu_add_streamField nu omega x

/-- The reciprocal Hölder exponent governing the freezing radius. -/
def streamFreezingExponent (M : ABKModel d) : ℝ :=
  (streamHolderExponent M)⁻¹

/-- The dimensionless amplitude in the explicit freezing radius. -/
def streamFreezingAmplitude (M : ABKModel d) (omega : FullSample d M.gamma)
    (nu delta : ℝ) : ℝ :=
  min 1 (delta * nu / (1 + 3 * streamFieldHolderConst M omega))

/-- An explicit radius on which the coefficient frozen at `x` has contrast at
most `delta`. -/
def streamFreezingRadius (M : ABKModel d) (omega : FullSample d M.gamma)
    (nu delta : ℝ) (x : Vec d) : ℝ :=
  Real.rpow
    (streamFreezingAmplitude M omega nu delta / (1 + euclideanNorm x))
    (streamFreezingExponent M)

theorem streamFreezingExponent_pos (M : ABKModel d) :
    0 < streamFreezingExponent M := by
  exact inv_pos.mpr (streamHolderExponent_pos M)

theorem streamFreezingAmplitude_pos (M : ABKModel d)
    (omega : FullSample d M.gamma) {nu delta : ℝ}
    (hnu : 0 < nu) (hdelta : 0 < delta) :
    0 < streamFreezingAmplitude M omega nu delta := by
  unfold streamFreezingAmplitude
  exact lt_min (by norm_num) (div_pos (mul_pos hdelta hnu)
    (by have := streamFieldHolderConst_nonneg M omega; positivity))

theorem streamFreezingAmplitude_le_one (M : ABKModel d)
    (omega : FullSample d M.gamma) (nu delta : ℝ) :
    streamFreezingAmplitude M omega nu delta ≤ 1 := by
  exact min_le_left _ _

theorem streamFreezingRadius_pos (M : ABKModel d)
    (omega : FullSample d M.gamma) {nu delta : ℝ}
    (hnu : 0 < nu) (hdelta : 0 < delta) (x : Vec d) :
    0 < streamFreezingRadius M omega nu delta x := by
  unfold streamFreezingRadius
  apply Real.rpow_pos_of_pos
  exact div_pos (streamFreezingAmplitude_pos M omega hnu hdelta)
    (by have := euclideanNorm_nonneg x; positivity)

private theorem streamFreezingBase_le_one (M : ABKModel d)
    (omega : FullSample d M.gamma) (nu delta : ℝ) (x : Vec d) :
    streamFreezingAmplitude M omega nu delta / (1 + euclideanNorm x) ≤ 1 := by
  have hden : 1 ≤ 1 + euclideanNorm x := by
    exact le_add_of_nonneg_right (euclideanNorm_nonneg x)
  exact (div_le_one (by positivity)).2
    ((streamFreezingAmplitude_le_one M omega nu delta).trans hden)

theorem streamFreezingRadius_le_one (M : ABKModel d)
    (omega : FullSample d M.gamma) {nu delta : ℝ}
    (hnu : 0 < nu) (hdelta : 0 < delta) (x : Vec d) :
    streamFreezingRadius M omega nu delta x ≤ 1 := by
  unfold streamFreezingRadius
  simpa only [Real.rpow_eq_pow, Real.one_rpow] using Real.rpow_le_rpow
    (div_nonneg (streamFreezingAmplitude_pos M omega hnu hdelta).le
      (add_nonneg zero_le_one (euclideanNorm_nonneg x)))
    (streamFreezingBase_le_one M omega nu delta x)
    (streamFreezingExponent_pos M).le

theorem streamFreezingRadius_eq_polynomial (M : ABKModel d)
    (omega : FullSample d M.gamma) {nu delta : ℝ}
    (hnu : 0 < nu) (hdelta : 0 < delta) (x : Vec d) :
    streamFreezingRadius M omega nu delta x =
      Real.rpow (streamFreezingAmplitude M omega nu delta)
          (streamFreezingExponent M) *
        Real.rpow (1 + euclideanNorm x) (-streamFreezingExponent M) := by
  unfold streamFreezingRadius
  simp only [Real.rpow_eq_pow]
  rw [Real.div_rpow (streamFreezingAmplitude_pos M omega hnu hdelta).le
    (add_nonneg zero_le_one (euclideanNorm_nonneg x)) (streamFreezingExponent M)]
  rw [Real.rpow_neg (by have := euclideanNorm_nonneg x; positivity)]
  simp only [div_eq_mul_inv]

private theorem euclideanNorm_add_le (x y : Vec d) :
    euclideanNorm (x + y) ≤ euclideanNorm x + euclideanNorm y := by
  rw [euclideanNorm_eq_norm_ofVec, euclideanNorm_eq_norm_ofVec,
    euclideanNorm_eq_norm_ofVec, show HilbertVec.ofVec (x + y) =
      HilbertVec.ofVec x + HilbertVec.ofVec y by rfl]
  exact norm_add_le _ _

private theorem streamFreezingRadius_rpow_holder (M : ABKModel d)
    (omega : FullSample d M.gamma) {nu delta : ℝ}
    (hnu : 0 < nu) (hdelta : 0 < delta) (x : Vec d) :
    Real.rpow (streamFreezingRadius M omega nu delta x)
        (streamHolderExponent M) =
      streamFreezingAmplitude M omega nu delta / (1 + euclideanNorm x) := by
  unfold streamFreezingRadius streamFreezingExponent
  simp only [Real.rpow_eq_pow]
  exact Real.rpow_inv_rpow
    (div_nonneg (streamFreezingAmplitude_pos M omega hnu hdelta).le
      (add_nonneg zero_le_one (euclideanNorm_nonneg x)))
    (streamHolderExponent_pos M).ne'

private theorem matrixOperatorNorm_eq_applyMat_norm (A : Mat d) :
    matrixOperatorNorm A = ‖HilbertVec.applyMat A‖ := by
  rw [matrixOperatorNorm]
  congr 1

private theorem normalized_streamCoefficient_sub_one (M : ABKModel d)
    (omega : FullSample d M.gamma) {nu : ℝ} (hnu : 0 < nu)
    (x y : Vec d) :
    normalizedFrozenCoeff nu (streamCoefficient nu omega) x y - (1 : Mat d) =
      nu⁻¹ • (streamField omega y - streamField omega x) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [normalizedFrozenCoeff, streamCoefficient]
    field_simp [hnu.ne']
    ring
  · simp [normalizedFrozenCoeff, streamCoefficient, hij]

private theorem normalized_streamCoefficient_distance (M : ABKModel d)
    (omega : FullSample d M.gamma) {nu : ℝ} (hnu : 0 < nu)
    (x y : Vec d) :
    ‖HilbertVec.applyMat
        (normalizedFrozenCoeff nu (streamCoefficient nu omega) x y - (1 : Mat d))‖ =
      nu⁻¹ * matrixOperatorNorm (streamField omega y - streamField omega x) := by
  rw [normalized_streamCoefficient_sub_one M omega hnu]
  have happly : HilbertVec.applyMat (nu⁻¹ •
      (streamField omega y - streamField omega x)) =
      nu⁻¹ • HilbertVec.applyMat (streamField omega y - streamField omega x) := by
    ext v i
    simp [HilbertVec.applyMat_apply, matVecMul, Finset.mul_sum, mul_assoc]
  rw [happly, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnu),
    ← matrixOperatorNorm_eq_applyMat_norm]

private theorem streamFreezing_pointwise (M : ABKModel d)
    (omega : FullSample d M.gamma) {nu delta : ℝ}
    (hnu : 0 < nu) (hdelta : 0 < delta) (x : Vec d)
    {y : Vec d} (hy : y ∈ euclideanBall x
      (streamFreezingRadius M omega nu delta x)) :
    ‖HilbertVec.applyMat
        (normalizedFrozenCoeff nu (streamCoefficient nu omega) x y - (1 : Mat d))‖ ≤
      delta := by
  let r := streamFreezingRadius M omega nu delta x
  let t := euclideanNorm x
  let C := streamFieldHolderConst M omega
  have hrpos : 0 < r := streamFreezingRadius_pos M omega hnu hdelta x
  have hrle : r ≤ 1 := streamFreezingRadius_le_one M omega hnu hdelta x
  have hdist : euclideanNorm (y - x) < r :=
    DivergenceFormProcess.Decay.euclideanNorm_sub_lt_of_mem_euclideanBall hrpos.le hy
  have hdist1 : euclideanNorm (y - x) < 1 := hdist.trans_le hrle
  have hyNorm : euclideanNorm y ≤ 1 + t := by
    calc
      euclideanNorm y = euclideanNorm ((y - x) + x) := by congr 1; abel
      _ ≤ euclideanNorm (y - x) + euclideanNorm x := euclideanNorm_add_le _ _
      _ ≤ 1 + t := by
        unfold t
        simpa only [add_comm] using add_le_add_right hdist1.le (euclideanNorm x)
  have hxR : euclideanNorm x ≤ 2 + t := by
    unfold t
    linarith only
  have hyR : euclideanNorm y ≤ 2 + t := hyNorm.trans (by linarith only)
  have hholder := matrixOperatorNorm_streamField_sub_le_of_euclidean M omega
    (R := 2 + t) (by unfold t; linarith only [euclideanNorm_nonneg x])
    (x := y) (y := x) (by simpa only [euclideanNorm] using hyR)
    (by simpa only [euclideanNorm] using hxR)
  have hpowdist : Real.rpow (euclideanNorm (y - x)) (streamHolderExponent M) ≤
      Real.rpow r (streamHolderExponent M) :=
    Real.rpow_le_rpow (euclideanNorm_nonneg _) hdist.le (streamHolderExponent_pos M).le
  have hmod0 : 0 ≤ streamFieldHolderModulus M omega (2 + t) := by
    unfold streamFieldHolderModulus
    exact mul_nonneg (streamFieldHolderConst_nonneg M omega)
      (by unfold t; linarith only [euclideanNorm_nonneg x])
  have hfield : matrixOperatorNorm (streamField omega y - streamField omega x) ≤
      C * (3 + t) * Real.rpow r (streamHolderExponent M) := by
    calc
      matrixOperatorNorm (streamField omega y - streamField omega x) ≤
          streamFieldHolderModulus M omega (2 + t) *
            Real.rpow (euclideanNorm (y - x)) (streamHolderExponent M) := hholder
      _ ≤ streamFieldHolderModulus M omega (2 + t) *
            Real.rpow r (streamHolderExponent M) :=
        mul_le_mul_of_nonneg_left hpowdist hmod0
      _ = C * (3 + t) * Real.rpow r (streamHolderExponent M) := by
        unfold streamFieldHolderModulus C
        ring
  have hamp_le : streamFreezingAmplitude M omega nu delta ≤
      delta * nu / (1 + 3 * C) := min_le_right _ _
  have hC0 : 0 ≤ C := by unfold C; exact streamFieldHolderConst_nonneg M omega
  have ht0 : 0 ≤ t := by unfold t; exact euclideanNorm_nonneg x
  have hratio : C * (3 + t) / (1 + t) ≤ 3 * C := by
    apply (div_le_iff₀ (by linarith only [ht0])).2
    have h := mul_le_mul_of_nonneg_left (show 3 + t ≤ 3 * (1 + t) by
      linarith only [ht0]) hC0
    convert h using 1
    all_goals ring
  have hamp_budget : (1 + 3 * C) * streamFreezingAmplitude M omega nu delta ≤
      delta * nu := by
    exact (mul_le_mul_of_nonneg_left hamp_le (by positivity)).trans_eq
      (by
        field_simp)
  have hfieldBudget : matrixOperatorNorm (streamField omega y - streamField omega x) ≤
      delta * nu := by
    rw [streamFreezingRadius_rpow_holder M omega hnu hdelta x] at hfield
    calc
      matrixOperatorNorm (streamField omega y - streamField omega x) ≤
          C * (3 + t) *
            (streamFreezingAmplitude M omega nu delta / (1 + t)) := hfield
      _ = (C * (3 + t) / (1 + t)) * streamFreezingAmplitude M omega nu delta := by ring
      _ ≤ (3 * C) * streamFreezingAmplitude M omega nu delta :=
        mul_le_mul_of_nonneg_right hratio
          (streamFreezingAmplitude_pos M omega hnu hdelta).le
      _ ≤ (1 + 3 * C) * streamFreezingAmplitude M omega nu delta :=
        mul_le_mul_of_nonneg_right (by linarith only)
          (streamFreezingAmplitude_pos M omega hnu hdelta).le
      _ ≤ delta * nu := hamp_budget
  rw [normalized_streamCoefficient_distance M omega hnu]
  apply (inv_mul_le_iff₀ hnu).2
  exact hfieldBudget.trans_eq (mul_comm delta nu)

/-- The explicit radius gives the small normalized coefficient contrast needed
by the freezing argument. -/
theorem coefficientIdentityDistanceLE_streamCoefficient (M : ABKModel d)
    (omega : FullSample d M.gamma) {nu delta : ℝ}
    (hnu : 0 < nu) (hdelta : 0 < delta) (x : Vec d) :
    CoefficientIdentityDistanceLE
      (euclideanBall x (streamFreezingRadius M omega nu delta x))
      (normalizedFrozenCoeff nu (streamCoefficient nu omega) x) delta := by
  filter_upwards [ae_restrict_mem
      (isOpen_euclideanBall x (streamFreezingRadius M omega nu delta x)).measurableSet]
    with y hy
  exact streamFreezing_pointwise M omega hnu hdelta x hy

end

end Algsuperdiff.Section5.Field
