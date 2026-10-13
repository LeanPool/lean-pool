/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Freezing.SkewConst
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Ported.CoefficientBounds
public import LeanPool.HighContrastHomogenization.Support.Probability.RegCoeffField.EllipticSet
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# LocalContrast

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Small contrast after freezing a continuous skew field

Subtracting the skew part at a centre and dividing by the scalar symmetric
part produces a coefficient equal to the identity at that centre. Continuity
makes this coefficient uniformly close to the identity on a sufficiently
small ball. On a compact set, the radius can be chosen uniformly.
-/

namespace Algsuperdiff.StochasticProcess.Common.Regularity.Freezing

open MeasureTheory HCPolySupport
open Algsuperdiff.Section4.Provider.ExcessDecay
open Algsuperdiff.StochasticProcess.Common.Regularity.Ported

noncomputable section

variable {d : ℕ}

/-- The coefficient obtained by subtracting the skew part frozen at `z` and
normalizing its scalar symmetric part. -/
def normalizedFrozenCoeff (nu : ℝ) (a : CoeffField d) (z : Vec d) : CoeffField d :=
  fun y ↦ nu⁻¹ • (a y - (a z - nu • (1 : Mat d)))

/-- Matrix action on the Euclidean realization, as a linear map into bounded
operators. -/
noncomputable def matrixToHilbertOperatorLinear :
    Mat d →ₗ[ℝ] (HilbertVec d →L[ℝ] HilbertVec d) where
  toFun := HilbertVec.applyMat
  map_add' := by
    intro A B
    ext x i
    simp [HilbertVec.applyMat_apply, matVecMul, Finset.sum_add_distrib, add_mul]
  map_smul' := by
    intro c A
    ext x i
    simp [HilbertVec.applyMat_apply, matVecMul, Finset.mul_sum, mul_assoc]

/-- Matrix action on the Euclidean realization is continuous in the matrix,
by finite-dimensionality. -/
noncomputable def matrixToHilbertOperator :
    Mat d →L[ℝ] (HilbertVec d →L[ℝ] HilbertVec d) :=
  ⟨matrixToHilbertOperatorLinear,
    matrixToHilbertOperatorLinear.continuous_of_finiteDimensional⟩

/-- The normalized skew coefficient represented as an operator on Euclidean Hilbert space. -/
def normalizedSkewOperator (nu : ℝ) (a : CoeffField d) :
    Vec d → (HilbertVec d →L[ℝ] HilbertVec d) :=
  fun y ↦ matrixToHilbertOperator (nu⁻¹ • (a y - nu • (1 : Mat d)))

private theorem continuousOn_normalizedSkewOperator
    {U : Set (Vec d)} {nu : ℝ} {a : CoeffField d}
    (hcont : ContinuousOn (fun y ↦ a y - nu • (1 : Mat d)) U) :
    ContinuousOn (normalizedSkewOperator nu a) U := by
  have h : ContinuousOn (fun y ↦ nu⁻¹ • (a y - nu • (1 : Mat d))) U :=
    (continuousOn_const : ContinuousOn (fun _ : Vec d => nu⁻¹) U).smul hcont
  exact matrixToHilbertOperator.continuous.comp_continuousOn h

private theorem normalizedFrozenCoeff_sub_one_applyMat_eq
    (nu : ℝ) (hnu : 0 < nu) (a : CoeffField d) (z y : Vec d) :
    HilbertVec.applyMat (normalizedFrozenCoeff nu a z y - (1 : Mat d)) =
      normalizedSkewOperator nu a y - normalizedSkewOperator nu a z := by
  have hmat :
      normalizedFrozenCoeff nu a z y - (1 : Mat d) =
        nu⁻¹ • (a y - nu • (1 : Mat d)) -
          nu⁻¹ • (a z - nu • (1 : Mat d)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [normalizedFrozenCoeff]
      field_simp [hnu.ne']
      ring
    · simp [normalizedFrozenCoeff, hij]
      ring
  change matrixToHilbertOperator
      (normalizedFrozenCoeff nu a z y - (1 : Mat d)) = _
  rw [hmat, map_sub]
  rfl

/-- A matrix whose symmetric part is `nu • I` differs from that scalar
matrix by a skew matrix. -/
theorem sub_scalar_one_isSkew_of_symmPart_eq {nu : ℝ} {A : Mat d}
    (hA : symmPart A = nu • (1 : Mat d)) :
    matTranspose (A - nu • (1 : Mat d)) = -(A - nu • (1 : Mat d)) := by
  ext i j
  have hij := congrFun (congrFun hA i) j
  by_cases h : i = j
  · subst j
    simp [symmPart, matTranspose] at hij ⊢
    linarith only [hij]
  · have hji : j ≠ i := Ne.symm h
    simp [symmPart, matTranspose, h, hji] at hij ⊢
    linarith only [hij]

/-- The normalized frozen coefficient retains exactly the identity as its
symmetric part. -/
theorem symmPart_normalizedFrozenCoeff_eq_one
    {nu : ℝ} (hnu : 0 < nu) {a : CoeffField d}
    (hsymm : ∀ y, symmPart (a y) = nu • (1 : Mat d)) (z y : Vec d) :
    symmPart (normalizedFrozenCoeff nu a z y) = (1 : Mat d) := by
  have hk := sub_scalar_one_isSkew_of_symmPart_eq (hsymm z)
  rw [normalizedFrozenCoeff, symmPart_smul,
    symmPart_sub_const_of_skew hk, hsymm y, ← mul_smul]
  field_simp [hnu.ne']
  simp

private theorem matVecMul_one_local (v : Vec d) :
    matVecMul (1 : Mat d) v = v := by
  funext i
  simp [matVecMul, Matrix.one_apply]

private theorem applyMat_one_local (v : HilbertVec d) :
    HilbertVec.applyMat (1 : Mat d) v = v := by
  rw [HilbertVec.applyMat_apply, matVecMul_one_local,
    HilbertVec.ofVec_toVec]

private theorem applyMat_eq_add_sub_one (A : Mat d) (v : HilbertVec d) :
    HilbertVec.applyMat A v =
      v + HilbertVec.applyMat (A - (1 : Mat d)) v := by
  have hdecomp : matrixToHilbertOperator A =
      matrixToHilbertOperator (1 : Mat d) +
        matrixToHilbertOperator (A - 1) := by
    calc
      matrixToHilbertOperator A =
          matrixToHilbertOperator ((1 : Mat d) + (A - 1)) := by
        congr 1
        abel
      _ = matrixToHilbertOperator (1 : Mat d) +
          matrixToHilbertOperator (A - 1) := map_add _ _ _
  change matrixToHilbertOperator A v = _
  calc
    matrixToHilbertOperator A v =
        ((matrixToHilbertOperator (1 : Mat d) +
          matrixToHilbertOperator (A - 1)) :
            HilbertVec d →L[ℝ] HilbertVec d) v :=
      congrArg (fun T ↦ T v) hdecomp
    _ = HilbertVec.applyMat (1 : Mat d) v +
        HilbertVec.applyMat (A - 1) v := rfl
    _ = v + HilbertVec.applyMat (A - 1) v := by rw [applyMat_one_local]

/-- Operator distance from the identity controls the full operator norm. -/
theorem applyMat_opNorm_le_one_add {A : Mat d} {delta : ℝ}
    (hdelta : 0 ≤ delta)
    (hA : ‖HilbertVec.applyMat (A - (1 : Mat d))‖ ≤ delta) :
    ‖HilbertVec.applyMat A‖ ≤ 1 + delta := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) ?_
  intro v
  rw [applyMat_eq_add_sub_one]
  calc
    ‖v + HilbertVec.applyMat (A - (1 : Mat d)) v‖ ≤
        ‖v‖ + ‖HilbertVec.applyMat (A - (1 : Mat d)) v‖ := norm_add_le _ _
    _ ≤ ‖v‖ + delta * ‖v‖ := add_le_add (le_refl _)
      ((HilbertVec.applyMat (A - (1 : Mat d))).le_opNorm v |>.trans
        (mul_le_mul_of_nonneg_right hA (norm_nonneg v)))
    _ = (1 + delta) * ‖v‖ := by ring

/-- Exact identity symmetric part plus operator-distance `delta` derives an
ellipticity certificate with explicit constants; no ellipticity hypothesis is
assumed. -/
theorem isEllipticMatrix_one_sq_one_add_of_symmPart_eq_one
    {A : Mat d} {delta : ℝ} (hdelta : 0 ≤ delta)
    (hsymm : symmPart A = (1 : Mat d))
    (hA : ‖HilbertVec.applyMat (A - (1 : Mat d))‖ ≤ delta) :
    IsEllipticMatrix 1 ((1 + delta) ^ 2) A := by
  rw [isEllipticMatrix_iff_isEllipticEntryLU]
  have hone : (1 : ℝ) ≤ 1 + delta := by
    simpa only [zero_add, add_comm] using add_le_add_left hdelta 1
  refine ⟨zero_lt_one, ?_, ?_, ?_⟩
  · calc
      (1 : ℝ) = 1 ^ 2 := by norm_num
      _ ≤ (1 + delta) ^ 2 := pow_le_pow_left₀ (by norm_num) hone 2
  · intro v
    rw [one_mul, ← vecDot_matVecMul_symmPart, hsymm]
    rw [matVecMul_one_local]
    rfl
  · intro v
    have hop := applyMat_opNorm_le_one_add hdelta hA
    have hsquare : ‖HilbertVec.applyMat A‖ ^ 2 ≤ (1 + delta) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hop 2
    calc
      vecNormSq (matVecMul A v) ≤
          ‖HilbertVec.applyMat A‖ ^ 2 * vecNormSq v :=
        vecNormSq_matVecMul_le_applyMat_opNorm_sq_mul A v
      _ ≤ (1 + delta) ^ 2 * vecNormSq v :=
        mul_le_mul_of_nonneg_right hsquare (vecNormSq_nonneg v)
      _ = (1 + delta) ^ 2 * vecDot v (matVecMul A v) := by
        rw [← vecDot_matVecMul_symmPart A v, hsymm, matVecMul_one_local]
        rfl

/-- The pointwise ellipticity certificate for the normalized coefficient
frozen at `z`. -/
theorem isEllipticMatrix_normalizedFrozenCoeff
    {nu delta : ℝ} (hnu : 0 < nu) {a : CoeffField d}
    (hsymm : ∀ y, symmPart (a y) = nu • (1 : Mat d))
    {z y : Vec d} (hdelta : 0 ≤ delta)
    (hy : ‖HilbertVec.applyMat
      (normalizedFrozenCoeff nu a z y - (1 : Mat d))‖ ≤ delta) :
    IsEllipticMatrix 1 ((1 + delta) ^ 2)
      (normalizedFrozenCoeff nu a z y) :=
  isEllipticMatrix_one_sq_one_add_of_symmPart_eq_one hdelta
    (symmPart_normalizedFrozenCoeff_eq_one hnu hsymm z y) hy

/-- Continuity of the skew part makes every normalized frozen coefficient
continuous. -/
theorem continuousOn_normalizedFrozenCoeff
    {U : Set (Vec d)} {nu : ℝ} {a : CoeffField d}
    (hcont : ContinuousOn (fun y ↦ a y - nu • (1 : Mat d)) U)
    (z : Vec d) : ContinuousOn (normalizedFrozenCoeff nu a z) U := by
  have ha : ContinuousOn a U := by
    intro y hy
    have heq : a = fun x ↦ (a x - nu • (1 : Mat d)) + nu • (1 : Mat d) := by
      funext x
      abel
    rw [heq]
    exact (hcont y hy).add continuousWithinAt_const
  have hsub : ContinuousOn (fun y ↦ a y - (a z - nu • (1 : Mat d))) U :=
    ha.sub (continuousOn_const : ContinuousOn (fun _ : Vec d => a z - nu • (1 : Mat d)) U)
  have h : ContinuousOn (fun y ↦ nu⁻¹ • (a y - (a z - nu • (1 : Mat d)))) U :=
    (continuousOn_const : ContinuousOn (fun _ : Vec d => nu⁻¹) U).smul hsub
  exact h

/-- Ellipticity of the normalized frozen coefficient on a measurable subset of
the set carrying the continuity, with the explicit constants `1` and
`(1 + delta) ^ 2`. -/
theorem isEllipticFieldOn_normalizedFrozenCoeff
    {U W : Set (Vec d)} {nu delta : ℝ} {a : CoeffField d}
    (hW : MeasurableSet W) (hnu : 0 < nu)
    (hsymm : ∀ y, symmPart (a y) = nu • (1 : Mat d))
    (hcont : ContinuousOn (fun y ↦ a y - nu • (1 : Mat d)) U)
    (hWU : W ⊆ U)
    (z : Vec d) (hdelta : 0 ≤ delta)
    (hbound : ∀ y ∈ W, ‖HilbertVec.applyMat
      (normalizedFrozenCoeff nu a z y - (1 : Mat d))‖ ≤ delta) :
    IsEllipticFieldOn 1 ((1 + delta) ^ 2) W
      (normalizedFrozenCoeff nu a z) := by
  classical
  have hcoeff : ContinuousOn (normalizedFrozenCoeff nu a z) W :=
    (continuousOn_normalizedFrozenCoeff hcont z).mono hWU
  refine ⟨?_, fun y hy ↦ isEllipticMatrix_normalizedFrozenCoeff
    hnu hsymm hdelta (hbound y hy)⟩
  refine (measurable_pi_iff).2 fun i ↦ (measurable_pi_iff).2 fun j ↦ ?_
  have hij : ContinuousOn (fun x ↦ normalizedFrozenCoeff nu a z x i j) W :=
    continuousOn_pi.mp (continuousOn_pi.mp hcoeff i) j
  exact hij.measurable_piecewise continuousOn_const hW

/-- At every point of an open set, continuity of the skew part gives a ball
on which the normalized frozen coefficient is arbitrarily close to the
identity in the ruled operator norm. -/
theorem exists_ball_coefficientIdentityDistanceLE_normalizedFrozenCoeff
    {U : Set (Vec d)} {nu delta : ℝ} {a : CoeffField d}
    (hU : IsOpen U) (hnu : 0 < nu)
    (hsymm : ∀ y, symmPart (a y) = nu • (1 : Mat d))
    (hcont : ContinuousOn (fun y ↦ a y - nu • (1 : Mat d)) U)
    {z : Vec d} (hz : z ∈ U) (hdelta : 0 < delta) :
    ∃ r > 0, euclideanBall z r ⊆ U ∧
      CoefficientIdentityDistanceLE (euclideanBall z r)
        (normalizedFrozenCoeff nu a z) delta ∧
      IsEllipticFieldOn 1 ((1 + delta) ^ 2) (euclideanBall z r)
        (normalizedFrozenCoeff nu a z) := by
  have hF : ContinuousAt (normalizedSkewOperator nu a) z :=
    (continuousOn_normalizedSkewOperator hcont z hz).continuousAt
      (hU.mem_nhds hz)
  obtain ⟨s, hs, hsF⟩ := (Metric.continuousAt_iff.mp hF) delta hdelta
  obtain ⟨t, ht, htU⟩ := Metric.isOpen_iff.mp hU z hz
  have hpoint : ∀ y ∈ euclideanBall z (min s t),
      ‖HilbertVec.applyMat
        (normalizedFrozenCoeff nu a z y - (1 : Mat d))‖ ≤ delta := by
    intro y hy
    rw [normalizedFrozenCoeff_sub_one_applyMat_eq nu hnu a z y]
    have hydist : dist y z < s :=
      (HCPolySupport.euclideanBall_subset_metricBall (lt_min hs ht) hy).trans_le
        (min_le_left s t)
    simpa only [dist_eq_norm] using (hsF hydist).le
  refine ⟨min s t, lt_min hs ht, ?_, ?_, ?_⟩
  · intro y hy
    exact htU ((HCPolySupport.euclideanBall_subset_metricBall (lt_min hs ht) hy).trans_le
      (min_le_right s t))
  · filter_upwards [ae_restrict_mem (isOpen_euclideanBall z (min s t)).measurableSet]
      with y hy
    exact hpoint y hy
  · exact isEllipticFieldOn_normalizedFrozenCoeff
      (isOpen_euclideanBall z (min s t)).measurableSet hnu
      hsymm hcont (fun _ hy ↦
        htU ((HCPolySupport.euclideanBall_subset_metricBall (lt_min hs ht) hy).trans_le
          (min_le_right s t))) z hdelta.le hpoint

end

end Algsuperdiff.StochasticProcess.Common.Regularity.Freezing
