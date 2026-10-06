/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedEnergyIntervalConj
public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegularisedMildEnergy

/-!
# Real-valuedness of the Fourier solution of the mild equation

The heat, Leray and Stokes symbols commute with the reflected conjugation
`ĝ ↦ conj ĝ(-·)`, and so does the frequency-side right-hand side of the mild
equation `eq:reg-mild-forced` whenever its data are Fourier transforms of real
fields. Consequently the complex solution curve is the complexification of its
real part, and the inverse transform of its frequency gradient is real. These
are the facts behind the exact energy equality of `thm:regularised`.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal FourierTransform ComplexConjugate

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

theorem complexVecConj_complexifyValue (y : L2Vec3) :
    complexVecConj (complexifyValue y) = complexifyValue y := by
  change complexVecConj (complexifyFrequency y) = complexifyFrequency y
  apply PiLp.ext
  intro i
  simp [complexVecConj_apply, complexifyFrequency]

theorem complexTensorConj_complexifyTensorValue (y : RealTensor3) :
    complexTensorConj (complexifyTensorValue y) = complexifyTensorValue y := by
  change complexTensorConj (WithLp.toLp 2 fun i => complexifyValue (y i)) =
    WithLp.toLp 2 fun i => complexifyValue (y i)
  apply PiLp.ext
  intro i
  simp only [complexTensorConj_apply, complexVecConj_complexifyValue]

theorem conjLp_complexifyVectorL2 (x : RealVectorL2) :
    conjLp complexVecConj (complexifyVectorL2 x) = complexifyVectorL2 x := by
  apply Lp.ext
  filter_upwards [conjLp_ae complexVecConj (complexifyVectorL2 x),
    complexifyValue.coeFn_compLpL (p := 2) (μ := volume) x] with ξ h1 h2
  change (conjLp complexVecConj (complexifyVectorL2 x) : L2Vec3 → ComplexVec3) ξ =
    (complexifyValue.compLpL 2 volume x : L2Vec3 → ComplexVec3) ξ
  rw [h1]
  change complexVecConj ((complexifyValue.compLpL 2 volume x : L2Vec3 → ComplexVec3) ξ) = _
  rw [h2, complexVecConj_complexifyValue]

theorem conjLp_complexifyTensorL2 (x : RealTensorL2) :
    conjLp complexTensorConj (complexifyTensorL2 x) = complexifyTensorL2 x := by
  apply Lp.ext
  filter_upwards [conjLp_ae complexTensorConj (complexifyTensorL2 x),
    complexifyTensorValue.coeFn_compLpL (p := 2) (μ := volume) x] with ξ h1 h2
  change (conjLp complexTensorConj (complexifyTensorL2 x) : L2Vec3 → ComplexTensor3) ξ =
    (complexifyTensorValue.compLpL 2 volume x : L2Vec3 → ComplexTensor3) ξ
  rw [h1]
  change complexTensorConj
    ((complexifyTensorValue.compLpL 2 volume x : L2Vec3 → ComplexTensor3) ξ) = _
  rw [h2, complexTensorConj_complexifyTensorValue]

/-- The Fourier transform of a real vector field is invariant under the
reflected conjugation. -/
theorem conjReflectLp_fourier_complexifyVectorL2 (x : RealVectorL2) :
    conjReflectLp complexVecConj
        (Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3 (complexifyVectorL2 x)) =
      Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3 (complexifyVectorL2 x) := by
  rw [← fourierTransform_conjLp complexVecConj complexVecConj_smul,
    conjLp_complexifyVectorL2]

/-- The Fourier transform of a real tensor field is invariant under the
reflected conjugation. -/
theorem conjReflectLp_fourier_complexifyTensorL2 (x : RealTensorL2) :
    conjReflectLp complexTensorConj
        (Lp.fourierTransformₗᵢ L2Vec3 ComplexTensor3 (complexifyTensorL2 x)) =
      Lp.fourierTransformₗᵢ L2Vec3 ComplexTensor3 (complexifyTensorL2 x) := by
  rw [← fourierTransform_conjLp complexTensorConj complexTensorConj_smul,
    conjLp_complexifyTensorL2]

/-- The heat multiplier commutes with the reflected conjugation. -/
theorem conjReflectLp_heatMultiplier_smul (t : ℝ) (ht : 0 ≤ t) (g : ComplexVectorL2) :
    conjReflectLp complexVecConj (heatMultiplier t ht • g) =
      heatMultiplier t ht • conjReflectLp complexVecConj g := by
  have hneg := Measure.measurePreserving_neg (volume : Measure L2Vec3)
  apply Lp.ext
  filter_upwards [conjReflectLp_ae complexVecConj (heatMultiplier t ht • g),
    hneg.quasiMeasurePreserving.ae (heatMultiplier_smul_ae_eq t ht g),
    heatMultiplier_smul_ae_eq t ht (conjReflectLp complexVecConj g),
    conjReflectLp_ae complexVecConj g] with ξ h1 h2 h3 h4
  rw [h1, h2, h3, h4, complexVecConj_smul]
  congr 1
  simp only [heatSymbol, norm_neg, Complex.conj_ofReal]

/-- A measurable Fourier multiplier whose symbol is symmetric under the
reflected conjugation commutes with it. -/
theorem conjReflectLp_measurableFourierMultiplier
    {F G : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [MeasurableSpace F] [BorelSpace F]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
    (σF : F ≃ₗᵢ[ℝ] F) (σG : G ≃ₗᵢ[ℝ] G)
    (m : L2Vec3 × F → G) (hm : Measurable m) (C : ℝ)
    (hbound : ∀ ξ x, ‖m (ξ, x)‖ ≤ C * ‖x‖)
    (hsym : ∀ ξ x, σG (m (-ξ, x)) = m (ξ, σF x))
    (f : Lp (α := L2Vec3) F 2) :
    conjReflectLp σG (measurableFourierMultiplier m hm C hbound f) =
      measurableFourierMultiplier m hm C hbound (conjReflectLp σF f) := by
  have hneg := Measure.measurePreserving_neg (volume : Measure L2Vec3)
  apply Lp.ext
  filter_upwards [conjReflectLp_ae σG (measurableFourierMultiplier m hm C hbound f),
    hneg.quasiMeasurePreserving.ae (measurableFourierMultiplier_ae_eq m hm C hbound f),
    measurableFourierMultiplier_ae_eq m hm C hbound (conjReflectLp σF f),
    conjReflectLp_ae σF f] with ξ h1 h2 h3 h4
  rw [h1, h2, h3, h4, hsym]

theorem tensorDivergenceLinear_neg_freq (ξ : L2Vec3) (T : ComplexTensor3) :
    tensorDivergenceLinear (-ξ) T = -tensorDivergenceLinear ξ T := by
  simp [tensorDivergenceLinear_apply, Finset.sum_neg_distrib]

theorem complexVecConj_tensorDivergenceLinear (ξ : L2Vec3) (T : ComplexTensor3) :
    complexVecConj (tensorDivergenceLinear ξ T) =
      tensorDivergenceLinear ξ (complexTensorConj T) := by
  simp only [tensorDivergenceLinear_apply, map_sum, complexVecConj_smul, Complex.conj_ofReal,
    complexTensorConj_apply]

theorem lerayApplyFormula_neg_freq (ξ : L2Vec3) (z : ComplexVec3) :
    lerayApplyFormula (-ξ) z = lerayApplyFormula ξ z := by
  have h1 : complexifyFrequency (-ξ) = -complexifyFrequency ξ := by
    apply PiLp.ext
    intro i
    simp [complexifyFrequency]
  have h2 : inverseFrequencyNormSq (-ξ) = inverseFrequencyNormSq ξ := by
    simp [inverseFrequencyNormSq, norm_neg]
  simp only [lerayApplyFormula, h1, h2, inner_neg_left, mul_neg, neg_smul, smul_neg, neg_neg]

theorem complexVecConj_lerayApplyFormula (ξ : L2Vec3) (z : ComplexVec3) :
    complexVecConj (lerayApplyFormula ξ z) = lerayApplyFormula ξ (complexVecConj z) := by
  have ha : complexVecConj (complexifyFrequency ξ) = complexifyFrequency ξ :=
    complexVecConj_complexifyValue ξ
  have hin : conj (inner ℂ (complexifyFrequency ξ) z) =
      inner ℂ (complexifyFrequency ξ) (complexVecConj z) := by
    simp [PiLp.inner_apply, complexifyFrequency, complexVecConj_apply, map_sum]
  simp only [lerayApplyFormula, map_sub, complexVecConj_smul, ha, map_mul, Complex.conj_ofReal,
    hin]

theorem lerayApplyFormula_neg (ξ : L2Vec3) (z : ComplexVec3) :
    lerayApplyFormula ξ (-z) = -lerayApplyFormula ξ z := by
  rw [← leraySymbol_apply_eq_formula, map_neg, leraySymbol_apply_eq_formula]

theorem complexVecConj_stokesApplyFormula (t : ℝ) (ξ : L2Vec3) (T : ComplexTensor3) :
    complexVecConj (stokesApplyFormula t (-ξ) T) =
      stokesApplyFormula t ξ (complexTensorConj T) := by
  have hh : heatSymbol t (-ξ) = heatSymbol t ξ := by
    simp [heatSymbol]
  have hc0 : conj (heatSymbol t ξ) = heatSymbol t ξ := Complex.conj_ofReal _
  have hc : conj (heatSymbol t ξ * (2 * Real.pi * Complex.I)) =
      -(heatSymbol t ξ * (2 * Real.pi * Complex.I)) := by
    rw [map_mul, hc0, map_mul, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
    ring
  simp only [stokesApplyFormula, hh, complexVecConj_smul, hc, lerayApplyFormula_neg_freq,
    tensorDivergenceLinear_neg_freq, lerayApplyFormula_neg, map_neg,
    complexVecConj_lerayApplyFormula, complexVecConj_tensorDivergenceLinear, neg_smul,
    smul_neg, neg_neg]

/-- The Stokes multiplier commutes with the reflected conjugation. -/
theorem conjReflectLp_stokesFourierMultiplier {t : ℝ} (ht : 0 < t) (g : ComplexTensorL2) :
    conjReflectLp complexVecConj (stokesFourierMultiplier ht g) =
      stokesFourierMultiplier ht (conjReflectLp complexTensorConj g) := by
  unfold stokesFourierMultiplier
  exact conjReflectLp_measurableFourierMultiplier complexTensorConj complexVecConj _ _ _ _
    (fun ξ T => complexVecConj_stokesApplyFormula t ξ T) g

/-- The Leray multiplier commutes with the reflected conjugation. -/
theorem conjReflectLp_lerayFourierMultiplier (g : ComplexVectorL2) :
    conjReflectLp complexVecConj (lerayFourierMultiplier g) =
      lerayFourierMultiplier (conjReflectLp complexVecConj g) := by
  unfold lerayFourierMultiplier
  exact conjReflectLp_measurableFourierMultiplier complexVecConj complexVecConj _ _ _ _
    (fun ξ z => by rw [lerayApplyFormula_neg_freq, complexVecConj_lerayApplyFormula]) g

/-- The frequency-side right-hand side of `eq:reg-mild-forced` is invariant
under the reflected conjugation when its data are. -/
theorem conjReflectLp_forcedFourierMild (b : ComplexVectorL2)
    (hb : conjReflectLp complexVecConj b = b) (F : ℝ → ComplexTensorL2)
    (hF : ∀ s, conjReflectLp complexTensorConj (F s) = F s) (H : ℝ → ComplexVectorL2)
    (hH : ∀ s, conjReflectLp complexVecConj (H s) = H s) (t : ℝ) (ht : 0 ≤ t) :
    conjReflectLp complexVecConj (forcedFourierMild b F H t ht) =
      forcedFourierMild b F H t ht := by
  unfold forcedFourierMild
  rw [map_add, conjReflectLp_heatMultiplier_smul, hb]
  congr 1
  rw [← conjReflectEquiv_apply complexVecConj complexVecConj_involutive,
    ← ContinuousLinearEquiv.integral_comp_comm]
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  simp only [conjReflectEquiv_apply, map_add, map_neg]
  congr 2
  · unfold forcedFourierStokesIntegrand
    split_ifs with hs
    · rw [conjReflectLp_stokesFourierMultiplier, hF]
    · exact map_zero _
  · unfold forcedFourierForceIntegrand
    split_ifs with hs
    · rw [conjReflectLp_heatMultiplier_smul, conjReflectLp_lerayFourierMultiplier, hH]
    · exact map_zero _

/-- The complex solution curve of the forced mild equation is invariant under
coordinatewise conjugation. -/
theorem conjLp_forcedComplexCurve (b : RealVectorL2) (F : ℝ → RealTensorL2)
    (h : ℝ → RealVectorL2) (s : ℝ) :
    conjLp complexVecConj (forcedComplexCurve b F h s) = forcedComplexCurve b F h s := by
  unfold forcedComplexCurve
  split_ifs with hs
  · rw [conjLp_fourierTransform_symm complexVecConj complexVecConj_smul,
      conjReflectLp_forcedFourierMild _ (conjReflectLp_fourier_complexifyVectorL2 b)
        (forcedFourierTensorCurve F) (fun r => conjReflectLp_fourier_complexifyTensorL2 (F r))
        (forcedFourierForceCurve h) (fun r => conjReflectLp_fourier_complexifyVectorL2 (h r))]
  · exact map_zero _

/-- A complex field fixed by coordinatewise conjugation is the
complexification of its real part. -/
theorem complexifyVectorL2_realPartVectorL2_of_conj (w : ComplexVectorL2)
    (hw : conjLp complexVecConj w = w) :
    complexifyVectorL2 (realPartVectorL2 w) = w := by
  have hae := conjLp_ae complexVecConj w
  rw [hw] at hae
  apply Lp.ext
  filter_upwards [complexifyValue.coeFn_compLpL (p := 2) (μ := volume) (realPartVectorL2 w),
    realPartValue.coeFn_compLpL (p := 2) (μ := volume) w, hae] with ξ h1 h2 h3
  change (complexifyValue.compLpL 2 volume (realPartVectorL2 w) : L2Vec3 → ComplexVec3) ξ = _
  rw [h1]
  change complexifyValue ((realPartValue.compLpL 2 volume w : L2Vec3 → L2Vec3) ξ) = _
  rw [h2]
  change complexifyFrequency (WithLp.toLp 2 fun i => ((w : L2Vec3 → ComplexVec3) ξ i).re) = _
  apply PiLp.ext
  intro i
  have hi := congrArg (fun z : ComplexVec3 => z i) h3
  simp only [complexVecConj_apply] at hi
  simp only [complexifyFrequency, PiLp.toLp_apply]
  exact Complex.conj_eq_iff_re.mp hi.symm

/-- The complex solution curve of the forced mild equation is the
complexification of its real part. -/
theorem forcedComplexCurve_eq_complexify (b : RealVectorL2) (F : ℝ → RealTensorL2)
    (h : ℝ → RealVectorL2) (s : ℝ) :
    forcedComplexCurve b F h s =
      complexifyVectorL2 (realPartVectorL2 (forcedComplexCurve b F h s)) :=
  (complexifyVectorL2_realPartVectorL2_of_conj _ (conjLp_forcedComplexCurve b F h s)).symm

/-- The inverse transform of the frequency gradient of a field with
conjugation-symmetric transform is fixed by coordinatewise conjugation. -/
theorem conjLp_forcedFourierGrad (v : ComplexVectorL2)
    (hv : MemLp (forcedFourierGradHat v) 2 volume)
    (hreal : conjReflectLp complexVecConj (Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3 v) =
      Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3 v) :
    conjLp complexTensorConj (forcedFourierGrad v hv) = forcedFourierGrad v hv := by
  have hneg := Measure.measurePreserving_neg (volume : Measure L2Vec3)
  have hW := conjReflectLp_ae complexVecConj (Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3 v)
  rw [hreal] at hW
  unfold forcedFourierGrad
  rw [conjLp_fourierTransform_symm complexTensorConj complexTensorConj_smul]
  congr 1
  apply Lp.ext
  filter_upwards [conjReflectLp_ae complexTensorConj (hv.toLp (forcedFourierGradHat v)),
    hneg.quasiMeasurePreserving.ae hv.coeFn_toLp, hv.coeFn_toLp, hW] with ξ h1 h2 h3 h4
  rw [h1, h2, h3]
  apply PiLp.ext
  intro i
  simp only [forcedFourierGradHat, complexTensorConj_apply, PiLp.toLp_apply,
    complexVecConj_smul]
  rw [← h4]
  congr 1
  simp only [PiLp.neg_apply, Complex.ofReal_neg, map_mul, map_neg, Complex.conj_ofReal,
    Complex.conj_I, map_ofNat]
  ring

end CKN.Leray

end
