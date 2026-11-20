/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Analysis.WholePlaneH1Core

/-!
# Fourier tails of whole-plane weak `H¹` fields

This module supplies the quantitative Fourier-tail estimate used in a
Fréchet--Kolmogorov proof of local Rellich compactness.  The weak `H¹` graph
is first mapped continuously back to its order-one Bessel coefficient.  A
radial high-frequency cutoff is then applied to the inverse Bessel multiplier.

The final estimate is uniform on bounded subsets of `WholePlaneH1 F` and has
the explicit decay `(1 + R²)⁻¹/²`.  No representative-level regularity of
the weak `H¹` field is used.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory
open scoped ENNReal FourierTransform

/-! ## Recovering the Bessel coefficient from the weak graph -/

/-- The bounded derivative-recovery symbol as an `L∞` multiplier. -/
def h1RecoverDerivLInf (j : Fin 2) :
    Lp ℂ ∞ (volume : Measure WholePlane) :=
  (memLp_top_of_bound (μ := (volume : Measure WholePlane))
    (h1RecoverDeriv_hasTemperateGrowth j).1.continuous.aestronglyMeasurable
    1 (ae_of_all _ (norm_h1RecoverDeriv_le j))).toLp _

/-- The `L∞` class `h1RecoverDerivLInf j` is represented almost everywhere by the pointwise
derivative-recovery symbol `h1RecoverDeriv j`. -/
theorem h1RecoverDerivLInf_coe_ae (j : Fin 2) :
    (h1RecoverDerivLInf j : WholePlane → ℂ) =ᵐ[volume]
      h1RecoverDeriv j := by
  exact MemLp.coeFn_toLp _

/-- The mass contribution to recovery of the order-one Bessel coefficient. -/
def wholePlaneH1MassCoeffRecovery
    (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] :
    WholePlaneH1 F →L[ℂ] WholePlaneL2 F :=
  (scalarVectorMulL2 (E := F) volume h1RecoverMassLInf).comp
    ((wholePlaneFourierAnalysis F).toContinuousLinearEquiv.toContinuousLinearMap.comp
      (wholePlaneH1Embedding F))

/-- The contribution of one stored weak derivative to recovery of the
order-one Bessel coefficient. -/
def wholePlaneH1DerivCoeffRecovery
    (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] (j : Fin 2) :
    WholePlaneH1 F →L[ℂ] WholePlaneL2 F :=
  (scalarVectorMulL2 (E := F) volume (h1RecoverDerivLInf j)).comp
    ((wholePlaneFourierAnalysis F).toContinuousLinearEquiv.toContinuousLinearMap.comp
      (wholePlaneH1FirstDerivative F j))

/-- Continuous recovery of the order-one Bessel coefficient from the value
and the two weak derivatives stored in `WholePlaneH1 F`. -/
def wholePlaneH1CoeffRecovery
    (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] :
    WholePlaneH1 F →L[ℂ] WholePlaneL2 F :=
  wholePlaneH1MassCoeffRecovery F +
    wholePlaneH1DerivCoeffRecovery F 0 +
      wholePlaneH1DerivCoeffRecovery F 1

/-- Unfolding of the recovery map: the order-one Bessel coefficient of a weak `H¹` graph
element is the mass multiplier applied to the Fourier transform of the stored value, plus the
two derivative multipliers applied to the Fourier transforms of the stored weak derivatives. -/
@[simp] theorem wholePlaneH1CoeffRecovery_apply
    (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] (u : WholePlaneH1 F) :
    wholePlaneH1CoeffRecovery F u =
      scalarVectorMulL2 (E := F) volume h1RecoverMassLInf
          (wholePlaneFourierAnalysis F (wholePlaneH1Embedding F u)) +
        scalarVectorMulL2 (E := F) volume (h1RecoverDerivLInf 0)
          (wholePlaneFourierAnalysis F
            (wholePlaneH1FirstDerivative F 0 u)) +
        scalarVectorMulL2 (E := F) volume (h1RecoverDerivLInf 1)
          (wholePlaneFourierAnalysis F
            (wholePlaneH1FirstDerivative F 1 u)) := by
  rfl

/-- Pointwise multiplier identity behind recovery of the Bessel coefficient. -/
theorem h1CoeffRecovery_symbol_identity (xi : WholePlane) :
    h1RecoverMass xi * h1RecoverMass xi +
        h1RecoverDeriv 0 xi * h1CoeffDerivSymbol 0 xi +
        h1RecoverDeriv 1 xi * h1CoeffDerivSymbol 1 xi = 1 := by
  have h := h1Recover_symbol_identity xi
  simp only [Fin.sum_univ_two] at h
  calc
    h1RecoverMass xi * h1RecoverMass xi +
          h1RecoverDeriv 0 xi * h1CoeffDerivSymbol 0 xi +
          h1RecoverDeriv 1 xi * h1CoeffDerivSymbol 1 xi =
        h1RecoverMass xi *
          (h1RecoverMass xi +
            h1RecoverDeriv 0 xi *
              ((2 * Real.pi * Complex.I) * (xi 0 : ℂ)) +
            h1RecoverDeriv 1 xi *
              ((2 * Real.pi * Complex.I) * (xi 1 : ℂ))) := by
      simp only [h1CoeffDerivSymbol]
      ring
    _ = h1RecoverMass xi *
        (((1 + ‖xi‖ ^ 2) ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
      rw [add_assoc, h]
    _ = 1 := by
      have hs : ((Real.sqrt (1 + ‖xi‖ ^ 2) : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast (Real.sqrt_pos.2 (by positivity)).ne'
      rw [show (((1 + ‖xi‖ ^ 2) ^ (1 / 2 : ℝ) : ℝ) : ℂ) =
          ((Real.sqrt (1 + ‖xi‖ ^ 2) : ℝ) : ℂ) by
        norm_cast
        rw [Real.sqrt_eq_rpow]]
      simp [h1RecoverMass, hs]

/-- Recovering after synthesizing a Bessel coefficient is exactly the
identity on coefficient space. -/
theorem wholePlaneH1CoeffRecovery_h1CoeffToGraph
    (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] (c : WholePlaneL2 F) :
    wholePlaneH1CoeffRecovery F (h1CoeffToGraph F c) = c := by
  rw [wholePlaneH1CoeffRecovery_apply]
  change
    scalarVectorMulL2 (E := F) volume h1RecoverMassLInf
          (wholePlaneFourierAnalysis F (h1CoeffToValueL2 F c)) +
        scalarVectorMulL2 (E := F) volume (h1RecoverDerivLInf 0)
          (wholePlaneFourierAnalysis F (h1CoeffToDerivL2 F 0 c)) +
        scalarVectorMulL2 (E := F) volume (h1RecoverDerivLInf 1)
          (wholePlaneFourierAnalysis F (h1CoeffToDerivL2 F 1 c)) = c
  simp only [h1CoeffToValueL2_fourier, h1CoeffToDerivL2_fourier]
  let m := scalarVectorMulL2 (E := F) volume h1RecoverMassLInf c
  let q0 := scalarVectorMulL2 (E := F) volume
    (h1CoeffDerivSymbolLInf 0) c
  let q1 := scalarVectorMulL2 (E := F) volume
    (h1CoeffDerivSymbolLInf 1) c
  let a := scalarVectorMulL2 (E := F) volume h1RecoverMassLInf m
  let b := scalarVectorMulL2 (E := F) volume (h1RecoverDerivLInf 0) q0
  let d := scalarVectorMulL2 (E := F) volume (h1RecoverDerivLInf 1) q1
  change a + b + d = c
  apply Lp.ext
  filter_upwards [
    Lp.coeFn_add a b,
    Lp.coeFn_add (a + b) d,
    scalarVectorMulL2_coe_ae (E := F) volume h1RecoverMassLInf m,
    scalarVectorMulL2_coe_ae (E := F) volume h1RecoverMassLInf c,
    scalarVectorMulL2_coe_ae (E := F) volume
      (h1RecoverDerivLInf 0) q0,
    scalarVectorMulL2_coe_ae (E := F) volume
      (h1CoeffDerivSymbolLInf 0) c,
    scalarVectorMulL2_coe_ae (E := F) volume
      (h1RecoverDerivLInf 1) q1,
    scalarVectorMulL2_coe_ae (E := F) volume
      (h1CoeffDerivSymbolLInf 1) c,
    h1RecoverMassLInf_coe_ae,
    h1RecoverDerivLInf_coe_ae 0,
    h1RecoverDerivLInf_coe_ae 1,
    h1CoeffDerivSymbolLInf_coe_ae 0,
    h1CoeffDerivSymbolLInf_coe_ae 1]
    with xi hab habd ha hm hb hq0 hd hq1 hmass hr0 hr1 hs0 hs1
  rw [habd, Pi.add_apply, hab, Pi.add_apply, ha, hm, hb, hq0, hd, hq1,
    hmass, hr0, hr1, hs0, hs1]
  rw [smul_smul, smul_smul, smul_smul, ← add_smul, ← add_smul,
    h1CoeffRecovery_symbol_identity, one_smul]

/-- Bessel synthesis after coefficient recovery gives back the original weak
`H¹` graph element. -/
theorem h1CoeffToGraph_wholePlaneH1CoeffRecovery
    (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] (u : WholePlaneH1 F) :
    h1CoeffToGraph F (wholePlaneH1CoeffRecovery F u) = u := by
  obtain ⟨c, rfl⟩ := h1CoeffToGraph_surjective F u
  rw [wholePlaneH1CoeffRecovery_h1CoeffToGraph]

/-- The recovered coefficient synthesizes to the physical `L²` value of the
weak graph element. -/
theorem h1CoeffToValueL2_wholePlaneH1CoeffRecovery
    (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] (u : WholePlaneH1 F) :
    h1CoeffToValueL2 F (wholePlaneH1CoeffRecovery F u) =
      wholePlaneH1Embedding F u := by
  rw [← wholePlaneH1Embedding_h1CoeffToGraph F
    (wholePlaneH1CoeffRecovery F u),
    h1CoeffToGraph_wholePlaneH1CoeffRecovery]

/-! ## Radial high-frequency cutoff -/

/-- The inverse Bessel multiplier restricted to frequencies `R ≤ ‖xi‖`. -/
def h1HighFrequencyRecoverMass (R : ℝ) (xi : WholePlane) : ℂ :=
  if R ≤ ‖xi‖ then h1RecoverMass xi else 0

/-- The frequency-truncated inverse Bessel symbol is strongly measurable: it is the continuous
symbol `h1RecoverMass` glued to `0` across the measurable set `{ξ | R ≤ ‖ξ‖}`. -/
theorem h1HighFrequencyRecoverMass_stronglyMeasurable (R : ℝ) :
    StronglyMeasurable (h1HighFrequencyRecoverMass R) := by
  unfold h1HighFrequencyRecoverMass
  exact StronglyMeasurable.piecewise
    (measurableSet_le measurable_const continuous_norm.measurable)
    (h1RecoverMass_hasTemperateGrowth.1.continuous.stronglyMeasurable)
    stronglyMeasurable_const

/-- The frequency-truncated inverse Bessel symbol is bounded by one at every frequency. -/
theorem norm_h1HighFrequencyRecoverMass_le_one
    (R : ℝ) (xi : WholePlane) :
    ‖h1HighFrequencyRecoverMass R xi‖ ≤ 1 := by
  by_cases hxi : R ≤ ‖xi‖
  · simpa [h1HighFrequencyRecoverMass, hxi] using
      norm_h1RecoverMass_le xi
  · simp [h1HighFrequencyRecoverMass, hxi]

/-- The explicit high-frequency decay factor. -/
def h1HighFrequencyDecay (R : ℝ) : ℝ :=
  (Real.sqrt (1 + R ^ 2))⁻¹

/-- The decay factor `(1 + R²)^(-1/2)` is nonnegative. -/
theorem h1HighFrequencyDecay_nonneg (R : ℝ) :
    0 ≤ h1HighFrequencyDecay R := by
  unfold h1HighFrequencyDecay
  positivity

/-- For `R ≥ 0` the truncated inverse Bessel symbol is bounded everywhere by
`h1HighFrequencyDecay R = (1 + R²)^(-1/2)`: on `{R ≤ ‖ξ‖}` this is monotonicity of
`t ↦ (1 + t²)^(-1/2)`, and off that set the symbol vanishes. -/
theorem norm_h1HighFrequencyRecoverMass_le_decay
    {R : ℝ} (hR : 0 ≤ R) (xi : WholePlane) :
    ‖h1HighFrequencyRecoverMass R xi‖ ≤ h1HighFrequencyDecay R := by
  by_cases hxi : R ≤ ‖xi‖
  · rw [h1HighFrequencyRecoverMass, ite_eq_left hxi,
      h1RecoverMass, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
    unfold h1HighFrequencyDecay
    have hsq : R ^ 2 ≤ ‖xi‖ ^ 2 :=
      (sq_le_sq₀ hR (norm_nonneg xi)).2 hxi
    have hsqrt : Real.sqrt (1 + R ^ 2) ≤
        Real.sqrt (1 + ‖xi‖ ^ 2) := by
      apply Real.sqrt_le_sqrt
      linarith
    have hxiSqrt : 0 < Real.sqrt (1 + ‖xi‖ ^ 2) := by
      positivity
    have hRSqrt : 0 < Real.sqrt (1 + R ^ 2) := by
      positivity
    exact (inv_le_inv₀ hxiSqrt hRSqrt).2 hsqrt
  · rw [h1HighFrequencyRecoverMass, ite_eq_right hxi, norm_zero]
    exact h1HighFrequencyDecay_nonneg R

/-- The high-frequency inverse Bessel symbol as a quotient-level `L∞`
multiplier. -/
def h1HighFrequencyRecoverMassLInf (R : ℝ) :
    Lp ℂ ∞ (volume : Measure WholePlane) :=
  (memLp_top_of_bound (μ := (volume : Measure WholePlane))
    (h1HighFrequencyRecoverMass_stronglyMeasurable R).aestronglyMeasurable
    1 (ae_of_all _ (norm_h1HighFrequencyRecoverMass_le_one R))).toLp _

/-- The `L∞` class of the high-frequency multiplier is represented almost everywhere by the
truncated symbol `h1HighFrequencyRecoverMass R`. -/
theorem h1HighFrequencyRecoverMassLInf_coe_ae (R : ℝ) :
    (h1HighFrequencyRecoverMassLInf R : WholePlane → ℂ) =ᵐ[volume]
      h1HighFrequencyRecoverMass R := by
  exact MemLp.coeFn_toLp _

/-- For `R ≥ 0` the `L∞` norm of the high-frequency multiplier is at most
`h1HighFrequencyDecay R = (1 + R²)^(-1/2)`; this is where the tail decay enters. -/
theorem norm_h1HighFrequencyRecoverMassLInf_le_decay
    {R : ℝ} (hR : 0 ≤ R) :
    ‖h1HighFrequencyRecoverMassLInf R‖ ≤ h1HighFrequencyDecay R := by
  unfold h1HighFrequencyRecoverMassLInf
  rw [Lp.norm_toLp, eLpNorm_exponent_top
    (h1HighFrequencyRecoverMass_stronglyMeasurable R).aestronglyMeasurable]
  have htop : eLpNormEssSup (h1HighFrequencyRecoverMass R) volume ≤
      ENNReal.ofReal (h1HighFrequencyDecay R) :=
    eLpNormEssSup_le_of_ae_bound
      (ae_of_all _ (norm_h1HighFrequencyRecoverMass_le_decay hR))
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top htop).trans_eq
    (ENNReal.toReal_ofReal (h1HighFrequencyDecay_nonneg R))

/-! ## The physical high-frequency tail -/

/-- High-frequency physical `L²` tail obtained from an order-one Bessel
coefficient. -/
def wholePlaneH1HighFrequencyTailFromCoeff
    (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] (R : ℝ) :
    WholePlaneL2 F →L[ℂ] WholePlaneL2 F :=
  (wholePlaneFourierSynthesis F).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (scalarVectorMulL2 (E := F) volume
      (h1HighFrequencyRecoverMassLInf R))

/-- The high-frequency part of the physical embedding of a weak `H¹` field. -/
def wholePlaneH1HighFrequencyTail
    (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] (R : ℝ) :
    WholePlaneH1 F →L[ℂ] WholePlaneL2 F :=
  (wholePlaneH1HighFrequencyTailFromCoeff F R).comp
    (wholePlaneH1CoeffRecovery F)

/-- Fourier transform of the high-frequency tail: it is the truncated inverse Bessel multiplier
applied to the recovered order-one Bessel coefficient of the weak `H¹` field. -/
theorem wholePlaneH1HighFrequencyTail_fourier
    (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] (R : ℝ) (u : WholePlaneH1 F) :
    wholePlaneFourierAnalysis F (wholePlaneH1HighFrequencyTail F R u) =
      scalarVectorMulL2 (E := F) volume
        (h1HighFrequencyRecoverMassLInf R)
        (wholePlaneH1CoeffRecovery F u) := by
  exact wholePlaneFourierAnalysis_synthesis F _

/-- Fourier synthesis on `WholePlaneL2 F` preserves norms (Plancherel). -/
theorem norm_wholePlaneFourierSynthesis
    (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] (f : WholePlaneL2 F) :
    ‖wholePlaneFourierSynthesis F f‖ = ‖f‖ :=
  (wholePlaneFourierSynthesis F).norm_map f

/-- Uniform Fourier-tail estimate on the weak `H¹` graph.  Since the norm of
the fixed recovery map is finite and `h1HighFrequencyDecay R → 0`, this is
the quantitative high-frequency input for local Rellich compactness. -/
theorem norm_wholePlaneH1HighFrequencyTail_le
    (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] {R : ℝ} (hR : 0 ≤ R) (u : WholePlaneH1 F) :
    ‖wholePlaneH1HighFrequencyTail F R u‖ ≤
      h1HighFrequencyDecay R * ‖wholePlaneH1CoeffRecovery F‖ * ‖u‖ := by
  change ‖wholePlaneFourierSynthesis F
      (scalarVectorMulL2 (E := F) volume
        (h1HighFrequencyRecoverMassLInf R)
        (wholePlaneH1CoeffRecovery F u))‖ ≤ _
  rw [norm_wholePlaneFourierSynthesis]
  calc
    ‖scalarVectorMulL2 (E := F) volume
        (h1HighFrequencyRecoverMassLInf R)
        (wholePlaneH1CoeffRecovery F u)‖ ≤
        ‖h1HighFrequencyRecoverMassLInf R‖ *
          ‖wholePlaneH1CoeffRecovery F u‖ :=
      norm_scalarVectorMulL2_apply_le volume _ _
    _ ≤ h1HighFrequencyDecay R *
        ‖wholePlaneH1CoeffRecovery F u‖ :=
      mul_le_mul_of_nonneg_right
        (norm_h1HighFrequencyRecoverMassLInf_le_decay hR) (norm_nonneg _)
    _ ≤ h1HighFrequencyDecay R *
        (‖wholePlaneH1CoeffRecovery F‖ * ‖u‖) :=
      mul_le_mul_of_nonneg_left
        ((wholePlaneH1CoeffRecovery F).le_opNorm u)
        (h1HighFrequencyDecay_nonneg R)
    _ = h1HighFrequencyDecay R *
        ‖wholePlaneH1CoeffRecovery F‖ * ‖u‖ := by ring

/-- Operator-norm form of the uniform Fourier-tail estimate.  This is the
form directly consumed by norm-limit arguments for compact operators. -/
theorem norm_wholePlaneH1HighFrequencyTail_operator_le
    (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] {R : ℝ} (hR : 0 ≤ R) :
    ‖wholePlaneH1HighFrequencyTail F R‖ ≤
      h1HighFrequencyDecay R * ‖wholePlaneH1CoeffRecovery F‖ := by
  refine ContinuousLinearMap.opNorm_le_bound
    (wholePlaneH1HighFrequencyTail F R)
    (M := h1HighFrequencyDecay R * ‖wholePlaneH1CoeffRecovery F‖)
    (mul_nonneg (h1HighFrequencyDecay_nonneg R)
      (norm_nonneg (wholePlaneH1CoeffRecovery F))) ?_
  intro u
  simpa [mul_assoc] using norm_wholePlaneH1HighFrequencyTail_le F hR u

end

end FastDynamo
