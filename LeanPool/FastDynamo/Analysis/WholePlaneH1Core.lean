/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Analysis.WholePlaneH2
public import LeanPool.FastDynamo.Analysis.Holder
public import LeanPool.FastDynamo.Analysis.WholePlaneSobolev

/-!
# Bessel realization and Schwartz core for weak whole-plane H¹

This module identifies the direct weak-derivative graph model
`WholePlaneH1` with the order-one Bessel-potential realization.  The
identification is proved in the direction needed for density: bounded
Fourier multipliers recover the Bessel coefficient from a weak graph jet,
and every Bessel coefficient continuously synthesizes a weak graph jet.

The final results show that the coefficient-to-graph map is surjective and
that Schwartz coefficients synthesize Schwartz physical fields
whose `L²` value and first derivatives are exactly the corresponding graph
components.  No smoothness or density assertion is assumed in the graph
definition.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory
open scoped ENNReal FourierTransform LineDeriv SchwartzMap Real

/-- Bounded inverse order-one Bessel weight used to recover the physical
field from its weighted Fourier coefficient. -/
def h1RecoverMass (xi : WholePlane) : ℂ :=
  ((Real.sqrt (1 + ‖xi‖ ^ 2))⁻¹ : ℝ)

/-- Bounded multiplier recovering one weak derivative from the physical
field and its stored first derivatives. -/
def h1RecoverDeriv (j : Fin 2) (xi : WholePlane) : ℂ :=
  (-(Complex.I / (2 * Real.pi : ℝ))) * (xi j : ℂ) * h1RecoverMass xi

/-- The inverse Bessel weight `⟨ξ⟩⁻¹` has temperate growth, so it acts on tempered
distributions as a Fourier multiplier. -/
theorem h1RecoverMass_hasTemperateGrowth :
    h1RecoverMass.HasTemperateGrowth := by
  rw [show h1RecoverMass = fun xi : WholePlane =>
      (((1 + ‖xi‖ ^ 2) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) by
    funext xi
    unfold h1RecoverMass
    norm_cast
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (by positivity)]]
  exact (Complex.ofRealCLM.hasTemperateGrowth).comp
    (Function.hasTemperateGrowth_one_add_norm_sq_rpow
      WholePlane (-(1 / 2 : ℝ)))

/-- The `j`th derivative-recovery symbol `-(i/2π) ξ_j ⟨ξ⟩⁻¹` has temperate growth. -/
theorem h1RecoverDeriv_hasTemperateGrowth (j : Fin 2) :
    (h1RecoverDeriv j).HasTemperateGrowth := by
  unfold h1RecoverDeriv
  have hcoord : Function.HasTemperateGrowth
      (fun xi : WholePlane => (xi j : ℂ)) := by
    let pj : WholePlane →L[ℝ] ℝ := EuclideanSpace.proj j
    have hpj : Function.HasTemperateGrowth pj := pj.hasTemperateGrowth
    have hcoe := (Complex.ofRealCLM.hasTemperateGrowth).comp hpj
    convert hcoe using 1
    funext xi
    simp [pj]
  exact ((Function.HasTemperateGrowth.const _).mul hcoord).mul
    h1RecoverMass_hasTemperateGrowth

/-- The inverse Bessel weight is bounded by one, since `1 ≤ ⟨ξ⟩`. -/
theorem norm_h1RecoverMass_le (xi : WholePlane) :
    ‖h1RecoverMass xi‖ ≤ 1 := by
  rw [h1RecoverMass, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  exact (inv_le_one₀ (by positivity)).mpr
    ((Real.one_le_sqrt).2 (by nlinarith [sq_nonneg ‖xi‖]))

/-- Each derivative-recovery symbol is bounded by one, using `|ξ_j| ≤ ⟨ξ⟩` and `2π ≥ 1`. -/
theorem norm_h1RecoverDeriv_le (j : Fin 2) (xi : WholePlane) :
    ‖h1RecoverDeriv j xi‖ ≤ 1 := by
  unfold h1RecoverDeriv h1RecoverMass
  rw [norm_mul, norm_mul, norm_neg, Complex.norm_div,
    Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  have hmass :
      ‖(((Real.sqrt (1 + ‖xi‖ ^ 2))⁻¹ : ℝ) : ℂ)‖ =
        (Real.sqrt (1 + ‖xi‖ ^ 2))⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  rw [hmass]
  have hcoord : |xi j| ≤ ‖xi‖ := by
    have h := abs_real_inner_le_norm xi (wholePlaneBasis j)
    rw [inner_wholePlaneBasis] at h
    simpa [wholePlaneBasis] using h
  have hsqrt_pos : 0 < Real.sqrt (1 + ‖xi‖ ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hsqrt_sq : Real.sqrt (1 + ‖xi‖ ^ 2) ^ 2 = 1 + ‖xi‖ ^ 2 := by
    rw [Real.sq_sqrt (by positivity)]
  have hnorm_sqrt : ‖xi‖ ≤ Real.sqrt (1 + ‖xi‖ ^ 2) := by
    nlinarith [sq_nonneg (‖xi‖ - Real.sqrt (1 + ‖xi‖ ^ 2))]
  have hratio : |xi j| * (Real.sqrt (1 + ‖xi‖ ^ 2))⁻¹ ≤ 1 := by
    rw [mul_inv_le_iff₀ hsqrt_pos]
    simpa only [one_mul] using hcoord.trans hnorm_sqrt
  have hratioC : ‖(xi j : ℂ)‖ *
      (Real.sqrt (1 + ‖xi‖ ^ 2))⁻¹ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hratio
  have hpi : 1 / (2 * Real.pi) ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith [Real.two_le_pi]
  calc
    (1 / (2 * Real.pi)) * ‖(xi j : ℂ)‖ *
          (Real.sqrt (1 + ‖xi‖ ^ 2))⁻¹ =
        (1 / (2 * Real.pi)) *
          (‖(xi j : ℂ)‖ * (Real.sqrt (1 + ‖xi‖ ^ 2))⁻¹) := by ring
    _ ≤ 1 * 1 := mul_le_mul hpi hratioC (by positivity) (by positivity)
    _ = 1 := one_mul 1

-- First test the exact scalar identity pointwise.
/-- Pointwise symbol identity behind the Bessel realization: the mass symbol plus the two
derivative symbols against the derivative multipliers `2π i ξ_j` reconstruct the order-one
Bessel weight `⟨ξ⟩`. -/
theorem h1Recover_symbol_identity (xi : WholePlane) :
    h1RecoverMass xi +
        ∑ j : Fin 2,
          h1RecoverDeriv j xi *
            ((2 * Real.pi * Complex.I) * (xi j : ℂ)) =
      ((1 + ‖xi‖ ^ 2) ^ (1 / 2 : ℝ) : ℝ) := by
  rw [Fin.sum_univ_two]
  simp only [h1RecoverDeriv, h1RecoverMass]
  have hpos : 0 < 1 + ‖xi‖ ^ 2 := by positivity
  have hsqrt_pos : 0 < Real.sqrt (1 + ‖xi‖ ^ 2) := Real.sqrt_pos.2 hpos
  have hsqrt_sq : Real.sqrt (1 + ‖xi‖ ^ 2) ^ 2 = 1 + ‖xi‖ ^ 2 := by
    rw [Real.sq_sqrt hpos.le]
  have hnorm : ‖xi‖ ^ 2 = xi 0 ^ 2 + xi 1 ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [Fin.sum_univ_two]
  rw [← Real.sqrt_eq_rpow]
  push_cast
  ring_nf
  simp only [Complex.I_sq]
  norm_cast
  field_simp [ne_of_gt hsqrt_pos]
  norm_num at *
  nlinarith

/-- Distributional form of the previous identity: the order-one Bessel potential of `T` is
the bounded multiplier `h1RecoverMass` applied to `T` plus the bounded multipliers
`h1RecoverDeriv j` applied to its distributional derivatives. -/
theorem h1Recover_distribution_identity
    (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (T : TemperedDistribution WholePlane F) :
    TemperedDistribution.besselPotential WholePlane F 1 T =
      TemperedDistribution.fourierMultiplierCLM F h1RecoverMass T +
        ∑ j : Fin 2,
          TemperedDistribution.fourierMultiplierCLM F (h1RecoverDeriv j)
            (∂_{wholePlaneBasis j} T) := by
  unfold TemperedDistribution.besselPotential
  apply (FourierTransform.fourierCLE ℂ
    (TemperedDistribution WholePlane F)).injective
  simp only [TemperedDistribution.fourierMultiplierCLM_apply,
    FourierTransform.fourierCLE_apply,
    FourierTransform.fourier_fourierInv_eq, map_add, map_sum,
    TemperedDistribution.fourier_lineDerivOp_eq,
    map_smul]
  ext phi
  simp only [TemperedDistribution.smulLeftCLM_apply_apply,
    add_apply, _root_.sum_apply, smul_apply]
  simp_rw [← map_smul]
  rw [← map_sum, ← map_add]
  congr 1
  ext xi
  simp only [add_apply, _root_.sum_apply]
  have hweight : Function.HasTemperateGrowth
      (fun x : WholePlane =>
        (((1 + ‖x‖ ^ 2) ^ (1 / 2 : ℝ) : ℝ) : ℂ)) := by
    exact (Complex.ofRealCLM.hasTemperateGrowth).comp
      (Function.hasTemperateGrowth_one_add_norm_sq_rpow
        WholePlane (1 / 2 : ℝ))
  have hcoord (j : Fin 2) : Function.HasTemperateGrowth
      (fun x : WholePlane => ((inner ℝ x (wholePlaneBasis j) : ℝ) : ℂ)) := by
    fun_prop
  rw [SchwartzMap.smulLeftCLM_apply_apply hweight]
  rw [SchwartzMap.smulLeftCLM_apply_apply h1RecoverMass_hasTemperateGrowth]
  simp_rw [SchwartzMap.smulLeftCLM_apply_apply (hcoord _)]
  simp_rw [SchwartzMap.smulLeftCLM_apply_apply
    (h1RecoverDeriv_hasTemperateGrowth _)]
  simp_rw [inner_wholePlaneBasis]
  simp only [smul_eq_mul]
  rw [← h1Recover_symbol_identity]
  simp only [Fin.sum_univ_two, smul_apply, smul_eq_mul]
  ring

/-- A weak `H¹` graph element represents a tempered distribution of Bessel-potential
Sobolev order one, since the previous identity writes its order-one Bessel potential as a
sum of bounded multipliers applied to `L²` data. -/
theorem wholePlaneH1_memSobolev_one
    (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] (u : WholePlaneH1 F) :
    TemperedDistribution.MemSobolev 1 2
      (wholePlaneL2ToTempered F (wholePlaneH1Embedding F u)) := by
  let T := wholePlaneL2ToTempered F (wholePlaneH1Embedding F u)
  have hL2 (f : WholePlaneL2 F) :
      TemperedDistribution.MemSobolev 0 2
        (wholePlaneL2ToTempered F f) := by
    exact TemperedDistribution.memSobolev_zero_iff.mpr ⟨f, rfl⟩
  have hmass : TemperedDistribution.MemSobolev 0 2
      (TemperedDistribution.fourierMultiplierCLM F h1RecoverMass T) := by
    exact (hL2 (wholePlaneH1Embedding F u)).fourierMultiplierCLM_of_bounded
      h1RecoverMass_hasTemperateGrowth
      ⟨1, norm_h1RecoverMass_le⟩
  have hderiv (j : Fin 2) : TemperedDistribution.MemSobolev 0 2
      (TemperedDistribution.fourierMultiplierCLM F (h1RecoverDeriv j)
        (∂_{wholePlaneBasis j} T)) := by
    rw [show ∂_{wholePlaneBasis j} T =
        wholePlaneL2ToTempered F (wholePlaneH1FirstDerivative F j u) by
      exact wholePlaneH1_firstDerivative_distribution F u j]
    exact (hL2 (wholePlaneH1FirstDerivative F j u)).fourierMultiplierCLM_of_bounded
      (h1RecoverDeriv_hasTemperateGrowth j)
      ⟨1, norm_h1RecoverDeriv_le j⟩
  have hbp : TemperedDistribution.MemSobolev 0 2
      (TemperedDistribution.besselPotential WholePlane F 1 T) := by
    rw [h1Recover_distribution_identity, Fin.sum_univ_two]
    exact hmass.add ((hderiv 0).add (hderiv 1))
  simpa [T] using
    (TemperedDistribution.memSobolev_besselPotential_iff
      (s := 0) (r := 1) (f := T)).mp hbp

/-- Fourier coefficient recovering the `j`-th physical derivative from the
order-one Bessel coefficient. -/
def h1CoeffDerivSymbol (j : Fin 2) (xi : WholePlane) : ℂ :=
  (2 * Real.pi * Complex.I) * (xi j : ℂ) * h1RecoverMass xi

/-- The symbol `2π i ξ_j ⟨ξ⟩⁻¹`, which recovers the `j`th derivative from the order-one
Bessel coefficient, has temperate growth. -/
theorem h1CoeffDerivSymbol_hasTemperateGrowth (j : Fin 2) :
    (h1CoeffDerivSymbol j).HasTemperateGrowth := by
  unfold h1CoeffDerivSymbol
  have hcoord : Function.HasTemperateGrowth
      (fun xi : WholePlane => (xi j : ℂ)) := by
    let pj : WholePlane →L[ℝ] ℝ := EuclideanSpace.proj j
    have hpj : Function.HasTemperateGrowth pj := pj.hasTemperateGrowth
    have hcoe := (Complex.ofRealCLM.hasTemperateGrowth).comp hpj
    convert hcoe using 1
    funext xi
    simp [pj]
  exact ((Function.HasTemperateGrowth.const _).mul hcoord).mul
    h1RecoverMass_hasTemperateGrowth

/-- The derivative-recovery symbol is bounded by `2π`, since `|ξ_j| ≤ ⟨ξ⟩`. -/
theorem norm_h1CoeffDerivSymbol_le (j : Fin 2) (xi : WholePlane) :
    ‖h1CoeffDerivSymbol j xi‖ ≤ 2 * Real.pi := by
  unfold h1CoeffDerivSymbol h1RecoverMass
  have hconst : ‖(2 * Real.pi : ℂ) * Complex.I‖ = 2 * Real.pi := by
    simp [abs_of_pos Real.pi_pos]
  have hmass :
      ‖(((Real.sqrt (1 + ‖xi‖ ^ 2))⁻¹ : ℝ) : ℂ)‖ =
        (Real.sqrt (1 + ‖xi‖ ^ 2))⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  rw [norm_mul, norm_mul, hconst, Complex.norm_real, Real.norm_eq_abs, hmass]
  have hcoord : |xi j| ≤ ‖xi‖ := by
    have h := abs_real_inner_le_norm xi (wholePlaneBasis j)
    rw [inner_wholePlaneBasis] at h
    simpa [wholePlaneBasis] using h
  have hsqrt_pos : 0 < Real.sqrt (1 + ‖xi‖ ^ 2) := by positivity
  have hnorm_sqrt : ‖xi‖ ≤ Real.sqrt (1 + ‖xi‖ ^ 2) := by
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt (by positivity)]
    nlinarith
  have hratio : |xi j| * (Real.sqrt (1 + ‖xi‖ ^ 2))⁻¹ ≤ 1 := by
    rw [mul_inv_le_iff₀ hsqrt_pos]
    simpa only [one_mul] using hcoord.trans hnorm_sqrt
  calc
    (2 * Real.pi) * |xi j| * (Real.sqrt (1 + ‖xi‖ ^ 2))⁻¹ =
        (2 * Real.pi) *
          (|xi j| * (Real.sqrt (1 + ‖xi‖ ^ 2))⁻¹) := by ring
    _ ≤ (2 * Real.pi) * 1 :=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = 2 * Real.pi := mul_one _

/-- Bounded `L∞` representative of the mass-recovery symbol. -/
def h1RecoverMassLInf : Lp ℂ ∞ (volume : Measure WholePlane) :=
  (memLp_top_of_bound (μ := (volume : Measure WholePlane))
    h1RecoverMass_hasTemperateGrowth.1.continuous.aestronglyMeasurable
    1 (ae_of_all _ norm_h1RecoverMass_le)).toLp _

/-- Bounded `L∞` representative of a derivative-recovery symbol. -/
def h1CoeffDerivSymbolLInf (j : Fin 2) :
    Lp ℂ ∞ (volume : Measure WholePlane) :=
  (memLp_top_of_bound (μ := (volume : Measure WholePlane))
    (h1CoeffDerivSymbol_hasTemperateGrowth j).1.continuous.aestronglyMeasurable
    (2 * Real.pi) (ae_of_all _ (norm_h1CoeffDerivSymbol_le j))).toLp _

/-- The `L∞` class of the inverse Bessel weight has that symbol as an almost everywhere
representative. -/
theorem h1RecoverMassLInf_coe_ae :
    (h1RecoverMassLInf : WholePlane → ℂ) =ᵐ[volume] h1RecoverMass := by
  exact MemLp.coeFn_toLp _

/-- The `L∞` class of the `j`th derivative-recovery symbol has that symbol as an almost
everywhere representative. -/
theorem h1CoeffDerivSymbolLInf_coe_ae (j : Fin 2) :
    (h1CoeffDerivSymbolLInf j : WholePlane → ℂ) =ᵐ[volume]
      h1CoeffDerivSymbol j := by
  exact MemLp.coeFn_toLp _

/-- Physical `L²` value recovered from an order-one Bessel coefficient. -/
def h1CoeffToValueL2 (F : Type*) [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [CompleteSpace F] :
    WholePlaneL2 F →L[ℂ] WholePlaneL2 F :=
  (wholePlaneFourierSynthesis F).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (scalarVectorMulL2 (E := F) volume h1RecoverMassLInf)

/-- The `j`-th `L²` derivative recovered from an order-one Bessel
coefficient. -/
def h1CoeffToDerivL2 (F : Type*) [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [CompleteSpace F] (j : Fin 2) :
    WholePlaneL2 F →L[ℂ] WholePlaneL2 F :=
  (wholePlaneFourierSynthesis F).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (scalarVectorMulL2 (E := F) volume (h1CoeffDerivSymbolLInf j))

/-- The Fourier transform of the recovered physical value is the coefficient multiplied by
the inverse Bessel weight. -/
theorem h1CoeffToValueL2_fourier (F : Type*) [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [CompleteSpace F] (c : WholePlaneL2 F) :
    wholePlaneFourierAnalysis F (h1CoeffToValueL2 F c) =
      scalarVectorMulL2 (E := F) volume h1RecoverMassLInf c := by
  exact wholePlaneFourierAnalysis_synthesis F _

/-- The Fourier transform of the recovered `j`th derivative is the coefficient multiplied by
the symbol `2π i ξ_j ⟨ξ⟩⁻¹`. -/
theorem h1CoeffToDerivL2_fourier (F : Type*) [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [CompleteSpace F] (j : Fin 2)
    (c : WholePlaneL2 F) :
    wholePlaneFourierAnalysis F (h1CoeffToDerivL2 F j c) =
      scalarVectorMulL2 (E := F) volume (h1CoeffDerivSymbolLInf j) c := by
  exact wholePlaneFourierAnalysis_synthesis F _

/-- Distributional form: the recovered physical value represents the tempered distribution
obtained from `c` by the temperate multiplier `h1RecoverMass`. -/
theorem h1CoeffToValueL2_distribution (F : Type*)
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (c : WholePlaneL2 F) :
    𝓕 (wholePlaneL2ToTempered F (h1CoeffToValueL2 F c)) =
      TemperedDistribution.smulLeftCLM F h1RecoverMass
        (wholePlaneL2ToTempered F c) := by
  rw [fourier_wholePlaneL2ToTempered, h1CoeffToValueL2_fourier]
  exact (smulLeftCLM_wholePlaneL2ToTempered_eq_of_ae
    h1RecoverMass h1RecoverMass_hasTemperateGrowth c
    (scalarVectorMulL2 (E := F) volume h1RecoverMassLInf c) (by
      filter_upwards [scalarVectorMulL2_coe_ae (E := F) volume h1RecoverMassLInf c,
        h1RecoverMassLInf_coe_ae] with xi hmul hsym
      simpa [hsym] using hmul)).symm

/-- Distributional form: the recovered `j`th derivative represents the tempered distribution
obtained from `c` by the temperate multiplier `h1CoeffDerivSymbol j`. -/
theorem h1CoeffToDerivL2_distribution (F : Type*)
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (j : Fin 2) (c : WholePlaneL2 F) :
    𝓕 (wholePlaneL2ToTempered F (h1CoeffToDerivL2 F j c)) =
      TemperedDistribution.smulLeftCLM F (h1CoeffDerivSymbol j)
        (wholePlaneL2ToTempered F c) := by
  rw [fourier_wholePlaneL2ToTempered, h1CoeffToDerivL2_fourier]
  exact (smulLeftCLM_wholePlaneL2ToTempered_eq_of_ae
    (h1CoeffDerivSymbol j) (h1CoeffDerivSymbol_hasTemperateGrowth j) c
    (scalarVectorMulL2 (E := F) volume (h1CoeffDerivSymbolLInf j) c) (by
      filter_upwards [scalarVectorMulL2_coe_ae (E := F) volume
          (h1CoeffDerivSymbolLInf j) c,
        h1CoeffDerivSymbolLInf_coe_ae j] with xi hmul hsym
      simpa [hsym] using hmul)).symm

/-- The recovered value and derivatives form a weak jet: the distributional `j`th
derivative of the recovered value is the recovered `j`th derivative. -/
theorem h1CoeffToValueL2_hasWeakDerivative (F : Type*)
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (c : WholePlaneL2 F) (j : Fin 2) :
    ∂_{wholePlaneBasis j}
        (wholePlaneL2ToTempered F (h1CoeffToValueL2 F c)) =
      wholePlaneL2ToTempered F (h1CoeffToDerivL2 F j c) := by
  apply (FourierTransform.fourierCLE ℂ
    (TemperedDistribution WholePlane F)).injective
  change 𝓕 (∂_{wholePlaneBasis j}
      (wholePlaneL2ToTempered F (h1CoeffToValueL2 F c))) =
    𝓕 (wholePlaneL2ToTempered F (h1CoeffToDerivL2 F j c))
  have hcoord : Function.HasTemperateGrowth
      (fun xi : WholePlane => ((inner ℝ xi (wholePlaneBasis j) : ℝ) : ℂ)) := by
    fun_prop
  rw [TemperedDistribution.fourier_lineDerivOp_eq,
    h1CoeffToValueL2_distribution, h1CoeffToDerivL2_distribution]
  rw [TemperedDistribution.smulLeftCLM_smulLeftCLM_apply
    h1RecoverMass_hasTemperateGrowth hcoord]
  rw [← smul_apply]
  rw [← TemperedDistribution.smulLeftCLM_smul
    (h1RecoverMass_hasTemperateGrowth.mul hcoord)
    (2 * Real.pi * Complex.I)]
  congr 2
  funext xi
  simp [h1CoeffDerivSymbol, inner_wholePlaneBasis]
  ring

/-- Continuous map from an order-one Bessel coefficient to its full weak
first-order jet. -/
def h1CoeffToAmbient (F : Type*) [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [CompleteSpace F] :
    WholePlaneL2 F →L[ℂ] WholePlaneH1Ambient F :=
  (PiLp.continuousLinearEquiv 2 ℂ
      (fun _ : WholePlaneJet1Index => WholePlaneL2 F)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun q => q.elim
      (h1CoeffToValueL2 F) (h1CoeffToDerivL2 F))

/-- The value slot of the assembled first-order jet is the recovered physical value. -/
@[simp] theorem h1CoeffToAmbient_none (F : Type*) [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [CompleteSpace F] (c : WholePlaneL2 F) :
    h1CoeffToAmbient F c none = h1CoeffToValueL2 F c := by
  rfl

/-- The `j`th derivative slot of the assembled first-order jet is the recovered `j`th
derivative. -/
@[simp] theorem h1CoeffToAmbient_some (F : Type*) [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [CompleteSpace F] (c : WholePlaneL2 F)
    (j : Fin 2) :
    h1CoeffToAmbient F c (some j) = h1CoeffToDerivL2 F j c := by
  rfl

/-- Continuous Bessel-coefficient-to-graph map. -/
def h1CoeffToGraph (F : Type*) [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [CompleteSpace F] :
    WholePlaneL2 F →L[ℂ] WholePlaneH1 F :=
  (h1CoeffToAmbient F).codRestrict (wholePlaneH1Graph F) fun c => by
    rw [mem_wholePlaneH1Graph_iff]
    intro j
    simp only [h1CoeffToAmbient_none, h1CoeffToAmbient_some]
    exact h1CoeffToValueL2_hasWeakDerivative F c j

/-- The physical value of the synthesized weak-`H¹` field is the value recovery of its
order-one Bessel coefficient. -/
theorem wholePlaneH1Embedding_h1CoeffToGraph
    (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] (c : WholePlaneL2 F) :
    wholePlaneH1Embedding F (h1CoeffToGraph F c) = h1CoeffToValueL2 F c := by
  rfl

/-- The `j`th weak derivative of the synthesized field is the corresponding derivative
recovery of its coefficient. -/
theorem wholePlaneH1FirstDerivative_h1CoeffToGraph
    (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] (c : WholePlaneL2 F) (j : Fin 2) :
    wholePlaneH1FirstDerivative F j (h1CoeffToGraph F c) =
      h1CoeffToDerivL2 F j c := by
  rfl

/-- The recovery mass is exactly the order-minus-one Bessel symbol. -/
theorem h1RecoverMass_eq_besselNegativeOne :
    h1RecoverMass = fun xi : WholePlane =>
      (((1 + ‖xi‖ ^ 2) ^ ((-1 : ℝ) / 2) : ℝ) : ℂ) := by
  funext xi
  unfold h1RecoverMass
  norm_cast
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (by positivity)]
  congr 1
  rw [Rat.cast_divInt]
  norm_num

/-- The physical value recovered from a bundled order-one coefficient
represents exactly the bundled Sobolev distribution. -/
theorem wholePlaneL2ToTempered_h1CoeffToValueL2
    (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] (u : WholePlaneSobolev 1 F) :
    wholePlaneL2ToTempered F
        (h1CoeffToValueL2 F (wholePlaneSobolevCoeff 1 F u)) =
      wholePlaneSobolevToTempered 1 F u := by
  apply (FourierTransform.fourierCLE ℂ
    (TemperedDistribution WholePlane F)).injective
  change 𝓕 (wholePlaneL2ToTempered F
      (h1CoeffToValueL2 F (wholePlaneSobolevCoeff 1 F u))) =
    𝓕 (wholePlaneSobolevToTempered 1 F u)
  rw [h1CoeffToValueL2_distribution,
    fourier_wholePlaneSobolevToTempered]
  rw [h1RecoverMass_eq_besselNegativeOne]

/-- Every weak `H¹` graph jet comes from an order-one Bessel coefficient. -/
theorem h1CoeffToGraph_surjective
    (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] : Function.Surjective (h1CoeffToGraph F) := by
  intro u
  obtain ⟨s, hs⟩ :=
    (memSobolev_iff_exists_wholePlaneSobolev 1 F
      (wholePlaneL2ToTempered F (wholePlaneH1Embedding F u))).mp
        (wholePlaneH1_memSobolev_one F u)
  refine ⟨wholePlaneSobolevCoeff 1 F s, ?_⟩
  apply wholePlaneH1Embedding_injective F
  apply wholePlaneL2ToTempered_injective F
  rw [wholePlaneH1Embedding_h1CoeffToGraph]
  rw [wholePlaneL2ToTempered_h1CoeffToValueL2]
  exact hs

/-! ## Schwartz coefficients give Schwartz physical core elements -/

/-- Physical Schwartz function obtained by applying the inverse Bessel
weight to a Schwartz coefficient and then inverse Fourier transforming. -/
def h1CoeffSchwartzToPhysical (F : Type*) [NormedAddCommGroup F]
    [InnerProductSpace ℂ F]
    (f : SchwartzMap WholePlane F) : SchwartzMap WholePlane F :=
  𝓕⁻ (SchwartzMap.smulLeftCLM F h1RecoverMass f)

/-- On a Schwartz input the bounded `L²` multiplier by the inverse Bessel weight agrees with
the Schwartz-level multiplier, after passing to `L²` classes. -/
private theorem scalarVectorMul_h1RecoverMass_schwartz
    (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (f : SchwartzMap WholePlane F) :
    scalarVectorMulL2 (E := F) volume h1RecoverMassLInf
        (f.toLp 2 volume) =
      (SchwartzMap.smulLeftCLM F h1RecoverMass f).toLp 2 volume := by
  apply Lp.ext
  filter_upwards [scalarVectorMulL2_coe_ae (E := F) volume
      h1RecoverMassLInf (f.toLp 2 volume),
    h1RecoverMassLInf_coe_ae,
    f.coeFn_toLp 2 volume,
    (SchwartzMap.smulLeftCLM F h1RecoverMass f).coeFn_toLp 2 volume]
      with xi hmul hmass hf hout
  rw [hmul, hmass, hf, hout]
  exact (SchwartzMap.smulLeftCLM_apply_apply
    h1RecoverMass_hasTemperateGrowth f xi).symm

/-- The `L²` class of the Schwartz physical field synthesized from a Schwartz coefficient is
the value recovery of the coefficient's `L²` class. -/
theorem h1CoeffSchwartzToPhysical_toLp
    (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] (f : SchwartzMap WholePlane F) :
    (h1CoeffSchwartzToPhysical F f).toLp 2 volume =
      h1CoeffToValueL2 F (f.toLp 2 volume) := by
  unfold h1CoeffSchwartzToPhysical h1CoeffToValueL2
  rw [ContinuousLinearMap.comp_apply,
    scalarVectorMul_h1RecoverMass_schwartz]
  exact (SchwartzMap.toLp_fourierInv_eq
    (SchwartzMap.smulLeftCLM F h1RecoverMass f)).symm

/-- Its classical `j`th derivative, taken in the Schwartz space, has `L²` class equal to the
`j`th derivative recovery of the coefficient; so Schwartz data give core elements
of the weak graph. -/
theorem h1CoeffSchwartzToPhysical_deriv_toLp
    (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] (f : SchwartzMap WholePlane F) (j : Fin 2) :
    (∂_{wholePlaneBasis j} (h1CoeffSchwartzToPhysical F f)).toLp 2 volume =
      h1CoeffToDerivL2 F j (f.toLp 2 volume) := by
  apply wholePlaneL2ToTempered_injective F
  rw [← h1CoeffToValueL2_hasWeakDerivative F (f.toLp 2 volume) j]
  rw [← h1CoeffSchwartzToPhysical_toLp]
  have hphysical :
      wholePlaneL2ToTempered F
          ((h1CoeffSchwartzToPhysical F f).toLp 2 volume) =
        SchwartzMap.toTemperedDistributionCLM WholePlane F volume
          (h1CoeffSchwartzToPhysical F f) := by
    rw [wholePlaneL2ToTempered_apply,
      Lp.toTemperedDistribution_toLp_eq]
  rw [hphysical]
  rw [wholePlaneL2ToTempered_apply,
    Lp.toTemperedDistribution_toLp_eq]
  exact (TemperedDistribution.lineDerivOp_toTemperedDistributionCLM_eq
    (μ := (volume : Measure WholePlane))
    (h1CoeffSchwartzToPhysical F f) (wholePlaneBasis j)).symm

/-- Schwartz coefficients are dense after Bessel synthesis into the weak
`H¹` graph. -/
theorem denseRange_h1CoeffSchwartzToGraph :
    DenseRange (fun f : SchwartzMap WholePlane ℂ =>
      h1CoeffToGraph ℂ (f.toLp 2 volume)) := by
  change DenseRange
    (h1CoeffToGraph ℂ ∘ SchwartzMap.toLpCLM ℝ ℂ 2 volume)
  exact (h1CoeffToGraph_surjective ℂ).denseRange.comp
    (SchwartzMap.denseRange_toLpCLM (F := ℂ) (p := 2)
      ENNReal.ofNat_ne_top)
    (h1CoeffToGraph ℂ).continuous

/-- Every scalar weak `H¹` jet has a single Schwartz sequence converging in
`L²` simultaneously with both stored first derivatives. -/
theorem exists_schwartz_tendsto_wholePlaneScalarH1
    (u : WholePlaneScalarH1) :
    ∃ useq : ℕ → SchwartzMap WholePlane ℂ,
      Filter.Tendsto (fun n => (useq n).toLp 2 volume)
          Filter.atTop (nhds (wholePlaneH1Embedding ℂ u)) ∧
        ∀ j : Fin 2,
          Filter.Tendsto
            (fun n => (∂_{wholePlaneBasis j} (useq n)).toLp 2 volume)
            Filter.atTop (nhds (wholePlaneH1FirstDerivative ℂ j u)) := by
  obtain ⟨cseq, hcseq⟩ :=
    (mem_closure_iff_seq_limit.mp (denseRange_h1CoeffSchwartzToGraph u))
  choose fseq hfseq using hcseq.1
  have hgraph : Filter.Tendsto
      (fun n => h1CoeffToGraph ℂ ((fseq n).toLp 2 volume))
      Filter.atTop (nhds u) := by
    exact hcseq.2.congr'
      (Filter.Eventually.of_forall fun n => (hfseq n).symm)
  refine ⟨fun n => h1CoeffSchwartzToPhysical ℂ (fseq n), ?_, ?_⟩
  · have h := ((wholePlaneH1Embedding ℂ).continuous.tendsto u).comp hgraph
    change Filter.Tendsto
      (fun n => wholePlaneH1Embedding ℂ
        (h1CoeffToGraph ℂ ((fseq n).toLp 2 volume)))
      Filter.atTop (nhds (wholePlaneH1Embedding ℂ u)) at h
    simpa only [wholePlaneH1Embedding_h1CoeffToGraph,
      h1CoeffSchwartzToPhysical_toLp] using h
  · intro j
    have h := ((wholePlaneH1FirstDerivative ℂ j).continuous.tendsto u).comp hgraph
    change Filter.Tendsto
      (fun n => wholePlaneH1FirstDerivative ℂ j
        (h1CoeffToGraph ℂ ((fseq n).toLp 2 volume)))
      Filter.atTop (nhds (wholePlaneH1FirstDerivative ℂ j u)) at h
    simpa only [wholePlaneH1FirstDerivative_h1CoeffToGraph,
      h1CoeffSchwartzToPhysical_deriv_toLp] using h

private theorem inner_recoverySymbols {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] (j : Fin 2) (xi : WholePlane) (a b : F) :
    inner ℂ (h1RecoverMass xi • a) (h1CoeffDerivSymbol j xi • b) =
      -inner ℂ (h1CoeffDerivSymbol j xi • a) (h1RecoverMass xi • b) := by
  simp only [inner_smul_left, inner_smul_right, h1RecoverMass, h1CoeffDerivSymbol,
    map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  ring

private theorem inner_L2_recoverySymbols (F : Type*) [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] (j : Fin 2) (c d : WholePlaneL2 F) :
    inner ℂ (scalarVectorMulL2 volume h1RecoverMassLInf c)
        (scalarVectorMulL2 volume (h1CoeffDerivSymbolLInf j) d) =
      -inner ℂ (scalarVectorMulL2 volume (h1CoeffDerivSymbolLInf j) c)
        (scalarVectorMulL2 volume h1RecoverMassLInf d) := by
  simp only [MeasureTheory.L2.inner_def, ← MeasureTheory.integral_neg]
  apply integral_congr_ae
  filter_upwards [
    scalarVectorMulL2_coe_ae (E := F) volume h1RecoverMassLInf c,
    scalarVectorMulL2_coe_ae (E := F) volume (h1CoeffDerivSymbolLInf j) d,
    scalarVectorMulL2_coe_ae (E := F) volume (h1CoeffDerivSymbolLInf j) c,
    scalarVectorMulL2_coe_ae (E := F) volume h1RecoverMassLInf d,
    h1RecoverMassLInf_coe_ae, h1CoeffDerivSymbolLInf_coe_ae j] with xi hmc hqd hqc hmd hm hq
  simpa only [hmc, hqd, hqc, hmd, hm, hq] using inner_recoverySymbols j xi (c xi) (d xi)

/-- A whole-plane weak coordinate derivative is skew-adjoint on `H¹`.
Equivalently, integration by parts has no boundary term on the whole plane. -/
theorem wholePlaneH1_integrationByParts
    (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] (u v : WholePlaneH1 F) (j : Fin 2) :
    inner ℂ (wholePlaneH1Embedding F u)
        (wholePlaneH1FirstDerivative F j v) =
      -inner ℂ (wholePlaneH1FirstDerivative F j u)
        (wholePlaneH1Embedding F v) := by
  obtain ⟨c, rfl⟩ := h1CoeffToGraph_surjective F u
  obtain ⟨d, rfl⟩ := h1CoeffToGraph_surjective F v
  rw [wholePlaneH1Embedding_h1CoeffToGraph,
    wholePlaneH1FirstDerivative_h1CoeffToGraph,
    wholePlaneH1FirstDerivative_h1CoeffToGraph,
    wholePlaneH1Embedding_h1CoeffToGraph]
  calc
    inner ℂ (h1CoeffToValueL2 F c) (h1CoeffToDerivL2 F j d) =
        inner ℂ (wholePlaneFourierAnalysis F (h1CoeffToValueL2 F c))
          (wholePlaneFourierAnalysis F (h1CoeffToDerivL2 F j d)) :=
      (inner_wholePlaneFourierAnalysis F _ _).symm
    _ = inner ℂ
          (scalarVectorMulL2 (E := F) volume h1RecoverMassLInf c)
          (scalarVectorMulL2 (E := F) volume
            (h1CoeffDerivSymbolLInf j) d) :=
      congrArg₂ (inner ℂ) (h1CoeffToValueL2_fourier F c)
        (h1CoeffToDerivL2_fourier F j d)
    _ = -inner ℂ
          (scalarVectorMulL2 (E := F) volume
            (h1CoeffDerivSymbolLInf j) c)
          (scalarVectorMulL2 (E := F) volume h1RecoverMassLInf d) :=
      inner_L2_recoverySymbols F j c d
    _ = -inner ℂ
          (wholePlaneFourierAnalysis F (h1CoeffToDerivL2 F j c))
          (wholePlaneFourierAnalysis F (h1CoeffToValueL2 F d)) :=
      congrArg Neg.neg <| (congrArg₂ (inner ℂ)
        (h1CoeffToDerivL2_fourier F j c)
        (h1CoeffToValueL2_fourier F d)).symm
    _ = -inner ℂ (h1CoeffToDerivL2 F j c)
          (h1CoeffToValueL2 F d) :=
      congrArg Neg.neg <| inner_wholePlaneFourierAnalysis F
        (h1CoeffToDerivL2 F j c) (h1CoeffToValueL2 F d)

/-- Integration by parts between a strong `H²` field and a weak `H¹` test
field, for one ordered pair of transverse derivatives. -/
theorem wholePlaneH2H1_integrationByParts
    (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] (u : WholePlaneH2 F) (v : WholePlaneH1 F)
    (j k : Fin 2) :
    inner ℂ (wholePlaneH1FirstDerivative F k v)
        (wholePlaneH2FirstDerivative F j u) =
      -inner ℂ (wholePlaneH1Embedding F v)
        (wholePlaneH2SecondDerivative F j k u) := by
  have h := wholePlaneH1_integrationByParts F v
    (wholePlaneFirstDerivativeToH1 F j u) k
  rw [wholePlaneH1FirstDerivative_firstDerivativeToH1,
    wholePlaneH1Embedding_firstDerivativeToH1] at h
  exact neg_eq_iff_eq_neg.mp h.symm

/-- The transverse gradient pairing is the negative weak pairing with the
whole-plane Laplacian. -/
theorem wholePlaneH2H1_gradientLaplacian_integrationByParts
    (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] (u : WholePlaneH2 F) (v : WholePlaneH1 F) :
    ∑ j : Fin 2,
        inner ℂ (wholePlaneH1FirstDerivative F j v)
          (wholePlaneH2FirstDerivative F j u) =
      -inner ℂ (wholePlaneH1Embedding F v)
        (wholePlaneLaplacian F u) := by
  rw [Fin.sum_univ_two, wholePlaneLaplacian_apply, inner_add_right]
  rw [wholePlaneH2H1_integrationByParts F u v 0 0,
    wholePlaneH2H1_integrationByParts F u v 1 1]
  ring

/-- In one fixed axial Fourier sector, the axial derivative pairing between
a strong `H²` field and a weak `H¹` test contributes the positive frequency
square. -/
theorem wholePlaneH2H1_fixedNAxialPairing
    (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] (N : ℝ) (u : WholePlaneH2 F) (v : WholePlaneH1 F) :
    inner ℂ
        ((Complex.I * (N : ℂ)) • wholePlaneH1Embedding F v)
        ((Complex.I * (N : ℂ)) • wholePlaneH2Embedding F u) =
      (N : ℂ) ^ 2 *
        inner ℂ (wholePlaneH1Embedding F v)
          (wholePlaneH2Embedding F u) := by
  rw [inner_smul_left, inner_smul_right]
  simp
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The full fixed-frequency gradient pairing is the negative weak pairing
with the strong fixed-frequency Laplacian `Δ⊥ - N²`. -/
theorem wholePlaneH2H1_fixedNGradientLaplacian_integrationByParts
    (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] (N : ℝ) (u : WholePlaneH2 F) (v : WholePlaneH1 F) :
    (∑ j : Fin 2,
        inner ℂ (wholePlaneH1FirstDerivative F j v)
          (wholePlaneH2FirstDerivative F j u)) +
      inner ℂ
        ((Complex.I * (N : ℂ)) • wholePlaneH1Embedding F v)
        ((Complex.I * (N : ℂ)) • wholePlaneH2Embedding F u) =
      -inner ℂ (wholePlaneH1Embedding F v)
        (wholePlaneLaplacian F u -
          ((N : ℂ) ^ 2) • wholePlaneH2Embedding F u) := by
  rw [wholePlaneH2H1_gradientLaplacian_integrationByParts F u v,
    wholePlaneH2H1_fixedNAxialPairing F N u v,
    inner_sub_right, inner_smul_right]
  ring

end

end FastDynamo
