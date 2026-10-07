/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedR12FinalVelocityReg
public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierPhysicalRange
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselGlobalPath
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselDerivativeL2Map

/-!
# Physical H¹ traces of the regularized mild path

The Bessel path supplies continuous L² classes for its ordered derivatives.
This module identifies those classes with the pointwise derivatives of the
regularized velocity on the full closed time interval.
-/

public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform SchwartzMap LineDeriv
open CKN CKN.Foundation.Parabolic CKN.Leray
open scoped Real


noncomputable section

namespace ESS.LPS

private theorem regularisedH1Path
    (ρ : CKN.Leray.RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (a : Vec3 → Vec3) (ha : CKN.IsInJ a) (T : ℝ) (hT : 0 ≤ T) :
    ∃ v : C(CKN.Leray.RegularizedMildTimeInterval T,
        BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * 2 : ℕ) : ℝ) 2),
      (∀ t : CKN.Leray.RegularizedMildTimeInterval T,
        CKN.Leray.regularisedBesselSobolevToL2CLM
            ((2 * 2 : ℕ) : ℝ) (by norm_num) (v t) =
          CKN.Leray.complexifyVectorL2
            (CKN.Leray.regularizedGlobalMildCurve ρ ε hε
              (CKN.Leray.realVectorL2OfCoordinateFunction
                (CKN.Leray.regUniformMollifiedInitial ρ ε hε a)
                (CKN.Leray.regMollifiedInitial_isInJ ρ ε hε ha).1)
              (CKN.Leray.regUniformMollifiedInitial_mildJData
                ρ ε hε ha) t.1)) ∧
      Continuous (fun t : CKN.Leray.RegularizedMildTimeInterval T =>
        CKN.Leray.realPartVectorL2
          (CKN.Leray.regularisedBesselSobolevToL2CLM
            ((2 * 2 : ℕ) : ℝ) (by norm_num) (v t))) ∧
      ∀ j : Fin 3, Continuous (fun t :
          CKN.Leray.RegularizedMildTimeInterval T =>
        CKN.Leray.realPartVectorL2
          (CKN.Leray.regularisedBesselEvenOrderedDerivativeL2 2
            [WithLp.toLp 2 (CKN.basisVec j)] (by norm_num) (v t))) := by
  obtain ⟨v, hv⟩ := CKN.Leray.regUniformMollifiedInitial_global_bessel_path
    ρ ε hε a ha 2 T hT
  refine ⟨v, ?_, ?_, ?_⟩
  · intro t
    exact hv t
  · exact CKN.Leray.realPartVectorL2.continuous.comp
      ((CKN.Leray.regularisedBesselSobolevToL2CLM
        ((2 * 2 : ℕ) : ℝ) (by norm_num)).continuous.comp v.continuous)
  · intro j
    exact CKN.Leray.realPartVectorL2.continuous.comp
      ((CKN.Leray.regularisedBesselEvenOrderedDerivativeL2CLM
        2 [WithLp.toLp 2 (CKN.basisVec j)] (by norm_num)).continuous.comp
          v.continuous)

/-- The inverse Bessel weight of order four used for the regularized H1 trace. -/
@[expose] def regH1InverseWeight (ξ : L2Vec3) : ℂ :=
  (((1 + ‖ξ‖ ^ 2) ^ (-2 : ℝ) : ℝ) : ℂ)

private theorem regH1InverseWeight_continuous :
    Continuous regH1InverseWeight := by
  have hbase : Continuous (fun ξ : L2Vec3 =>
      (1 + ‖ξ‖ ^ 2 : ℝ)) := by fun_prop
  have hpow : Continuous (fun ξ : L2Vec3 =>
      (1 + ‖ξ‖ ^ 2 : ℝ) ^ (-2 : ℝ)) :=
    hbase.rpow_const (p := (-2 : ℝ)) (fun ξ =>
      Or.inl (by positivity : (1 + ‖ξ‖ ^ 2 : ℝ) ≠ 0))
  change Continuous (fun ξ : L2Vec3 =>
    (((1 + ‖ξ‖ ^ 2) ^ (-2 : ℝ) : ℝ) : ℂ))
  exact Complex.continuous_ofReal.comp hpow

theorem regH1InverseWeight_memLp :
    MemLp regH1InverseWeight ∞ volume := by
  apply memLp_top_of_bound regH1InverseWeight_continuous.aestronglyMeasurable 1
  filter_upwards [] with ξ
  have hbase : 1 ≤ (1 + ‖ξ‖ ^ 2 : ℝ) := by
    have hsq : 0 ≤ ‖ξ‖ ^ 2 := sq_nonneg _
    linarith only [hsq]
  have hexp : (-2 : ℝ) ≤ 0 := by norm_num
  have hpow := Real.rpow_le_one_of_one_le_of_nonpos hbase hexp
  change ‖(((1 + ‖ξ‖ ^ 2) ^ (-2 : ℝ) : ℝ) : ℂ)‖ ≤ 1
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  exact hpow

private theorem regH1InverseWeight_temperate :
    regH1InverseWeight.HasTemperateGrowth := by
  unfold regH1InverseWeight
  fun_prop

/-- The inverse Bessel weight represented as an essentially bounded multiplier. -/
@[expose] def regH1InverseWeightLp : Lp (α := L2Vec3) ℂ ∞ :=
  regH1InverseWeight_memLp.toLp regH1InverseWeight

/-- The coordinate derivative symbol multiplied by the inverse Bessel weight. -/
@[expose] def regH1DerivativeMultiplier (j : Fin 3) (ξ : L2Vec3) : ℂ :=
  regR12CoordSymbol j ξ * regH1InverseWeight ξ

private theorem regH1DerivativeMultiplier_continuous (j : Fin 3) :
    Continuous (regH1DerivativeMultiplier j) := by
  unfold regH1DerivativeMultiplier
  exact (regR12CoordSymbol_continuous j).mul regH1InverseWeight_continuous

private theorem regH1DerivativeMultiplier_bound (j : Fin 3) (ξ : L2Vec3) :
    ‖regH1DerivativeMultiplier j ξ‖ ≤ 2 * π := by
  have hbase : 1 ≤ (1 + ‖ξ‖ ^ 2 : ℝ) := by
    have hsq : 0 ≤ ‖ξ‖ ^ 2 := sq_nonneg _
    linarith only [hsq]
  have hexp : (-1 : ℝ) ≤ 0 := by norm_num
  have hweight := Real.rpow_le_one_of_one_le_of_nonpos hbase hexp
  have hsymbol : ‖regR12CoordSymbol j ξ‖ ≤ 2 * π * (1 + ‖ξ‖ ^ 2) := by
    calc
      ‖regR12CoordSymbol j ξ‖ ≤ 2 * π * ‖ξ‖ := regR12CoordSymbol_norm_le j ξ
      _ ≤ 2 * π * (1 + ‖ξ‖ ^ 2) := by
        gcongr
        nlinarith only [sq_nonneg (‖ξ‖ - 1 / 2), norm_nonneg ξ]
  unfold regH1DerivativeMultiplier regH1InverseWeight
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  calc
    ‖regR12CoordSymbol j ξ‖ * (1 + ‖ξ‖ ^ 2) ^ (-2 : ℝ)
        ≤ (2 * π * (1 + ‖ξ‖ ^ 2)) * (1 + ‖ξ‖ ^ 2) ^ (-2 : ℝ) :=
          mul_le_mul_of_nonneg_right hsymbol (Real.rpow_nonneg (by positivity) _)
    _ = 2 * π * (1 + ‖ξ‖ ^ 2) ^ (-1 : ℝ) := by
          have hx : 0 < (1 + ‖ξ‖ ^ 2 : ℝ) := by positivity
          calc
            2 * π * (1 + ‖ξ‖ ^ 2) * (1 + ‖ξ‖ ^ 2) ^ (-2 : ℝ)
                = 2 * π * ((1 + ‖ξ‖ ^ 2 : ℝ) ^ (1 : ℝ) *
                    (1 + ‖ξ‖ ^ 2 : ℝ) ^ (-2 : ℝ)) := by
                      rw [Real.rpow_one]
                      ring
            _ = 2 * π * (1 + ‖ξ‖ ^ 2) ^ ((1 : ℝ) + (-2 : ℝ)) := by
                  rw [← Real.rpow_add hx (1 : ℝ) (-2 : ℝ)]
            _ = 2 * π * (1 + ‖ξ‖ ^ 2) ^ (-1 : ℝ) := by
                  congr 2
                  norm_num
    _ ≤ 2 * π := by
          have h := mul_le_mul_of_nonneg_left hweight (by positivity : 0 ≤ 2 * π)
          simpa only [mul_one] using h

private theorem regH1DerivativeMultiplier_memLp (j : Fin 3) :
    MemLp (regH1DerivativeMultiplier j) ∞ volume := by
  apply memLp_top_of_bound
    (regH1DerivativeMultiplier_continuous j).aestronglyMeasurable (2 * π)
  filter_upwards [] with ξ
  exact regH1DerivativeMultiplier_bound j ξ

private theorem regH1DerivativeMultiplier_temperate (j : Fin 3) :
    (regH1DerivativeMultiplier j).HasTemperateGrowth := by
  have hs : (regR12CoordSymbol j).HasTemperateGrowth := by
    unfold regR12CoordSymbol regR12DirSymbol
    fun_prop
  change (regR12CoordSymbol j * regH1InverseWeight).HasTemperateGrowth
  exact hs.mul regH1InverseWeight_temperate

private theorem regH1CoordinateMultiplier_eq (j : Fin 3) :
    regR12CoordSymbol j = fun ξ : L2Vec3 =>
      (2 * π * Complex.I) * ((inner ℝ ξ
        (WithLp.toLp 2 (basisVec j) : L2Vec3) : ℝ) : ℂ) := by
  funext ξ
  simp only [regR12CoordSymbol, regR12DirSymbol]
  push_cast
  ring

private theorem regH1CoordinateMultiplier_temperate (j : Fin 3) :
    (fun ξ : L2Vec3 => ((inner ℝ ξ
      (WithLp.toLp 2 (basisVec j) : L2Vec3) : ℝ) : ℂ)).HasTemperateGrowth := by
  fun_prop

private theorem regH1CoordinateMultiplier_smulLeftCLM (j : Fin 3) :
    TemperedDistribution.smulLeftCLM ComplexVec3 (regR12CoordSymbol j) =
      (2 * π * Complex.I) • TemperedDistribution.smulLeftCLM ComplexVec3
        (fun ξ : L2Vec3 => ((inner ℝ ξ
          (WithLp.toLp 2 (basisVec j) : L2Vec3) : ℝ) : ℂ)) := by
  rw [regH1CoordinateMultiplier_eq]
  exact TemperedDistribution.smulLeftCLM_smul
    (regH1CoordinateMultiplier_temperate j) _

private theorem regR12FreqCurve_eq_weightedLift
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (a : Vec3 → Vec3) (ha : CKN.IsInJ a) (T : ℝ) (hT : 0 ≤ T)
    (v : C(RegularizedMildTimeInterval T,
      BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * 2 : ℕ) : ℝ) 2))
    (hv : ∀ t : RegularizedMildTimeInterval T,
      regularisedBesselSobolevToL2CLM ((2 * 2 : ℕ) : ℝ) (by norm_num) (v t) =
        complexifyVectorL2 (regR12Curve ρ ε hε a ha t.1))
    (t : ℝ) (ht : t ∈ Set.Icc 0 T) :
    regR12FreqCurve ρ ε hε a ha t =
      regH1InverseWeightLp • regR12LiftFreq T hT v t := by
  apply Lp.ext
  filter_upwards [regR12FreqCurve_ae_eq ρ ε hε a ha T hT v hv t ht,
    regH1InverseWeight_memLp.coeFn_toLp,
    Lp.coeFn_lpSMul (r := 2) regH1InverseWeightLp
      (regR12LiftFreq T hT v t)] with ξ hfreq hweight hsmul
  change regR12FreqCurve ρ ε hε a ha t ξ = _ at hfreq
  change regH1InverseWeightLp ξ = regH1InverseWeight ξ at hweight
  calc
    regR12FreqCurve ρ ε hε a ha t ξ =
        regH1InverseWeight ξ • regR12LiftFreq T hT v t ξ := by
          simpa [regH1InverseWeight] using hfreq
    _ = regH1InverseWeightLp ξ • regR12LiftFreq T hT v t ξ := by rw [← hweight]
    _ = (regH1InverseWeightLp • regR12LiftFreq T hT v t) ξ := hsmul.symm

private theorem regH1Curve_fourier_toDistr
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (a : Vec3 → Vec3) (ha : CKN.IsInJ a) (T : ℝ) (hT : 0 ≤ T)
    (v : C(RegularizedMildTimeInterval T,
      BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * 2 : ℕ) : ℝ) 2))
    (hv : ∀ t : RegularizedMildTimeInterval T,
      regularisedBesselSobolevToL2CLM ((2 * 2 : ℕ) : ℝ) (by norm_num) (v t) =
        complexifyVectorL2 (regR12Curve ρ ε hε a ha t.1))
    (t : ℝ) (ht : t ∈ Set.Icc 0 T) :
    𝓕 ((v ⟨t, ht⟩).toDistr) =
      ((regH1InverseWeightLp • regR12LiftFreq T hT v t : ComplexVectorL2) :
        𝓢'(L2Vec3, ComplexVec3)) := by
  have hphysical := hv ⟨t, ht⟩
  rw [regularisedBesselSobolevToL2CLM_apply] at hphysical
  have hcurveDist :
      ((complexifyVectorL2 (regR12Curve ρ ε hε a ha t) : ComplexVectorL2) :
        𝓢'(L2Vec3, ComplexVec3)) = (v ⟨t, ht⟩).toDistr := by
    calc
      _ = ((regularisedBesselSobolevToL2 ((2 * 2 : ℕ) : ℝ) (by norm_num)
          (v ⟨t, ht⟩) : ComplexVectorL2) : 𝓢'(L2Vec3, ComplexVec3)) := by
            exact (congrArg (fun f : ComplexVectorL2 =>
              (f : 𝓢'(L2Vec3, ComplexVec3))) hphysical).symm
      _ = (v ⟨t, ht⟩).toDistr :=
        regularisedBesselSobolevToL2_toTemperedDistribution_eq
          ((2 * 2 : ℕ) : ℝ) (by norm_num) (v ⟨t, ht⟩)
  have hfreqDist :
      (regR12FreqCurve ρ ε hε a ha t : 𝓢'(L2Vec3, ComplexVec3)) =
        𝓕 ((v ⟨t, ht⟩).toDistr) := by
    calc
      _ = 𝓕 ((complexifyVectorL2 (regR12Curve ρ ε hε a ha t) :
          ComplexVectorL2) : 𝓢'(L2Vec3, ComplexVec3)) := by
            unfold regR12FreqCurve
            exact (MeasureTheory.Lp.fourier_toTemperedDistribution_eq _).symm
      _ = 𝓕 ((v ⟨t, ht⟩).toDistr) := by rw [hcurveDist]
  calc
    𝓕 ((v ⟨t, ht⟩).toDistr) =
        (regR12FreqCurve ρ ε hε a ha t : 𝓢'(L2Vec3, ComplexVec3)) := hfreqDist.symm
    _ = ((regH1InverseWeightLp • regR12LiftFreq T hT v t : ComplexVectorL2) :
        𝓢'(L2Vec3, ComplexVec3)) := by
          exact (congrArg (fun f : ComplexVectorL2 =>
            (f : 𝓢'(L2Vec3, ComplexVec3)))
            (regR12FreqCurve_eq_weightedLift ρ ε hε a ha T hT v hv t ht))

private theorem regH1Derivative_toDistr
    (T : ℝ)
    (v : C(RegularizedMildTimeInterval T,
      BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * 2 : ℕ) : ℝ) 2))
    (t : RegularizedMildTimeInterval T) (j : Fin 3) :
    ((regularisedBesselEvenOrderedDerivativeL2 2
      [WithLp.toLp 2 (basisVec j)] (by norm_num) (v t) : ComplexVectorL2) :
        𝓢'(L2Vec3, ComplexVec3)) =
      ∂_{(WithLp.toLp 2 (basisVec j) : L2Vec3)} (v t).toDistr := by
  have h := regularisedBesselEvenOrderedDerivativeL2_toDistr 2
    [WithLp.toLp 2 (basisVec j)] (by norm_num) (v t)
  rw [regularisedOrderedDistributionDerivativeCLM_apply] at h
  simpa using h

private theorem regH1Derivative_fourier_ae
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (a : Vec3 → Vec3) (ha : CKN.IsInJ a) (T : ℝ) (hT : 0 ≤ T)
    (v : C(RegularizedMildTimeInterval T,
      BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * 2 : ℕ) : ℝ) 2))
    (hv : ∀ t : RegularizedMildTimeInterval T,
      regularisedBesselSobolevToL2CLM ((2 * 2 : ℕ) : ℝ) (by norm_num) (v t) =
        complexifyVectorL2 (regR12Curve ρ ε hε a ha t.1))
    (t : ℝ) (ht : t ∈ Set.Icc 0 T) (j : Fin 3) :
    ((Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3
      (regularisedBesselEvenOrderedDerivativeL2 2
        [WithLp.toLp 2 (basisVec j)] (by norm_num) (v ⟨t, ht⟩)) :
        ComplexVectorL2) : L2Vec3 → ComplexVec3) =ᵐ[volume]
      fun ξ => regR12CoordSymbol j ξ • regH1InverseWeight ξ •
        (regR12LiftFreq T hT v t : L2Vec3 → ComplexVec3) ξ := by
  let G : ComplexVectorL2 := regR12LiftFreq T hT v t
  let D : ComplexVectorL2 := regularisedBesselEvenOrderedDerivativeL2 2
    [WithLp.toLp 2 (basisVec j)] (by norm_num) (v ⟨t, ht⟩)
  let W : Lp (α := L2Vec3) ℂ ∞ := regH1InverseWeightLp
  let A : Lp (α := L2Vec3) ℂ ∞ :=
    (regH1DerivativeMultiplier_memLp j).toLp (regH1DerivativeMultiplier j)
  have hVFourier : 𝓕 ((v ⟨t, ht⟩).toDistr) = (W • G : ComplexVectorL2) := by
    exact regH1Curve_fourier_toDistr ρ ε hε a ha T hT v hv t ht
  have hDfourier : 𝓕 (D : 𝓢'(L2Vec3, ComplexVec3)) =
      (2 * π * Complex.I) •
        TemperedDistribution.smulLeftCLM ComplexVec3
          (fun ξ : L2Vec3 => inner ℝ ξ
            (WithLp.toLp 2 (basisVec j) : L2Vec3))
          (𝓕 ((v ⟨t, ht⟩).toDistr)) := by
    rw [show (D : 𝓢'(L2Vec3, ComplexVec3)) =
      ∂_{(WithLp.toLp 2 (basisVec j) : L2Vec3)} (v ⟨t, ht⟩).toDistr from by
        exact regH1Derivative_toDistr T v ⟨t, ht⟩ j,
      TemperedDistribution.fourier_lineDerivOp_eq]
  have hDfourierCoord : 𝓕 (D : 𝓢'(L2Vec3, ComplexVec3)) =
      TemperedDistribution.smulLeftCLM ComplexVec3 (regR12CoordSymbol j)
        (𝓕 ((v ⟨t, ht⟩).toDistr)) := by
    calc
      _ = (2 * π * Complex.I) •
          TemperedDistribution.smulLeftCLM ComplexVec3
            (fun ξ : L2Vec3 => inner ℝ ξ
              (WithLp.toLp 2 (basisVec j) : L2Vec3))
            (𝓕 ((v ⟨t, ht⟩).toDistr)) := hDfourier
      _ = TemperedDistribution.smulLeftCLM ComplexVec3 (regR12CoordSymbol j)
          (𝓕 ((v ⟨t, ht⟩).toDistr)) := by
            exact congrArg
              (fun L : 𝓢'(L2Vec3, ComplexVec3) →L[ℂ]
                𝓢'(L2Vec3, ComplexVec3) => L (𝓕 ((v ⟨t, ht⟩).toDistr)))
              (regH1CoordinateMultiplier_smulLeftCLM j).symm
  have hWdist : (W • G : ComplexVectorL2) =
      TemperedDistribution.smulLeftCLM ComplexVec3 regH1InverseWeight
        (G : 𝓢'(L2Vec3, ComplexVec3)) := by
    exact MeasureTheory.Lp.toTemperedDistribution_smul_eq
      (p := ∞) (q := 2) (r := 2) regH1InverseWeight_temperate
      regH1InverseWeight_memLp G
  have hAdist : (A • G : ComplexVectorL2) =
      TemperedDistribution.smulLeftCLM ComplexVec3
        (regH1DerivativeMultiplier j) (G : 𝓢'(L2Vec3, ComplexVec3)) := by
    exact MeasureTheory.Lp.toTemperedDistribution_smul_eq
      (p := ∞) (q := 2) (r := 2) (regH1DerivativeMultiplier_temperate j)
      (regH1DerivativeMultiplier_memLp j) G
  have hDA : 𝓕 (D : 𝓢'(L2Vec3, ComplexVec3)) =
      (A • G : ComplexVectorL2) := by
    calc
      _ = TemperedDistribution.smulLeftCLM ComplexVec3 (regR12CoordSymbol j)
          (𝓕 ((v ⟨t, ht⟩).toDistr)) := hDfourierCoord
      _ = TemperedDistribution.smulLeftCLM ComplexVec3 (regR12CoordSymbol j)
          (W • G : ComplexVectorL2) := by rw [hVFourier]
      _ = TemperedDistribution.smulLeftCLM ComplexVec3 (regR12CoordSymbol j)
          (TemperedDistribution.smulLeftCLM ComplexVec3 regH1InverseWeight
            (G : 𝓢'(L2Vec3, ComplexVec3))) := by rw [hWdist]
      _ = TemperedDistribution.smulLeftCLM ComplexVec3
          (fun ξ => regH1InverseWeight ξ * regR12CoordSymbol j ξ)
          (G : 𝓢'(L2Vec3, ComplexVec3)) := by
            exact TemperedDistribution.smulLeftCLM_smulLeftCLM_apply
              regH1InverseWeight_temperate (by
                unfold regR12CoordSymbol regR12DirSymbol
                fun_prop) _
      _ = TemperedDistribution.smulLeftCLM ComplexVec3
          (regH1DerivativeMultiplier j) (G : 𝓢'(L2Vec3, ComplexVec3)) := by
            have hmult : (fun ξ : L2Vec3 =>
                regH1InverseWeight ξ * regR12CoordSymbol j ξ) =
                regH1DerivativeMultiplier j := by
              funext ξ
              simp [regH1DerivativeMultiplier, mul_comm]
            rw [hmult]
      _ = (A • G : ComplexVectorL2) := hAdist.symm
  have hL2eq : Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3 D = A • G := by
    have hinj : Function.Injective
        (fun g : ComplexVectorL2 => (g : 𝓢'(L2Vec3, ComplexVec3))) :=
      LinearMap.ker_eq_bot.mp
        (MeasureTheory.Lp.ker_toTemperedDistributionCLM_eq_bot
          (F := ComplexVec3) (μ := volume) (p := 2))
    apply hinj
    calc
      _ = 𝓕 (D : 𝓢'(L2Vec3, ComplexVec3)) :=
        (MeasureTheory.Lp.fourier_toTemperedDistribution_eq D).symm
      _ = (A • G : ComplexVectorL2) := hDA
  have hLpAE := (Lp.ext_iff).mp hL2eq
  filter_upwards [hLpAE, (regH1DerivativeMultiplier_memLp j).coeFn_toLp,
    Lp.coeFn_lpSMul (r := 2) A G] with ξ hLp hA hsmul
  change (Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3 D) ξ = _ at hLp
  change A ξ = regH1DerivativeMultiplier j ξ at hA
  change (A • G : ComplexVectorL2) ξ = A ξ • G ξ at hsmul
  rw [hLp, hsmul, hA]
  simp [G, regH1DerivativeMultiplier, regH1InverseWeight, smul_smul]

private theorem regH1Derivative_field_ae
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (a : Vec3 → Vec3) (ha : CKN.IsInJ a) (T : ℝ) (hT : 0 ≤ T)
    (v : C(RegularizedMildTimeInterval T,
      BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * 2 : ℕ) : ℝ) 2))
    (hv : ∀ t : RegularizedMildTimeInterval T,
      regularisedBesselSobolevToL2CLM ((2 * 2 : ℕ) : ℝ) (by norm_num) (v t) =
        complexifyVectorL2 (regR12Curve ρ ε hε a ha t.1))
    (t : ℝ) (ht : t ∈ Set.Icc 0 T) (j : Fin 3) :
    regR12WeightedField (regR12CoordSymbol j) (regR12LiftFreq T hT v t) =ᵐ[volume]
      regularisedBesselEvenOrderedDerivativeL2 2
        [WithLp.toLp 2 (basisVec j)] (by norm_num) (v ⟨t, ht⟩) := by
  refine regR12WeightedField_ae_eq
    (regR12CoordSymbol j) ((regR12CoordSymbol_continuous j).aestronglyMeasurable)
    (2 * π) (by positivity) (fun ξ => ?_)
    (regR12LiftFreq T hT v t)
    (regularisedBesselEvenOrderedDerivativeL2 2
      [WithLp.toLp 2 (basisVec j)] (by norm_num) (v ⟨t, ht⟩)) ?_
  · simpa [regR12CoordSymbol] using regR12_first_norm_le j ξ
  · exact regH1Derivative_fourier_ae ρ ε hε a ha T hT v hv t ht j

private theorem regH1CoordinateRealPart
    (z : ComplexVectorL2) (x : Vec3) (i : Fin 3) :
    regR12CoordCLM i (z (WithLp.toLp 2 x)) =
      realPartVectorL2Representative z x i := by
  change Complex.re (z (WithLp.toLp 2 x) i) =
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm
      (WithLp.toLp 2 (fun k : Fin 3 =>
        Complex.re (z (WithLp.toLp 2 x) k))) i
  simp

private theorem regH1Derivative_pointwise_ae
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (a : Vec3 → Vec3) (ha : CKN.IsInJ a) (T : ℝ) (hT : 0 ≤ T)
    (v : C(RegularizedMildTimeInterval T,
      BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * 2 : ℕ) : ℝ) 2))
    (hv : ∀ t : RegularizedMildTimeInterval T,
      regularisedBesselSobolevToL2CLM ((2 * 2 : ℕ) : ℝ) (by norm_num) (v t) =
        complexifyVectorL2 (regR12Curve ρ ε hε a ha t.1))
    (t : ℝ) (ht : t ∈ Set.Icc 0 T) (i j : Fin 3) :
    (fun x : Vec3 => spatialPartial
      (fun y : ParabolicPoint => regR12Velocity ρ ε hε a ha y i) j (x, t)) =ᵐ[volume]
      fun x => realPartVectorL2Representative
        (regularisedBesselEvenOrderedDerivativeL2 2
          [WithLp.toLp 2 (basisVec j)] (by norm_num) (v ⟨t, ht⟩)) x i := by
  have hfield := regH1Derivative_field_ae ρ ε hε a ha T hT v hv t ht j
  have htransport := vec3ToL2Vec3_measurePreserving.quasiMeasurePreserving.ae hfield
  filter_upwards [htransport] with x hx
  rw [regR12Velocity_D_eq_model ρ ε hε a ha T hT v hv (x, t) ht i j]
  unfold regR12SpaceTimeField
  have hM : (fun ξ : L2Vec3 => regR12CoordSymbol j ξ *
      (fun _ : L2Vec3 => (1 : ℂ)) ξ) = regR12CoordSymbol j := by
    funext ξ
    simp
  rw [hM]
  change regR12CoordCLM i
      (regR12WeightedField (regR12CoordSymbol j) (regR12LiftFreq T hT v t)
        (WithLp.toLp 2 x)) = _
  calc
    _ = regR12CoordCLM i
        ((regularisedBesselEvenOrderedDerivativeL2 2
          [WithLp.toLp 2 (basisVec j)] (by norm_num) (v ⟨t, ht⟩))
          (WithLp.toLp 2 x)) := congrArg (regR12CoordCLM i) hx
    _ = realPartVectorL2Representative
        (regularisedBesselEvenOrderedDerivativeL2 2
          [WithLp.toLp 2 (basisVec j)] (by norm_num) (v ⟨t, ht⟩)) x i :=
          regH1CoordinateRealPart _ x i

/-- The regularized velocity and its pointwise first derivatives are the
continuous physical L² paths of the Bessel lift, on the full closed interval.
This supplies the physical `H¹` trace at the initial time. -/
theorem lps_regularised_h1_trace
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (a : Vec3 → Vec3) (ha : CKN.IsInJ a) (T : ℝ) (hT : 0 ≤ T) :
    ∃ U : C(RegularizedMildTimeInterval T, RealVectorL2),
      ∃ DU : Fin 3 → C(RegularizedMildTimeInterval T, RealVectorL2),
        (∀ s : RegularizedMildTimeInterval T,
          (fun x : Vec3 => regR12Velocity ρ ε hε a ha (x, s.1)) =ᵐ[volume]
            realVectorL2Representative (U s)) ∧
        ∀ s : RegularizedMildTimeInterval T, ∀ i j : Fin 3,
          (fun x : Vec3 => spatialPartial
            (fun y : ParabolicPoint => regR12Velocity ρ ε hε a ha y i)
            j (x, s.1)) =ᵐ[volume]
              fun x => realVectorL2Representative (DU j s) x i := by
  obtain ⟨v, hv, hCU, hCD⟩ :=
    regularisedH1Path ρ ε hε a ha T hT
  let U : C(RegularizedMildTimeInterval T, RealVectorL2) :=
    ⟨fun s => realPartVectorL2
        (regularisedBesselSobolevToL2CLM ((2 * 2 : ℕ) : ℝ)
          (by norm_num) (v s)), by
        simpa only [regularisedBesselSobolevToL2CLM_apply] using hCU⟩
  let DU : Fin 3 → C(RegularizedMildTimeInterval T, RealVectorL2) := fun j =>
    ⟨fun s => realPartVectorL2
      (regularisedBesselEvenOrderedDerivativeL2 2
        [WithLp.toLp 2 (basisVec j)] (by norm_num) (v s)), hCD j⟩
  refine ⟨U, DU, ?_, ?_⟩
  · intro s
    have hcurve : U s = regR12Curve ρ ε hε a ha s.1 := by
      change realPartVectorL2
        (regularisedBesselSobolevToL2CLM ((2 * 2 : ℕ) : ℝ)
          (by norm_num) (v s)) = _
      rw [hv s]
      exact realPartVectorL2_complexifyVectorL2 _
    calc
      (fun x : Vec3 => regR12Velocity ρ ε hε a ha (x, s.1)) =ᵐ[volume]
          realVectorL2Representative (regR12Curve ρ ε hε a ha s.1) :=
            regR12Velocity_slice_ae_eq ρ ε hε a ha T hT v hv s.1 s.2
      _ =ᵐ[volume] realVectorL2Representative (U s) := by rw [← hcurve]
  · intro s i j
    have hpoint := regH1Derivative_pointwise_ae ρ ε hε a ha T hT v hv
      s.1 s.2 i j
    have hreal := realPartVectorL2Representative_eq_ae
      (regularisedBesselEvenOrderedDerivativeL2 2
        [WithLp.toLp 2 (basisVec j)] (by norm_num) (v s))
    calc
      (fun x : Vec3 => spatialPartial
        (fun y : ParabolicPoint => regR12Velocity ρ ε hε a ha y i)
        j (x, s.1)) =ᵐ[volume]
          (fun x => realPartVectorL2Representative
            (regularisedBesselEvenOrderedDerivativeL2 2
              [WithLp.toLp 2 (basisVec j)] (by norm_num) (v s)) x i) := hpoint
      _ =ᵐ[volume] fun x => realVectorL2Representative (DU j s) x i := by
            filter_upwards [hreal.symm] with x hx
            exact congrArg (fun w : Vec3 => w i) hx

/-- The physical squared `H¹` energy of the regularized path is continuous on
the closed time interval, including its initial trace (`prop:lps-local-strong`). -/
theorem lps_regularised_h1_energy_continuous
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (a : Vec3 → Vec3) (ha : CKN.IsInJ a) (T : ℝ) (hT : 0 ≤ T) :
    ∃ U : C(RegularizedMildTimeInterval T, RealVectorL2),
      ∃ DU : Fin 3 → C(RegularizedMildTimeInterval T, RealVectorL2),
        (∀ s : RegularizedMildTimeInterval T,
          (fun x : Vec3 => regR12Velocity ρ ε hε a ha (x, s.1)) =ᵐ[volume]
            realVectorL2Representative (U s)) ∧
        (∀ s : RegularizedMildTimeInterval T, ∀ i j : Fin 3,
          (fun x : Vec3 => spatialPartial
            (fun y : ParabolicPoint => regR12Velocity ρ ε hε a ha y i)
            j (x, s.1)) =ᵐ[volume]
              fun x => realVectorL2Representative (DU j s) x i) ∧
        Continuous (fun s : RegularizedMildTimeInterval T =>
          ‖U s‖ ^ (2 : ℕ) + ∑ j : Fin 3, ‖DU j s‖ ^ (2 : ℕ)) := by
  obtain ⟨U, DU, hU, hDU⟩ := lps_regularised_h1_trace ρ ε hε a ha T hT
  refine ⟨U, DU, hU, hDU, ?_⟩
  have hUenergy : Continuous (fun s : RegularizedMildTimeInterval T =>
      ‖U s‖ ^ (2 : ℕ)) := (continuous_norm.comp U.continuous).pow 2
  have hDUenergy : ∀ j : Fin 3, Continuous (fun s :
      RegularizedMildTimeInterval T => ‖DU j s‖ ^ (2 : ℕ)) := fun j =>
    (continuous_norm.comp (DU j).continuous).pow 2
  exact hUenergy.add (continuous_finsetSum Finset.univ fun j _ => hDUenergy j)

end ESS.LPS

end
