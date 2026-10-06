/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedTensorBesselSchwartz
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselEmbedding

/-!
# Tensor Bessel-potential fields as spatial L² fields

At nonnegative order, the inverse tensor Bessel multiplier realizes a complete
Bessel-potential field as a spatial L² tensor. The realization agrees with the
canonical lift of every Schwartz tensor.
-/

public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform SchwartzMap

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

@[expose]
def regularisedTensorBesselInverseSymbol
    (s : ℝ) (p : L2Vec3 × ComplexTensor3) : ComplexTensor3 :=
  (((1 + ‖p.1‖ ^ 2) ^ (-s / 2) : ℝ) : ℂ) • p.2

theorem regularisedTensorBesselInverseSymbol_measurable (s : ℝ) :
    Measurable (regularisedTensorBesselInverseSymbol s) := by
  unfold regularisedTensorBesselInverseSymbol
  fun_prop

theorem regularisedTensorBesselInverseSymbol_norm_le
    (s : ℝ) (hs : 0 ≤ s) (ξ : L2Vec3) (v : ComplexTensor3) :
    ‖regularisedTensorBesselInverseSymbol s (ξ, v)‖ ≤ ‖v‖ := by
  have hbase : 1 ≤ (1 + ‖ξ‖ ^ 2 : ℝ) := by
    have hsq : 0 ≤ ‖ξ‖ ^ 2 := sq_nonneg _
    linarith only [hsq]
  have hexp : -s / 2 ≤ 0 := by linarith only [hs]
  have hweight : (1 + ‖ξ‖ ^ 2) ^ (-s / 2) ≤ (1 : ℝ) :=
    Real.rpow_le_one_of_one_le_of_nonpos hbase hexp
  unfold regularisedTensorBesselInverseSymbol
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  exact (mul_le_mul_of_nonneg_right hweight (norm_nonneg v)).trans_eq (one_mul _)

@[expose]
def regularisedTensorBesselFourierMultiplier
    (s : ℝ) (hs : 0 ≤ s) (F : ComplexTensorL2) : ComplexTensorL2 :=
  measurableFourierMultiplier
    (regularisedTensorBesselInverseSymbol s)
    (regularisedTensorBesselInverseSymbol_measurable s)
    1
    (fun ξ v => by simpa only [one_mul] using
      regularisedTensorBesselInverseSymbol_norm_le s hs ξ v)
    F

theorem regularisedTensorBesselFourierMultiplier_add
    (s : ℝ) (hs : 0 ≤ s) (F G : ComplexTensorL2) :
    regularisedTensorBesselFourierMultiplier s hs (F + G) =
      regularisedTensorBesselFourierMultiplier s hs F +
        regularisedTensorBesselFourierMultiplier s hs G := by
  apply Lp.ext
  filter_upwards [
    measurableFourierMultiplier_ae_eq
      (regularisedTensorBesselInverseSymbol s)
      (regularisedTensorBesselInverseSymbol_measurable s) 1
      (fun ξ v => by simpa only [one_mul] using
        regularisedTensorBesselInverseSymbol_norm_le s hs ξ v) (F + G),
    measurableFourierMultiplier_ae_eq
      (regularisedTensorBesselInverseSymbol s)
      (regularisedTensorBesselInverseSymbol_measurable s) 1
      (fun ξ v => by simpa only [one_mul] using
        regularisedTensorBesselInverseSymbol_norm_le s hs ξ v) F,
    measurableFourierMultiplier_ae_eq
      (regularisedTensorBesselInverseSymbol s)
      (regularisedTensorBesselInverseSymbol_measurable s) 1
      (fun ξ v => by simpa only [one_mul] using
        regularisedTensorBesselInverseSymbol_norm_le s hs ξ v) G,
    Lp.coeFn_add F G,
    Lp.coeFn_add
      (regularisedTensorBesselFourierMultiplier s hs F)
      (regularisedTensorBesselFourierMultiplier s hs G)]
      with ξ hsum hF hG hFG hOut
  change regularisedTensorBesselFourierMultiplier s hs (F + G) ξ =
    regularisedTensorBesselInverseSymbol s (ξ, (F + G) ξ) at hsum
  change regularisedTensorBesselFourierMultiplier s hs F ξ =
    regularisedTensorBesselInverseSymbol s (ξ, F ξ) at hF
  change regularisedTensorBesselFourierMultiplier s hs G ξ =
    regularisedTensorBesselInverseSymbol s (ξ, G ξ) at hG
  calc
    regularisedTensorBesselFourierMultiplier s hs (F + G) ξ =
        regularisedTensorBesselInverseSymbol s (ξ, (F + G) ξ) := hsum
    _ = regularisedTensorBesselInverseSymbol s (ξ, F ξ) +
        regularisedTensorBesselInverseSymbol s (ξ, G ξ) := by
          rw [hFG]
          simp only [Pi.add_apply, regularisedTensorBesselInverseSymbol, smul_add]
    _ = regularisedTensorBesselFourierMultiplier s hs F ξ +
        regularisedTensorBesselFourierMultiplier s hs G ξ := by rw [hF, hG]
    _ = (regularisedTensorBesselFourierMultiplier s hs F +
        regularisedTensorBesselFourierMultiplier s hs G) ξ := hOut.symm

theorem regularisedTensorBesselFourierMultiplier_smul
    (s : ℝ) (hs : 0 ≤ s) (c : ℂ) (F : ComplexTensorL2) :
    regularisedTensorBesselFourierMultiplier s hs (c • F) =
      c • regularisedTensorBesselFourierMultiplier s hs F := by
  apply Lp.ext
  filter_upwards [
    measurableFourierMultiplier_ae_eq
      (regularisedTensorBesselInverseSymbol s)
      (regularisedTensorBesselInverseSymbol_measurable s) 1
      (fun ξ v => by simpa only [one_mul] using
        regularisedTensorBesselInverseSymbol_norm_le s hs ξ v) (c • F),
    measurableFourierMultiplier_ae_eq
      (regularisedTensorBesselInverseSymbol s)
      (regularisedTensorBesselInverseSymbol_measurable s) 1
      (fun ξ v => by simpa only [one_mul] using
        regularisedTensorBesselInverseSymbol_norm_le s hs ξ v) F,
    Lp.coeFn_smul c F,
    Lp.coeFn_smul c (regularisedTensorBesselFourierMultiplier s hs F)]
      with ξ hsmul hF hInput hOut
  change regularisedTensorBesselFourierMultiplier s hs (c • F) ξ =
    regularisedTensorBesselInverseSymbol s (ξ, (c • F) ξ) at hsmul
  change regularisedTensorBesselFourierMultiplier s hs F ξ =
    regularisedTensorBesselInverseSymbol s (ξ, F ξ) at hF
  calc
    regularisedTensorBesselFourierMultiplier s hs (c • F) ξ =
        regularisedTensorBesselInverseSymbol s (ξ, (c • F) ξ) := hsmul
    _ = c • regularisedTensorBesselInverseSymbol s (ξ, F ξ) := by
          rw [hInput]
          simp only [Pi.smul_apply, regularisedTensorBesselInverseSymbol]
          exact smul_comm _ _ _
    _ = c • regularisedTensorBesselFourierMultiplier s hs F ξ := by rw [hF]
    _ = (c • regularisedTensorBesselFourierMultiplier s hs F) ξ := hOut.symm

@[expose]
def regularisedTensorBesselSobolevToL2Fun
    (s : ℝ) (hs : 0 ≤ s)
    (F : BesselPotentialSpace L2Vec3 ComplexTensor3 s 2) : ComplexTensorL2 :=
  (MeasureTheory.Lp.fourierTransformₗᵢ L2Vec3 ComplexTensor3).symm
    (regularisedTensorBesselFourierMultiplier s hs
      ((MeasureTheory.Lp.fourierTransformₗᵢ L2Vec3 ComplexTensor3) F.toLp))

theorem regularisedTensorBesselSobolevToL2_norm_le_fun
    (s : ℝ) (hs : 0 ≤ s)
    (F : BesselPotentialSpace L2Vec3 ComplexTensor3 s 2) :
    ‖regularisedTensorBesselSobolevToL2Fun s hs F‖ ≤ ‖F‖ := by
  let ℱ := MeasureTheory.Lp.fourierTransformₗᵢ L2Vec3 ComplexTensor3
  change ‖ℱ.symm (regularisedTensorBesselFourierMultiplier s hs
      (ℱ F.toLp))‖ ≤ ‖F‖
  rw [ℱ.symm.norm_map]
  calc
    ‖regularisedTensorBesselFourierMultiplier s hs (ℱ F.toLp)‖
      ≤ 1 * ‖ℱ F.toLp‖ := by
        exact measurableFourierMultiplier_norm_le _ _ _ _ _
    _ = ‖F‖ := by rw [one_mul, ℱ.norm_map, BesselPotentialSpace.norm_toLp_eq]

/-- A nonnegative-order tensor Bessel-potential field determines its spatial
L² representative by the inverse Bessel weight in Fourier space. -/
@[expose]
def regularisedTensorBesselSobolevToL2
    (s : ℝ) (hs : 0 ≤ s) :
    BesselPotentialSpace L2Vec3 ComplexTensor3 s 2 →L[ℂ] ComplexTensorL2 := by
  let L : BesselPotentialSpace L2Vec3 ComplexTensor3 s 2 →ₗ[ℂ] ComplexTensorL2 := {
    toFun := regularisedTensorBesselSobolevToL2Fun s hs
    map_add' := by
      intro F G
      simp only [regularisedTensorBesselSobolevToL2Fun,
        BesselPotentialSpace.toLp_add, map_add,
        regularisedTensorBesselFourierMultiplier_add]
    map_smul' := by
      intro c F
      simp only [regularisedTensorBesselSobolevToL2Fun,
        BesselPotentialSpace.toLp_smul, map_smul,
        regularisedTensorBesselFourierMultiplier_smul]
      rfl
  }
  exact L.mkContinuous 1 (by
    intro F
    change ‖regularisedTensorBesselSobolevToL2Fun s hs F‖ ≤ 1 * ‖F‖
    simpa only [one_mul] using
      regularisedTensorBesselSobolevToL2_norm_le_fun s hs F)


@[expose]
def regularisedTensorBesselInverseWeight (s : ℝ) (ξ : L2Vec3) : ℂ :=
  (((1 + ‖ξ‖ ^ 2) ^ (-s / 2) : ℝ) : ℂ)

private theorem regularisedTensorBesselInverseWeight_continuous (s : ℝ) :
    Continuous (regularisedTensorBesselInverseWeight s) := by
  have hbase : Continuous (fun ξ : L2Vec3 => (1 + ‖ξ‖ ^ 2 : ℝ)) := by
    fun_prop
  have hpow : Continuous (fun ξ : L2Vec3 =>
      (1 + ‖ξ‖ ^ 2 : ℝ) ^ (-s / 2)) := by
    apply continuous_iff_continuousAt.mpr
    intro ξ
    exact (Real.continuousAt_rpow_const _ _
      (Or.inl (by positivity))).comp hbase.continuousAt
  exact Complex.continuous_ofReal.comp hpow

theorem regularisedTensorBesselInverseWeight_memLp
    (s : ℝ) (hs : 0 ≤ s) :
    MemLp (regularisedTensorBesselInverseWeight s) ∞ volume := by
  apply memLp_top_of_bound
    (regularisedTensorBesselInverseWeight_continuous s).aestronglyMeasurable 1
  filter_upwards [] with ξ
  have hbase : 1 ≤ (1 + ‖ξ‖ ^ 2 : ℝ) := by
    have hsq : 0 ≤ ‖ξ‖ ^ 2 := sq_nonneg _
    linarith only [hsq]
  have hexp : -s / 2 ≤ 0 := by linarith only [hs]
  have hbound := Real.rpow_le_one_of_one_le_of_nonpos hbase hexp
  change ‖(((1 + ‖ξ‖ ^ 2) ^ (-s / 2) : ℝ) : ℂ)‖ ≤ 1
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  exact hbound

@[expose]
def regularisedTensorBesselInverseWeightLp
    (s : ℝ) (hs : 0 ≤ s) : Lp (α := L2Vec3) ℂ ∞ :=
  (regularisedTensorBesselInverseWeight_memLp s hs).toLp
    (regularisedTensorBesselInverseWeight s)

private theorem regularisedTensorBesselInverseWeightLp_ae_eq
    (s : ℝ) (hs : 0 ≤ s) :
    (fun ξ : L2Vec3 => regularisedTensorBesselInverseWeightLp s hs ξ) =ᵐ[volume]
      regularisedTensorBesselInverseWeight s :=
  (regularisedTensorBesselInverseWeight_memLp s hs).coeFn_toLp

private theorem regularisedTensorBesselFourierMultiplier_eq_smul
    (s : ℝ) (hs : 0 ≤ s) (F : ComplexTensorL2) :
    regularisedTensorBesselFourierMultiplier s hs F =
      regularisedTensorBesselInverseWeightLp s hs • F := by
  apply Lp.ext
  filter_upwards [
    measurableFourierMultiplier_ae_eq
      (regularisedTensorBesselInverseSymbol s)
      (regularisedTensorBesselInverseSymbol_measurable s) 1
      (fun ξ v => by simpa only [one_mul] using
        regularisedTensorBesselInverseSymbol_norm_le s hs ξ v) F,
    regularisedTensorBesselInverseWeightLp_ae_eq s hs,
    Lp.coeFn_lpSMul (r := 2)
      (regularisedTensorBesselInverseWeightLp s hs) F]
      with ξ hM hW hS
  change regularisedTensorBesselFourierMultiplier s hs F ξ =
    regularisedTensorBesselInverseSymbol s (ξ, F ξ) at hM
  calc
    regularisedTensorBesselFourierMultiplier s hs F ξ =
        regularisedTensorBesselInverseSymbol s (ξ, F ξ) := hM
    _ = regularisedTensorBesselInverseWeight s ξ • F ξ := rfl
    _ = regularisedTensorBesselInverseWeightLp s hs ξ • F ξ := by rw [hW]
    _ = (regularisedTensorBesselInverseWeightLp s hs • F) ξ := hS.symm

private theorem regularisedTensorBesselSobolevToL2_toTemperedDistribution_eq
    (s : ℝ) (hs : 0 ≤ s)
    (F : BesselPotentialSpace L2Vec3 ComplexTensor3 s 2) :
    ((regularisedTensorBesselSobolevToL2 s hs F : ComplexTensorL2) :
      𝓢'(L2Vec3, ComplexTensor3)) = F.toDistr := by
  let ℱ := MeasureTheory.Lp.fourierTransformₗᵢ L2Vec3 ComplexTensor3
  have hweightTemperate :
      (regularisedTensorBesselInverseWeight s).HasTemperateGrowth := by
    unfold regularisedTensorBesselInverseWeight
    fun_prop
  have hsmul := MeasureTheory.Lp.toTemperedDistribution_smul_eq
    (p := ∞) (q := 2) (r := 2)
    hweightTemperate (regularisedTensorBesselInverseWeight_memLp s hs)
    (ℱ F.toLp)
  have hFourier :
      𝓕 (((regularisedTensorBesselSobolevToL2 s hs F : ComplexTensorL2) :
        𝓢'(L2Vec3, ComplexTensor3))) = 𝓕 F.toDistr := by
    have hleft : 𝓕 (((regularisedTensorBesselSobolevToL2 s hs F :
        ComplexTensorL2) : 𝓢'(L2Vec3, ComplexTensor3))) =
        ((regularisedTensorBesselFourierMultiplier s hs (ℱ F.toLp) :
          ComplexTensorL2) : 𝓢'(L2Vec3, ComplexTensor3)) := by
      rw [MeasureTheory.Lp.fourier_toTemperedDistribution_eq]
      change ((ℱ (ℱ.symm (regularisedTensorBesselFourierMultiplier s hs
        (ℱ F.toLp))) : ComplexTensorL2) :
        𝓢'(L2Vec3, ComplexTensor3)) = _
      rw [ℱ.apply_symm_apply]
    have hright : 𝓕 F.toDistr =
        TemperedDistribution.smulLeftCLM ComplexTensor3
          (regularisedTensorBesselInverseWeight s)
          ((ℱ F.toLp : ComplexTensorL2) :
            𝓢'(L2Vec3, ComplexTensor3)) := by
      have hbase : F.toDistr =
          TemperedDistribution.besselPotential L2Vec3 ComplexTensor3
            (-s) F.toLp := by
        exact (BesselPotentialSpace.besselPotential_neg_toLp_eq (f := F)).symm
      rw [hbase,
        TemperedDistribution.fourier_besselPotential_eq_smulLeftCLM_fourier_apply,
        MeasureTheory.Lp.fourier_toTemperedDistribution_eq]
      rfl
    rw [hleft, hright, regularisedTensorBesselFourierMultiplier_eq_smul]
    exact hsmul
  have h' := congrArg
    (fun D : 𝓢'(L2Vec3, ComplexTensor3) => 𝓕⁻ D) hFourier
  simpa only [fourierInv_fourier_eq] using h'

/-- The inverse Bessel-weighted tensor L² field agrees with the canonical
Bessel lift of a Schwartz tensor. -/
theorem regularisedTensorBesselSobolevToL2_schwartz
    (s : ℝ) (hs : 0 ≤ s)
    (ψ : 𝓢(L2Vec3, ComplexTensor3)) :
    regularisedTensorBesselSobolevToL2 s hs
      (regularisedTensorBesselOfSchwartz s ψ) = ψ.toLp 2 := by
  apply (LinearMap.ker_eq_bot.mp
    (MeasureTheory.Lp.ker_toTemperedDistributionCLM_eq_bot
      (F := ComplexTensor3) (μ := volume) (p := 2)))
  exact (regularisedTensorBesselSobolevToL2_toTemperedDistribution_eq
    s hs (regularisedTensorBesselOfSchwartz s ψ)).trans
      ((regularisedTensorBesselOfSchwartz_toDistr s ψ).trans
        (Lp.toTemperedDistribution_toLp_eq ψ).symm)

end CKN.Leray

end
