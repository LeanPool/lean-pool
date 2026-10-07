/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierRealification
public import Mathlib.Analysis.FunctionalSpaces.BesselPotentialSpace

/-!
# Sobolev data as spatial L² fields

The bundled Bessel potential space is complete. At nonnegative order its
inverse Fourier multiplier yields a spatial L² field with norm bounded by
the Sobolev norm.
-/

public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform SchwartzMap

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- The inverse Bessel-potential symbol acting on a complex Fourier vector. -/
@[expose]
def regularisedBesselInverseSymbol
    (s : ℝ) (p : L2Vec3 × ComplexVec3) : ComplexVec3 :=
  (((1 + ‖p.1‖ ^ 2) ^ (-s / 2) : ℝ) : ℂ) • p.2

theorem regularisedBesselInverseSymbol_measurable (s : ℝ) :
    Measurable (regularisedBesselInverseSymbol s) := by
  unfold regularisedBesselInverseSymbol
  fun_prop

theorem regularisedBesselInverseSymbol_norm_le
    (s : ℝ) (hs : 0 ≤ s) (ξ : L2Vec3) (v : ComplexVec3) :
    ‖regularisedBesselInverseSymbol s (ξ, v)‖ ≤ ‖v‖ := by
  have hbase : 1 ≤ (1 + ‖ξ‖ ^ 2 : ℝ) := by
    have hsq : 0 ≤ ‖ξ‖ ^ 2 := sq_nonneg _
    linarith only [hsq]
  have hexp : -s / 2 ≤ 0 := by linarith only [hs]
  have hweight : (1 + ‖ξ‖ ^ 2) ^ (-s / 2) ≤ (1 : ℝ) :=
    Real.rpow_le_one_of_one_le_of_nonpos hbase hexp
  unfold regularisedBesselInverseSymbol
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  exact (mul_le_mul_of_nonneg_right hweight (norm_nonneg v)).trans_eq (one_mul _)

/-- The bounded Fourier multiplier implementing the inverse Bessel weight on vector-valued
fields. -/
@[expose]
def regularisedBesselFourierMultiplier
    (s : ℝ) (hs : 0 ≤ s) (F : ComplexVectorL2) : ComplexVectorL2 :=
  measurableFourierMultiplier
    (regularisedBesselInverseSymbol s)
    (regularisedBesselInverseSymbol_measurable s)
    1
    (fun ξ v => by simpa only [one_mul] using
      regularisedBesselInverseSymbol_norm_le s hs ξ v)
    F

theorem regularisedBesselFourierMultiplier_add
    (s : ℝ) (hs : 0 ≤ s) (F G : ComplexVectorL2) :
    regularisedBesselFourierMultiplier s hs (F + G) =
      regularisedBesselFourierMultiplier s hs F +
        regularisedBesselFourierMultiplier s hs G := by
  apply Lp.ext
  filter_upwards [
    measurableFourierMultiplier_ae_eq
      (regularisedBesselInverseSymbol s)
      (regularisedBesselInverseSymbol_measurable s) 1
      (fun ξ v => by simpa only [one_mul] using
        regularisedBesselInverseSymbol_norm_le s hs ξ v) (F + G),
    measurableFourierMultiplier_ae_eq
      (regularisedBesselInverseSymbol s)
      (regularisedBesselInverseSymbol_measurable s) 1
      (fun ξ v => by simpa only [one_mul] using
        regularisedBesselInverseSymbol_norm_le s hs ξ v) F,
    measurableFourierMultiplier_ae_eq
      (regularisedBesselInverseSymbol s)
      (regularisedBesselInverseSymbol_measurable s) 1
      (fun ξ v => by simpa only [one_mul] using
        regularisedBesselInverseSymbol_norm_le s hs ξ v) G,
    Lp.coeFn_add F G,
    Lp.coeFn_add
      (regularisedBesselFourierMultiplier s hs F)
      (regularisedBesselFourierMultiplier s hs G)]
      with ξ hsum hF hG hFG hOut
  change regularisedBesselFourierMultiplier s hs (F + G) ξ =
    regularisedBesselInverseSymbol s (ξ, (F + G) ξ) at hsum
  change regularisedBesselFourierMultiplier s hs F ξ =
    regularisedBesselInverseSymbol s (ξ, F ξ) at hF
  change regularisedBesselFourierMultiplier s hs G ξ =
    regularisedBesselInverseSymbol s (ξ, G ξ) at hG
  calc
    regularisedBesselFourierMultiplier s hs (F + G) ξ =
        regularisedBesselInverseSymbol s (ξ, (F + G) ξ) := hsum
    _ = regularisedBesselInverseSymbol s (ξ, F ξ) +
        regularisedBesselInverseSymbol s (ξ, G ξ) := by
          rw [hFG]
          simp only [Pi.add_apply, regularisedBesselInverseSymbol, smul_add]
    _ = regularisedBesselFourierMultiplier s hs F ξ +
        regularisedBesselFourierMultiplier s hs G ξ := by rw [hF, hG]
    _ = (regularisedBesselFourierMultiplier s hs F +
        regularisedBesselFourierMultiplier s hs G) ξ := hOut.symm

theorem regularisedBesselFourierMultiplier_smul
    (s : ℝ) (hs : 0 ≤ s) (c : ℂ) (F : ComplexVectorL2) :
    regularisedBesselFourierMultiplier s hs (c • F) =
      c • regularisedBesselFourierMultiplier s hs F := by
  apply Lp.ext
  filter_upwards [
    measurableFourierMultiplier_ae_eq
      (regularisedBesselInverseSymbol s)
      (regularisedBesselInverseSymbol_measurable s) 1
      (fun ξ v => by simpa only [one_mul] using
        regularisedBesselInverseSymbol_norm_le s hs ξ v) (c • F),
    measurableFourierMultiplier_ae_eq
      (regularisedBesselInverseSymbol s)
      (regularisedBesselInverseSymbol_measurable s) 1
      (fun ξ v => by simpa only [one_mul] using
        regularisedBesselInverseSymbol_norm_le s hs ξ v) F,
    Lp.coeFn_smul c F,
    Lp.coeFn_smul c (regularisedBesselFourierMultiplier s hs F)]
      with ξ hsmul hF hInput hOut
  change regularisedBesselFourierMultiplier s hs (c • F) ξ =
    regularisedBesselInverseSymbol s (ξ, (c • F) ξ) at hsmul
  change regularisedBesselFourierMultiplier s hs F ξ =
    regularisedBesselInverseSymbol s (ξ, F ξ) at hF
  calc
    regularisedBesselFourierMultiplier s hs (c • F) ξ =
        regularisedBesselInverseSymbol s (ξ, (c • F) ξ) := hsmul
    _ = c • regularisedBesselInverseSymbol s (ξ, F ξ) := by
          rw [hInput]
          simp only [Pi.smul_apply, regularisedBesselInverseSymbol]
          exact smul_comm _ _ _
    _ = c • regularisedBesselFourierMultiplier s hs F ξ := by rw [hF]
    _ = (c • regularisedBesselFourierMultiplier s hs F) ξ := hOut.symm

/-- A nonnegative-order Bessel potential field determines a complex spatial
L² field by applying the inverse Bessel weight in Fourier space. -/
@[expose]
def regularisedBesselSobolevToL2
    (s : ℝ) (hs : 0 ≤ s)
    (f : BesselPotentialSpace L2Vec3 ComplexVec3 s 2) :
    ComplexVectorL2 :=
  (MeasureTheory.Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3).symm
  (regularisedBesselFourierMultiplier s hs
      ((MeasureTheory.Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3) f.toLp))

/-- The Fourier transform of the physical L² realization is the inverse
Bessel scalar weight times the weighted L² Fourier coordinate. -/
theorem regularisedBesselSobolevToL2_fourier_ae
    (s : ℝ) (hs : 0 ≤ s)
    (f : BesselPotentialSpace L2Vec3 ComplexVec3 s 2) :
    (fun ξ : L2Vec3 =>
      (MeasureTheory.Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3)
        (regularisedBesselSobolevToL2 s hs f) ξ) =ᵐ[volume]
      (fun ξ : L2Vec3 =>
        (((1 + ‖ξ‖ ^ 2) ^ (-s / 2) : ℝ) : ℂ) •
          (MeasureTheory.Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3)
            f.toLp ξ) := by
  let ℱ := MeasureTheory.Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3
  change (fun ξ => ℱ (ℱ.symm
      (regularisedBesselFourierMultiplier s hs (ℱ f.toLp))) ξ)
    =ᵐ[volume] fun ξ => regularisedBesselInverseSymbol s
      (ξ, ℱ f.toLp ξ)
  rw [ℱ.apply_symm_apply]
  exact measurableFourierMultiplier_ae_eq
    (regularisedBesselInverseSymbol s)
    (regularisedBesselInverseSymbol_measurable s) 1
    (fun ξ v => by simpa only [one_mul] using
      regularisedBesselInverseSymbol_norm_le s hs ξ v)
    (ℱ f.toLp)

/-- The underlying spatial L² norm is at most the Bessel-potential
Sobolev norm at every nonnegative order. -/
theorem regularisedBesselSobolevToL2_norm_le
    (s : ℝ) (hs : 0 ≤ s)
    (f : BesselPotentialSpace L2Vec3 ComplexVec3 s 2) :
    ‖regularisedBesselSobolevToL2 s hs f‖ ≤ ‖f‖ := by
  let ℱ := MeasureTheory.Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3
  change ‖ℱ.symm (regularisedBesselFourierMultiplier s hs
      (ℱ f.toLp))‖ ≤ ‖f‖
  rw [ℱ.symm.norm_map]
  calc
    ‖regularisedBesselFourierMultiplier s hs (ℱ f.toLp)‖
      ≤ 1 * ‖ℱ f.toLp‖ := by
        exact measurableFourierMultiplier_norm_le _ _ _ _ _
    _ = ‖f‖ := by rw [one_mul, ℱ.norm_map, BesselPotentialSpace.norm_toLp_eq]

/-- The nonnegative-order Bessel potential space embeds continuously into
the complex spatial L² space through its inverse Fourier weight. -/
@[expose]
def regularisedBesselSobolevToL2CLM
    (s : ℝ) (hs : 0 ≤ s) :
    BesselPotentialSpace L2Vec3 ComplexVec3 s 2 →L[ℂ]
      ComplexVectorL2 := by
  let L : BesselPotentialSpace L2Vec3 ComplexVec3 s 2 →ₗ[ℂ]
      ComplexVectorL2 := {
    toFun := regularisedBesselSobolevToL2 s hs
    map_add' := by
      intro f g
      simp only [regularisedBesselSobolevToL2,
        BesselPotentialSpace.toLp_add, map_add,
        regularisedBesselFourierMultiplier_add]
    map_smul' := by
      intro c f
      simp only [regularisedBesselSobolevToL2,
        BesselPotentialSpace.toLp_smul, map_smul,
        regularisedBesselFourierMultiplier_smul]
      rfl
  }
  exact L.mkContinuous 1 (by
    intro f
    change ‖regularisedBesselSobolevToL2 s hs f‖ ≤
      1 * ‖f‖
    simpa only [one_mul] using
      regularisedBesselSobolevToL2_norm_le s hs f)

@[simp]
theorem regularisedBesselSobolevToL2CLM_apply
    (s : ℝ) (hs : 0 ≤ s)
    (f : BesselPotentialSpace L2Vec3 ComplexVec3 s 2) :
    regularisedBesselSobolevToL2CLM s hs f =
      regularisedBesselSobolevToL2 s hs f := rfl

/-- The scalar Fourier weight defining the inverse Bessel-potential operator. -/
@[expose]
def regularisedBesselInverseWeight (s : ℝ) (ξ : L2Vec3) : ℂ :=
  (((1 + ‖ξ‖ ^ 2) ^ (-s / 2) : ℝ) : ℂ)

private theorem regularisedBesselInverseWeight_continuous (s : ℝ) :
    Continuous (regularisedBesselInverseWeight s) := by
  have hbase : Continuous (fun ξ : L2Vec3 => (1 + ‖ξ‖ ^ 2 : ℝ)) := by
    fun_prop
  have hpow : Continuous (fun ξ : L2Vec3 =>
      (1 + ‖ξ‖ ^ 2 : ℝ) ^ (-s / 2)) := by
    apply continuous_iff_continuousAt.mpr
    intro ξ
    exact (Real.continuousAt_rpow_const _ _
      (Or.inl (by positivity))).comp hbase.continuousAt
  exact Complex.continuous_ofReal.comp hpow

theorem regularisedBesselInverseWeight_memLp
    (s : ℝ) (hs : 0 ≤ s) :
    MemLp (regularisedBesselInverseWeight s) ∞ volume := by
  apply memLp_top_of_bound
    (regularisedBesselInverseWeight_continuous s).aestronglyMeasurable 1
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

/-- The `L∞` representative of the inverse Bessel Fourier weight. -/
@[expose]
def regularisedBesselInverseWeightLp
    (s : ℝ) (hs : 0 ≤ s) : Lp (α := L2Vec3) ℂ ∞ :=
  (regularisedBesselInverseWeight_memLp s hs).toLp
    (regularisedBesselInverseWeight s)

private theorem regularisedBesselInverseWeightLp_ae_eq
    (s : ℝ) (hs : 0 ≤ s) :
    (fun ξ : L2Vec3 => regularisedBesselInverseWeightLp s hs ξ) =ᵐ[volume]
      regularisedBesselInverseWeight s :=
  (regularisedBesselInverseWeight_memLp s hs).coeFn_toLp

private theorem regularisedBesselFourierMultiplier_eq_smul
    (s : ℝ) (hs : 0 ≤ s) (F : ComplexVectorL2) :
    regularisedBesselFourierMultiplier s hs F =
      regularisedBesselInverseWeightLp s hs • F := by
  apply Lp.ext
  filter_upwards [
    measurableFourierMultiplier_ae_eq
      (regularisedBesselInverseSymbol s)
      (regularisedBesselInverseSymbol_measurable s) 1
      (fun ξ v => by simpa only [one_mul] using
        regularisedBesselInverseSymbol_norm_le s hs ξ v) F,
    regularisedBesselInverseWeightLp_ae_eq s hs,
    Lp.coeFn_lpSMul (r := 2)
      (regularisedBesselInverseWeightLp s hs) F]
      with ξ hM hW hS
  change regularisedBesselFourierMultiplier s hs F ξ =
    regularisedBesselInverseSymbol s (ξ, F ξ) at hM
  calc
    regularisedBesselFourierMultiplier s hs F ξ =
        regularisedBesselInverseSymbol s (ξ, F ξ) := hM
    _ = regularisedBesselInverseWeight s ξ • F ξ := rfl
    _ = regularisedBesselInverseWeightLp s hs ξ • F ξ := by rw [hW]
    _ = (regularisedBesselInverseWeightLp s hs • F) ξ := hS.symm

/-- The inverse-weight L² field represents the underlying Bessel-potential
tempered distribution. -/
theorem regularisedBesselSobolevToL2_toTemperedDistribution_eq
    (s : ℝ) (hs : 0 ≤ s)
    (f : BesselPotentialSpace L2Vec3 ComplexVec3 s 2) :
    ((regularisedBesselSobolevToL2 s hs f : ComplexVectorL2) :
      𝓢'(L2Vec3, ComplexVec3)) = f.toDistr := by
  let ℱ := MeasureTheory.Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3
  have hweightTemperate :
      (regularisedBesselInverseWeight s).HasTemperateGrowth := by
    unfold regularisedBesselInverseWeight
    fun_prop
  have hsmul := MeasureTheory.Lp.toTemperedDistribution_smul_eq
    (p := ∞) (q := 2) (r := 2)
    hweightTemperate (regularisedBesselInverseWeight_memLp s hs)
    (ℱ f.toLp)
  have hFourier :
      𝓕 (((regularisedBesselSobolevToL2 s hs f : ComplexVectorL2) :
        𝓢'(L2Vec3, ComplexVec3))) = 𝓕 f.toDistr := by
    have hleft : 𝓕 (((regularisedBesselSobolevToL2 s hs f :
        ComplexVectorL2) : 𝓢'(L2Vec3, ComplexVec3))) =
        ((regularisedBesselFourierMultiplier s hs (ℱ f.toLp) :
          ComplexVectorL2) : 𝓢'(L2Vec3, ComplexVec3)) := by
      rw [MeasureTheory.Lp.fourier_toTemperedDistribution_eq]
      change ((ℱ (ℱ.symm (regularisedBesselFourierMultiplier s hs
        (ℱ f.toLp))) : ComplexVectorL2) :
        𝓢'(L2Vec3, ComplexVec3)) = _
      rw [ℱ.apply_symm_apply]
    have hright : 𝓕 f.toDistr =
        TemperedDistribution.smulLeftCLM ComplexVec3
          (regularisedBesselInverseWeight s)
          ((ℱ f.toLp : ComplexVectorL2) :
            𝓢'(L2Vec3, ComplexVec3)) := by
      have hbase : f.toDistr =
          TemperedDistribution.besselPotential L2Vec3 ComplexVec3
            (-s) f.toLp := by
        exact (BesselPotentialSpace.besselPotential_neg_toLp_eq (f := f)).symm
      rw [hbase,
        TemperedDistribution.fourier_besselPotential_eq_smulLeftCLM_fourier_apply,
        MeasureTheory.Lp.fourier_toTemperedDistribution_eq]
      rfl
    rw [hleft, hright, regularisedBesselFourierMultiplier_eq_smul]
    exact hsmul
  have h' := congrArg
    (fun D : 𝓢'(L2Vec3, ComplexVec3) => 𝓕⁻ D) hFourier
  simpa only [fourierInv_fourier_eq] using h'

end CKN.Leray

end
