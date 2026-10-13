/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Ported.WeakTesting
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Ported.HarmonicGradientSubmean
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.NormalizedL2

/-!
# NormalizedEnergy

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Normalized Euclidean energy calculus for the small-contrast iteration
-/

namespace Algsuperdiff.StochasticProcess.Common.Regularity.Ported

open MeasureTheory HCPolySupport
open Algsuperdiff.Section4.Support
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- Dictionary from the vector normalized energy to the Hilbert realization's
ordinary `L²` norm. -/
theorem vectorNormalizedL2On_eq_toReal_eLpNorm_div
    {W : Set (Vec d)} {F : Vec d → Vec d}
    (hF : MemVectorL2 W F) :
    vectorNormalizedL2On W F =
      (eLpNorm (fun x => HilbertVec.ofVec (F x)) 2 (volume.restrict W)).toReal /
        Real.sqrt ((volume W).toReal) := by
  have hHF : MemLp (fun x => HilbertVec.ofVec (F x)) 2 (volume.restrict W) :=
    memHilbertVectorL2_hilbertifyVecField hF
  have hnorm : MemLp (fun x => euclideanNorm (F x)) 2 (volume.restrict W) := by
    simpa only [euclideanNorm_eq_norm_ofVec] using hHF.norm
  unfold vectorNormalizedL2On
  rw [Algsuperdiff.Section4.Support.normalizedL2On_eq_toReal_eLpNorm_div
    hnorm]
  have hfun : (fun x => euclideanNorm (F x)) =
      fun x => ‖HilbertVec.ofVec (F x)‖ := by
    funext x
    exact euclideanNorm_eq_norm_ofVec (F x)
  rw [hfun, eLpNorm_norm _ hHF.aestronglyMeasurable]

/-- Raw and normalized Euclidean energies differ by the square root of the
window volume. -/
theorem sqrt_integral_vecNormSq_eq_sqrt_volume_mul_vectorNormalizedL2On
    {W : Set (Vec d)} {F : Vec d → Vec d}
    (hW : 0 < (volume W).toReal) (hF : MemVectorL2 W F) :
    Real.sqrt (∫ x in W, vecNormSq (F x) ∂volume) =
      Real.sqrt ((volume W).toReal) * vectorNormalizedL2On W F := by
  have hHF : MemLp (fun x => HilbertVec.ofVec (F x)) 2 (volume.restrict W) :=
    memHilbertVectorL2_hilbertifyVecField hF
  have hnorm : MemLp (fun x => euclideanNorm (F x)) 2 (volume.restrict W) := by
    simpa only [euclideanNorm_eq_norm_ofVec] using hHF.norm
  have hsq := HCPolySupport.toReal_eLpNorm_two_sq_eq_integral_sq hnorm
  have hnonneg : 0 ≤ (eLpNorm (fun x => euclideanNorm (F x)) 2
      (volume.restrict W)).toReal := ENNReal.toReal_nonneg
  have hsqrt : Real.sqrt (∫ x in W, vecNormSq (F x) ∂volume) =
      (eLpNorm (fun x => euclideanNorm (F x)) 2 (volume.restrict W)).toReal := by
    have hIntEq : (∫ x in W, vecNormSq (F x) ∂volume) =
        ∫ x in W, euclideanNorm (F x) ^ 2 ∂volume := by
      apply integral_congr_ae
      filter_upwards with x
      exact (euclideanNorm_sq (F x)).symm
    rw [hIntEq, ← hsq, Real.sqrt_sq hnonneg]
  rw [hsqrt, vectorNormalizedL2On_eq_toReal_eLpNorm_div hF]
  have hfun : (fun x => euclideanNorm (F x)) =
      fun x => ‖HilbertVec.ofVec (F x)‖ := by
    funext x
    exact euclideanNorm_eq_norm_ofVec _
  rw [hfun, eLpNorm_norm _ hHF.aestronglyMeasurable]
  field_simp [ne_of_gt (Real.sqrt_pos.2 hW)]

/-- Minkowski for normalized Euclidean vector energy. -/
theorem vectorNormalizedL2On_add_le
    {W : Set (Vec d)} {F G : Vec d → Vec d}
    (hF : MemVectorL2 W F) (hG : MemVectorL2 W G) :
    vectorNormalizedL2On W (fun x => F x + G x) ≤
      vectorNormalizedL2On W F + vectorNormalizedL2On W G := by
  have hHF : MemLp (fun x => HilbertVec.ofVec (F x)) 2 (volume.restrict W) :=
    memHilbertVectorL2_hilbertifyVecField hF
  have hHG : MemLp (fun x => HilbertVec.ofVec (G x)) 2 (volume.restrict W) :=
    memHilbertVectorL2_hilbertifyVecField hG
  have hsum : MemVectorL2 W (fun x => F x + G x) := hF.add hG
  have htri : eLpNorm (fun x => HilbertVec.ofVec (F x + G x)) 2
      (volume.restrict W) ≤
      eLpNorm (fun x => HilbertVec.ofVec (F x)) 2 (volume.restrict W) +
        eLpNorm (fun x => HilbertVec.ofVec (G x)) 2 (volume.restrict W) := by
    have heq : (fun x => HilbertVec.ofVec (F x + G x)) =
        (fun x => HilbertVec.ofVec (F x)) + fun x => HilbertVec.ofVec (G x) := by
      funext x
      exact (HilbertVec.ofVecL d).map_add (F x) (G x)
    rw [heq]
    exact eLpNorm_add_le one_le_two
  have hne : eLpNorm (fun x => HilbertVec.ofVec (F x)) 2 (volume.restrict W) +
      eLpNorm (fun x => HilbertVec.ofVec (G x)) 2 (volume.restrict W) ≠ ∞ :=
    ENNReal.add_ne_top.2 ⟨hHF.eLpNorm_lt_top.ne, hHG.eLpNorm_lt_top.ne⟩
  have hreal := ENNReal.toReal_mono hne htri
  rw [ENNReal.toReal_add hHF.eLpNorm_lt_top.ne hHG.eLpNorm_lt_top.ne] at hreal
  rw [vectorNormalizedL2On_eq_toReal_eLpNorm_div hsum,
    vectorNormalizedL2On_eq_toReal_eLpNorm_div hF,
    vectorNormalizedL2On_eq_toReal_eLpNorm_div hG, ← add_div]
  exact div_le_div_of_nonneg_right hreal (Real.sqrt_nonneg _)

/-- Triangle inequality in subtraction form. -/
theorem vectorNormalizedL2On_sub_le
    {W : Set (Vec d)} {F G : Vec d → Vec d}
    (hF : MemVectorL2 W F) (hG : MemVectorL2 W G) :
    vectorNormalizedL2On W (fun x => F x - G x) ≤
      vectorNormalizedL2On W F + vectorNormalizedL2On W G := by
  have h := vectorNormalizedL2On_add_le hF hG.neg
  simpa [sub_eq_add_neg, euclideanNorm_neg, vectorNormalizedL2On,
    normalizedL2On] using h

/-- Restriction of the normalized Euclidean vector L2 carrier. -/
theorem vectorNormalizedL2On_le_of_subset
    {W W' : Set (Vec d)} {f : Vec d → Vec d}
    (hsub : W' ⊆ W) (hWpos : 0 < (volume W).toReal)
    (hW'pos : 0 < (volume W').toReal)
    (hf : MemLp (fun x => HilbertVec.ofVec (f x)) 2 (volume.restrict W)) :
    vectorNormalizedL2On W' f ≤
      Real.sqrt ((volume W).toReal / (volume W').toReal) *
        vectorNormalizedL2On W f := by
  have hnorm : MemLp (fun x => euclideanNorm (f x)) 2 (volume.restrict W) := by
    simpa only [euclideanNorm_eq_norm_ofVec] using hf.norm
  unfold vectorNormalizedL2On
  exact Algsuperdiff.Section4.Support.normalizedL2On_le_of_subset
    hsub hWpos hW'pos hnorm.integrable_sq

/-- The exact volume ratio between a ball and its half-radius subball. -/
theorem volume_ratio_half_euclideanBall [NeZero d]
    (z : Vec d) {r : ℝ} (hr : 0 < r) :
    (volume (euclideanBall z r)).toReal /
        (volume (euclideanBall z (r / 2))).toReal = (2 : ℝ) ^ d := by
  rw [volume_euclideanBall_toReal_eq_sphereMeasure_mul_pow_div z hr,
    volume_euclideanBall_toReal_eq_sphereMeasure_mul_pow_div z (by positivity : 0 < r / 2)]
  have hσ : (Algsuperdiff.Section4.Provider.ExcessDecay.Schauder.sphereMeasure d).real Set.univ ≠
    0 :=
    Algsuperdiff.Section4.Provider.ExcessDecay.Schauder.sphereMeasure_real_univ_ne_zero
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne d
  have hr0 : r ≠ 0 := hr.ne'
  rw [div_pow]
  field_simp

/-- Square-root form of the half-ball volume ratio. -/
theorem sqrt_volume_ratio_half_euclideanBall [NeZero d]
    (z : Vec d) {r : ℝ} (hr : 0 < r) :
    Real.sqrt ((volume (euclideanBall z r)).toReal /
        (volume (euclideanBall z (r / 2))).toReal) =
      (1 / 2 : ℝ) ^ (-(d : ℝ) / 2) := by
  rw [volume_ratio_half_euclideanBall z hr]
  rw [show Real.sqrt ((2 : ℝ) ^ d) = (2 : ℝ) ^ ((d : ℝ) / 2) by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast,
      ← Real.rpow_mul (by norm_num : 0 ≤ (2 : ℝ))]
    congr 2
    ring]
  rw [show -(d : ℝ) / 2 = -((d : ℝ) / 2) by ring,
    Real.rpow_neg_eq_inv_rpow]
  norm_num

end

end Algsuperdiff.StochasticProcess.Common.Regularity.Ported
