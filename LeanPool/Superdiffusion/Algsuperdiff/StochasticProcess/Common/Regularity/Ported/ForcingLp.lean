/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Ported.NormalizedEnergy
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# ForcingLp

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Local normalized `L²` control from the source `L^p` datum
-/

namespace Algsuperdiff.StochasticProcess.Common.Regularity.Ported

open MeasureTheory HCPolySupport
open scoped ENNReal

open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-- Restriction and finite-measure exponent lowering from the source carrier
to the quadratic weak-test carrier. -/
theorem memVectorL2_of_memVectorLpOn_of_subset
    {U W : Set (Vec d)} {p : ℝ} {f : Vec d → Vec d}
    [IsFiniteMeasure (volume.restrict W)]
    (hp2 : 2 ≤ p) (hWU : W ⊆ U) (hf : MemVectorLpOn U p f) :
    MemVectorL2 W f := by
  have hp2E : (2 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_ofNat]
    exact ENNReal.ofReal_le_ofReal hp2
  have hfHilbert2W :
      MemLp (fun x => HilbertVec.ofVec (f x)) 2 (volume.restrict W) :=
    (hf.mono_measure (Measure.restrict_mono hWU le_rfl)).mono_exponent hp2E
  simpa only [Function.comp_apply,
    HilbertVec.continuousLinearEquivVec_apply, HilbertVec.toVec_ofVec] using!
    (HilbertVec.continuousLinearEquivVec d).toContinuousLinearMap.comp_memLp'
      hfHilbert2W

/-- Volume restricted to a set and scaled by the inverse of its volume. -/
noncomputable def normalizedVolumeOn (W : Set (Vec d)) : Measure (Vec d) :=
  (volume W)⁻¹ • volume.restrict W

private theorem normalizedVolumeOn_isProbability
    {W : Set (Vec d)} (hW0 : volume W ≠ 0) (hWtop : volume W ≠ ∞) :
    IsProbabilityMeasure (normalizedVolumeOn W) := by
  refine ⟨?_⟩
  rw [normalizedVolumeOn, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply_univ]
  exact ENNReal.inv_mul_cancel hW0 hWtop

private theorem vectorNormalizedL2On_eq_normalizedVolume_eLpNorm_toReal
    {W : Set (Vec d)} {f : Vec d → Vec d}
    (hW : 0 < (volume W).toReal) (hf : MemVectorL2 W f) :
    vectorNormalizedL2On W f =
      (eLpNorm (fun x => euclideanNorm (f x)) 2 (normalizedVolumeOn W)).toReal := by
  rw [vectorNormalizedL2On_eq_toReal_eLpNorm_div hf]
  have hHF : MemLp (fun x => HilbertVec.ofVec (f x)) 2 (volume.restrict W) :=
    memHilbertVectorL2_hilbertifyVecField hf
  have hfun : (fun x => euclideanNorm (f x)) =
      fun x => ‖HilbertVec.ofVec (f x)‖ := by
    funext x
    exact euclideanNorm_eq_norm_ofVec _
  have hmeasN : AEStronglyMeasurable (fun x => euclideanNorm (f x)) (volume.restrict W) := by
    rw [hfun]
    exact hHF.aestronglyMeasurable.norm
  rw [normalizedVolumeOn, eLpNorm_smul_measure_of_ne_top (by norm_num) _ _ hmeasN,
    smul_eq_mul, ENNReal.toReal_mul]
  rw [hfun, eLpNorm_norm _ hHF.aestronglyMeasurable]
  have hV0 : volume W ≠ 0 := (ENNReal.toReal_ne_zero.mp hW.ne').1
  have hVtop : volume W ≠ ∞ := (ENNReal.toReal_ne_zero.mp hW.ne').2
  rw [← ENNReal.toReal_rpow, ENNReal.toReal_inv]
  norm_num
  rw [Real.sqrt_eq_rpow]
  have hVr : 0 < (volume W).toReal := hW
  rw [Real.inv_rpow hVr.le]
  ring

/-- Finite-measure Hölder embedding in exactly the normalized vector carrier.
The volume factor is explicit and therefore can be evaluated geometrically on
balls without hiding exponent dependence in a constant. -/
theorem vectorNormalizedL2On_le_volume_rpow_mul_vectorLpSizeOn
    {U W : Set (Vec d)} {p : ℝ} {f : Vec d → Vec d}
    (hp0 : 0 < p) (hp2 : 2 ≤ p)
    (hWU : W ⊆ U) (hW : 0 < (volume W).toReal)
    (hf : MemVectorLpOn U p f) :
    vectorNormalizedL2On W f ≤
      (volume W).toReal ^ (-1 / p) * vectorLpSizeOn U p f := by
  let g : Vec d → ℝ := fun x => euclideanNorm (f x)
  have hpE : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hp2E : (2 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_ofNat]
    exact ENNReal.ofReal_le_ofReal hp2
  have hfScalar : MemLp g (ENNReal.ofReal p) (volume.restrict U) := by
    simpa [g, euclideanNorm_eq_norm_ofVec] using hf.norm
  have hfW : MemLp g (ENNReal.ofReal p) (volume.restrict W) :=
    hfScalar.mono_measure (Measure.restrict_mono hWU le_rfl)
  have hW0 : volume W ≠ 0 := (ENNReal.toReal_ne_zero.mp hW.ne').1
  have hWtop : volume W ≠ ∞ := (ENNReal.toReal_ne_zero.mp hW.ne').2
  let : IsProbabilityMeasure (normalizedVolumeOn W) :=
    normalizedVolumeOn_isProbability hW0 hWtop
  have hdown : eLpNorm g 2 (normalizedVolumeOn W) ≤
      eLpNorm g (ENNReal.ofReal p) (normalizedVolumeOn W) :=
    eLpNorm_le_eLpNorm_of_exponent_le hp2E
  have hrestrict : eLpNorm g (ENNReal.ofReal p) (volume.restrict W) ≤
      eLpNorm g (ENNReal.ofReal p) (volume.restrict U) :=
    eLpNorm_mono_measure g (Measure.restrict_mono hWU le_rfl)
  have hscaled : eLpNorm g (ENNReal.ofReal p) (normalizedVolumeOn W) ≤
      (volume W)⁻¹ ^ (ENNReal.ofReal p).toReal⁻¹ *
        eLpNorm g (ENNReal.ofReal p) (volume.restrict U) := by
    rw [normalizedVolumeOn, eLpNorm_smul_measure_of_ne_top hpE _ _ hfW.aestronglyMeasurable,
      smul_eq_mul, one_div]
    simpa [mul_comm] using mul_le_mul_left hrestrict
      ((volume W)⁻¹ ^ (ENNReal.ofReal p).toReal⁻¹)
  have htop : (volume W)⁻¹ ^ (ENNReal.ofReal p).toReal⁻¹ *
      eLpNorm g (ENNReal.ofReal p) (volume.restrict U) ≠ ∞ :=
    ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by positivity) (ENNReal.inv_ne_top.mpr hW0))
      hfScalar.eLpNorm_ne_top
  have hreal := ENNReal.toReal_mono htop (hdown.trans hscaled)
  let : IsFiniteMeasure (volume.restrict W) :=
    ⟨by
      rw [Measure.restrict_apply_univ]
      exact lt_top_iff_ne_top.mpr hWtop⟩
  have hf2W : MemVectorL2 W f :=
    memVectorL2_of_memVectorLpOn_of_subset hp2 hWU hf
  rw [← vectorNormalizedL2On_eq_normalizedVolume_eLpNorm_toReal hW hf2W] at hreal
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal hp0.le] at hreal
  have hrpow : (volume W).toReal⁻¹ ^ p⁻¹ =
      (volume W).toReal ^ (-1 / p) := by
    rw [Real.inv_rpow hW.le, ← Real.rpow_neg hW.le]
    congr 1
    ring
  rw [hrpow] at hreal
  simpa [g, vectorLpSizeOn] using hreal

end

end Algsuperdiff.StochasticProcess.Common.Regularity.Ported
