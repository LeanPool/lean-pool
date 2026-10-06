/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.RellichBalls
public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayLimitSlices
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Leray Limit Slices2

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Filter
open scoped ENNReal Topology
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- Uniform square-integral bounds on a compact exhaustion give a global
`L²` representative of each positive-time slice. -/
theorem lerayLimit_slice_memLp_of_compactIntegralBounds
    (u : ℝ → Vec3 → Vec3) (K : ℕ → Set Vec3)
    (hK : AECover (volume : Measure Vec3) atTop K)
    (C : ℝ) (hC : 0 ≤ C)
    (huMeas : ∀ t, Measurable (fun x : Vec3 => u t x))
    (hbound : ∀ t, 0 < t → ∀ n,
      (∫⁻ x in K n,
        ENNReal.ofReal (vec3EuclideanNorm (u t x)) ^ (2 : ℝ) ∂volume) ≤
          ENNReal.ofReal C ^ (2 : ℕ)) :
    ∀ t, 0 < t →
      ∃ hu : MemLp
        (fun x : Vec3 => (WithLp.toLp 2 (u t x) : L2Vec3)) 2 volume,
        ‖hu.toLp (fun x : Vec3 => (WithLp.toLp 2 (u t x) : L2Vec3))‖ ≤ C := by
  intro t ht
  let f : Vec3 → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (vec3EuclideanNorm (u t x)) ^ (2 : ℝ)
  have hf : AEMeasurable f volume := by
    apply (ENNReal.measurable_ofReal.comp
      (continuous_vec3EuclideanNorm.measurable.comp (huMeas t))).aemeasurable.pow_const
  have hconverge : Tendsto
      (fun n => ∫⁻ x in K n, f x ∂volume) atTop (𝓝 (∫⁻ x, f x ∂volume)) :=
    hK.lintegral_tendsto_of_nat hf
  have hglobal : (∫⁻ x, f x ∂volume) ≤ ENNReal.ofReal C ^ (2 : ℕ) :=
    le_of_tendsto hconverge (Eventually.of_forall fun n => by
      simpa only [f] using hbound t ht n)
  have hfinite : (∫⁻ x, f x ∂volume) < ⊤ := by
    have hCtop : ENNReal.ofReal C ^ (2 : ℕ) < ⊤ := by finiteness
    exact lt_of_le_of_lt hglobal hCtop
  have hu : MemLp
      (fun x : Vec3 => (WithLp.toLp 2 (u t x) : L2Vec3)) 2 volume :=
    CKN.Foundation.memLp_two_vec3_of_lintegral_sq_lt_top volume (u t)
      (huMeas t) (by simpa [f] using hfinite)
  have hnorm := eLpNorm_eq_lintegral_rpow_enorm_toReal
    (p := (2 : ℝ≥0∞)) (μ := volume)
    (f := fun x : Vec3 => (WithLp.toLp 2 (u t x) : L2Vec3))
    (by norm_num) (by norm_num) hu.aestronglyMeasurable
  have hpoint (x : Vec3) :
      ‖(WithLp.toLp 2 (u t x) : L2Vec3)‖ₑ ^ (2 : ℝ) = f x := by
    rw [← ofReal_norm, ← vec3EuclideanNorm_eq_l2]
  have hnorm' :
      eLpNorm (fun x : Vec3 => (WithLp.toLp 2 (u t x) : L2Vec3)) 2 volume =
        (∫⁻ x, f x ∂volume) ^ (1 / 2 : ℝ) := by
    rw [hnorm]
    congr 1
    exact lintegral_congr_ae (Eventually.of_forall hpoint)
  refine ⟨hu, ?_⟩
  rw [Lp.norm_def]
  have hLpNorm :
      eLpNorm (fun x : Vec3 => hu.toLp
        (fun y : Vec3 => (WithLp.toLp 2 (u t y) : L2Vec3)) x) 2 volume =
        eLpNorm (fun x : Vec3 => (WithLp.toLp 2 (u t x) : L2Vec3)) 2 volume :=
    eLpNorm_congr_ae hu.coeFn_toLp
  rw [hLpNorm, hnorm']
  have hroot : (∫⁻ x, f x ∂volume) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal C := by
    calc
      (∫⁻ x, f x ∂volume) ^ (1 / 2 : ℝ) ≤
          (ENNReal.ofReal C ^ (2 : ℕ)) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow hglobal (by norm_num)
      _ = ENNReal.ofReal C := by
        rw [← ENNReal.ofReal_pow hC 2]
        rw [ENNReal.ofReal_rpow_of_nonneg (sq_nonneg C)
          (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        congr 1
        rw [← Real.rpow_natCast C 2, ← Real.rpow_mul hC]
        norm_num
  calc
    ((∫⁻ x, f x ∂volume) ^ (1 / 2 : ℝ)).toReal ≤ (ENNReal.ofReal C).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hroot
    _ = C := ENNReal.toReal_ofReal hC

end CKN.Leray

end
