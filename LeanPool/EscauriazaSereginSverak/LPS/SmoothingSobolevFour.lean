/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.GagliardoNirenberg
public import LeanPool.CaffarelliKohnNirenberg.Foundation.LocalSobolevCalculus
public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.SerrinPairingLimit

/-!
# Intermediate integrability of smooth Sobolev derivatives

The first derivatives of a smooth whole-space `H²` function belong to
`L⁴`. This is the integrability part of the middle Leibniz split at
order two in `eq:lps-Hm-energy`.
-/

public section

open MeasureTheory Set
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- Interpolation between the whole-space `L²` and `L⁶` norms at
the `L⁴` exponent (eq:lps-Hm-energy). -/
theorem lps_eLpNorm_four_le_two_six {f : Vec3 → ℝ}
    (hf : AEStronglyMeasurable f volume) :
    eLpNorm f 4 volume ≤
      eLpNorm f 2 volume ^ (1 / 4 : ℝ) *
        eLpNorm f 6 volume ^ (3 / 4 : ℝ) := by
  let w : Vec3 → ℝ := fun x => ‖f x‖ ^ (1 / 4 : ℝ)
  let v : Vec3 → ℝ := fun x => ‖f x‖ ^ (3 / 4 : ℝ)
  have hw : AEStronglyMeasurable w volume :=
    (hf.norm.aemeasurable.pow_const _).aestronglyMeasurable
  have hv : AEStronglyMeasurable v volume :=
    (hf.norm.aemeasurable.pow_const _).aestronglyMeasurable
  have htriple : ENNReal.HolderTriple 8 8 4 := by
    refine ⟨?_⟩
    rw [show (8 : ℝ≥0∞) = ENNReal.ofReal 8 by norm_num,
      ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 8),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by norm_num,
      ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 4)]
    norm_num
  have hholder : eLpNorm (fun x => w x * v x) 4 volume ≤
      eLpNorm w 8 volume * eLpNorm v 8 volume := by
    simpa [ENNReal.smul_def, one_mul] using
      (eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm
        (μ := volume) (p := 8) (q := 8) (r := 4)
        (fun a b : ℝ => a * b) 1 continuous_mul hw hv
        (Filter.Eventually.of_forall fun x => by
          simp [w, v, Real.norm_eq_abs, one_mul]))
  have hprod : (fun x => w x * v x) = fun x => ‖f x‖ := by
    funext x
    change ‖f x‖ ^ (1 / 4 : ℝ) * ‖f x‖ ^ (3 / 4 : ℝ) = ‖f x‖
    rw [← Real.rpow_add' (norm_nonneg _) (by norm_num)]
    norm_num
  have hw2 : eLpNorm w 8 volume = eLpNorm f 2 volume ^ (1 / 4 : ℝ) := by
    rw [eLpNorm_norm_rpow f hf (by norm_num : (0 : ℝ) < 1 / 4)]
    have he : (8 : ℝ≥0∞) * ENNReal.ofReal (1 / 4 : ℝ) = 2 := by
      rw [show (8 : ℝ≥0∞) = ENNReal.ofReal 8 by norm_num,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8)]
      norm_num
    rw [he]
  have hv6 : eLpNorm v 8 volume = eLpNorm f 6 volume ^ (3 / 4 : ℝ) := by
    rw [eLpNorm_norm_rpow f hf (by norm_num : (0 : ℝ) < 3 / 4)]
    have he : (8 : ℝ≥0∞) * ENNReal.ofReal (3 / 4 : ℝ) = 6 := by
      rw [show (8 : ℝ≥0∞) = ENNReal.ofReal 8 by norm_num,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8)]
      norm_num
    rw [he]
  rw [hprod, eLpNorm_norm f hf, hw2, hv6] at hholder
  exact hholder

/-- A smooth scalar field with all ordered derivatives through order two
in `L²` has every first derivative in `L⁴` (eq:lps-Hm-energy). -/
theorem lps_smooth_first_derivative_memLp_four
    (f : Vec3 → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hL2 : ∀ α : List (Fin 3), α.length ≤ 2 →
      MemLp (wordDeriv α f) 2 volume) (j : Fin 3) :
    MemLp (spatialDeriv f j) 4 volume := by
  let g : Vec3 → ℝ := spatialDeriv f j
  have hgSmooth : ContDiff ℝ (⊤ : ℕ∞) g := contDiff_wordDeriv hf [j]
  have hg2 : MemLp g 2 volume := by
    simpa only [g, wordDeriv] using hL2 [j] (by simp)
  have hgd2 (k : Fin 3) : MemLp (spatialDeriv g k) 2 volume := by
    simpa only [g, wordDeriv] using hL2 [j, k] (by simp)
  let v : H1Function (Set.univ : Set Vec3) :=
    { toFun := g
      grad := fun x k => spatialDeriv g k x
      memL2 := by
        simpa [CKN.MemL2On, CKN.MemLpOn, CKN.volumeOn,
          Measure.restrict_univ] using hg2
      gradMemL2 := by
        intro k
        simpa [CKN.GradMemL2On, CKN.MemL2On, CKN.MemLpOn,
          CKN.volumeOn, Measure.restrict_univ] using hgd2 k
      hasWeakGradient := by
        intro k
        exact HasWeakPartialDerivOn.of_contDiff
          (hgSmooth.of_le (by simp)) }
  have hvgrad2 : MemLp v.grad 2 volume :=
    (memLp_pi_iff).2 (fun k => by simpa [v] using hgd2 k)
  have h6bound := (Classical.choose_spec CKN.sobolev_L6_global).2 v
  have h6finite : eLpNorm g 6 volume < ⊤ := by
    have hCfinite := (Classical.choose_spec CKN.sobolev_L6_global).1
    have hRfinite := ENNReal.mul_lt_top
      (lt_top_iff_ne_top.mpr hCfinite) hvgrad2.eLpNorm_lt_top
    exact lt_of_le_of_lt
      (by simpa [CKN.lpNormOn, CKN.weakGradientLpNormOn,
        Measure.restrict_univ, v] using h6bound) hRfinite
  have hg6 : MemLp g 6 volume := memLp_iff.mpr h6finite
  have hg4 : MemLp g 4 volume :=
    serrin_memLp_interpolate (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hg2 hg6
  exact hg4

/-- The first derivative's `L⁴` norm is quantitatively controlled by
its `L²` norm and the `L²` norm of its full gradient
(`eq:lps-Hm-energy`). -/
theorem lps_smooth_first_derivative_four_bound
    (f : Vec3 → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hL2 : ∀ α : List (Fin 3), α.length ≤ 2 →
      MemLp (wordDeriv α f) 2 volume) (j : Fin 3) :
    eLpNorm (spatialDeriv f j) 4 volume ≤
      eLpNorm (spatialDeriv f j) 2 volume ^ (1 / 4 : ℝ) *
        (gagliardoNirenbergSobolevConstant *
          eLpNorm (fun x => vec3EuclideanNorm
            (fun k => spatialDeriv (spatialDeriv f j) k x))
            2 volume) ^ (3 / 4 : ℝ) := by
  let g : Vec3 → ℝ := spatialDeriv f j
  have hgSmooth : ContDiff ℝ (⊤ : ℕ∞) g := contDiff_wordDeriv hf [j]
  have hg2 : MemLp g 2 volume := by
    simpa only [g, wordDeriv] using hL2 [j] (by simp)
  have hgd2 (k : Fin 3) : MemLp (spatialDeriv g k) 2 volume := by
    simpa only [g, wordDeriv] using hL2 [j, k] (by simp)
  let v : H1Function (Set.univ : Set Vec3) :=
    { toFun := g
      grad := fun x k => spatialDeriv g k x
      memL2 := by
        simpa [CKN.MemL2On, CKN.MemLpOn, CKN.volumeOn,
          Measure.restrict_univ] using hg2
      gradMemL2 := by
        intro k
        simpa [CKN.GradMemL2On, CKN.MemL2On, CKN.MemLpOn,
          CKN.volumeOn, Measure.restrict_univ] using hgd2 k
      hasWeakGradient := by
        intro k
        exact HasWeakPartialDerivOn.of_contDiff
          (hgSmooth.of_le (by simp)) }
  have hvgrad2 : MemLp v.grad 2 volume :=
    (memLp_pi_iff).2 (fun k => by simpa [v] using hgd2 k)
  have hgradLe : eLpNorm v.grad 2 volume ≤
      eLpNorm (fun x => vec3EuclideanNorm (v.grad x)) 2 volume := by
    rw [← eLpNorm_norm v.grad hvgrad2.aestronglyMeasurable]
    apply eLpNorm_mono_ae_real (hvgrad2.aestronglyMeasurable.norm)
    filter_upwards [] with x
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using
      CKN.Foundation.Parabolic.norm_le_vec3EuclideanNorm (v.grad x)
  have h6bound : eLpNorm g 6 volume ≤
      gagliardoNirenbergSobolevConstant *
        eLpNorm (fun x => vec3EuclideanNorm (v.grad x)) 2 volume := by
    calc
      _ ≤ gagliardoNirenbergSobolevConstant *
          eLpNorm v.grad 2 volume := by
        simpa [gagliardoNirenbergSobolevConstant, CKN.lpNormOn,
          CKN.weakGradientLpNormOn, Measure.restrict_univ, v] using
          (Classical.choose_spec CKN.sobolev_L6_global).2 v
      _ ≤ _ := mul_le_mul_of_nonneg_left hgradLe (by positivity)
  calc
    eLpNorm (spatialDeriv f j) 4 volume ≤
        eLpNorm g 2 volume ^ (1 / 4 : ℝ) *
          eLpNorm g 6 volume ^ (3 / 4 : ℝ) :=
      lps_eLpNorm_four_le_two_six hgSmooth.continuous.aestronglyMeasurable
    _ ≤ eLpNorm g 2 volume ^ (1 / 4 : ℝ) *
          (gagliardoNirenbergSobolevConstant *
            eLpNorm (fun x => vec3EuclideanNorm (v.grad x))
              2 volume) ^ (3 / 4 : ℝ) := by
      gcongr
    _ = _ := rfl

end ESS
