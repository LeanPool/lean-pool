/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.H1.Basic
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic
public import LeanPool.CaffarelliKohnNirenberg.Setting.SobolevGlobalL6

/-!
# Whole-space Gagliardo–Nirenberg interpolation

The `L^{10/3}` inequality follows by interpolating between `L²` and the
whole-space `L⁶` Sobolev estimate for representative-level `H¹` functions.
-/

public section

open MeasureTheory
open scoped ENNReal
open CKN
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN

private theorem eLpNorm_interpolate_two_six_tenThirds
    {μ : Measure Vec3} {f : Vec3 → ℝ}
    (hf : AEStronglyMeasurable f μ) :
    eLpNorm f (ENNReal.ofReal (10 / 3 : ℝ)) μ ≤
      eLpNorm f 2 μ ^ (2 / 5 : ℝ) * eLpNorm f 6 μ ^ (3 / 5 : ℝ) := by
  let w : Vec3 → ℝ := fun x => ‖f x‖ ^ (2 / 5 : ℝ)
  let v : Vec3 → ℝ := fun x => ‖f x‖ ^ (3 / 5 : ℝ)
  have hw : AEStronglyMeasurable w μ := by
    simpa [w, Function.comp_def] using
      ((Real.continuous_rpow_const (q := (2 / 5 : ℝ)) (by norm_num)).aemeasurable.comp_aemeasurable
        hf.aemeasurable.norm).aestronglyMeasurable
  have hv : AEStronglyMeasurable v μ := by
    simpa [v, Function.comp_def] using
      ((Real.continuous_rpow_const (q := (3 / 5 : ℝ)) (by norm_num)).aemeasurable.comp_aemeasurable
        hf.aemeasurable.norm).aestronglyMeasurable
  have hholder : eLpNorm (fun x => w x * v x) (ENNReal.ofReal (10 / 3 : ℝ)) μ ≤
      eLpNorm w (ENNReal.ofReal 5) μ * eLpNorm v (ENNReal.ofReal 10) μ := by
    have htriple : ENNReal.HolderTriple (ENNReal.ofReal 5) (ENNReal.ofReal 10)
        (ENNReal.ofReal (10 / 3 : ℝ)) := by
      refine ⟨?_⟩
      rw [← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 5),
        ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 10),
        ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 10 / 3),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      norm_num
    have := htriple
    simpa [ENNReal.smul_def, one_mul] using
      (eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm
        (μ := μ) (p := ENNReal.ofReal 5) (q := ENNReal.ofReal 10)
        (r := ENNReal.ofReal (10 / 3 : ℝ))
        (fun a b : ℝ => a * b) 1 continuous_mul hw hv
        (Filter.Eventually.of_forall fun x => by
          simp [w, v, Real.norm_eq_abs, one_mul]))
  have hprod : (fun x => w x * v x) = fun x => ‖f x‖ := by
    funext x
    by_cases hx : ‖f x‖ = 0
    · have hfx : f x = 0 := norm_eq_zero.mp hx
      simp [w, v, hfx, Real.zero_rpow]
    · change ‖f x‖ ^ (2 / 5 : ℝ) * ‖f x‖ ^ (3 / 5 : ℝ) = ‖f x‖
      rw [← Real.rpow_add (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hx))]
      norm_num
  have hwp : eLpNorm w (ENNReal.ofReal 5) μ = eLpNorm f 2 μ ^ (2 / 5 : ℝ) := by
    have hraw := eLpNorm_norm_rpow f hf (q := (2 / 5 : ℝ)) (by norm_num)
      (p := ENNReal.ofReal 5)
    have hexp : ENNReal.ofReal 5 * ENNReal.ofReal (2 / 5 : ℝ) = 2 := by
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 5)]
      norm_num
    rw [hexp] at hraw
    simpa [w] using hraw
  have hvp : eLpNorm v (ENNReal.ofReal 10) μ = eLpNorm f 6 μ ^ (3 / 5 : ℝ) := by
    have hraw := eLpNorm_norm_rpow f hf (q := (3 / 5 : ℝ)) (by norm_num)
      (p := ENNReal.ofReal 10)
    have hexp : ENNReal.ofReal 10 * ENNReal.ofReal (3 / 5 : ℝ) = 6 := by
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 10)]
      norm_num
    rw [hexp] at hraw
    simpa [v] using hraw
  rw [hprod, hwp, hvp, eLpNorm_norm f hf] at hholder
  exact hholder

/-- The chosen CKN whole-space Sobolev constant used in `eq:gn-ten-thirds`. -/
@[expose]
noncomputable def gagliardoNirenbergSobolevConstant : ℝ≥0∞ :=
  Classical.choose CKN.sobolev_L6_global

/-- The default Pi norm squared is bounded by the Euclidean velocity norm squared.
This comparison is used when reading the Leray–Hopf slice bound. -/
theorem enorm_sq_le_vec3Euclidean_sq (v : Vec3) :
    ‖v‖ₑ ^ (2 : ℝ) ≤
      ENNReal.ofReal (vec3EuclideanNorm v) ^ (2 : ℝ) := by
  rw [← ofReal_norm]
  exact ENNReal.rpow_le_rpow
    (ENNReal.ofReal_le_ofReal
      (CKN.Foundation.Parabolic.norm_le_vec3EuclideanNorm v))
    (by norm_num : (0 : ℝ) ≤ 2)

/-- The Euclidean velocity norm squared is bounded by three times the default
Pi norm squared. -/
theorem vec3Euclidean_sq_le_three_enorm_sq (v : Vec3) :
    ENNReal.ofReal (vec3EuclideanNorm v) ^ (2 : ℝ) ≤
      3 * ‖v‖ₑ ^ (2 : ℝ) := by
  have hreal : vec3EuclideanNorm v ^ (2 : ℕ) ≤
      3 * ‖v‖ ^ (2 : ℕ) := by
    have hpow := pow_le_pow_left₀ (vec3EuclideanNorm_nonneg v)
      (CKN.Foundation.Parabolic.vec3EuclideanNorm_le_sqrt_three_mul_norm v) 2
    calc
      vec3EuclideanNorm v ^ (2 : ℕ) ≤
          (Real.sqrt 3 * ‖v‖) ^ (2 : ℕ) := hpow
      _ = 3 * ‖v‖ ^ (2 : ℕ) := by
        rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  calc
    ENNReal.ofReal (vec3EuclideanNorm v) ^ (2 : ℝ) =
        ENNReal.ofReal (vec3EuclideanNorm v ^ (2 : ℕ)) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (vec3EuclideanNorm_nonneg v)
        (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num [Real.rpow_natCast]
    _ ≤ ENNReal.ofReal (3 * ‖v‖ ^ (2 : ℕ)) :=
      ENNReal.ofReal_le_ofReal hreal
    _ = 3 * ‖v‖ₑ ^ (2 : ℝ) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3),
        show ENNReal.ofReal (3 : ℝ) = 3 by norm_num,
        ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
      norm_num [ENNReal.rpow_natCast]

/-- The whole-space `L^{10/3}` Gagliardo–Nirenberg inequality in `eq:gn-ten-thirds`.
The `L⁶` step is the CKN whole-space Sobolev theorem. -/
theorem h1_gagliardoNirenberg_tenThirds
    (v : H1Function (Set.univ : Set Vec3)) :
    eLpNorm v.toFun (ENNReal.ofReal (10 / 3 : ℝ)) volume ≤
      gagliardoNirenbergSobolevConstant ^ (3 / 5 : ℝ) *
        eLpNorm v.toFun 2 volume ^ (2 / 5 : ℝ) *
          eLpNorm (fun x => vec3EuclideanNorm (v.grad x)) 2 volume ^ (3 / 5 : ℝ) := by
  have hv2 : MemLp v.toFun 2 volume := by
    simpa [CKN.MemL2On, CKN.MemLpOn, CKN.volumeOn] using v.memL2
  have hgradFun (i : Fin 3) : MemLp (fun x => v.grad x i) 2 volume := by
    simpa [CKN.MemL2On, CKN.MemLpOn, CKN.volumeOn] using v.grad_memL2 i
  have hgrad2 : MemLp v.grad 2 volume := (memLp_pi_iff).2 hgradFun
  have hgradNormLeEuclidean : eLpNorm v.grad 2 volume ≤
      eLpNorm (fun x => vec3EuclideanNorm (v.grad x)) 2 volume := by
    rw [← eLpNorm_norm v.grad hgrad2.aestronglyMeasurable]
    apply eLpNorm_mono_ae_real (hgrad2.aestronglyMeasurable.norm)
    filter_upwards [] with x
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using
      CKN.Foundation.Parabolic.norm_le_vec3EuclideanNorm (v.grad x)
  have hv6Sup : eLpNorm v.toFun 6 volume ≤
      gagliardoNirenbergSobolevConstant * eLpNorm v.grad 2 volume := by
    simpa [gagliardoNirenbergSobolevConstant, CKN.lpNormOn,
      CKN.weakGradientLpNormOn, Measure.restrict_univ] using
      (Classical.choose_spec CKN.sobolev_L6_global).2 v
  have hv6 : eLpNorm v.toFun 6 volume ≤
      gagliardoNirenbergSobolevConstant *
        eLpNorm (fun x => vec3EuclideanNorm (v.grad x)) 2 volume := by
    calc
      eLpNorm v.toFun 6 volume ≤
          gagliardoNirenbergSobolevConstant * eLpNorm v.grad 2 volume := hv6Sup
      _ ≤ gagliardoNirenbergSobolevConstant *
            eLpNorm (fun x => vec3EuclideanNorm (v.grad x)) 2 volume :=
        mul_le_mul_of_nonneg_left hgradNormLeEuclidean (by positivity)
  calc
    eLpNorm v.toFun (ENNReal.ofReal (10 / 3 : ℝ)) volume ≤
        eLpNorm v.toFun 2 volume ^ (2 / 5 : ℝ) *
          eLpNorm v.toFun 6 volume ^ (3 / 5 : ℝ) :=
      eLpNorm_interpolate_two_six_tenThirds hv2.aestronglyMeasurable
    _ ≤ eLpNorm v.toFun 2 volume ^ (2 / 5 : ℝ) *
          (gagliardoNirenbergSobolevConstant *
            eLpNorm (fun x => vec3EuclideanNorm (v.grad x)) 2 volume) ^
              (3 / 5 : ℝ) := by
      gcongr
    _ = gagliardoNirenbergSobolevConstant ^ (3 / 5 : ℝ) *
          eLpNorm v.toFun 2 volume ^ (2 / 5 : ℝ) *
            eLpNorm (fun x => vec3EuclideanNorm (v.grad x)) 2 volume ^
              (3 / 5 : ℝ) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 3 / 5)]
      ac_rfl

end CKN

end
