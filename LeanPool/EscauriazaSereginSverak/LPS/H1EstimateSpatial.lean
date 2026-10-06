/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.GagliardoNirenberg
public import LeanPool.EscauriazaSereginSverak.PartV.SerrinCrossIdentity
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.H1.Basic
public import LeanPool.CaffarelliKohnNirenberg.Setting.SobolevGlobalL6
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeSet
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Spatial interpolation for the strong-solution estimate

The finite-exponent `H¹` estimate uses interpolation between `L²` and the
whole-space `L⁶` Sobolev bound (`lem:lps-H1-estimate`).
-/

public section

open MeasureTheory Set
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

private theorem lps_interpolate_two_six
    {f : Vec3 → ℝ} {q : ℝ} (hq2 : 2 < q) (hq6 : q < 6)
    (hf : AEStronglyMeasurable f volume) :
    eLpNorm f (ENNReal.ofReal q) volume ≤
      eLpNorm f 2 volume ^ (1 - 3 * (1 / 2 - 1 / q)) *
        eLpNorm f 6 volume ^ (3 * (1 / 2 - 1 / q)) := by
  let θ : ℝ := 3 * (1 / 2 - 1 / q)
  have hq0 : 0 < q := by linarith only [hq2]
  have hθ0 : 0 < θ := by
    dsimp [θ]
    have h : 1 / q < 1 / 2 := by
      rw [div_lt_div_iff₀ hq0 (by norm_num : (0 : ℝ) < 2)]
      linarith only [hq2]
    linarith only [h]
  have hθ1 : θ < 1 := by
    dsimp [θ]
    have h : 1 / 6 < 1 / q := by
      rw [div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 6) hq0]
      linarith only [hq6]
    linarith only [h]
  let P : ℝ := 2 / (1 - θ)
  let S : ℝ := 6 / θ
  have hP : 0 < P := by dsimp [P]; positivity
  have hS : 0 < S := by dsimp [S]; positivity
  have hrecip : P⁻¹ + S⁻¹ = q⁻¹ := by
    dsimp [P, S, θ]
    field_simp
    ring
  have hHolder : ENNReal.HolderTriple (ENNReal.ofReal P) (ENNReal.ofReal S)
      (ENNReal.ofReal q) := by
    refine ⟨?_⟩
    rw [← ENNReal.ofReal_inv_of_pos hP, ← ENNReal.ofReal_inv_of_pos hS,
      ← ENNReal.ofReal_inv_of_pos hq0,
      ← ENNReal.ofReal_add (by positivity) (by positivity), hrecip]
  have hw : AEStronglyMeasurable (fun x => ‖f x‖ ^ (1 - θ)) volume := by
    simpa [Function.comp_def] using
      ((Real.continuous_rpow_const (q := 1 - θ) (sub_pos.mpr hθ1).le).aemeasurable.comp_aemeasurable
        hf.aemeasurable.norm).aestronglyMeasurable
  have hv : AEStronglyMeasurable (fun x => ‖f x‖ ^ θ) volume := by
    simpa [Function.comp_def] using
      ((Real.continuous_rpow_const (q := θ) hθ0.le).aemeasurable.comp_aemeasurable
        hf.aemeasurable.norm).aestronglyMeasurable
  have hprod : (fun x => ‖f x‖ ^ (1 - θ) * ‖f x‖ ^ θ) = fun x => ‖f x‖ := by
    funext x
    by_cases hx : ‖f x‖ = 0
    · rw [hx, Real.zero_rpow (sub_pos.mpr hθ1).ne', Real.zero_rpow hθ0.ne', zero_mul]
    · rw [← Real.rpow_add (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hx))]
      norm_num
  have hHolderNorm :
      eLpNorm (fun x => ‖f x‖ ^ (1 - θ) * ‖f x‖ ^ θ)
          (ENNReal.ofReal q) volume ≤
        eLpNorm (fun x => ‖f x‖ ^ (1 - θ)) (ENNReal.ofReal P) volume *
          eLpNorm (fun x => ‖f x‖ ^ θ) (ENNReal.ofReal S) volume := by
    have h := eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm
      (μ := volume) (p := ENNReal.ofReal P) (q := ENNReal.ofReal S)
      (r := ENNReal.ofReal q) (fun a b : ℝ => a * b) 1 continuous_mul hw hv
      (Filter.Eventually.of_forall fun x => by simp [Real.norm_eq_abs, one_mul])
    simpa [ENNReal.smul_def, one_mul] using h
  have hwp :
      eLpNorm (fun x => ‖f x‖ ^ (1 - θ)) (ENNReal.ofReal P) volume =
        eLpNorm f 2 volume ^ (1 - θ) := by
    have hraw := eLpNorm_norm_rpow f hf (q := 1 - θ)
      (sub_pos.mpr hθ1) (p := ENNReal.ofReal P)
    have hPe : ENNReal.ofReal P * ENNReal.ofReal (1 - θ) = 2 := by
      rw [← ENNReal.ofReal_mul hP.le]
      dsimp [P]
      rw [div_mul_cancel₀ _ (ne_of_gt (sub_pos.mpr hθ1))]
      norm_num
    rw [hPe] at hraw
    simpa using hraw
  have hvs :
      eLpNorm (fun x => ‖f x‖ ^ θ) (ENNReal.ofReal S) volume =
        eLpNorm f 6 volume ^ θ := by
    have hraw := eLpNorm_norm_rpow f hf (q := θ) hθ0 (p := ENNReal.ofReal S)
    have hSe : ENNReal.ofReal S * ENNReal.ofReal θ = 6 := by
      rw [← ENNReal.ofReal_mul hS.le]
      dsimp [S]
      rw [div_mul_cancel₀ _ hθ0.ne']
      norm_num
    rw [hSe] at hraw
    simpa using hraw
  rw [hprod, eLpNorm_norm f hf, hwp, hvs] at hHolderNorm
  simpa [θ] using hHolderNorm

private theorem lps_h1_function_six
    (h : H1Function (Set.univ : Set Vec3)) :
    eLpNorm h.toFun 6 volume ≤
      gagliardoNirenbergSobolevConstant *
        eLpNorm (fun x => vec3EuclideanNorm (h.grad x)) 2 volume := by
  have hgradFun (i : Fin 3) : MemLp (fun x => h.grad x i) 2 volume := by
    simpa [CKN.MemL2On, CKN.MemLpOn, CKN.volumeOn] using h.gradMemL2 i
  have hgrad : MemLp h.grad 2 volume := (memLp_pi_iff).2 hgradFun
  have hgradLe : eLpNorm h.grad 2 volume ≤
      eLpNorm (fun x => vec3EuclideanNorm (h.grad x)) 2 volume := by
    rw [← eLpNorm_norm h.grad hgrad.aestronglyMeasurable]
    apply eLpNorm_mono_ae_real (hgrad.aestronglyMeasurable.norm)
    filter_upwards [] with x
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using
      CKN.Foundation.Parabolic.norm_le_vec3EuclideanNorm (h.grad x)
  have hglobal := (Classical.choose_spec CKN.sobolev_L6_global).2 h
  have hglobal' : eLpNorm h.toFun 6 volume ≤
      gagliardoNirenbergSobolevConstant * eLpNorm h.grad 2 volume := by
    simpa [gagliardoNirenbergSobolevConstant, CKN.lpNormOn,
      CKN.weakGradientLpNormOn, Measure.restrict_univ] using hglobal
  exact hglobal'.trans (mul_le_mul_of_nonneg_left hgradLe (by positivity))

private theorem lps_h1_interpolate_two_six
    {s : ℝ} (hs : 3 < s) {α : Type} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} (hf : AEStronglyMeasurable f μ) :
    eLpNorm f (ENNReal.ofReal (2 * s / (s - 2))) μ ≤
      eLpNorm f 2 μ ^ ((s - 3) / s) * eLpNorm f 6 μ ^ (3 / s) := by
  let θ₀ : ℝ := (s - 3) / s
  let θ₁ : ℝ := 3 / s
  let p : ℝ := 2 * s / (s - 3)
  let q : ℝ := 2 * s
  let r : ℝ := 2 * s / (s - 2)
  let w : α → ℝ := fun x => ‖f x‖ ^ θ₀
  let v : α → ℝ := fun x => ‖f x‖ ^ θ₁
  have hs0 : 0 < s := lt_trans (by norm_num) hs
  have hs2 : 0 < s - 2 := by linarith only [hs]
  have hs3 : 0 < s - 3 := by linarith only [hs]
  have hp : 0 < p := by dsimp [p]; positivity
  have hq : 0 < q := by dsimp [q]; positivity
  have hr : 0 < r := by dsimp [r]; positivity
  have hθ₀ : 0 < θ₀ := by dsimp [θ₀]; positivity
  have hθ₁ : 0 < θ₁ := by dsimp [θ₁]; positivity
  have hθ : θ₀ + θ₁ = 1 := by
    dsimp [θ₀, θ₁]
    field_simp [ne_of_gt hs0]
    ring
  have hrecip : p⁻¹ + q⁻¹ = r⁻¹ := by
    dsimp [p, q, r]
    field_simp [ne_of_gt hs0, ne_of_gt hs2, ne_of_gt hs3]
    ring
  have htriple : ENNReal.HolderTriple (ENNReal.ofReal p) (ENNReal.ofReal q)
      (ENNReal.ofReal r) := by
    exact serrin_holder_ofReal3 hp hq hr hrecip
  have hw : AEStronglyMeasurable w μ := by
    simpa [w, Function.comp_def] using
      ((Real.continuous_rpow_const (q := θ₀) hθ₀.le).aemeasurable.comp_aemeasurable
        hf.aemeasurable.norm).aestronglyMeasurable
  have hv : AEStronglyMeasurable v μ := by
    simpa [v, Function.comp_def] using
      ((Real.continuous_rpow_const (q := θ₁) hθ₁.le).aemeasurable.comp_aemeasurable
        hf.aemeasurable.norm).aestronglyMeasurable
  have hholder : eLpNorm (fun x => w x * v x) (ENNReal.ofReal r) μ ≤
      eLpNorm w (ENNReal.ofReal p) μ * eLpNorm v (ENNReal.ofReal q) μ := by
    simpa using
      (eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm
        (p := ENNReal.ofReal p) (q := ENNReal.ofReal q) (r := ENNReal.ofReal r)
        (fun a b : ℝ => a * b) 1 continuous_mul hw hv
        (Filter.Eventually.of_forall fun x => by
          change ‖w x * v x‖ ≤ (1 : ℝ) * ‖w x‖ * ‖v x‖
          rw [norm_mul]
          simp)
        (hpqr := htriple))
  have hprod : (fun x => w x * v x) = fun x => ‖f x‖ := by
    funext x
    by_cases hx : f x = 0
    · simp [w, v, hx, Real.zero_rpow, hθ₀.ne', hθ₁.ne']
    · have hnorm : 0 < ‖f x‖ := norm_pos_iff.mpr hx
      change ‖f x‖ ^ θ₀ * ‖f x‖ ^ θ₁ = ‖f x‖
      rw [← Real.rpow_add hnorm, hθ, Real.rpow_one]
  have hwp : eLpNorm w (ENNReal.ofReal p) μ =
      eLpNorm f 2 μ ^ θ₀ := by
    have hraw := eLpNorm_norm_rpow f hf (q := θ₀) hθ₀ (p := ENNReal.ofReal p)
    have hexp : ENNReal.ofReal p * ENNReal.ofReal θ₀ = 2 := by
      rw [← ENNReal.ofReal_mul hp.le]
      have hreal : p * θ₀ = 2 := by
        dsimp [p, θ₀]
        field_simp [ne_of_gt hs0, ne_of_gt hs3]
      rw [hreal]
      norm_num
    rw [hexp] at hraw
    simpa [w] using hraw
  have hvp : eLpNorm v (ENNReal.ofReal q) μ =
      eLpNorm f 6 μ ^ θ₁ := by
    have hraw := eLpNorm_norm_rpow f hf (q := θ₁) hθ₁ (p := ENNReal.ofReal q)
    have hexp : ENNReal.ofReal q * ENNReal.ofReal θ₁ = 6 := by
      rw [← ENNReal.ofReal_mul hq.le]
      have hreal : q * θ₁ = 6 := by
        dsimp [q, θ₁]
        field_simp [ne_of_gt hs0]
        ring
      rw [hreal]
      norm_num
    rw [hexp] at hraw
    simpa [v] using hraw
  rw [hprod, hwp, hvp, eLpNorm_norm f hf] at hholder
  simpa [p, q, r, θ₀, θ₁] using hholder

/-- Whole-space interpolation of a vector field with componentwise `H¹` data,
used for the gradient in `lem:lps-H1-estimate`. -/
theorem lps_h1_vector_interpolation
    {s : ℝ} (hs : 3 < s) {u : Vec3 → Vec3} {Du : Vec3 → Fin 3 → Vec3}
    (hu2 : MemLp u 2 volume) (hDu2 : MemLp Du 2 volume)
    (hgrad : ∀ i : Fin 3, HasWeakGradientOn (Set.univ : Set Vec3)
      (fun x => u x i) (fun x => Du x i)) :
    eLpNorm u (ENNReal.ofReal (2 * s / (s - 2))) volume ≤
      3 * gagliardoNirenbergSobolevConstant ^ (3 / s) *
        (2 : ℝ≥0∞) ^ (3 / s) *
        eLpNorm u 2 volume ^ ((s - 3) / s) * eLpNorm Du 2 volume ^ (3 / s) := by
  let r : ℝ := 2 * s / (s - 2)
  let θ₀ : ℝ := (s - 3) / s
  let θ₁ : ℝ := 3 / s
  let Wsum : Vec3 → ℝ := fun x => ∑ i : Fin 3, |u x i|
  let hH1 : ∀ i : Fin 3, H1Function (Set.univ : Set Vec3) := fun i =>
    { toFun := fun x => u x i
      grad := fun x => Du x i
      memL2 := by
        simpa [CKN.MemL2On, CKN.MemLpOn, CKN.volumeOn, Measure.restrict_univ] using hu2.eval i
      gradMemL2 := by
        intro j
        simpa [CKN.MemL2On, CKN.MemLpOn, CKN.volumeOn, Measure.restrict_univ] using
          (hDu2.eval i).eval j
      hasWeakGradient := hgrad i }
  have hrpos : 0 < r := by
    dsimp [r]
    have hs0 : 0 < s := lt_trans (by norm_num) hs
    have hs2 : 0 < s - 2 := by linarith only [hs]
    positivity
  have hθ₀pos : 0 < θ₀ := by
    dsimp [θ₀]
    positivity
  have hθ₁pos : 0 < θ₁ := by
    dsimp [θ₁]
    positivity
  have hWsum_nonneg (x : Vec3) : 0 ≤ Wsum x := by
    dsimp [Wsum]
    positivity
  have huBound (x : Vec3) : ‖u x‖ ≤ Wsum x := by
    apply (pi_norm_le_iff_of_nonneg (hWsum_nonneg x)).2
    intro i
    dsimp [Wsum]
    calc
      ‖u x i‖ = |u x i| := Real.norm_eq_abs _
      _ ≤ ∑ j : Fin 3, |u x j| :=
        Finset.single_le_sum (fun j _ => abs_nonneg (u x j)) (Finset.mem_univ i)
  have huVectorLe : eLpNorm u (ENNReal.ofReal r) volume ≤ eLpNorm Wsum (ENNReal.ofReal r) volume :=
    eLpNorm_mono_ae_real hu2.aestronglyMeasurable (Filter.Eventually.of_forall huBound)
  have hsumLp : eLpNorm Wsum (ENNReal.ofReal r) volume ≤
      ∑ i : Fin 3, eLpNorm (fun x => |u x i|) (ENNReal.ofReal r) volume := by
    have hsumEq : Wsum = ∑ i : Fin 3, (fun x : Vec3 => |u x i|) := by
      funext x
      rfl
    rw [hsumEq]
    exact eLpNorm_sum_le (μ := volume) (p := ENNReal.ofReal r)
      (f := fun i x => |u x i|) (s := Finset.univ) (by
        have h1 : 1 ≤ r := by
          dsimp [r]
          have hs0 : 0 < s := lt_trans (by norm_num) hs
          have hs2 : 0 < s - 2 := by linarith only [hs]
          have hden : 0 < s - 2 := hs2
          rw [le_div_iff₀ hden]
          nlinarith only [hs]
        simpa using ENNReal.ofReal_le_ofReal h1)
  have hsumLp' : eLpNorm Wsum (ENNReal.ofReal r) volume ≤
      ∑ i : Fin 3, eLpNorm (fun x => u x i) (ENNReal.ofReal r) volume := by
    refine hsumLp.trans ?_
    apply Finset.sum_le_sum
    intro i hi
    have hcoord : AEStronglyMeasurable (fun x => u x i) volume :=
      (ContinuousLinearMap.proj (R := ℝ) i).continuous.comp_aestronglyMeasurable
        hu2.aestronglyMeasurable
    have heq := eLpNorm_congr_norm_ae (p := ENNReal.ofReal r)
      (continuous_abs.comp_aestronglyMeasurable hcoord) hcoord
      (Filter.Eventually.of_forall fun x => by simp [Real.norm_eq_abs])
    exact le_of_eq heq
  have hrow2 (i : Fin 3) :
      eLpNorm (hH1 i).toFun 2 volume ≤ eLpNorm u 2 volume := by
    have hrow := eLpNorm_mono_ae ((hH1 i).memL2.aestronglyMeasurable)
      (μ := CKN.volumeOn (Set.univ : Set Vec3)) (p := (2 : ℝ≥0∞))
      (Filter.Eventually.of_forall fun x => by
        simpa only [show (hH1 i).toFun = fun x => u x i from rfl] using
          norm_le_pi_norm (u x) i)
    simpa [CKN.MemL2On, CKN.MemLpOn, CKN.volumeOn, Measure.restrict_univ] using hrow
  have hrowGrad (i : Fin 3) :
      eLpNorm (fun x => vec3EuclideanNorm ((hH1 i).grad x)) 2 volume ≤
        (2 : ℝ≥0∞) * eLpNorm Du 2 volume := by
    have hrowGradLp : MemLp (hH1 i).grad 2 volume := by
      apply (memLp_pi_iff).2
      intro j
      simpa [CKN.GradMemL2On, CKN.MemLpOn, CKN.volumeOn, Measure.restrict_univ] using
        (hH1 i).gradMemL2 j
    have hmeas : AEStronglyMeasurable
        (fun x => vec3EuclideanNorm ((hH1 i).grad x)) volume :=
      continuous_vec3EuclideanNorm.comp_aestronglyMeasurable
        hrowGradLp.aestronglyMeasurable
    have hpoint : ∀ᵐ x ∂volume,
        ‖vec3EuclideanNorm ((hH1 i).grad x)‖ ≤ 2 * ‖Du x‖ := by
      filter_upwards [] with x
      rw [Real.norm_eq_abs, abs_of_nonneg (vec3EuclideanNorm_nonneg _)]
      change vec3EuclideanNorm (fun j => Du x i j) ≤ 2 * ‖Du x‖
      have hrow : ‖(fun j => Du x i j : Vec3)‖ ≤ ‖Du x‖ := norm_le_pi_norm (Du x) i
      have hsqrt : Real.sqrt 3 ≤ 2 := by
        nlinarith only [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3]
      calc
        vec3EuclideanNorm (fun j => Du x i j) ≤
            Real.sqrt 3 * ‖(fun j => Du x i j : Vec3)‖ :=
          vec3EuclideanNorm_le_sqrt_three_mul_norm _
        _ ≤ Real.sqrt 3 * ‖Du x‖ := mul_le_mul_of_nonneg_left hrow (Real.sqrt_nonneg 3)
        _ ≤ 2 * ‖Du x‖ := mul_le_mul_of_nonneg_right hsqrt (norm_nonneg _)
    have hmul := eLpNorm_le_mul_eLpNorm_of_ae_le_mul hmeas hpoint (2 : ℝ≥0∞)
    simpa only [ENNReal.ofReal_ofNat] using hmul
  have hgradDefaultLp (i : Fin 3) : MemLp (hH1 i).grad 2 volume := by
    apply (memLp_pi_iff).2
    intro j
    simpa [CKN.GradMemL2On, CKN.MemLpOn, CKN.volumeOn, Measure.restrict_univ] using
      (hH1 i).gradMemL2 j
  have hgradDefaultEuclidean (i : Fin 3) :
      eLpNorm (hH1 i).grad 2 volume ≤
        eLpNorm (fun x => vec3EuclideanNorm ((hH1 i).grad x)) 2 volume := by
    rw [← eLpNorm_norm (hH1 i).grad (hgradDefaultLp i).aestronglyMeasurable]
    apply eLpNorm_mono_ae_real ((hgradDefaultLp i).aestronglyMeasurable.norm)
    filter_upwards [] with x
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using
      CKN.Foundation.Parabolic.norm_le_vec3EuclideanNorm ((hH1 i).grad x)
  have hrow_interpolation (i : Fin 3) :
      eLpNorm (fun x => u x i) (ENNReal.ofReal r) volume ≤
        gagliardoNirenbergSobolevConstant ^ θ₁ *
          eLpNorm u 2 volume ^ θ₀ * (2 * eLpNorm Du 2 volume) ^ θ₁ := by
    have h6base : eLpNorm (hH1 i).toFun 6 volume ≤
        gagliardoNirenbergSobolevConstant * eLpNorm (hH1 i).grad 2 volume := by
      simpa [gagliardoNirenbergSobolevConstant, CKN.lpNormOn,
        CKN.weakGradientLpNormOn, Measure.restrict_univ] using
        (Classical.choose_spec CKN.sobolev_L6_global).2 (hH1 i)
    have h6 : eLpNorm (hH1 i).toFun 6 volume ≤
        gagliardoNirenbergSobolevConstant *
          (2 * eLpNorm Du 2 volume) := by
      calc
        eLpNorm (hH1 i).toFun 6 volume ≤
            gagliardoNirenbergSobolevConstant * eLpNorm (hH1 i).grad 2 volume := h6base
        _ ≤ gagliardoNirenbergSobolevConstant *
              eLpNorm (fun x => vec3EuclideanNorm ((hH1 i).grad x)) 2 volume :=
          mul_le_mul_of_nonneg_left (hgradDefaultEuclidean i) (by positivity)
        _ ≤ gagliardoNirenbergSobolevConstant * (2 * eLpNorm Du 2 volume) := by
          gcongr
          exact hrowGrad i
    have hinterp := lps_h1_interpolate_two_six hs
      (by
        simpa [CKN.MemL2On, CKN.MemLpOn, CKN.volumeOn, Measure.restrict_univ] using
          (hH1 i).memL2.aestronglyMeasurable)
    calc
      eLpNorm (fun x => u x i) (ENNReal.ofReal r) volume =
          eLpNorm (hH1 i).toFun (ENNReal.ofReal r) volume := by rfl
      _ ≤ eLpNorm (hH1 i).toFun 2 volume ^ θ₀ *
            eLpNorm (hH1 i).toFun 6 volume ^ θ₁ := by
        simpa [r, θ₀, θ₁] using hinterp
      _ ≤ eLpNorm u 2 volume ^ θ₀ *
            (gagliardoNirenbergSobolevConstant * (2 * eLpNorm Du 2 volume)) ^ θ₁ := by
        gcongr
        exact hrow2 i
      _ = gagliardoNirenbergSobolevConstant ^ θ₁ *
            eLpNorm u 2 volume ^ θ₀ * (2 * eLpNorm Du 2 volume) ^ θ₁ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hθ₁pos.le]
        ac_rfl
  calc
    eLpNorm u (ENNReal.ofReal r) volume ≤ eLpNorm Wsum (ENNReal.ofReal r) volume := huVectorLe
    _ ≤ ∑ i : Fin 3, eLpNorm (fun x => u x i) (ENNReal.ofReal r) volume := hsumLp'
    _ ≤ ∑ _i : Fin 3,
          gagliardoNirenbergSobolevConstant ^ θ₁ * eLpNorm u 2 volume ^ θ₀ *
            (2 * eLpNorm Du 2 volume) ^ θ₁ := by
        apply Finset.sum_le_sum
        intro i hi
        exact hrow_interpolation i
    _ = 3 * gagliardoNirenbergSobolevConstant ^ θ₁ * (2 : ℝ≥0∞) ^ θ₁ *
          eLpNorm u 2 volume ^ θ₀ * eLpNorm Du 2 volume ^ θ₁ := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          ENNReal.mul_rpow_of_nonneg _ _ hθ₁pos.le]
        ring

/-- Interpolation of the full first spatial derivative using componentwise
weak second derivatives, in the finite-exponent form of
`lem:lps-H1-estimate`. -/
theorem lps_h1_gradient_interpolation
    {s : ℝ} (hs : 3 < s) {Du : Vec3 → Fin 3 → Vec3}
    {D2u : Vec3 → Fin 3 → Fin 3 → Vec3}
    (hDu2 : MemLp Du 2 volume) (hD2u2 : MemLp D2u 2 volume)
    (hgrad : ∀ i j : Fin 3,
      HasWeakGradientOn (Set.univ : Set Vec3)
        (fun x => Du x i j) (fun x => D2u x i j)) :
    eLpNorm (fun x => ∑ i : Fin 3, ‖Du x i‖)
        (ENNReal.ofReal (2 * s / (s - 2))) volume ≤
      9 * gagliardoNirenbergSobolevConstant ^ (3 / s) *
        (2 : ℝ≥0∞) ^ (3 / s) * eLpNorm Du 2 volume ^ ((s - 3) / s) *
          eLpNorm D2u 2 volume ^ (3 / s) := by
  let r : ℝ := 2 * s / (s - 2)
  let θ₀ : ℝ := (s - 3) / s
  let θ₁ : ℝ := 3 / s
  have hs0 : 0 < s := lt_trans (by norm_num) hs
  have hden : 0 < s - 2 := by linarith only [hs]
  have hr1 : 1 ≤ r := by
    dsimp [r]
    rw [le_div_iff₀ hden]
    nlinarith only [hs]
  have hθ₀pos : 0 < θ₀ := by dsimp [θ₀]; positivity
  have hθ₁pos : 0 < θ₁ := by dsimp [θ₁]; positivity
  have hrow2 (i : Fin 3) :
      eLpNorm (fun x => Du x i) 2 volume ≤ eLpNorm Du 2 volume := by
    apply eLpNorm_mono_ae ((hDu2.eval i).aestronglyMeasurable)
    filter_upwards [] with x
    exact norm_le_pi_norm (Du x) i
  have hrowD2 (i : Fin 3) :
      eLpNorm (fun x => D2u x i) 2 volume ≤ eLpNorm D2u 2 volume := by
    apply eLpNorm_mono_ae ((hD2u2.eval i).aestronglyMeasurable)
    filter_upwards [] with x
    exact norm_le_pi_norm (D2u x) i
  have hrow (i : Fin 3) :
      eLpNorm (fun x => Du x i) (ENNReal.ofReal r) volume ≤
        3 * gagliardoNirenbergSobolevConstant ^ θ₁ * (2 : ℝ≥0∞) ^ θ₁ *
          eLpNorm Du 2 volume ^ θ₀ * eLpNorm D2u 2 volume ^ θ₁ := by
    have h := lps_h1_vector_interpolation hs (hDu2.eval i) (hD2u2.eval i)
      (hgrad i)
    have h' : eLpNorm (fun x => Du x i) (ENNReal.ofReal r) volume ≤
        3 * gagliardoNirenbergSobolevConstant ^ (3 / s) * (2 : ℝ≥0∞) ^ (3 / s) *
          eLpNorm (fun x => Du x i) 2 volume ^ ((s - 3) / s) *
            eLpNorm (fun x => D2u x i) 2 volume ^ (3 / s) := by
      simpa [r, θ₀, θ₁] using h
    calc
      eLpNorm (fun x => Du x i) (ENNReal.ofReal r) volume ≤ _ := h'
      _ ≤ 3 * gagliardoNirenbergSobolevConstant ^ θ₁ * (2 : ℝ≥0∞) ^ θ₁ *
            eLpNorm Du 2 volume ^ θ₀ * eLpNorm D2u 2 volume ^ θ₁ := by
        gcongr
        · exact hrow2 i
        · exact hrowD2 i
  have hsum :
      eLpNorm (fun x : Vec3 => ∑ i : Fin 3, ‖Du x i‖)
          (ENNReal.ofReal r) volume ≤
        ∑ i : Fin 3, eLpNorm (fun x => ‖Du x i‖)
          (ENNReal.ofReal r) volume := by
    exact eLpNorm_sum_le (μ := volume) (p := ENNReal.ofReal r)
      (f := fun i x => ‖Du x i‖) (s := Finset.univ)
      (by simpa using ENNReal.ofReal_le_ofReal hr1)
  have hrowNorm (i : Fin 3) :
      eLpNorm (fun x : Vec3 => ‖Du x i‖) (ENNReal.ofReal r) volume =
        eLpNorm (fun x => Du x i) (ENNReal.ofReal r) volume := by
    exact eLpNorm_norm (fun x => Du x i) (hDu2.eval i).aestronglyMeasurable
  calc
    eLpNorm (fun x : Vec3 => ∑ i : Fin 3, ‖Du x i‖)
        (ENNReal.ofReal r) volume ≤
      ∑ i : Fin 3, eLpNorm (fun x => ‖Du x i‖) (ENNReal.ofReal r) volume := hsum
    _ ≤ ∑ _i : Fin 3,
          3 * gagliardoNirenbergSobolevConstant ^ θ₁ * (2 : ℝ≥0∞) ^ θ₁ *
            eLpNorm Du 2 volume ^ θ₀ * eLpNorm D2u 2 volume ^ θ₁ := by
      apply Finset.sum_le_sum
      intro i hi
      rw [hrowNorm i]
      exact hrow i
    _ = 9 * gagliardoNirenbergSobolevConstant ^ θ₁ * (2 : ℝ≥0∞) ^ θ₁ *
          eLpNorm Du 2 volume ^ θ₀ * eLpNorm D2u 2 volume ^ θ₁ := by
      simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      ring
  

private theorem lps_h1_young {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {A B D : ℝ}, 0 ≤ A → 0 ≤ B → 0 ≤ D →
      A * B ^ (1 - θ) * D ^ (1 + θ) ≤
        (1 / 2 : ℝ) * D ^ 2 + C * A ^ (2 / (1 - θ)) * B ^ 2 := by
  let p : ℝ := 2 / (1 + θ)
  let q : ℝ := 2 / (1 - θ)
  let lam : ℝ := (p / 2) ^ (1 / p)
  let C : ℝ := (lam⁻¹ ^ q) / q
  have hp0 : 0 < p := by
    dsimp [p]
    exact div_pos (by norm_num) (by linarith only [hθ0])
  have hq0 : 0 < q := by
    dsimp [q]
    exact div_pos (by norm_num) (sub_pos.mpr hθ1)
  have hpq : p⁻¹ + q⁻¹ = 1 := by
    dsimp [p, q]
    field_simp
    ring
  have hconj : p.HolderConjugate q := ⟨by simpa using hpq, hp0, hq0⟩
  have hLam : 0 < lam := by
    dsimp [lam]
    exact Real.rpow_pos_of_pos (div_pos hp0 (by norm_num)) _
  have hLamPow : lam ^ p = p / 2 := by
    dsimp [lam]
    rw [← Real.rpow_mul (by positivity : 0 ≤ p / 2)]
    have hpow : (1 / p) * p = 1 := by field_simp
    rw [hpow, Real.rpow_one]
  have hθp : (1 + θ) * p = 2 := by
    dsimp [p]
    field_simp [ne_of_gt (by positivity : 0 < 1 + θ)]
  have hθq : (1 - θ) * q = 2 := by
    dsimp [q]
    field_simp [ne_of_gt (sub_pos.mpr hθ1)]
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro A B D hA hB hD
  let X : ℝ := lam * D ^ (1 + θ)
  let Y : ℝ := A * B ^ (1 - θ) * lam⁻¹
  have hXnonneg : 0 ≤ X := by dsimp [X]; positivity
  have hYnonneg : 0 ≤ Y := by dsimp [Y]; positivity
  have hYoung := Real.young_inequality_of_nonneg hXnonneg hYnonneg hconj
  have hXpow : X ^ p / p = (1 / 2 : ℝ) * D ^ 2 := by
    dsimp [X]
    rw [Real.mul_rpow (le_of_lt hLam) (Real.rpow_nonneg hD _), hLamPow,
      ← Real.rpow_mul hD]
    rw [hθp]
    field_simp [hp0.ne']
    rw [← Real.rpow_natCast D 2]
    rfl
  have hYpow : Y ^ q / q = C * A ^ q * B ^ 2 := by
    dsimp [Y, C]
    rw [show A * B ^ (1 - θ) * lam⁻¹ = A * (B ^ (1 - θ) * lam⁻¹) by ring]
    rw [Real.mul_rpow hA (mul_nonneg (Real.rpow_nonneg hB _) (inv_nonneg.mpr hLam.le)),
      Real.mul_rpow (Real.rpow_nonneg hB _) (inv_nonneg.mpr hLam.le),
      ← Real.rpow_mul hB, hθq]
    field_simp [hq0.ne']
    rw [← Real.rpow_natCast B 2]
    rfl
  have hXY : X * Y = A * B ^ (1 - θ) * D ^ (1 + θ) := by
    dsimp [X, Y]
    field_simp [ne_of_gt hLam]
  calc
    A * B ^ (1 - θ) * D ^ (1 + θ) = X * Y := hXY.symm
    _ ≤ X ^ p / p + Y ^ q / q := hYoung
    _ = (1 / 2 : ℝ) * D ^ 2 + C * A ^ q * B ^ 2 := by rw [hXpow, hYpow]
    _ = (1 / 2 : ℝ) * D ^ 2 + C * A ^ (2 / (1 - θ)) * B ^ 2 := by rfl

/-- The finite-exponent Young absorption used after the spatial interpolation
in `lem:lps-H1-estimate`. -/
theorem lps_h1_finite_absorption
    {s : ℝ} (hs : 3 < s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {A B D : ℝ}, 0 ≤ A → 0 ≤ B → 0 ≤ D →
      A * B ^ (1 - 3 / s) * D ^ (1 + 3 / s) ≤
        (1 / 2 : ℝ) * D ^ 2 + C * A ^ (2 * s / (s - 3)) * B ^ 2 := by
  have hs0 : 0 < s := lt_trans (by norm_num) hs
  let θ : ℝ := 3 / s
  have hθ0 : 0 < θ := by dsimp [θ]; positivity
  have hθ1 : θ < 1 := by
    dsimp [θ]
    rw [div_lt_one hs0]
    linarith only [hs]
  have hpow : 2 / (1 - 3 / s) = 2 * s / (s - 3) := by
    field_simp [ne_of_gt hs0, ne_of_gt (show 0 < s - 3 by linarith only [hs])]
  simpa [θ, hpow] using lps_h1_young hθ0 hθ1

/-- The separate `L^2_t L^∞_x` Young absorption in
`lem:lps-H1-estimate`. -/
theorem lps_h1_infinite_absorption
    {A B D : ℝ} :
    A * B * D ≤ (1 / 2 : ℝ) * D ^ 2 + (1 / 2 : ℝ) * A ^ 2 * B ^ 2 := by
  nlinarith only [sq_nonneg (D - A * B)]

/-- The finite Serrin absorption turns the strong-equation pairing estimate
into the differential inequality used by Grönwall (`lem:lps-H1-estimate`). -/
theorem lps_h1_finite_differential_absorption
    {s : ℝ} (hs : 3 < s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {dy d A B D f : ℝ},
      0 ≤ A → 0 ≤ B → 0 ≤ D → B ^ 2 = f → D ^ 2 = d →
      dy + 2 * d ≤ 2 * (A * B ^ (1 - 3 / s) * D ^ (1 + 3 / s)) →
      dy + d ≤ 2 * C * A ^ (2 * s / (s - 3)) * f := by
  obtain ⟨C, hC, hAbsAll⟩ := lps_h1_finite_absorption hs
  refine ⟨C, hC, ?_⟩
  intro dy d A B D f hA hB hD hBsq hDsq hBalance
  have hAbs := hAbsAll hA hB hD
  have hAbs2 :
      2 * (A * B ^ (1 - 3 / s) * D ^ (1 + 3 / s)) ≤
        d + 2 * C * A ^ (2 * s / (s - 3)) * f := by
    calc
      2 * (A * B ^ (1 - 3 / s) * D ^ (1 + 3 / s)) ≤
          2 * ((1 / 2 : ℝ) * D ^ 2 +
            C * A ^ (2 * s / (s - 3)) * B ^ 2) :=
        mul_le_mul_of_nonneg_left hAbs (by norm_num)
      _ = D ^ 2 + 2 * C * A ^ (2 * s / (s - 3)) * B ^ 2 := by ring
      _ = d + 2 * C * A ^ (2 * s / (s - 3)) * f := by rw [hDsq, hBsq]
  calc
    dy + d = (dy + 2 * d) - d := by ring
    _ ≤ 2 * (A * B ^ (1 - 3 / s) * D ^ (1 + 3 / s)) - d :=
      sub_le_sub_right hBalance d
    _ ≤ (d + 2 * C * A ^ (2 * s / (s - 3)) * f) - d :=
      sub_le_sub_right hAbs2 d
    _ = 2 * C * A ^ (2 * s / (s - 3)) * f := by ring

/-- The endpoint Serrin absorption turns the strong-equation pairing estimate
into its separate `L²_t L∞_x` differential inequality (`lem:lps-H1-estimate`). -/
theorem lps_h1_infinite_differential_absorption
    {dy d A B D f : ℝ}
    (hBsq : B ^ 2 = f) (hDsq : D ^ 2 = d)
    (hBalance : dy + 2 * d ≤ 2 * (A * B * D)) :
    dy + d ≤ A ^ 2 * f := by
  have hAbs2 : 2 * (A * B * D) ≤ d + A ^ 2 * f := by
    calc
      2 * (A * B * D) ≤
          2 * ((1 / 2 : ℝ) * D ^ 2 + (1 / 2 : ℝ) * A ^ 2 * B ^ 2) :=
        mul_le_mul_of_nonneg_left lps_h1_infinite_absorption (by norm_num)
      _ = D ^ 2 + A ^ 2 * B ^ 2 := by ring
      _ = d + A ^ 2 * f := by rw [hDsq, hBsq]
  calc
    dy + d = (dy + 2 * d) - d := by ring
    _ ≤ 2 * (A * B * D) - d := sub_le_sub_right hBalance d
    _ ≤ (d + A ^ 2 * f) - d := sub_le_sub_right hAbs2 d
    _ = A ^ 2 * f := by ring

/-- Interpolation of an `H¹` function between its `L²` norm and the
whole-space `L⁶` Sobolev estimate, in the exponents used by
`lem:lps-H1-estimate`. -/
theorem lps_h1_function_interpolation
    {q : ℝ} (hq2 : 2 < q) (hq6 : q < 6)
    (h : H1Function (Set.univ : Set Vec3)) :
    eLpNorm h.toFun (ENNReal.ofReal q) volume ≤
      eLpNorm h.toFun 2 volume ^ (1 - 3 * (1 / 2 - 1 / q)) *
        (gagliardoNirenbergSobolevConstant *
          eLpNorm (fun x => vec3EuclideanNorm (h.grad x)) 2 volume) ^
            (3 * (1 / 2 - 1 / q)) := by
  have hmem : MemLp h.toFun 2 volume := by
    simpa [CKN.MemL2On, CKN.MemLpOn, CKN.volumeOn] using h.memL2
  calc
    eLpNorm h.toFun (ENNReal.ofReal q) volume ≤
        eLpNorm h.toFun 2 volume ^ (1 - 3 * (1 / 2 - 1 / q)) *
          eLpNorm h.toFun 6 volume ^ (3 * (1 / 2 - 1 / q)) :=
      lps_interpolate_two_six hq2 hq6 hmem.aestronglyMeasurable
    _ ≤ eLpNorm h.toFun 2 volume ^ (1 - 3 * (1 / 2 - 1 / q)) *
          (gagliardoNirenbergSobolevConstant *
            eLpNorm (fun x => vec3EuclideanNorm (h.grad x)) 2 volume) ^
              (3 * (1 / 2 - 1 / q)) := by
      have hθ : 0 ≤ 3 * (1 / 2 - 1 / q) := by
        have hq0 : 0 < q := by linarith only [hq2]
        have h : 1 / q < 1 / 2 := by
          rw [div_lt_div_iff₀ hq0 (by norm_num : (0 : ℝ) < 2)]
          linarith only [hq2]
        positivity
      gcongr
      exact lps_h1_function_six h

/-- The finite branch of the mixed Serrin integral makes its spatial norm
integrable to the critical time power on any open time interval. This moment
is the coefficient used in the Gronwall estimate of `lem:lps-H1-estimate`. -/
theorem lps_h1_finite_time_moment_integrable
    {t₀ t₁ s : ℝ} {u : ParabolicPoint → Vec3}
    (hu : AEStronglyMeasurable u
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ t₁))))
    (hs : 3 < s)
    (hmix : (∫⁻ t in Ioo t₀ t₁,
      (∫⁻ x : Vec3,
        ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ s) ^
          ((2 * s / (s - 3)) / s)) < ⊤) :
    IntegrableOn
      (fun t : ℝ =>
        (eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u (x, t)))
          (ENNReal.ofReal s) volume).toReal ^ (2 * s / (s - 3)))
      (Ioo t₀ t₁) := by
  let μ : Measure (Vec3 × ℝ) :=
    (volume : Measure Vec3).prod (volume.restrict (Ioo t₀ t₁))
  have hslab :
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ t₁)) :
        Measure (Vec3 × ℝ)) = μ := by
    change (volume : Measure (Vec3 × ℝ)).restrict
        ((Set.univ : Set Vec3) ×ˢ Ioo t₀ t₁) = μ
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  have huProd : AEStronglyMeasurable u μ := hslab ▸ hu
  have hscalar : AEStronglyMeasurable
      (fun z : Vec3 × ℝ => vec3EuclideanNorm (u z)) μ :=
    continuous_vec3EuclideanNorm.comp_aestronglyMeasurable huProd
  let F : Vec3 × ℝ → ℝ≥0∞ := fun z =>
    ‖vec3EuclideanNorm (u z)‖ₑ ^ s
  have hF : AEMeasurable F μ := hscalar.enorm.pow_const _
  have hG : AEMeasurable (fun t : ℝ => ∫⁻ x : Vec3, F (x, t) ∂volume)
      (volume.restrict (Ioo t₀ t₁)) := hF.lintegral_prod_left'
  have hexp : 0 < (2 * s / (s - 3)) / s := by
    have hs0 : 0 < s := lt_trans (by norm_num) hs
    have hden : 0 < s - 3 := by linarith only [hs]
    positivity
  have hmomentMeas : AEMeasurable
      (fun t : ℝ => (∫⁻ x : Vec3, F (x, t) ∂volume) ^
        ((2 * s / (s - 3)) / s))
      (volume.restrict (Ioo t₀ t₁)) := hG.pow_const _
  have hFraw (z : Vec3 × ℝ) :
      ENNReal.ofReal (vec3EuclideanNorm (u z)) ^ s = F z := by
    rw [← Real.enorm_eq_ofReal (vec3EuclideanNorm_nonneg _)]
  have hEq :
      (∫⁻ t in Ioo t₀ t₁,
        (∫⁻ x : Vec3, F (x, t) ∂volume) ^ ((2 * s / (s - 3)) / s)) =
      (∫⁻ t in Ioo t₀ t₁,
        (∫⁻ x : Vec3,
          ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ s ∂volume) ^
            ((2 * s / (s - 3)) / s)) := by
    apply lintegral_congr
    intro t
    congr 1
    apply lintegral_congr
    intro x
    exact (hFraw (x, t)).symm
  have hmomentFinite :
      (∫⁻ t in Ioo t₀ t₁,
        (∫⁻ x : Vec3, F (x, t) ∂volume) ^ ((2 * s / (s - 3)) / s)) < ⊤ := by
    rw [hEq]
    exact hmix
  have hbase := integrable_toReal_of_lintegral_ne_top hmomentMeas hmomentFinite.ne
  have hsliceMeas : ∀ᵐ t ∂(volume.restrict (Ioo t₀ t₁)),
      AEStronglyMeasurable (fun x : Vec3 => vec3EuclideanNorm (u (x, t))) volume := by
    filter_upwards [huProd.prodMk_right] with t ht
    exact continuous_vec3EuclideanNorm.comp_aestronglyMeasurable ht
  refine hbase.congr ?_
  filter_upwards [hsliceMeas] with t ht
  have hs0 : ENNReal.ofReal s ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (lt_trans (by norm_num) hs)).ne'
  have hstop : ENNReal.ofReal s ≠ ⊤ := ENNReal.ofReal_ne_top
  have hsreal : (ENNReal.ofReal s).toReal = s :=
    ENNReal.toReal_ofReal (le_of_lt (lt_trans (by norm_num) hs))
  symm
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hs0 hstop ht, hsreal]
  have hroot : 0 ≤ (∫⁻ x : Vec3,
      ‖vec3EuclideanNorm (u (x, t))‖ₑ ^ s ∂volume).toReal := ENNReal.toReal_nonneg
  calc
    ((∫⁻ x : Vec3,
        ‖vec3EuclideanNorm (u (x, t))‖ₑ ^ s ∂volume) ^ (1 / s)).toReal ^
        (2 * s / (s - 3)) =
      (∫⁻ x : Vec3,
        ‖vec3EuclideanNorm (u (x, t))‖ₑ ^ s ∂volume).toReal ^
          ((1 / s) * (2 * s / (s - 3))) := by
      rw [← ENNReal.toReal_rpow, ← Real.rpow_mul hroot]
    _ = (∫⁻ x : Vec3,
        ‖vec3EuclideanNorm (u (x, t))‖ₑ ^ s ∂volume).toReal ^
          ((2 * s / (s - 3)) / s) := by
      congr 1
      ring
    _ = ((∫⁻ x : Vec3,
        ‖vec3EuclideanNorm (u (x, t))‖ₑ ^ s ∂volume) ^
          ((2 * s / (s - 3)) / s)).toReal := by
      rw [ENNReal.toReal_rpow]

/-- The finite Serrin coefficient is integrable on the closed interval as
well, since its endpoints have measure zero (`lem:lps-H1-estimate`). -/
theorem lps_h1_finite_time_moment_integrable_closed
    {t₀ t₁ s : ℝ} {u : ParabolicPoint → Vec3}
    (hu : AEStronglyMeasurable u
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ t₁))))
    (hs : 3 < s)
    (hmix : (∫⁻ t in Ioo t₀ t₁,
      (∫⁻ x : Vec3,
        ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ s) ^
          ((2 * s / (s - 3)) / s)) < ⊤) :
    IntegrableOn
      (fun t : ℝ =>
        (eLpNorm (fun x : Vec3 => vec3EuclideanNorm (u (x, t)))
          (ENNReal.ofReal s) volume).toReal ^ (2 * s / (s - 3)))
      (Icc t₀ t₁) := by
  have hopen := lps_h1_finite_time_moment_integrable hu hs hmix
  have hrestrict : (volume.restrict (Icc t₀ t₁) : Measure ℝ) =
      volume.restrict (Ioo t₀ t₁) :=
    Measure.restrict_congr_set Ioo_ae_eq_Icc.symm
  rw [IntegrableOn, hrestrict]
  exact hopen

end ESS

end
