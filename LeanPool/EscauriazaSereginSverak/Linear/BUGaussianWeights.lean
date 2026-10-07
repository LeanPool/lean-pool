/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.CarlemanGaussWeights
public import LeanPool.EscauriazaSereginSverak.Linear.UCDefs
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Vec3Norm

/-!
# Gaussian tail weights

The time weight comparison used in lem:bu-gaussian#weight-decay.
-/

public section


open MeasureTheory
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The fixed Gaussian decay exponent in the manuscript. -/
@[expose] def buGaussianBeta : ℝ := 1 / (10 : ℝ) ^ 6

/-- The logarithmic time weight at time 3/2 in the manuscript. -/
@[expose] def buGaussianH : ℝ := Real.log (gaussCarlemanTimeWeight (3 / 2))

/-- The logarithmic exponent of the collar Gaussian weight. -/
@[expose] def buGaussianLogTailExponent (a ρ s : ℝ) : ℝ :=
  -2 * a * Real.log (gaussCarlemanTimeWeight s) - ρ ^ 2 / (32 * s)

private theorem gaussCarlemanTimeWeight_hasDerivAt {s : ℝ} :
    HasDerivAt gaussCarlemanTimeWeight
      (Real.exp ((1 - s) / 3) * (1 - s / 3)) s := by
  change HasDerivAt (fun t : ℝ => t * Real.exp ((1 - t) / 3)) _ _
  have hlin : HasDerivAt (fun t : ℝ => (1 - t) / 3) (-1 / 3) s := by
    convert (HasDerivAt.const_sub 1 (hasDerivAt_id s)).div_const 3 using 1
    ext t
    simp [id]
  have hexp : HasDerivAt (fun t : ℝ => Real.exp ((1 - t) / 3))
      (Real.exp ((1 - s) / 3) * (-1 / 3)) s := by
    convert ((Real.hasDerivAt_exp ((1 - s) / 3)).comp s hlin) using 1
    ext t
    rfl
  have h := (hasDerivAt_id s).mul hexp
  convert h using 1
  · ext t
    rfl
  · simp
    ring_nf

private theorem gaussCarlemanTimeWeight_monotoneOn_three_halves :
    MonotoneOn gaussCarlemanTimeWeight (Set.Icc (3 / 2) 2) := by
  have hcont : ContinuousOn gaussCarlemanTimeWeight (Set.Icc (3 / 2) 2) := by
    intro s hs
    exact (gaussCarlemanTimeWeight_hasDerivAt.continuousAt).continuousWithinAt
  have hdiff : DifferentiableOn ℝ gaussCarlemanTimeWeight
      (interior (Set.Icc (3 / 2) 2)) := by
    intro s hs
    exact gaussCarlemanTimeWeight_hasDerivAt.differentiableAt.differentiableWithinAt
  have hderiv : ∀ s ∈ interior (Set.Icc (3 / 2) 2),
      0 ≤ deriv gaussCarlemanTimeWeight s := by
    intro s hs
    have hs' : 3 / 2 < s ∧ s < 2 := by simpa [interior_Icc] using hs
    rw [gaussCarlemanTimeWeight_hasDerivAt.deriv]
    apply mul_nonneg (Real.exp_pos _).le
    nlinarith only [hs'.2]
  exact monotoneOn_of_deriv_nonneg (convex_Icc _ _) hcont hdiff hderiv

private theorem buGaussianLogTailExponent_hasDerivAt
    {a ρ s : ℝ} (hs : 0 < s) :
    HasDerivAt (buGaussianLogTailExponent a ρ)
      (ρ ^ 2 / (32 * s ^ 2) - 2 * a * (1 / s - 1 / 3)) s := by
  have hweight : HasDerivAt gaussCarlemanTimeWeight
      (Real.exp ((1 - s) / 3) * (1 - s / 3)) s :=
    gaussCarlemanTimeWeight_hasDerivAt
  have hlog :
      HasDerivAt (fun t => Real.log (gaussCarlemanTimeWeight t))
        (1 / s - 1 / 3) s := by
    convert hweight.log (by dsimp [gaussCarlemanTimeWeight]; positivity) using 1
    dsimp [gaussCarlemanTimeWeight] at ⊢
    field_simp [Real.exp_ne_zero]
  have hgauss : HasDerivAt (fun t : ℝ => -ρ ^ 2 / (32 * t))
      (ρ ^ 2 / (32 * s ^ 2)) s := by
    convert (hasDerivAt_inv hs.ne').const_mul (-(ρ ^ 2 / 32)) using 1 <;>
      (try ext t) <;> field_simp
  have hsum := ((hlog.const_mul (-2 * a)).add hgauss)
  convert hsum using 1 <;>
    (try ext t) <;> simp [buGaussianLogTailExponent] <;>
      field_simp [hs.ne'] <;> ring_nf

/-- The logarithmic Gaussian tail exponent increases up to time 2
(lem:bu-gaussian#weight-decay). -/
theorem buGaussian_log_tail_monotone
    {a ρ β H : ℝ} (hH : 0 < H) (hβ : 0 < β)
    (hβH : β / H < 1 / 96) (ha : a = β * ρ ^ 2 / H) :
    MonotoneOn (buGaussianLogTailExponent a ρ) (Set.Icc (1 / 6) 2) := by
  have hcont : ContinuousOn (buGaussianLogTailExponent a ρ)
      (Set.Icc (1 / 6) 2) := by
    intro s hs
    have hspos : 0 < s := by linarith only [hs.1]
    exact (buGaussianLogTailExponent_hasDerivAt hspos).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ (buGaussianLogTailExponent a ρ)
      (interior (Set.Icc (1 / 6) 2)) := by
    intro s hs
    have hs' : 1 / 6 < s ∧ s < 2 := by simpa [interior_Icc] using hs
    have hspos : 0 < s := by linarith only [hs'.1]
    exact (buGaussianLogTailExponent_hasDerivAt hspos).differentiableAt.differentiableWithinAt
  have hderiv :
      ∀ s ∈ interior (Set.Icc (1 / 6) 2),
        0 ≤ deriv (buGaussianLogTailExponent a ρ) s := by
    intro s hs
    have hs' : 1 / 6 < s ∧ s < 2 := by simpa [interior_Icc] using hs
    have hspos : 0 < s := by linarith only [hs'.1]
    have hquad : s - s ^ 2 / 3 ≤ 3 / 4 := by
      nlinarith only [sq_nonneg (2 * s - 3)]
    have hsmall :
        (2 * (β / H)) * (3 / 4) < 1 / 32 := by
      calc
        (2 * (β / H)) * (3 / 4) = (3 / 2) * (β / H) := by ring
        _ < (3 / 2) * (1 / 96) :=
          mul_lt_mul_of_pos_left hβH (by norm_num)
        _ < 1 / 32 := by norm_num
    have hscaled :
        (2 * (β / H)) * (1 / s - 1 / 3) * (32 * s ^ 2) ≤ 1 := by
      have hspace := mul_le_mul_of_nonneg_left hquad
        (show 0 ≤ 2 * (β / H) by positivity)
      calc
        (2 * (β / H)) * (1 / s - 1 / 3) * (32 * s ^ 2) =
            32 * ((2 * (β / H)) * (s - s ^ 2 / 3)) := by
              field_simp [ne_of_gt hspos]
        _ ≤ 32 * ((2 * (β / H)) * (3 / 4)) :=
          mul_le_mul_of_nonneg_left hspace (by norm_num)
        _ ≤ 1 := by nlinarith only [hsmall]
    have hinner :
        (2 * (β / H)) * (1 / s - 1 / 3) ≤ 1 / (32 * s ^ 2) := by
      apply (le_div_iff₀ (by positivity : 0 < 32 * s ^ 2)).2
      exact hscaled
    have hformula :
        deriv (buGaussianLogTailExponent a ρ) s =
          ρ ^ 2 * (1 / (32 * s ^ 2) -
            (2 * (β / H)) * (1 / s - 1 / 3)) := by
      rw [(buGaussianLogTailExponent_hasDerivAt hspos).deriv, ha]
      field_simp
    rw [hformula]
    exact mul_nonneg (sq_nonneg ρ) (sub_nonneg.mpr hinner)
  exact monotoneOn_of_deriv_nonneg (convex_Icc _ _) hcont hdiff hderiv

/-- The collar weight equals the exponential of its logarithmic exponent on
positive times. -/
theorem buGaussian_weight_eq_exp_log_tail {a ρ s : ℝ} (hs : 0 < s) :
    gaussCarlemanTimeWeight s ^ (-2 * a) *
        Real.exp (-ρ ^ 2 / (32 * s)) =
      Real.exp (buGaussianLogTailExponent a ρ s) := by
  rw [Real.rpow_def_of_pos (by
    unfold gaussCarlemanTimeWeight
    positivity)]
  rw [← Real.exp_add]
  congr 1
  dsimp [buGaussianLogTailExponent]
  ring

private theorem log_gaussCarlemanTimeWeight_three_half_lower :
    1 / 6 < Real.log (gaussCarlemanTimeWeight (3 / 2 : ℝ)) := by
  have hlog := Real.lt_log_one_add_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)
  have hformula :
      Real.log (gaussCarlemanTimeWeight (3 / 2 : ℝ)) =
        Real.log (3 / 2 : ℝ) - 1 / 6 := by
    unfold gaussCarlemanTimeWeight
    rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp]
    norm_num
    ring
  rw [hformula]
  norm_num at hlog
  linarith only [hlog]

/-- The manuscript constants satisfy the hypotheses of the Gaussian
log-weight estimate. -/
theorem buGaussian_source_weight_parameters :
    0 < buGaussianBeta ∧ buGaussianBeta ≤ 1 / 128 ∧
      0 < buGaussianH ∧ buGaussianBeta / buGaussianH < 1 / 96 := by
  have hH : 1 / 6 < buGaussianH :=
    log_gaussCarlemanTimeWeight_three_half_lower
  have hβ : 0 < buGaussianBeta ∧ buGaussianBeta ≤ 1 / 128 := by
    norm_num [buGaussianBeta]
  have hHpos : 0 < buGaussianH := by
    have h16 : 0 < (1 / 6 : ℝ) := by norm_num
    linarith only [hH, h16]
  have hratio : buGaussianBeta / buGaussianH < 1 / 96 := by
    calc
      buGaussianBeta / buGaussianH < buGaussianBeta / (1 / 6) :=
        (div_lt_div_iff₀ hHpos
          (by norm_num : (0 : ℝ) < 1 / 6)).2 (by
            nlinarith only [hH, hβ.1])
      _ = 6 * buGaussianBeta := by field_simp
      _ < 1 / 96 := by norm_num [buGaussianBeta]
  exact ⟨hβ.1, hβ.2, hHpos, hratio⟩

/-- The late endpoint of the Gaussian time weight is at least its value at
time `3/2`, so its logarithm is nonnegative. -/
theorem buGaussian_time_weight_log_two_nonneg :
    0 ≤ Real.log (gaussCarlemanTimeWeight (2 : ℝ)) := by
  have hsource := buGaussian_source_weight_parameters
  have hweight : gaussCarlemanTimeWeight (3 / 2 : ℝ) ≤
      gaussCarlemanTimeWeight (2 : ℝ) :=
    gaussCarlemanTimeWeight_monotoneOn_three_halves
      ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ (by norm_num)
  have hlog := Real.log_le_log
    (by unfold gaussCarlemanTimeWeight; positivity) hweight
  have hpositive : 0 < Real.log (gaussCarlemanTimeWeight (3 / 2 : ℝ)) := by
    simpa [buGaussianH] using hsource.2.2.1
  linarith only [hlog, hpositive]

/-- The spatially independent endpoint of the Carleman time weight is the
source Gaussian factor (`lem:bu-gaussian#weight-decay`). -/
theorem buGaussian_time_weight_endpoint {a ρ : ℝ}
    (ha : a = buGaussianBeta * ρ ^ 2 / buGaussianH) :
    gaussCarlemanTimeWeight (3 / 2 : ℝ) ^ (-2 * a) =
      Real.exp (-2 * buGaussianBeta * ρ ^ 2) := by
  rw [Real.rpow_def_of_pos (by
    unfold gaussCarlemanTimeWeight
    positivity)]
  apply congrArg Real.exp
  have hHpos := buGaussian_source_weight_parameters.2.2.1
  have hHne : buGaussianH ≠ 0 := ne_of_gt hHpos
  change buGaussianH * (-2 * a) = _
  rw [ha]
  field_simp [hHne]

/-- The negative time power decreases on the late-time collar. -/
theorem buGaussian_time_weight_late_decreasing {a s : ℝ}
    (ha : 0 ≤ a) (hslo : 3 / 2 ≤ s) (hshi : s ≤ 2) :
    gaussCarlemanTimeWeight s ^ (-2 * a) ≤
      gaussCarlemanTimeWeight (3 / 2) ^ (-2 * a) := by
  have hmono := gaussCarlemanTimeWeight_monotoneOn_three_halves
  have hweight : gaussCarlemanTimeWeight (3 / 2) ≤
      gaussCarlemanTimeWeight s :=
    hmono ⟨by norm_num, by norm_num⟩ ⟨hslo, hshi⟩ hslo
  have hpos₁ : 0 < gaussCarlemanTimeWeight (3 / 2) := by
    unfold gaussCarlemanTimeWeight
    positivity
  have hpos₂ : 0 < gaussCarlemanTimeWeight s := by
    unfold gaussCarlemanTimeWeight
    positivity
  have hexponent : -2 * a ≤ 0 := by nlinarith only [ha]
  exact (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos hexponent)
    hpos₁ hpos₂ hweight

/-- The mass-only part of the late-time collar error has the source Gaussian
bound (`eq:bu-gaussian-collar`). -/
theorem buGaussian_omega2_pointwise_bound
    {a β ρ A barA scale s : ℝ} {x y : Vec3}
    (ha : 0 ≤ a) (hA : 0 ≤ A) (hAbar : A ≤ barA)
    (hslo : 3 / 2 ≤ s) (hshi : s ≤ 2)
    (hsmall : 4 * A * scale ^ 2 ≤ 1 / (8 * s))
    (hendpoint : gaussCarlemanTimeWeight (3 / 2) ^ (-2 * a) =
      Real.exp (-2 * β * ρ ^ 2))
    (v : Vec3) (hgrowth : vec3EuclideanNorm v ≤
      Real.exp (2 * A * vec3EuclideanNorm x ^ 2 +
        2 * A * scale ^ 2 * vec3EuclideanNorm y ^ 2)) :
    gaussCarlemanTimeWeight s ^ (-2 * a) *
        Real.exp (-(vec3EuclideanNorm y ^ 2) / (4 * s)) *
        vec3EuclideanNorm v ^ 2 ≤
      Real.exp (8 * barA * vec3EuclideanNorm x ^ 2) *
        Real.exp (-2 * β * ρ ^ 2) *
          Real.exp (-(vec3EuclideanNorm y ^ 2) / (8 * s)) := by
  let X : ℝ := vec3EuclideanNorm x ^ 2
  let Y : ℝ := vec3EuclideanNorm y ^ 2
  let W : ℝ := gaussCarlemanTimeWeight s ^ (-2 * a)
  let W₀ : ℝ := gaussCarlemanTimeWeight (3 / 2) ^ (-2 * a)
  let E : ℝ := Real.exp (-Y / (4 * s))
  let E₀ : ℝ := Real.exp (-Y / (8 * s))
  let V : ℝ := vec3EuclideanNorm v ^ 2
  have hspos : 0 < s := by linarith only [hslo]
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hY : 0 ≤ Y := by dsimp [Y]; positivity
  have htimeWeightPos : 0 < gaussCarlemanTimeWeight s := by
    unfold gaussCarlemanTimeWeight
    positivity
  have htimeWeight₀Pos : 0 < gaussCarlemanTimeWeight (3 / 2) := by
    unfold gaussCarlemanTimeWeight
    positivity
  have hW : 0 ≤ W := by
    dsimp [W]
    exact Real.rpow_nonneg htimeWeightPos.le _
  have hW₀ : 0 ≤ W₀ := by
    dsimp [W₀]
    exact Real.rpow_nonneg htimeWeight₀Pos.le _
  have hE : 0 ≤ E := by dsimp [E]; exact (Real.exp_pos _).le
  have hE₀ : 0 ≤ E₀ := by dsimp [E₀]; exact (Real.exp_pos _).le
  have hV : V ≤ Real.exp (4 * A * X + 4 * A * scale ^ 2 * Y) := by
    have hsq := (sq_le_sq₀ (vec3EuclideanNorm_nonneg v) (Real.exp_nonneg _)).2 hgrowth
    have hexp : Real.exp
        (2 * A * vec3EuclideanNorm x ^ 2 +
          2 * A * scale ^ 2 * vec3EuclideanNorm y ^ 2) ^ 2 =
        Real.exp (4 * A * X + 4 * A * scale ^ 2 * Y) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      dsimp [X, Y]
      ring
    dsimp [V, X, Y]
    rw [hexp] at hsq
    exact hsq
  have hYbound : 4 * A * scale ^ 2 * Y ≤ Y / (8 * s) := by
    calc
      4 * A * scale ^ 2 * Y = (4 * A * scale ^ 2) * Y := by ring
      _ ≤ (1 / (8 * s)) * Y := mul_le_mul_of_nonneg_right hsmall hY
      _ = Y / (8 * s) := by ring
  have hgaussExponent : -Y / (4 * s) + 4 * A * scale ^ 2 * Y ≤
      -Y / (8 * s) := by
    have hfirst : -Y / (4 * s) + 4 * A * scale ^ 2 * Y ≤
        -Y / (4 * s) + Y / (8 * s) := by linarith only [hYbound]
    calc
      -Y / (4 * s) + 4 * A * scale ^ 2 * Y ≤
          -Y / (4 * s) + Y / (8 * s) := hfirst
      _ = -Y / (8 * s) := by field_simp [ne_of_gt hspos]; ring
  have hgauss : E * Real.exp (4 * A * scale ^ 2 * Y) ≤ E₀ := by
    dsimp [E, E₀]
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr hgaussExponent
  have hweight : W ≤ W₀ := by
    dsimp [W, W₀]
    exact buGaussian_time_weight_late_decreasing ha hslo hshi
  have hcoeff : 4 * A ≤ 8 * barA := by nlinarith only [hA, hAbar]
  have hspaceExponent : 4 * A * X ≤ 8 * barA * X :=
    mul_le_mul_of_nonneg_right hcoeff hX
  have hspace : Real.exp (4 * A * X) ≤ Real.exp (8 * barA * X) :=
    Real.exp_le_exp.mpr hspaceExponent
  change W * E * V ≤ Real.exp (8 * barA * vec3EuclideanNorm x ^ 2) *
    Real.exp (-2 * β * ρ ^ 2) * E₀
  calc
    W * E * V ≤ W * E *
        Real.exp (4 * A * X + 4 * A * scale ^ 2 * Y) :=
      mul_le_mul_of_nonneg_left hV (mul_nonneg hW hE)
    _ = (W * Real.exp (4 * A * X)) *
        (E * Real.exp (4 * A * scale ^ 2 * Y)) := by
      dsimp [E]
      rw [Real.exp_add]
      ring
    _ ≤ (W * Real.exp (4 * A * X)) * E₀ :=
      mul_le_mul_of_nonneg_left hgauss (mul_nonneg hW (Real.exp_nonneg _))
    _ ≤ (W₀ * Real.exp (4 * A * X)) * E₀ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hweight (Real.exp_nonneg _)) hE₀
    _ ≤ (Real.exp (8 * barA * X) * W₀) * E₀ := by
      apply mul_le_mul_of_nonneg_right _ hE₀
      calc
        W₀ * Real.exp (4 * A * X) = Real.exp (4 * A * X) * W₀ := by ring
        _ ≤ Real.exp (8 * barA * X) * W₀ :=
          mul_le_mul_of_nonneg_right hspace hW₀
    _ = Real.exp (8 * barA * vec3EuclideanNorm x ^ 2) *
        Real.exp (-2 * β * ρ ^ 2) * E₀ := by
      rw [← hendpoint]

/-- The manuscript growth threshold makes the transverse Gaussian absorb the
rescaled growth on the late-time collar (`eq:bu-gaussian-collar`). -/
theorem buGaussian_source_spatial_absorption {A scale s : ℝ}
    (hA : 0 ≤ A) (hA0 : A ≤ 1 / (10 : ℝ) ^ 12)
    (hscale : scale ^ 2 ≤ 1 / 4)
    (hslo : 3 / 2 ≤ s) (hshi : s ≤ 2) :
    4 * A * scale ^ 2 ≤ 1 / (8 * s) := by
  have hspos : 0 < s := by linarith only [hslo]
  have hcoef : 4 * scale ^ 2 ≤ 1 := by nlinarith only [hscale]
  have hleft : 4 * A * scale ^ 2 = A * (4 * scale ^ 2) := by ring
  have hleftle : A * (4 * scale ^ 2) ≤ A := by
    calc
      A * (4 * scale ^ 2) ≤ A * 1 :=
        mul_le_mul_of_nonneg_left hcoef hA
      _ = A := by ring
  have hA16 : A ≤ 1 / 16 := by
    calc
      A ≤ 1 / (10 : ℝ) ^ 12 := hA0
      _ ≤ 1 / 16 := by norm_num
  have hfrac : 1 / 16 ≤ 1 / (8 * s) := by
    apply (le_div_iff₀ (by positivity : 0 < 8 * s)).2
    nlinarith only [hshi]
  calc
    4 * A * scale ^ 2 = A * (4 * scale ^ 2) := hleft
    _ ≤ A := hleftle
    _ ≤ 1 / 16 := hA16
    _ ≤ 1 / (8 * s) := hfrac

/-- The small source growth is absorbed by the transverse Gaussian at every
positive Carleman time up to two. -/
theorem buGaussian_source_spatial_absorption_all_times {A scale s : ℝ}
    (hA : 0 ≤ A) (hA0 : A ≤ 1 / (10 : ℝ) ^ 12)
    (hscale : scale ^ 2 ≤ 1 / 4) (hs : 0 < s) (hs2 : s ≤ 2) :
    4 * A * scale ^ 2 ≤ 1 / (8 * s) := by
  have hcoef : 4 * scale ^ 2 ≤ 1 := by nlinarith only [hscale]
  have hleft : 4 * A * scale ^ 2 = A * (4 * scale ^ 2) := by ring
  have hleftle : A * (4 * scale ^ 2) ≤ A := by
    calc
      A * (4 * scale ^ 2) ≤ A * 1 := mul_le_mul_of_nonneg_left hcoef hA
      _ = A := by ring
  have hA16 : A ≤ 1 / 16 := by
    calc
      A ≤ 1 / (10 : ℝ) ^ 12 := hA0
      _ ≤ 1 / 16 := by norm_num
  have hfrac : 1 / 16 ≤ 1 / (8 * s) := by
    apply (le_div_iff₀ (by positivity : 0 < 8 * s)).2
    nlinarith only [hs2]
  calc
    4 * A * scale ^ 2 = A * (4 * scale ^ 2) := hleft
    _ ≤ A := hleftle
    _ ≤ 1 / 16 := hA16
    _ ≤ 1 / (8 * s) := hfrac

/-- On a radial collar outside `ρ/2`, the weighted field is bounded by the
one-dimensional logarithmic tail used in `eq:bu-gaussian-collar`. -/
theorem buGaussian_radial_weighted_pointwise_bound
    {a ρ A barA scale s : ℝ} {x y : Vec3}
    (hA : 0 ≤ A) (hA0 : A ≤ 1 / (10 : ℝ) ^ 12)
    (hAbar : A ≤ barA)
    (hρ : 0 < ρ)
    (hscale : scale ^ 2 ≤ 1 / 4)
    (hs : 0 < s) (hs2 : s ≤ 2)
    (hradial : ρ / 2 ≤ vec3EuclideanNorm y)
    (v : Vec3)
    (hgrowth : vec3EuclideanNorm v ≤
      Real.exp (2 * A * vec3EuclideanNorm x ^ 2 +
        2 * A * scale ^ 2 * vec3EuclideanNorm y ^ 2)) :
    ucGaussianWeight a (y, s) * vec3EuclideanNorm v ^ 2 ≤
      Real.exp (8 * barA * vec3EuclideanNorm x ^ 2) *
        Real.exp (buGaussianLogTailExponent a ρ s) := by
  let X := vec3EuclideanNorm x ^ 2
  let Y := vec3EuclideanNorm y ^ 2
  have hsmall := buGaussian_source_spatial_absorption_all_times
    hA hA0 hscale hs hs2
  have hY : 0 ≤ Y := by dsimp [Y]; positivity
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hV : vec3EuclideanNorm v ^ 2 ≤
      Real.exp (4 * A * X + 4 * A * scale ^ 2 * Y) := by
    have hsq := (sq_le_sq₀ (vec3EuclideanNorm_nonneg v) (Real.exp_nonneg _)).2 hgrowth
    have hexp : Real.exp
        (2 * A * vec3EuclideanNorm x ^ 2 +
          2 * A * scale ^ 2 * vec3EuclideanNorm y ^ 2) ^ 2 =
        Real.exp (4 * A * X + 4 * A * scale ^ 2 * Y) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      dsimp [X, Y]
      ring
    dsimp [X, Y]
    rw [hexp] at hsq
    exact hsq
  have hYsmall : 4 * A * scale ^ 2 * Y ≤ Y / (8 * s) := by
    calc
      4 * A * scale ^ 2 * Y = (4 * A * scale ^ 2) * Y := by ring
      _ ≤ (1 / (8 * s)) * Y := mul_le_mul_of_nonneg_right hsmall hY
      _ = Y / (8 * s) := by ring
  have hgaussExp : -Y / (4 * s) + 4 * A * scale ^ 2 * Y ≤
      -Y / (8 * s) := by
    have hfirst : -Y / (4 * s) + 4 * A * scale ^ 2 * Y ≤
        -Y / (4 * s) + Y / (8 * s) := by linarith only [hYsmall]
    calc
      -Y / (4 * s) + 4 * A * scale ^ 2 * Y ≤
          -Y / (4 * s) + Y / (8 * s) := hfirst
      _ = -Y / (8 * s) := by field_simp [ne_of_gt hs]; ring
  have hradialSq : ρ ^ 2 / (32 * s) ≤ Y / (8 * s) := by
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 32 * s)
      (by positivity : (0 : ℝ) < 8 * s)).2
    have hnorm : 0 ≤ vec3EuclideanNorm y := vec3EuclideanNorm_nonneg y
    have hleft : 0 ≤ ρ / 2 := by positivity
    have hsquare : ρ ^ 2 / 4 ≤ vec3EuclideanNorm y ^ 2 := by
      have hsq := (sq_le_sq₀ hleft hnorm).2 hradial
      nlinarith only [hsq]
    nlinarith only [hsquare, hs]
  have htail : Real.exp (-Y / (8 * s)) ≤
      Real.exp (-ρ ^ 2 / (32 * s)) := by
    apply Real.exp_le_exp.mpr
    calc
      -Y / (8 * s) = -(Y / (8 * s)) := by ring
      _ ≤ -(ρ ^ 2 / (32 * s)) := neg_le_neg hradialSq
      _ = -ρ ^ 2 / (32 * s) := by ring
  have hspaceCoeff : 4 * A ≤ 8 * barA := by nlinarith only [hA, hAbar]
  have hspace : Real.exp (4 * A * X) ≤ Real.exp (8 * barA * X) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hspaceCoeff hX)
  let W := gaussCarlemanTimeWeight s ^ (-2 * a)
  let Eₓ := Real.exp (8 * barA * X)
  have hW : 0 ≤ W := by
    dsimp [W]
    unfold gaussCarlemanTimeWeight
    exact Real.rpow_nonneg (by positivity) _
  have hW0 : 0 ≤ gaussCarlemanTimeWeight s ^ (-2 * a) := by
    exact hW
  have hExpX : 0 ≤ Real.exp (4 * A * X) := Real.exp_nonneg _
  have hExpX' : 0 ≤ Eₓ := Real.exp_nonneg _
  have hExpY : 0 ≤ Real.exp (-Y / (4 * s)) := Real.exp_nonneg _
  have hExpResidual : 0 ≤ Real.exp (4 * A * scale ^ 2 * Y) :=
    Real.exp_nonneg _
  have hV' : vec3EuclideanNorm v ^ 2 ≤
      Real.exp (4 * A * X) * Real.exp (4 * A * scale ^ 2 * Y) := by
    rw [← Real.exp_add]
    simpa only [add_comm] using hV
  calc
    ucGaussianWeight a (y, s) * vec3EuclideanNorm v ^ 2 =
        W * Real.exp (-Y / (4 * s)) * vec3EuclideanNorm v ^ 2 := by
          simp [ucGaussianWeight, W, Y, mul_assoc]
    _ ≤ W * (Real.exp (4 * A * X) *
          (Real.exp (-Y / (4 * s)) *
            Real.exp (4 * A * scale ^ 2 * Y))) := by
          calc
            _ ≤ W * Real.exp (-Y / (4 * s)) *
                (Real.exp (4 * A * X) *
                  Real.exp (4 * A * scale ^ 2 * Y)) :=
                    mul_le_mul_of_nonneg_left hV' (mul_nonneg hW hExpY)
            _ = _ := by ring
    _ ≤ W * (Real.exp (4 * A * X) * Real.exp (-Y / (8 * s))) := by
          apply mul_le_mul_of_nonneg_left _ hW
          apply mul_le_mul_of_nonneg_left _ hExpX
          rw [← Real.exp_add]
          exact Real.exp_le_exp.mpr hgaussExp
    _ ≤ W * (Real.exp (8 * barA * X) *
          Real.exp (-ρ ^ 2 / (32 * s))) := by
          apply mul_le_mul_of_nonneg_left _ hW
          exact mul_le_mul hspace htail (Real.exp_nonneg _) (Real.exp_nonneg _)
    _ = Eₓ * (W * Real.exp (-ρ ^ 2 / (32 * s))) := by
          dsimp [Eₓ, W]
          ring
    _ = Real.exp (8 * barA * vec3EuclideanNorm x ^ 2) *
          Real.exp (buGaussianLogTailExponent a ρ s) := by
          calc
            _ = Real.exp (8 * barA * vec3EuclideanNorm x ^ 2) *
                (gaussCarlemanTimeWeight s ^ (-2 * a) *
                  Real.exp (-ρ ^ 2 / (32 * s))) := by
                    dsimp [Eₓ, W, X]
            _ = _ := by rw [buGaussian_weight_eq_exp_log_tail hs]

/-- The weight integral is bounded by its exponentially small endpoint value
(lem:bu-gaussian#weight-decay). -/
theorem buGaussian_log_tail_integral_bound
    {a ρ β H : ℝ} (hH : 0 < H) (hβ : 0 < β)
    (hβsmall : β ≤ 1 / 128) (hβH : β / H < 1 / 96)
    (ha : a = β * ρ ^ 2 / H) :
    (∫ s in (1 / 6 : ℝ)..2,
      Real.exp (buGaussianLogTailExponent a ρ s)) ≤
      2 * Real.exp (-2 * β * ρ ^ 2) := by
  have haNonneg : 0 ≤ a := by rw [ha]; positivity
  have hmono := buGaussian_log_tail_monotone hH hβ hβH ha
  have hend : buGaussianLogTailExponent a ρ 2 ≤ -2 * β * ρ ^ 2 := by
    have hlogHalf : 1 / 2 < Real.log 2 := by
      have h := Real.lt_log_one_add_of_pos (show (0 : ℝ) < 1 by norm_num)
      norm_num at h ⊢
      linarith only [h]
    have hlogwt :
        Real.log (gaussCarlemanTimeWeight 2) = Real.log 2 - 1 / 3 := by
      unfold gaussCarlemanTimeWeight
      rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp]
      norm_num
      ring
    have hlogwtpos : 0 < Real.log (gaussCarlemanTimeWeight 2) := by
      rw [hlogwt]
      linarith only [hlogHalf]
    have hneg : -2 * a ≤ 0 := by nlinarith only [haNonneg]
    have hfirst : -2 * a * Real.log (gaussCarlemanTimeWeight 2) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hneg (le_of_lt hlogwtpos)
    have hcoeff : 2 * β ≤ 1 / 64 := by nlinarith only [hβsmall]
    have hsecond : -ρ ^ 2 / 64 ≤ -2 * β * ρ ^ 2 := by
      nlinarith only [hcoeff, sq_nonneg ρ]
    dsimp [buGaussianLogTailExponent]
    norm_num
    linarith only [hfirst, hsecond]
  have hpoint : ∀ s ∈ Set.Icc (1 / 6 : ℝ) 2,
      Real.exp (buGaussianLogTailExponent a ρ s) ≤
        Real.exp (-2 * β * ρ ^ 2) := by
    intro s hs
    have hle : buGaussianLogTailExponent a ρ s ≤
        buGaussianLogTailExponent a ρ 2 :=
      hmono hs ⟨by norm_num, le_rfl⟩ hs.2
    exact Real.exp_le_exp.mpr (le_trans hle hend)
  have hcont : ContinuousOn (fun s =>
      Real.exp (buGaussianLogTailExponent a ρ s))
      (Set.Icc (1 / 6 : ℝ) 2) := by
    have hex : ContinuousOn (buGaussianLogTailExponent a ρ)
        (Set.Icc (1 / 6 : ℝ) 2) := by
      intro s hs
      have hspos : 0 < s := by linarith only [hs.1]
      exact (buGaussianLogTailExponent_hasDerivAt hspos).continuousAt.continuousWithinAt
    exact Real.continuous_exp.continuousOn.comp hex (by
      intro s hs
      exact Set.mem_univ _)
  have hInt : IntervalIntegrable
      (fun s : ℝ => Real.exp (buGaussianLogTailExponent a ρ s))
      volume (1 / 6 : ℝ) 2 :=
    hcont.intervalIntegrable_of_Icc (μ := volume) (by norm_num)
  calc
    (∫ s in (1 / 6 : ℝ)..2,
        Real.exp (buGaussianLogTailExponent a ρ s)) ≤
        ∫ s in (1 / 6 : ℝ)..2, (fun _ : ℝ =>
          Real.exp (-2 * β * ρ ^ 2)) s :=
      intervalIntegral.integral_mono_on (by norm_num) hInt
        intervalIntegrable_const hpoint
    _ = (2 - (1 / 6 : ℝ)) * Real.exp (-2 * β * ρ ^ 2) := by
      rw [intervalIntegral.integral_const]
      norm_num
    _ ≤ 2 * Real.exp (-2 * β * ρ ^ 2) := by
      have hexp : 0 ≤ Real.exp (-2 * β * ρ ^ 2) := (Real.exp_pos _).le
      nlinarith only [hexp]

/-- The collar polynomial is absorbed by the remaining Gaussian factor
(`lem:bu-gaussian#weight-decay`). -/
theorem buGaussian_polynomial_tail_bound {β H ρ : ℝ}
    (hβ : 0 < β) (hH : 0 < H) (hρ : 1 ≤ ρ) :
    (1 + (β / H) * ρ ^ 2) * (1 + ρ) ^ 2 *
        Real.exp (-2 * β * ρ ^ 2) ≤
      (16 * (1 + β / H) / β ^ 2) * Real.exp (-β * ρ ^ 2) := by
  have hρsq : 1 ≤ ρ ^ 2 := by nlinarith only [hρ]
  have hratio : 0 ≤ β / H := by positivity
  have hfactor₁ : 1 + (β / H) * ρ ^ 2 ≤ (1 + β / H) * ρ ^ 2 := by
    nlinarith only [hρsq, hratio]
  have hfactor₂ : (1 + ρ) ^ 2 ≤ 4 * ρ ^ 2 := by
    nlinarith only [hρ]
  have hpoly :
      (1 + (β / H) * ρ ^ 2) * (1 + ρ) ^ 2 ≤
        4 * (1 + β / H) * ρ ^ 4 := by
    calc
      (1 + (β / H) * ρ ^ 2) * (1 + ρ) ^ 2 ≤
          ((1 + β / H) * ρ ^ 2) * (1 + ρ) ^ 2 :=
        mul_le_mul_of_nonneg_right hfactor₁ (sq_nonneg _)
      _ ≤ ((1 + β / H) * ρ ^ 2) * (4 * ρ ^ 2) :=
        mul_le_mul_of_nonneg_left hfactor₂ (by positivity)
      _ = 4 * (1 + β / H) * ρ ^ 4 := by ring
  let x : ℝ := β * ρ ^ 2
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hExp : (1 + x / 2) ≤ Real.exp (x / 2) := by
    calc
      1 + x / 2 = x / 2 + 1 := by ring
      _ ≤ Real.exp (x / 2) := Real.add_one_le_exp _
  have hHalf : x / 2 ≤ 1 + x / 2 := by linarith only [hx]
  have hSq : (x / 2) ^ 2 ≤ (1 + x / 2) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).2 hHalf
  have hExpSq : (1 + x / 2) ^ 2 ≤ Real.exp (x / 2) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).2 hExp
  have hExpSum : (1 + x / 2) ^ 2 ≤ Real.exp x := by
    calc
      (1 + x / 2) ^ 2 ≤ Real.exp (x / 2) ^ 2 := hExpSq
      _ = Real.exp x := by rw [pow_two, ← Real.exp_add]; congr 1; ring
  have hρfour : ρ ^ 4 ≤ (4 / β ^ 2) * Real.exp x := by
    have hscaled : (x / 2) ^ 2 = (β ^ 2 / 4) * ρ ^ 4 := by
      dsimp [x]
      ring
    rw [hscaled] at hSq
    have hmul : β ^ 2 * ρ ^ 4 ≤ 4 * Real.exp x := by
      nlinarith only [hSq, hExpSum]
    have hβsq : 0 < β ^ 2 := sq_pos_of_pos hβ
    calc
      ρ ^ 4 = (β ^ 2 * ρ ^ 4) / β ^ 2 := by field_simp
      _ ≤ (4 * Real.exp x) / β ^ 2 := div_le_div_of_nonneg_right hmul hβsq.le
      _ = (4 / β ^ 2) * Real.exp x := by ring
  calc
    _ ≤ (4 * (1 + β / H) * ρ ^ 4) * Real.exp (-2 * β * ρ ^ 2) :=
      mul_le_mul_of_nonneg_right hpoly (Real.exp_nonneg _)
    _ ≤ (4 * (1 + β / H) * ((4 / β ^ 2) * Real.exp x)) *
        Real.exp (-2 * β * ρ ^ 2) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hρfour (by positivity)) (Real.exp_nonneg _)
    _ = (16 * (1 + β / H) / β ^ 2) * Real.exp (-β * ρ ^ 2) := by
      dsimp [x]
      calc
        _ = (16 * (1 + β / H) / β ^ 2) *
            (Real.exp (β * ρ ^ 2) * Real.exp (-2 * β * ρ ^ 2)) := by ring_nf
        _ = (16 * (1 + β / H) / β ^ 2) * Real.exp (-β * ρ ^ 2) := by
          rw [← Real.exp_add]
          congr 1; ring_nf

/-- The preceding interval estimate with the fixed manuscript exponent and
time weight. -/
theorem buGaussian_source_log_tail_integral_bound {a ρ : ℝ}
    (ha : a = buGaussianBeta * ρ ^ 2 / buGaussianH) :
    (∫ s in (1 / 6 : ℝ)..2,
      Real.exp (buGaussianLogTailExponent a ρ s)) ≤
      2 * Real.exp (-2 * buGaussianBeta * ρ ^ 2) := by
  obtain ⟨hβ, hβsmall, hH, hβH⟩ := buGaussian_source_weight_parameters
  exact buGaussian_log_tail_integral_bound hH hβ hβsmall hβH ha

end ESS
