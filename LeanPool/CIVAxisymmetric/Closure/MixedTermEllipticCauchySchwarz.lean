/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Closure.StretchingBounds
public import LeanPool.CIVAxisymmetric.Identities.Vorticity

/-!
# The elliptic Cauchy-Schwarz bound of `eq:aniso:closure:mixed:bound`

This file proves the third piece of the elliptic Cauchy-Schwarz step that feeds into the mixed
term bound `eq:aniso:closure:mixed:bound`: the classical `L²` Cauchy-Schwarz inequality splits
the two second-derivative-carrying summands of `eq:aniso:closure:mixed` by `∫|f g| ≤ √(∫f²) √(∫g²)`.
The caller supplies the elliptic bounds `‖χ ∇b‖ ≤ C √(Y+1)` and `‖χ ∇²b‖ ≤ C √(M+1)` as `hY`,
`hM`, `hY1`, `hM1`.
-/

public section

open MeasureTheory Set
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV



/-- The Cauchy-Schwarz inequality for the Bochner integral on `Vec3`, in the square-root form
used by the comparison energy estimate. -/
theorem abs_integral_mul_le_sqrt_mul_sqrt {f g : Vec3 → ℝ}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    |∫ x : Vec3, f x * g x| ≤ Real.sqrt (∫ x : Vec3, f x ^ 2) * Real.sqrt (∫ x : Vec3, g x ^ 2)
      := by
  have hpq : Real.HolderConjugate 2 2 := Real.HolderConjugate.two_two
  have hFabs : MemLp (fun x => |f x|) (ENNReal.ofReal (2 : ℝ)) volume := by
    have h2 : ENNReal.ofReal (2 : ℝ) = (2 : ENNReal) := by norm_num
    rw [h2]
    exact hf.abs
  have hGabs : MemLp (fun x => |g x|) (ENNReal.ofReal (2 : ℝ)) volume := by
    have h2 : ENNReal.ofReal (2 : ℝ) = (2 : ENNReal) := by norm_num
    rw [h2]
    exact hg.abs
  have h_nonneg_f : 0 ≤ᵐ[volume] fun x => |f x| :=
    Filter.Eventually.of_forall fun x => abs_nonneg _
  have h_nonneg_g : 0 ≤ᵐ[volume] fun x => |g x| :=
    Filter.Eventually.of_forall fun x => abs_nonneg _
  have h_holder := integral_mul_le_Lp_mul_Lq_of_nonneg hpq h_nonneg_f h_nonneg_g hFabs hGabs
  -- h_holder: ∫ |f| * |g| ≤ (∫ |f|^2)^(1/2) * (∫ |g|^2)^(1/2)
  have hrw : ∀ h : Vec3 → ℝ, (∫ x : Vec3, |h x| ^ (2 : ℝ)) = ∫ x : Vec3, h x ^ 2 := by
    intro h
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show |h x| ^ (2 : ℝ) = h x ^ 2
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
  rw [hrw f, hrw g] at h_holder
  have h_sqrt_eq : (∫ x : Vec3, f x ^ 2) ^ ((1 : ℝ) / (2 : ℝ)) = Real.sqrt (∫ x : Vec3, f x ^ 2)
    := by
    rw [Real.sqrt_eq_rpow]
  have h_sqrt_eq_g : (∫ x : Vec3, g x ^ 2) ^ ((1 : ℝ) / (2 : ℝ)) = Real.sqrt (∫ x : Vec3, g x ^
    2) := by
    rw [Real.sqrt_eq_rpow]
  rw [h_sqrt_eq, h_sqrt_eq_g] at h_holder
  -- h_holder: ∫ |f| * |g| ≤ √(∫ f²) * √(∫ g²)
  calc
    |∫ x : Vec3, f x * g x| ≤ ∫ x : Vec3, |f x * g x| := abs_integral_le_integral_abs
    _ = ∫ x : Vec3, |f x| * |g x| := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      show |f x * g x| = |f x| * |g x|
      rw [abs_mul]
    _ ≤ Real.sqrt (∫ x : Vec3, f x ^ 2) * Real.sqrt (∫ x : Vec3, g x ^ 2) := h_holder

/-- The elliptic Cauchy-Schwarz bound for the `z`-derivative term of
`eq:aniso:closure:mixed`.  The second-derivative factor is
`χ · ∂_z² u_z` and the first-derivative factor is `χ · (curl u)_z`; Cauchy-Schwarz gives
`∫ χ² (∂_z² u_z) ((curl u)_z) ≤ √(M+1) √Y`. -/
theorem abs_integral_cutoff_sq_secondPartial_mul_curl_le
    {u : ParabolicPoint → Vec3} {χ : Vec3 → ℝ} {t Y M : ℝ}
    (hf : MemLp (fun x : Vec3 => χ x
        * spatialSecondPartial (fun w => u w 2) 0 2 (x, t)) 2 volume)
    (hg : MemLp (fun x : Vec3 => χ x * curlComp u 2 (x, t)) 2 volume)
    (hM : (∫ x : Vec3, (χ x * spatialSecondPartial (fun w => u w 2) 0 2 (x, t)) ^ 2) ≤ M + 1)
    (hY : (∫ x : Vec3, (χ x * curlComp u 2 (x, t)) ^ 2) ≤ Y) :
    |∫ x : Vec3, χ x ^ 2 * spatialSecondPartial (fun w => u w 2) 0 2 (x, t) * curlComp u 2 (x, t)|
      ≤ Real.sqrt (M + 1) * Real.sqrt Y := by
  set f : Vec3 → ℝ := fun x => χ x * spatialSecondPartial (fun w => u w 2) 0 2 (x, t) with hf_def
  set g : Vec3 → ℝ := fun x => χ x * curlComp u 2 (x, t) with hg_def
  have h_abs_eq : (∫ x : Vec3, χ x ^ 2 * spatialSecondPartial (fun w => u w 2) 0 2 (x, t)
      * curlComp u 2 (x, t)) = (∫ x : Vec3, f x * g x) :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => by
      dsimp [f, g]
      ring)
  calc
    |∫ x : Vec3, χ x ^ 2 * spatialSecondPartial (fun w => u w 2) 0 2 (x, t)
        * curlComp u 2 (x, t)|
        = |∫ x : Vec3, f x * g x| := congrArg abs h_abs_eq
    _ ≤ Real.sqrt (∫ x : Vec3, f x ^ 2) * Real.sqrt (∫ x : Vec3, g x ^ 2) :=
      abs_integral_mul_le_sqrt_mul_sqrt hf hg
    _ = Real.sqrt (∫ x : Vec3,
        (χ x * spatialSecondPartial (fun w => u w 2) 0 2 (x, t)) ^ 2)
        * Real.sqrt (∫ x : Vec3, (χ x * curlComp u 2 (x, t)) ^ 2) := rfl
    _ ≤ Real.sqrt (M + 1) * Real.sqrt Y := by
      have h_sqrt_M : Real.sqrt (∫ x : Vec3,
          (χ x * spatialSecondPartial (fun w => u w 2) 0 2 (x, t)) ^ 2)
          ≤ Real.sqrt (M + 1) :=
        Real.sqrt_le_sqrt hM
      have h_sqrt_Y : Real.sqrt (∫ x : Vec3, (χ x * curlComp u 2 (x, t)) ^ 2)
          ≤ Real.sqrt Y :=
        Real.sqrt_le_sqrt hY
      have h_nonneg_sqrt_Mp1 : 0 ≤ Real.sqrt (M + 1) := Real.sqrt_nonneg _
      have h_nonneg_sqrt_Y_int : 0 ≤ Real.sqrt (∫ x : Vec3,
          (χ x * curlComp u 2 (x, t)) ^ 2) := Real.sqrt_nonneg _
      exact mul_le_mul h_sqrt_M h_sqrt_Y h_nonneg_sqrt_Y_int h_nonneg_sqrt_Mp1

/-- The elliptic Cauchy-Schwarz bound for the `r`-derivative term of
`eq:aniso:closure:mixed`.  The first-derivative factor is `χ · ∂_r u_z` and the
`z`-derivative-of-curl factor is `χ · ∂_z (curl u)_z`; Cauchy-Schwarz gives
`∫ χ² (∂_r u_z) (∂_z (curl u)_z) ≤ √(Y+1) √M`. -/
theorem abs_integral_cutoff_sq_firstPartial_mul_dzcurl_le
    {u : ParabolicPoint → Vec3} {χ : Vec3 → ℝ} {t Y M : ℝ}
    (hf : MemLp (fun x : Vec3 => χ x * spatialPartial (fun w => u w 2) 0 (x, t)) 2 volume)
    (hg : MemLp (fun x : Vec3 => χ x
        * spatialPartial (fun w => curlComp u 2 w) 2 (x, t)) 2 volume)
    (hY1 : (∫ x : Vec3, (χ x * spatialPartial (fun w => u w 2) 0 (x, t)) ^ 2) ≤ Y + 1)
    (hM1 : (∫ x : Vec3, (χ x * spatialPartial (fun w => curlComp u 2 w) 2 (x, t)) ^ 2) ≤ M) :
    |∫ x : Vec3, χ x ^ 2 * spatialPartial (fun w => u w 2) 0 (x, t)
        * spatialPartial (fun w => curlComp u 2 w) 2 (x, t)|
      ≤ Real.sqrt (Y + 1) * Real.sqrt M := by
  set f : Vec3 → ℝ := fun x => χ x * spatialPartial (fun w => u w 2) 0 (x, t) with hf_def
  set g : Vec3 → ℝ := fun x => χ x * spatialPartial (fun w => curlComp u 2 w) 2 (x, t) with hg_def
  have h_abs_eq : (∫ x : Vec3, χ x ^ 2 * spatialPartial (fun w => u w 2) 0 (x, t)
      * spatialPartial (fun w => curlComp u 2 w) 2 (x, t)) = (∫ x : Vec3, f x * g x) :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => by
      dsimp [f, g]
      ring)
  calc
    |∫ x : Vec3, χ x ^ 2 * spatialPartial (fun w => u w 2) 0 (x, t)
        * spatialPartial (fun w => curlComp u 2 w) 2 (x, t)|
        = |∫ x : Vec3, f x * g x| := congrArg abs h_abs_eq
    _ ≤ Real.sqrt (∫ x : Vec3, f x ^ 2) * Real.sqrt (∫ x : Vec3, g x ^ 2) :=
      abs_integral_mul_le_sqrt_mul_sqrt hf hg
    _ = Real.sqrt (∫ x : Vec3,
        (χ x * spatialPartial (fun w => u w 2) 0 (x, t)) ^ 2)
        * Real.sqrt (∫ x : Vec3,
          (χ x * spatialPartial (fun w => curlComp u 2 w) 2 (x, t)) ^ 2) := rfl
    _ ≤ Real.sqrt (Y + 1) * Real.sqrt M := by
      have h_sqrt_Y1 : Real.sqrt (∫ x : Vec3,
          (χ x * spatialPartial (fun w => u w 2) 0 (x, t)) ^ 2)
          ≤ Real.sqrt (Y + 1) :=
        Real.sqrt_le_sqrt hY1
      have h_sqrt_M1 : Real.sqrt (∫ x : Vec3,
          (χ x * spatialPartial (fun w => curlComp u 2 w) 2 (x, t)) ^ 2)
          ≤ Real.sqrt M :=
        Real.sqrt_le_sqrt hM1
      have h_nonneg_sqrt_Yp1 : 0 ≤ Real.sqrt (Y + 1) := Real.sqrt_nonneg _
      have h_nonneg_sqrt_M1_int : 0 ≤ Real.sqrt (∫ x : Vec3,
          (χ x * spatialPartial (fun w => curlComp u 2 w) 2 (x, t)) ^ 2) := Real.sqrt_nonneg _
      exact mul_le_mul h_sqrt_Y1 h_sqrt_M1 h_nonneg_sqrt_M1_int h_nonneg_sqrt_Yp1

end CIV
