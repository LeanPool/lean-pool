/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepSchauderInteriorHess
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepSchauderWindow

/-!
# OneStepEvenBoundHessian

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The two analytic atoms of the even-part bound `(★)`

The boundary branch of the Schauder gradient-Hölder estimate closes its **even part** by
comparing the harmonic competitor with its own first-order Taylor polynomial at a point of
the window and paying the resulting quadratic remainder against the Hessian.  This module
supplies the two atoms that argument consumes:

1. **Second-order Taylor with a Hessian remainder on a convex set.**  For `u` twice
   differentiable on a convex `S` with `‖D²u‖ ≤ M` there,
   ```text
     |u(q) − u(p) − Du(p)(q − p)| ≤ M · ‖q − p‖² ,     p, q ∈ S .
   ```
   The route is the mean-value inequality applied **twice** on the segment `[p, q] ⊆ S`: once to
   `Du` (giving `‖Du(z) − Du(p)‖ ≤ M‖q − p‖` along the segment) and once, in the `φ`-corrected
   form `Convex.norm_image_sub_le_of_norm_fderiv_le'`, to `u` itself.  The constant is `M` rather
   than the sharp `M/2`; the even-part bound is insensitive to that factor.  A `Vec d` shape is
   provided as well, obtained by transporting the convex set through the coordinate identification
   `toEuc`.

2. **The interior Hessian estimate re-read against the volume-normalized `L²`
   seminorm.**  The transplanted native estimate
   `interiorSecondDerivEstimateL2` measures the data by the CoarseGraining
   mean-square deviation on the *concentric* Euclidean ball.  The boundary
   branch instead carries its data as `Support.normalizedL2On W V` on an
   **arbitrary** window `W` that merely contains a sup-ball `Metric.ball p r`
   at the point.  Rebasing costs exactly the volume ratio `|W| / |euclideanBall
   p (r/2)|`, which the scale-free lower bound `volume_toReal_euclideanBall_ge`
   converts into the explicit factor `(|W| / rᵈ) · (2(d+1))ᵈ`; taking square
   roots gives
   ```text
     ‖D²V(p)‖ ≤ C(d) · r⁻¹ · r⁻¹ · √(|W| / rᵈ) · ‖V‖_{L²(W)} ,
   ```
   with `C(d) = 4 · C_native(d) · √((2(d+1))ᵈ)`, the `4` absorbing `(r/2)⁻¹(r/2)⁻¹ = 4r⁻¹r⁻¹`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

open MeasureTheory Metric Set InnerProductSpace
open HCPolySupport (Vec euclideanBall volumeAverage)
open HCPolySupport.Book.Ch01 (meanSquareDeviationOn)
open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-! ## 1. Differentiability from harmonicity -/

/-- A harmonic function is differentiable at each point of harmonicity. -/
theorem differentiableAt_of_harmonicAt {u : 𝔼 → ℝ} {z : 𝔼} (h : HarmonicAt u z) :
    DifferentiableAt ℝ u z :=
  h.1.differentiableAt (by norm_num)

/-- The derivative of a harmonic function is differentiable at each point of
harmonicity. -/
theorem differentiableAt_fderiv_of_harmonicAt {u : 𝔼 → ℝ} {z : 𝔼} (h : HarmonicAt u z) :
    DifferentiableAt ℝ (fderiv ℝ u) z := by
  have hc1 : ContDiffAt ℝ 1 (fderiv ℝ u) z := by
    have hstep := h.1.fderiv_right (m := 1) (by norm_num)
    simpa using hstep
  exact hc1.differentiableAt (by norm_num)

/-! ## 2. Second-order Taylor with a Hessian remainder -/

/-- **Second-order Taylor with a Hessian remainder on a convex set.** -/
theorem abs_sub_fderiv_apply_le_of_hessian_bound {u : 𝔼 → ℝ} {S : Set 𝔼} (hS : Convex ℝ S)
    (hdiff : ∀ z ∈ S, DifferentiableAt ℝ u z)
    (hdiff2 : ∀ z ∈ S, DifferentiableAt ℝ (fderiv ℝ u) z)
    {M : ℝ} (hM : ∀ z ∈ S, ‖fderiv ℝ (fderiv ℝ u) z‖ ≤ M)
    {p q : 𝔼} (hp : p ∈ S) (hq : q ∈ S) :
    |u q - u p - fderiv ℝ u p (q - p)| ≤ M * ‖q - p‖ ^ 2 := by
  have hTS : segment ℝ p q ⊆ S := hS.segment_subset hp hq
  have hTconv : Convex ℝ (segment ℝ p q) := convex_segment p q
  have hpT : p ∈ segment ℝ p q := left_mem_segment ℝ p q
  have hqT : q ∈ segment ℝ p q := right_mem_segment ℝ p q
  have hM0 : 0 ≤ M := le_trans (norm_nonneg (fderiv ℝ (fderiv ℝ u) p)) (hM p hp)
  -- On the segment the displacement from `p` never exceeds the full displacement.
  have hnorm : ∀ z ∈ segment ℝ p q, ‖z - p‖ ≤ ‖q - p‖ := by
    intro z hz
    obtain ⟨a, b, ha, hb, hab, hz'⟩ := hz
    have hab' : a = 1 - b := by linarith only [hab]
    have hzp : z - p = b • (q - p) := by
      rw [← hz', hab', sub_smul, one_smul, smul_sub]
      abel
    rw [hzp, norm_smul, Real.norm_eq_abs, abs_of_nonneg hb]
    exact mul_le_of_le_one_left (norm_nonneg _) (by linarith only [hab, ha])
  -- The mean-value inequality for `Du` on the segment.
  have hgrad : ∀ z ∈ segment ℝ p q, ‖fderiv ℝ u z - fderiv ℝ u p‖ ≤ M * ‖q - p‖ := by
    intro z hz
    have h1 : ‖fderiv ℝ u z - fderiv ℝ u p‖ ≤ M * ‖z - p‖ :=
      hTconv.norm_image_sub_le_of_norm_fderiv_le (fun w hw => hdiff2 w (hTS hw))
        (fun w hw => hM w (hTS hw)) hpT hz
    exact h1.trans (mul_le_mul_of_nonneg_left (hnorm z hz) hM0)
  -- The `φ`-corrected mean-value inequality for `u` on the segment.
  have hmain : ‖u q - u p - fderiv ℝ u p (q - p)‖ ≤ M * ‖q - p‖ * ‖q - p‖ :=
    hTconv.norm_image_sub_le_of_norm_fderiv_le' (φ := fderiv ℝ u p)
      (fun w hw => hdiff w (hTS hw)) hgrad hpT hqT
  rw [Real.norm_eq_abs] at hmain
  calc |u q - u p - fderiv ℝ u p (q - p)| ≤ M * ‖q - p‖ * ‖q - p‖ := hmain
    _ = M * ‖q - p‖ ^ 2 := by ring

/-- **Second-order Taylor, `Vec d` shape.** -/
theorem abs_sub_fderiv_apply_le_of_hessian_bound_vec {V : Vec d → ℝ} {S : Set (Vec d)}
    (hS : Convex ℝ S)
    (hharm : ∀ z ∈ S, HarmonicAt (V ∘ (toEuc.symm : 𝔼 → Vec d)) (toEuc z))
    {M : ℝ} (hM : ∀ z ∈ S,
      ‖fderiv ℝ (fderiv ℝ (V ∘ (toEuc.symm : 𝔼 → Vec d))) (toEuc z)‖ ≤ M)
    {p q : Vec d} (hp : p ∈ S) (hq : q ∈ S) :
    |V q - V p
        - fderiv ℝ (V ∘ (toEuc.symm : 𝔼 → Vec d)) (toEuc p) (toEuc q - toEuc p)|
      ≤ M * ‖toEuc q - toEuc p‖ ^ 2 := by
  have hlin : IsLinearMap ℝ (toEuc : Vec d → 𝔼) :=
    ⟨fun x y => map_add _ x y, fun c x => map_smul _ c x⟩
  have hconv : Convex ℝ ((toEuc : Vec d → 𝔼) '' S) := hS.is_linear_image hlin
  have hdiff : ∀ z ∈ (toEuc : Vec d → 𝔼) '' S,
      DifferentiableAt ℝ (V ∘ (toEuc.symm : 𝔼 → Vec d)) z := by
    rintro z ⟨w, hw, rfl⟩
    exact differentiableAt_of_harmonicAt (hharm w hw)
  have hdiff2 : ∀ z ∈ (toEuc : Vec d → 𝔼) '' S,
      DifferentiableAt ℝ (fderiv ℝ (V ∘ (toEuc.symm : 𝔼 → Vec d))) z := by
    rintro z ⟨w, hw, rfl⟩
    exact differentiableAt_fderiv_of_harmonicAt (hharm w hw)
  have hM' : ∀ z ∈ (toEuc : Vec d → 𝔼) '' S,
      ‖fderiv ℝ (fderiv ℝ (V ∘ (toEuc.symm : 𝔼 → Vec d))) z‖ ≤ M := by
    rintro z ⟨w, hw, rfl⟩
    exact hM w hw
  have hkey := abs_sub_fderiv_apply_le_of_hessian_bound (u := V ∘ (toEuc.symm : 𝔼 → Vec d))
    hconv hdiff hdiff2 hM' (mem_image_of_mem _ hp) (mem_image_of_mem _ hq)
  simpa only [Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply] using hkey

/-! ## 3. Coefficient algebra for the normalized Hessian estimate -/

/-- The volume-ratio identity behind the rebasing: the scale-free lower bound
`(ρ/(d+1))^d` for the ball volume at `ρ = r/2` turns `|W| / |B|` into
`(|W| / rᵈ) · (2(d+1))ᵈ`. -/
private theorem hess_vol_ratio_algebra (d : ℕ) (VW r : ℝ) :
    VW / ((r / 2 / ((d : ℝ) + 1)) ^ d) = VW / r ^ d * (2 * ((d : ℝ) + 1)) ^ d := by
  rw [div_div, div_pow, div_div_eq_mul_div, div_mul_eq_mul_div]

/-- The prefactor identity: `(r/2)⁻¹(r/2)⁻¹ = 4 r⁻¹ r⁻¹`, with the square-root factors
collected into the constant. -/
private theorem hess_norm_coeff_algebra (C₀ r A B N : ℝ) :
    C₀ * (r / 2)⁻¹ * (r / 2)⁻¹ * (A * B * N) = C₀ * 4 * B * r⁻¹ * r⁻¹ * A * N := by
  have h : (r / 2 : ℝ)⁻¹ = 2 * r⁻¹ := by
    rw [div_eq_mul_inv, mul_inv, inv_inv]; ring
  rw [h]; ring

/-! ## 4. The interior Hessian estimate against the normalized `L²` seminorm -/

/-- **The interior Hessian estimate against the normalized `L²` seminorm of the
window.**  For `V` classically harmonic on `W` and a point `p` carrying a sup-ball
of radius `r` inside `W`. -/
theorem exists_hessian_normalizedL2On_bound (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (W : Set (Vec d)) (V : Vec d → ℝ) (p : Vec d) (r : ℝ),
      volume W ≠ ⊤ → 0 < (volume W).toReal →
      HarmonicOnNhd (V ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
        ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' W) →
      IntegrableOn (fun y => V y ^ 2) W volume →
      0 < r → Metric.ball p r ⊆ W →
      ‖fderiv ℝ (fderiv ℝ (V ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))) (toEuc p)‖
        ≤ C * r⁻¹ * r⁻¹ * Real.sqrt ((volume W).toReal / r ^ d) * normalizedL2On W V := by
  obtain ⟨C₀, hC₀, hC⟩ := interiorSecondDerivEstimateL2 d
  refine ⟨C₀ * 4 * Real.sqrt ((2 * ((d : ℝ) + 1)) ^ d),
    mul_nonneg (mul_nonneg hC₀ (by norm_num)) (Real.sqrt_nonneg _), ?_⟩
  intro W V p r _ hWpos hharm hint hr hball
  have hr2 : (0 : ℝ) < r / 2 := by linarith only [hr]
  have hd1 : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  -- The Euclidean ball at `toEuc p` of radius `r` sits inside the transported window.
  have hsubimg : Metric.ball (toEuc p) r ⊆ toEuc '' W := by
    intro w hw
    have hq : toEuc (toEuc.symm w) ∈ Metric.ball (toEuc p) r := by
      rwa [ContinuousLinearEquiv.apply_symm_apply]
    have hmem : toEuc.symm w ∈ euclideanBall p r :=
      (mem_euclideanBall_toEuc_iff (toEuc.symm w) p hr).1 hq
    exact ⟨toEuc.symm w, hball (HCPolySupport.euclideanBall_subset_metricBall hr hmem),
      ContinuousLinearEquiv.apply_symm_apply _ _⟩
  -- The native centre estimate at `toEuc p`, inner radius `r/2`, constant `0`.
  have hcore := hC (V ∘ toEuc.symm) (toEuc p) (R := r) (r := r / 2) 0 hr2
    (by linarith only [hr2]) (hharm.mono hsubimg)
  -- The mean-square deviation against `0` is the volume average of the square.
  have hmsd : meanSquareDeviationOn (euclideanBall (toEuc.symm (toEuc p)) (r / 2))
        ((V ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d)) ∘ toEuc) 0
      = volumeAverage (euclideanBall p (r / 2)) (fun y => V y ^ 2) := by
    rw [ContinuousLinearEquiv.symm_apply_apply, comp_toEuc_symm_toEuc]
    simp only [meanSquareDeviationOn, sub_zero]
  rw [hmsd] at hcore
  -- The inner ball sits inside `W`.
  have hsubW : euclideanBall p (r / 2) ⊆ W :=
    subset_trans (HCPolySupport.euclideanBall_subset_metricBall hr2)
      (subset_trans (Metric.ball_subset_ball (by linarith only [hr])) hball)
  -- The inner ball has positive volume, by the scale-free lower bound.
  have hlow := volume_toReal_euclideanBall_ge p hr2
  have hlowpos : (0 : ℝ) < (r / 2 / ((d : ℝ) + 1)) ^ d :=
    pow_pos (div_pos hr2 hd1) d
  have hBpos : (0 : ℝ) < (volume (euclideanBall p (r / 2))).toReal :=
    lt_of_lt_of_le hlowpos hlow
  -- Rebasing the average onto `W` costs the volume ratio.
  have hSle := volumeAverage_le_of_subset (f := fun y => V y ^ 2) hsubW hWpos hBpos
    (fun x => sq_nonneg (V x)) hint
  -- The volume ratio, made explicit.
  have hratio : (volume W).toReal / (volume (euclideanBall p (r / 2))).toReal
      ≤ (volume W).toReal / r ^ d * (2 * ((d : ℝ) + 1)) ^ d := by
    have h1 : (volume W).toReal / (volume (euclideanBall p (r / 2))).toReal
        ≤ (volume W).toReal / ((r / 2 / ((d : ℝ) + 1)) ^ d) :=
      div_le_div_of_nonneg_left ENNReal.toReal_nonneg hlowpos hlow
    exact h1.trans (le_of_eq (hess_vol_ratio_algebra d (volume W).toReal r))
  -- Nonnegativity bookkeeping.
  have hX0 : (0 : ℝ) ≤ (volume W).toReal / r ^ d :=
    div_nonneg ENNReal.toReal_nonneg (pow_nonneg hr.le d)
  have hY0 : (0 : ℝ) ≤ (2 * ((d : ℝ) + 1)) ^ d := by positivity
  have hXY0 : (0 : ℝ) ≤ (volume W).toReal / r ^ d * (2 * ((d : ℝ) + 1)) ^ d :=
    mul_nonneg hX0 hY0
  have hN0 : (0 : ℝ) ≤ normalizedL2On W V := normalizedL2On_nonneg W V
  -- The average of the square on the inner ball, bounded by the normalized seminorm.
  have hS2 : volumeAverage (euclideanBall p (r / 2)) (fun y => V y ^ 2)
      ≤ (volume W).toReal / r ^ d * (2 * ((d : ℝ) + 1)) ^ d * normalizedL2On W V ^ 2 := by
    rw [normalizedL2On_sq]
    refine hSle.trans (mul_le_mul_of_nonneg_right hratio ?_)
    exact volumeAverage_sq_nonneg W V
  -- Take square roots.
  have hsqrt : Real.sqrt (volumeAverage (euclideanBall p (r / 2)) (fun y => V y ^ 2))
      ≤ Real.sqrt ((volume W).toReal / r ^ d) *
        Real.sqrt ((2 * ((d : ℝ) + 1)) ^ d) * normalizedL2On W V := by
    have h1 := Real.sqrt_le_sqrt hS2
    rwa [Real.sqrt_mul hXY0, Real.sqrt_sq hN0, Real.sqrt_mul hX0] at h1
  have hcoefnn : (0 : ℝ) ≤ C₀ * (r / 2)⁻¹ * (r / 2)⁻¹ :=
    mul_nonneg (mul_nonneg hC₀ (inv_nonneg.mpr hr2.le)) (inv_nonneg.mpr hr2.le)
  calc ‖fderiv ℝ (fderiv ℝ (V ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))) (toEuc p)‖
      ≤ C₀ * (r / 2)⁻¹ * (r / 2)⁻¹ *
          Real.sqrt (volumeAverage (euclideanBall p (r / 2)) (fun y => V y ^ 2)) := hcore
    _ ≤ C₀ * (r / 2)⁻¹ * (r / 2)⁻¹ * (Real.sqrt ((volume W).toReal / r ^ d) *
          Real.sqrt ((2 * ((d : ℝ) + 1)) ^ d) * normalizedL2On W V) :=
        mul_le_mul_of_nonneg_left hsqrt hcoefnn
    _ = C₀ * 4 * Real.sqrt ((2 * ((d : ℝ) + 1)) ^ d) * r⁻¹ * r⁻¹ *
          Real.sqrt ((volume W).toReal / r ^ d) * normalizedL2On W V :=
        hess_norm_coeff_algebra C₀ r (Real.sqrt ((volume W).toReal / r ^ d))
          (Real.sqrt ((2 * ((d : ℝ) + 1)) ^ d)) (normalizedL2On W V)

end

end Algsuperdiff.Section4.Provider.ExcessDecay.Schauder
