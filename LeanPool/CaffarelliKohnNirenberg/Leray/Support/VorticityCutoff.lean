/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Cutoff.Ball
public import LeanPool.CaffarelliKohnNirenberg.Pressure.LeibnizLaplacian
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Cutoffs for the vorticity bootstrap

Spatial cutoffs between two concentric Euclidean balls and time cutoffs vanishing near the bottom
of a time interval, with uniform bounds for their derivatives. The bounds depend only on the radii
and on the time collar, which makes the constants of `thm:vorticity-regularity`
of the Escauriaza–Seregin–Šverák manuscript independent of
the centre of the cylinder.
-/

public section

open MeasureTheory Set
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN

/-- A smooth spatial cutoff centred at the origin: equal to one on the closed ball of radius `r`,
supported in the open ball of radius `R`, with values in `[0, 1]`. -/
theorem vorticitySpatialCutoff_exists {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    ∃ φ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧
      tsupport φ ⊆ vec3Ball 0 R ∧
      (∀ x, vec3EuclideanNorm x ≤ r → φ x = 1) ∧
      (∀ x, 0 ≤ φ x) ∧ (∀ x, φ x ≤ 1) := by
  let r' : ℝ := (r + R) / 2
  have hr' : 0 ≤ r' := by dsimp [r']; linarith only [hr, hrR]
  have hr'R : r' < R := by dsimp [r']; linarith only [hrR]
  have hrr' : r < r' := by dsimp [r']; linarith only [hrR]
  have hnorm (x : Vec3) : vecEuclideanNorm (x - 0) = vec3EuclideanNorm x := by
    simp [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two]
  refine ⟨canonicalBallCutoff (0 : Vec3) r' R, canonicalBallCutoff_smooth 0 hr' hr'R,
    canonicalBallCutoff_hasCompactSupport hr' hr'R, ?_, ?_,
    canonicalBallCutoff_nonneg 0 r' R, canonicalBallCutoff_le_one 0 r' R⟩
  · intro x hx
    have hx' := canonicalBallCutoff_tsupport_subset_outer (x₀ := (0 : Vec3)) hr' hr'R hx
    rw [mem_euclideanBall_iff_vecEuclideanNorm_lt (hr.trans hrR), hnorm] at hx'
    simpa [vec3Ball] using hx'
  · intro x hx
    apply canonicalBallCutoff_eq_one_on_inner hr' hr'R
    rw [mem_euclideanBall_iff_vecEuclideanNorm_lt (hr.trans hrr'), hnorm]
    exact lt_of_le_of_lt hx hrr'

/-- A smooth compactly supported function on space has uniformly bounded first and second
coordinate derivatives. -/
theorem vorticitySmooth_derivative_bounds {φ : Vec3 → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) :
    ∃ L : ℝ, 0 ≤ L ∧ (∀ x j, |spatialDeriv φ j x| ≤ L) ∧
      (∀ x j k, |spatialDeriv (spatialDeriv φ j) k x| ≤ L) := by
  have hfirst (j : Fin 3) : ∃ C, ∀ x, ‖spatialDeriv φ j x‖ ≤ C := by
    apply (contDiff_spatialDeriv_smooth hφ j).continuous.bounded_above_of_compact_support
    exact hφc.fderiv_apply (𝕜 := ℝ) (basisVec j)
  have hsecond (j k : Fin 3) : ∃ C, ∀ x, ‖spatialDeriv (spatialDeriv φ j) k x‖ ≤ C := by
    apply (contDiff_spatialDeriv_smooth (contDiff_spatialDeriv_smooth hφ j)
      k).continuous.bounded_above_of_compact_support
    exact (hφc.fderiv_apply (𝕜 := ℝ) (basisVec j)).fderiv_apply (𝕜 := ℝ) (basisVec k)
  choose C₁ hC₁ using hfirst
  choose C₂ hC₂ using hsecond
  refine ⟨∑ j, |C₁ j| + ∑ j, ∑ k, |C₂ j k|, by positivity, ?_, ?_⟩
  · intro x j
    have h1 : |spatialDeriv φ j x| ≤ |C₁ j| := (hC₁ j x).trans (le_abs_self _)
    have h2 : |C₁ j| ≤ ∑ j, |C₁ j| :=
      Finset.single_le_sum (f := fun j => |C₁ j|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ j)
    have h3 : 0 ≤ ∑ j, ∑ k, |C₂ j k| := by positivity
    linarith only [h1, h2, h3]
  · intro x j k
    have h1 : |spatialDeriv (spatialDeriv φ j) k x| ≤ |C₂ j k| :=
      (hC₂ j k x).trans (le_abs_self _)
    have h2 : |C₂ j k| ≤ ∑ k, |C₂ j k| :=
      Finset.single_le_sum (f := fun k => |C₂ j k|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ k)
    have h3 : ∑ k, |C₂ j k| ≤ ∑ j, ∑ k, |C₂ j k| :=
      Finset.single_le_sum (f := fun j => ∑ k, |C₂ j k|) (fun _ _ => by positivity)
        (Finset.mem_univ j)
    have h4 : 0 ≤ ∑ j, |C₁ j| := by positivity
    linarith only [h1, h2, h3, h4]

/-- Translating a function translates its coordinate derivatives. -/
theorem vorticitySpatialDeriv_translate (φ : Vec3 → ℝ) (x₀ x : Vec3) (j : Fin 3) :
    spatialDeriv (fun y => φ (y - x₀)) j x = spatialDeriv φ j (x - x₀) := by
  unfold spatialDeriv
  rw [fderiv_comp_sub]

/-- A smooth time cutoff which vanishes up to `κ / 2`, equals one from `κ` on, takes values in
`[0, 1]` and has a bounded derivative. -/
theorem vorticityTimeCutoff_exists {κ : ℝ} (hκ : 0 < κ) :
    ∃ θ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) θ ∧ (∀ s, s ≤ κ / 2 → θ s = 0) ∧
      (∀ s, κ ≤ s → θ s = 1) ∧ (∀ s, 0 ≤ θ s) ∧ (∀ s, θ s ≤ 1) ∧
      ∃ L : ℝ, 0 ≤ L ∧ ∀ s, |deriv θ s| ≤ L := by
  let θ : ℝ → ℝ := fun s => Real.smoothTransition (2 * s / κ - 1)
  have hθ : ContDiff ℝ (⊤ : ℕ∞) θ :=
    Real.smoothTransition.contDiff.comp
      (((contDiff_const.mul contDiff_id).div_const κ).sub contDiff_const)
  have hzero : ∀ s, s ≤ κ / 2 → θ s = 0 := by
    intro s hs
    apply Real.smoothTransition.zero_of_nonpos
    have h1 : 2 * s / κ ≤ 1 := by
      rw [div_le_one hκ]
      linarith only [hs]
    linarith only [h1]
  have hone : ∀ s, κ ≤ s → θ s = 1 := by
    intro s hs
    apply Real.smoothTransition.one_of_one_le
    have h1 : 2 ≤ 2 * s / κ := by
      rw [le_div_iff₀ hκ]
      linarith only [hs]
    linarith only [h1]
  have hderivCont : Continuous (deriv θ) := hθ.continuous_deriv (by simp)
  have hbound : ∃ L, ∀ s ∈ Icc (κ / 2) κ, ‖deriv θ s‖ ≤ L :=
    (isCompact_Icc.image_of_continuousOn hderivCont.norm.continuousOn).isBounded.bddAbove
      |>.imp fun L hL s hs => hL ⟨s, hs, rfl⟩
  obtain ⟨L, hL⟩ := hbound
  have hflat : ∀ s, s ∉ Icc (κ / 2) κ → deriv θ s = 0 := by
    intro s hs
    rw [mem_Icc, not_and_or, not_le, not_le] at hs
    rcases hs with hs | hs
    · have hev : θ =ᶠ[nhds s] fun _ => 0 := by
        filter_upwards [Iio_mem_nhds hs] with y hy
        exact hzero y (le_of_lt hy)
      rw [hev.deriv_eq]
      simp
    · have hev : θ =ᶠ[nhds s] fun _ => 1 := by
        filter_upwards [Ioi_mem_nhds hs] with y hy
        exact hone y (le_of_lt hy)
      rw [hev.deriv_eq]
      simp
  refine ⟨θ, hθ, hzero, hone, fun s => Real.smoothTransition.nonneg _,
    fun s => Real.smoothTransition.le_one _, |L|, abs_nonneg L, ?_⟩
  intro s
  by_cases hs : s ∈ Icc (κ / 2) κ
  · exact (hL s hs).trans (le_abs_self L)
  · rw [hflat s hs, abs_zero]
    exact abs_nonneg L

end CKN
