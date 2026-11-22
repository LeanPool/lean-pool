/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! # Mollification of a function with a prescribed local Lipschitz profile

Let `u : F → ℝ` be integrable on a ball `B(a₀,R)` of a finite dimensional inner product space and
satisfy `|u(b + h w) - u(b)| ≤ |h| N(w)` for `b, b + h w ∈ B(a₀,R)`.  Then for every `δ > 0`
there is a smooth `G : F → ℝ` with `|G - u| ≤ δ` and `|dG(a) w| ≤ N(w)` for `a ∈ B(a₀,R/2)`.
-/

@[expose] public section

open MeasureTheory Metric Set Filter Function
open scoped Convolution Topology ContDiff

namespace CutCur

variable {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

theorem exists_contDiff_approx_lip (u : F → ℝ) (a₀ : F) {R : ℝ} (hR : 0 < R)
    (hu : IntegrableOn u (ball a₀ R)) (N : F → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hN0 : ∀ w, 0 ≤ N w) (hNC : ∀ w, N w ≤ C * ‖w‖)
    (hLip : ∀ b ∈ ball a₀ R, ∀ (w : F) (h : ℝ), b + h • w ∈ ball a₀ R →
      |u (b + h • w) - u b| ≤ |h| * N w) {δ : ℝ} (hδ : 0 < δ) :
    ∃ G : F → ℝ, ContDiff ℝ ∞ G ∧ ∀ a ∈ ball a₀ (R / 2),
      |G a - u a| ≤ δ ∧ ∀ w, |fderiv ℝ G a w| ≤ N w := by
  set ε : ℝ := min (R / 4) (δ / (C + 1)) with hε
  have hεpos : 0 < ε := lt_min (by positivity) (by positivity)
  have hε1 : ε ≤ R / 4 := min_le_left _ _
  have hε2 : ε ≤ δ / (C + 1) := min_le_right _ _
  let φ : ContDiffBump (0 : F) := ⟨ε / 2, ε, half_pos hεpos, half_lt_self hεpos⟩
  set u0 : F → ℝ := (ball a₀ R).indicator u with hu0
  have hu0int : Integrable u0 := hu.integrable_indicator measurableSet_ball
  have hu0loc : LocallyIntegrable u0 volume := hu0int.locallyIntegrable
  set G : F → ℝ := φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u0 with hG
  have hGsm : ContDiff ℝ ∞ G :=
    φ.hasCompactSupport_normed.contDiff_convolution_left _ φ.contDiff_normed hu0loc
  refine ⟨G, hGsm, fun a ha => ?_⟩
  have hmem : ∀ y, ‖y‖ < R / 4 → ∀ b, ‖b - a‖ < R / 4 → b - y ∈ ball a₀ R := by
    intro y hy b hb
    rw [mem_ball, dist_eq_norm] at ha ⊢
    have : b - y - a₀ = (a - a₀) + (b - a) - y := by abel
    rw [this]
    calc
      ‖(a - a₀) + (b - a) - y‖ ≤ ‖a - a₀‖ + ‖b - a‖ + ‖y‖ :=
        norm_sub_le_of_le (norm_add_le _ _) le_rfl
      _ < R := by linarith
  have ha' : a ∈ ball a₀ R := by
    rw [mem_ball] at ha ⊢; linarith
  constructor
  · -- value estimate
    have := φ.dist_normed_convolution_le (μ := volume) (x₀ := a) (ε := δ)
      (g := u0) hu0int.aestronglyMeasurable (fun x hx => ?_)
    · have hsimp' : u0 a = u a := by simp [hu0, ha']
      simpa [Real.dist_eq, hG, hsimp'] using this
    · have hxa : ‖x - a‖ < ε := by simpa [dist_eq_norm] using hx
      have hx' : x ∈ ball a₀ R := by
        have hzero : ‖(0 : F)‖ < R / 4 := by simp only [norm_zero]; positivity
        have := hmem 0 hzero x (by linarith)
        simpa using this
      have key := hLip a ha' (x - a) 1 (by simpa using hx')
      simp only [one_smul, add_sub_cancel, abs_one, one_mul] at key
      have hsimp : u0 x = u x := by simp [hu0, hx']
      have hsimp' : u0 a = u a := by simp [hu0, ha']
      rw [Real.dist_eq, hsimp, hsimp']
      refine key.trans ((hNC _).trans ?_)
      calc C * ‖x - a‖ ≤ C * ε := by gcongr
        _ ≤ C * (δ / (C + 1)) := by gcongr
        _ ≤ δ := by
          rw [← mul_div_assoc, div_le_iff₀ (by positivity)]; nlinarith
  · -- derivative estimate
    intro w
    have hdiff : DifferentiableAt ℝ G a := (hGsm.differentiable (by norm_num)).differentiableAt
    have hline : HasDerivAt (fun h : ℝ => G (a + h • w)) (fderiv ℝ G a w) 0 := by
      have h1 : HasDerivAt (fun h : ℝ => a + h • w) w 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add a
      exact (hdiff.hasFDerivAt).comp_hasDerivAt_of_eq 0 h1 (by simp)
    have hconv : ∀ b, G b = ∫ y, φ.normed volume y * u0 (b - y) := by
      intro b
      simp [hG, convolution_def]
    have hex : ∀ b, Integrable (fun y => φ.normed volume y * u0 (b - y)) := by
      intro b
      have := (φ.hasCompactSupport_normed (μ := volume)).convolutionExists_left
        (ContinuousLinearMap.lsmul ℝ ℝ) (φ.continuous_normed (μ := volume)) hu0loc b
      simpa [ConvolutionExistsAt] using this
    have hev : ∀ᶠ h in 𝓝 (0 : ℝ), ‖G (a + h • w) - G (a + (0 : ℝ) • w)‖ ≤ N w * ‖h - 0‖ := by
      have hball : ball (0 : ℝ) (R / 4 / (‖w‖ + 1)) ∈ 𝓝 (0 : ℝ) := ball_mem_nhds _ (by positivity)
      filter_upwards [hball] with h hh
      rw [mem_ball, Real.dist_eq, sub_zero] at hh
      have hhw : ‖h • w‖ < R / 4 := by
        rw [norm_smul, Real.norm_eq_abs]
        have : |h| * (‖w‖ + 1) < R / 4 := by
          rwa [lt_div_iff₀ (by positivity)] at hh
        nlinarith [norm_nonneg w, abs_nonneg h]
      simp only [zero_smul, add_zero, sub_zero, Real.norm_eq_abs]
      rw [hconv, hconv, ← integral_sub (hex _) (hex _)]
      have hbound : ∀ᵐ y ∂volume, ‖φ.normed volume y * u0 (a + h • w - y) -
          φ.normed volume y * u0 (a - y)‖ ≤ φ.normed volume y * (N w * |h|) := by
        refine Eventually.of_forall (fun y => ?_)
        by_cases hy : y ∈ ball (0 : F) ε
        · have hy' : ‖y‖ < R / 4 := by
            rw [mem_ball, dist_zero_right] at hy; linarith
          have haSmall : ‖a - a‖ < R / 4 := by
            simpa only [sub_self, norm_zero] using (show 0 < R / 4 by positivity)
          have h1 := hmem y hy' a haSmall
          have h2 : a + h • w - y ∈ ball a₀ R := hmem y hy' (a + h • w) (by simpa using hhw)
          have key := hLip (a - y) h1 w h (by
            have : a - y + h • w = a + h • w - y := by abel
            rwa [this])
          have e1 : u0 (a - y) = u (a - y) := by simp [hu0, h1]
          have e2 : u0 (a + h • w - y) = u (a - y + h • w) := by
            have : a - y + h • w = a + h • w - y := by abel
            rw [this]; simp [hu0, h2]
          rw [← mul_sub, norm_mul, Real.norm_of_nonneg (φ.nonneg_normed y), e1, e2,
            Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (by rw [mul_comm]; exact key) (φ.nonneg_normed y)
        · have : φ.normed volume y = 0 := by
            by_contra hne
            apply hy
            rw [← φ.support_normed_eq (μ := volume)]
            exact hne
          simp [this]
      have := norm_integral_le_of_norm_le ((φ.integrable_normed (μ := volume)).mul_const (N w *
        |h|)) hbound
      rw [integral_mul_const, φ.integral_normed, Real.norm_eq_abs] at this
      simpa using this
    have := hline.le_of_lip' (hN0 w) hev
    simpa [Real.norm_eq_abs] using this

end CutCur
