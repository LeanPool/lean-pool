/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Tilt.Temperate

/-!
# Integration by parts for tests of temperate growth

Bizeul–Klartag–Lehec (arXiv:2610.05474v1), eq. (15): for `μ = m.tilted (-V)` with `V ∈ C¹`, `∇V`
of polynomial growth and all exponential moments, and `u, v` of temperate growth (the class `𝒜`),
`∫ (ℒu) v dμ = -∫ ⟪∇u, ∇v⟫ dμ = ∫ u (ℒv) dμ`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped RealInnerProductSpace ContDiff

namespace FunctionalInequalities.Analysis.BakryEmery

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (m : Measure E) [m.IsAddHaarMeasure]

/-- Integration by parts against a compactly supported test: `∫ (ℒu) w dμ = -∫ ⟪∇u, ∇w⟫ dμ` for
`u ∈ C²` (no growth condition) and `w ∈ C²` with compact support. -/
theorem integral_weightedLaplacian_mul_eq_neg_of_hasCompactSupport {V f w : E → ℝ}
    (hV : ContDiff ℝ 1 V) (hf : ContDiff ℝ 2 f) (hw : ContDiff ℝ 2 w) (hwc : HasCompactSupport w) :
    ∫ x, weightedLaplacian V f x * w x ∂(m.tilted (-V)) =
      -∫ x, ⟪gradient f x, gradient w x⟫ ∂(m.tilted (-V)) := by
    obtain ⟨R₀, hR₀⟩ :=
      hwc.isCompact.isBounded.subset_closedBall (0 : E)
    let R : ℝ := max R₀ 0 + 1
    have hR : 0 < R := by
      dsimp [R]
      positivity
    let F : E → ℝ := fun x => cutoff R x * f x
    have hF : ContDiff ℝ 2 F := by
      dsimp [F]
      have hc : ContDiff ℝ 2 (cutoff R) :=
        (contDiff_cutoff (E := E) R).of_le (WithTop.coe_le_coe.mpr le_top)
      exact hc.mul hf
    have hFc : HasCompactSupport F := by
      dsimp [F]
      exact (hasCompactSupport_cutoff hR).mul_right
    have h_eq (x : E) (hx : x ∈ tsupport w) :
        f =ᶠ[𝓝 x] F := by
      have hx' : ‖x‖ ≤ max R₀ 0 := by
        have hx'' : x ∈ Metric.closedBall (0 : E) R₀ := hR₀ hx
        have hx''' : ‖x‖ ≤ R₀ := by
          simpa [Metric.mem_closedBall, dist_zero_right] using hx''
        exact hx'''.trans (le_max_left _ _)
      have hxR : x ∈ Metric.ball (0 : E) R := by
        rw [Metric.mem_ball, dist_zero_right]
        dsimp [R]
        linarith
      have hball : Metric.ball (0 : E) R ∈ 𝓝 x :=
        Metric.isOpen_ball.mem_nhds hxR
      filter_upwards [hball] with y hy
      have hy' : ‖y‖ ≤ R := by
        have hy'' : ‖y‖ < R := by
          simpa [Metric.mem_ball, dist_zero_right] using hy
        exact hy''.le
      change f y = cutoff R y * f y
      rw [cutoff_eq_one hR hy']
      ring
    have h_lap (x : E) :
        weightedLaplacian V f x * w x =
          weightedLaplacian V F x * w x := by
      by_cases hx : x ∈ tsupport w
      · have hl :
            weightedLaplacian V f x = weightedLaplacian V F x :=
          weightedLaplacian_congr_of_eventuallyEq V (h_eq x hx)
        rw [hl]
      · have hwx : w x = 0 :=
          image_eq_zero_of_notMem_tsupport hx
        rw [hwx]
        simp
    have h_grad (x : E) :
        ⟪gradient f x, gradient w x⟫ =
          ⟪gradient F x, gradient w x⟫ := by
      by_cases hx : x ∈ tsupport w
      · exact congrArg (fun z => ⟪z, gradient w x⟫)
          ((h_eq x hx).gradient_eq)
      · have hwx : w =ᶠ[𝓝 x] (fun _ : E => (0 : ℝ)) :=
          notMem_tsupport_iff_eventuallyEq.mp hx
        have hwgrad : gradient w x = 0 := by
          simpa using hwx.gradient_eq
        simp [hwgrad]
    have h₁ :
        (∫ x, weightedLaplacian V f x * w x ∂(m.tilted (-V))) =
          ∫ x, weightedLaplacian V F x * w x ∂(m.tilted (-V)) := by
      apply integral_congr_ae
      exact ae_of_all _ h_lap
    have h₂ :
        (∫ x, ⟪gradient f x, gradient w x⟫ ∂(m.tilted (-V))) =
          ∫ x, ⟪gradient F x, gradient w x⟫ ∂(m.tilted (-V)) := by
      apply integral_congr_ae
      exact ae_of_all _ h_grad
    have hw1 : ContDiff ℝ 1 w :=
      hw.of_le (show 1 ≤ 2 by norm_num)
    have hIBP :=
      integral_inner_gradient_tilted m hV hF hFc hw1
    calc
      ∫ x, weightedLaplacian V f x * w x ∂(m.tilted (-V)) =
          ∫ x, weightedLaplacian V F x * w x ∂(m.tilted (-V)) := h₁
      _ = -∫ x, (-weightedLaplacian V F x) * w x ∂(m.tilted (-V)) := by
        have hfun :
            (fun x => weightedLaplacian V F x * w x) =
              (fun x => -((-weightedLaplacian V F x) * w x)) := by
          funext x
          ring
        rw [hfun, integral_neg]
      _ = -∫ x, ⟪gradient F x, gradient w x⟫ ∂(m.tilted (-V)) := by
        rw [hIBP]
      _ = -∫ x, ⟪gradient f x, gradient w x⟫ ∂(m.tilted (-V)) := by
        rw [← h₂]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem ibp_temperate_bounds {f : E → ℝ} (hf : f.HasTemperateGrowth) :
    ∃ (k : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ x,
      |f x| ≤ C * (1 + ‖x‖) ^ k ∧
      ‖gradient f x‖ ≤ C * (1 + ‖x‖) ^ k ∧
      ‖iteratedFDeriv ℝ 2 f x‖ ≤ C * (1 + ‖x‖) ^ k := by
  obtain ⟨k, C, hC, hb⟩ := hf.norm_iteratedFDeriv_le_uniform 2
  refine ⟨k, C, hC, fun x => ⟨?_, ?_, hb 2 le_rfl x⟩⟩
  · simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hb 0 (by omega) x
  · simpa only [norm_gradient_eq_norm_iteratedFDeriv_one] using hb 1 (by omega) x

omit [MeasurableSpace E] [BorelSpace E] in
private theorem ibp_weightedLaplacian_bound {V f : E → ℝ}
    {CV C : ℝ} {kV k : ℕ} (hCV : 0 ≤ CV) (hC : 0 ≤ C)
    (hVg : ∀ x, ‖gradient V x‖ ≤ CV * (1 + ‖x‖) ^ kV)
    (hf : ∀ x, ‖gradient f x‖ ≤ C * (1 + ‖x‖) ^ k ∧
      ‖iteratedFDeriv ℝ 2 f x‖ ≤ C * (1 + ‖x‖) ^ k) (x : E) :
    |weightedLaplacian V f x| ≤
      ((Module.finrank ℝ E : ℝ) * C + CV * C) * (1 + ‖x‖) ^ (k + kV) := by
  have hp : 1 ≤ (1 + ‖x‖) ^ kV := one_le_pow₀ (by linarith [norm_nonneg x])
  calc
    |weightedLaplacian V f x| ≤
        (Module.finrank ℝ E : ℝ) * ‖iteratedFDeriv ℝ 2 f x‖ +
          ‖gradient V x‖ * ‖gradient f x‖ := by
      rw [weightedLaplacian_apply]
      exact (abs_sub _ _).trans (add_le_add (abs_laplacian_le f x)
        (abs_real_inner_le_norm _ _))
    _ ≤ (Module.finrank ℝ E : ℝ) * (C * (1 + ‖x‖) ^ k) +
          (CV * (1 + ‖x‖) ^ kV) * (C * (1 + ‖x‖) ^ k) := by
      gcongr
      · exact (hf x).2
      · exact hVg x
      · exact (hf x).1
    _ ≤ (Module.finrank ℝ E : ℝ) * (C * (1 + ‖x‖) ^ k) *
          (1 + ‖x‖) ^ kV +
          (CV * (1 + ‖x‖) ^ kV) * (C * (1 + ‖x‖) ^ k) := by
      have hm : (Module.finrank ℝ E : ℝ) * (C * (1 + ‖x‖) ^ k) ≤
          (Module.finrank ℝ E : ℝ) * (C * (1 + ‖x‖) ^ k) * (1 + ‖x‖) ^ kV :=
        le_mul_of_one_le_right (by positivity) hp
      exact add_le_add_left hm _
    _ = _ := by rw [pow_add]; ring

/-- **BKL (15)**, first equality, for `u, v ∈ 𝒜`: `∫ (ℒu) v dμ = -∫ ⟪∇u, ∇v⟫ dμ`. -/
theorem integral_weightedLaplacian_mul_eq_neg_of_hasTemperateGrowth {V f g : E → ℝ}
    (hV : ContDiff ℝ 1 V) {CV : ℝ} {kV : ℕ} (hVg : ∀ x, ‖gradient V x‖ ≤ CV * (1 + ‖x‖) ^ kV)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (m.tilted (-V)))
    (hf : f.HasTemperateGrowth) (hg : g.HasTemperateGrowth) :
    ∫ x, weightedLaplacian V f x * g x ∂(m.tilted (-V)) =
      -∫ x, ⟪gradient f x, gradient g x⟫ ∂(m.tilted (-V)) := by
  obtain ⟨kf, Cf, hCf, hfb⟩ := ibp_temperate_bounds hf
  obtain ⟨kg, Cg, hCg, hgb⟩ := ibp_temperate_bounds hg
  have hf2 : ContDiff ℝ 2 f := hf.1.of_le (WithTop.coe_le_coe.mpr le_top)
  have hg2 : ContDiff ℝ 2 g := hg.1.of_le (WithTop.coe_le_coe.mpr le_top)
  have hCV : 0 ≤ CV := by
    have h := hVg 0
    simp only [norm_zero, add_zero, one_pow, mul_one] at h
    exact (norm_nonneg _).trans h
  obtain ⟨K₀, hK₀⟩ := norm_iteratedFDeriv_cutoff_le (E := E) 1
  let K : ℝ := max K₀ 0
  have hK : 0 ≤ K := le_max_right _ _
  have hcut (n : ℕ) (x : E) : ‖gradient (cutoff ((n : ℝ) + 1)) x‖ ≤ K := by
    rw [norm_gradient_eq_norm_iteratedFDeriv_one]
    exact (hK₀ _ (by linarith [Nat.cast_nonneg (α := ℝ) n]) x).trans (le_max_left _ _)
  let w : ℕ → E → ℝ := fun n x => cutoff ((n : ℝ) + 1) x * g x
  have hw (n : ℕ) : ContDiff ℝ 2 (w n) :=
    ((contDiff_cutoff ((n : ℝ) + 1)).of_le (WithTop.coe_le_coe.mpr le_top)).mul hg2
  let A : ℝ := (Module.finrank ℝ E : ℝ) * Cf + CV * Cf
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hLf (x : E) : |weightedLaplacian V f x| ≤ A * (1 + ‖x‖) ^ (kf + kV) :=
    ibp_weightedLaplacian_bound hCV hCf hVg (fun x => (hfb x).2) x
  have hwb (n : ℕ) (x : E) : |w n x| ≤ Cg * (1 + ‖x‖) ^ kg := by
    dsimp only [w]
    rw [abs_mul]
    calc
      _ ≤ 1 * (Cg * (1 + ‖x‖) ^ kg) := by
        gcongr
        · exact abs_cutoff_le_one _ _
        · exact (hgb x).1
      _ = _ := one_mul _
  have hgw (n : ℕ) (x : E) : ‖gradient (w n) x‖ ≤ (Cg + Cg * K) * (1 + ‖x‖) ^ kg := by
    have hc : ContDiff ℝ 2 (cutoff ((n : ℝ) + 1) : E → ℝ) :=
      (contDiff_cutoff _).of_le (WithTop.coe_le_coe.mpr le_top)
    dsimp only [w]
    rw [gradient_mul (hc.differentiable (by norm_num) x) (hg2.differentiable (by norm_num) x)]
    calc
      _ ≤ ‖cutoff ((n : ℝ) + 1) x • gradient g x‖ + ‖g x • gradient (cutoff ((n : ℝ) + 1)) x‖ :=
        norm_add_le _ _
      _ =
          |cutoff ((n : ℝ) + 1) x| * ‖gradient g x‖ +
            |g x| * ‖gradient (cutoff ((n : ℝ) + 1)) x‖ := by
        simp only [norm_smul, Real.norm_eq_abs]
      _ ≤ 1 * (Cg * (1 + ‖x‖) ^ kg) + (Cg * (1 + ‖x‖) ^ kg) * K := by
        gcongr
        · exact abs_cutoff_le_one _ _
        · exact (hgb x).2.1
        · exact (hgb x).1
        · exact hcut n x
      _ = _ := by ring
  let F : ℕ → E → ℝ := fun n x => weightedLaplacian V f x * w n x
  let G : ℕ → E → ℝ := fun n x => ⟪gradient f x, gradient (w n) x⟫
  have hFbound (n : ℕ) (x : E) : ‖F n x‖ ≤ (A * Cg) * (1 + ‖x‖) ^ (kf + kV + kg) := by
    dsimp only [F]
    rw [Real.norm_eq_abs, abs_mul]
    calc
      _ ≤ (A * (1 + ‖x‖) ^ (kf + kV)) * (Cg * (1 + ‖x‖) ^ kg) := by
        gcongr
        · exact hLf x
        · exact hwb n x
      _ = _ := by rw [pow_add]; ring
  have hGbound (n : ℕ) (x : E) : ‖G n x‖ ≤ (Cf * (Cg + Cg * K)) * (1 + ‖x‖) ^ (kf + kg) := by
    dsimp only [G]
    rw [Real.norm_eq_abs]
    calc
      _ ≤ ‖gradient f x‖ * ‖gradient (w n) x‖ := abs_real_inner_le_norm _ _
      _ ≤ (Cf * (1 + ‖x‖) ^ kf) * ((Cg + Cg * K) * (1 + ‖x‖) ^ kg) := by
        gcongr
        · exact (hfb x).2.1
        · exact hgw n x
      _ = _ := by rw [pow_add]; ring
  have hFi : Integrable (fun x : E => (A * Cg) * (1 + ‖x‖) ^ (kf + kV + kg)) (m.tilted (-V)) := by
    apply
      FunctionalInequalities.Probability.integrable_of_norm_le_pow _ hexp (by fun_prop) (C :=
        A * Cg) (k := kf + kV + kg)
    intro x
    rw [Real.norm_of_nonneg (by positivity)]
  have hGi :
    Integrable (fun x : E => (Cf * (Cg + Cg * K)) * (1 + ‖x‖) ^ (kf + kg)) (m.tilted (-V)) := by
    apply
      FunctionalInequalities.Probability.integrable_of_norm_le_pow _ hexp (by fun_prop) (C :=
        Cf * (Cg + Cg * K)) (k := kf + kg)
    intro x
    rw [Real.norm_of_nonneg (by positivity)]
  have hlocal (x : E) : ∀ᶠ n : ℕ in atTop, w n =ᶠ[𝓝 x] g := by
    obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
    filter_upwards [eventually_ge_atTop N] with n hn
    have hnn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hx : ‖x‖ < (n : ℝ) + 1 := by linarith
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hx] with y hy
    dsimp only [w]
    rw [cutoff_eq_one (by positivity) hy.le, one_mul]
  have hFlim (x : E) : Tendsto (fun n => F n x) atTop (𝓝 (weightedLaplacian V f x * g x)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hlocal x] with n hn
    dsimp only [F]
    rw [hn.eq_of_nhds]
  have hGlim (x : E) : Tendsto (fun n => G n x) atTop (𝓝 ⟪gradient f x, gradient g x⟫) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hlocal x] with n hn
    dsimp only [G]
    rw [hn.gradient_eq]
  have hFt :=
    tendsto_integral_of_dominated_convergence
      (fun x : E => (A * Cg) * (1 + ‖x‖) ^ (kf + kV + kg))
      (fun n =>
        ((continuous_weightedLaplacian hV hf2).mul (hw n).continuous).aestronglyMeasurable)
      hFi (fun n => ae_of_all _ (hFbound n)) (ae_of_all _ hFlim)
  have hGt :=
    tendsto_integral_of_dominated_convergence
      (fun x : E => (Cf * (Cg + Cg * K)) * (1 + ‖x‖) ^ (kf + kg))
      (fun n =>
        ((continuous_gradient (hf2.of_le (by norm_num))).inner
            (continuous_gradient ((hw n).of_le (by norm_num)))).aestronglyMeasurable)
      hGi (fun n => ae_of_all _ (hGbound n)) (ae_of_all _ hGlim)
  have hIBP (n : ℕ) : (∫ x, F n x ∂(m.tilted (-V))) = -(∫ x, G n x ∂(m.tilted (-V))) :=
    integral_weightedLaplacian_mul_eq_neg_of_hasCompactSupport m hV hf2 (hw n)
      ((hasCompactSupport_cutoff (by positivity)).mul_right)
  have hneg := hGt.neg
  simp_rw [← hIBP] at hneg
  exact tendsto_nhds_unique hFt hneg

/-- **BKL (15)**, symmetry of the generator on `𝒜`: `∫ (ℒu) v dμ = ∫ u (ℒv) dμ`. -/
theorem integral_weightedLaplacian_mul_comm_of_hasTemperateGrowth {V f g : E → ℝ}
    (hV : ContDiff ℝ 1 V) {CV : ℝ} {kV : ℕ} (hVg : ∀ x, ‖gradient V x‖ ≤ CV * (1 + ‖x‖) ^ kV)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (m.tilted (-V)))
    (hf : f.HasTemperateGrowth) (hg : g.HasTemperateGrowth) :
    ∫ x, weightedLaplacian V f x * g x ∂(m.tilted (-V)) =
      ∫ x, f x * weightedLaplacian V g x ∂(m.tilted (-V)) := by
    calc
      ∫ x, weightedLaplacian V f x * g x ∂(m.tilted (-V)) =
          -∫ x, ⟪gradient f x, gradient g x⟫ ∂(m.tilted (-V)) :=
        integral_weightedLaplacian_mul_eq_neg_of_hasTemperateGrowth
          (m := m) (V := V) (f := f) (g := g) hV hVg hexp hf hg
      _ = -∫ x, ⟪gradient g x, gradient f x⟫ ∂(m.tilted (-V)) := by
        congr 1
        apply integral_congr_ae
        filter_upwards [] with x
        exact real_inner_comm _ _
      _ = ∫ x, weightedLaplacian V g x * f x ∂(m.tilted (-V)) :=
        (integral_weightedLaplacian_mul_eq_neg_of_hasTemperateGrowth
          (m := m) (V := V) (f := g) (g := f) hV hVg hexp hg hf).symm
      _ = ∫ x, f x * weightedLaplacian V g x ∂(m.tilted (-V)) := by
        apply integral_congr_ae
        filter_upwards [] with x
        exact mul_comm _ _

end FunctionalInequalities.Analysis.BakryEmery
