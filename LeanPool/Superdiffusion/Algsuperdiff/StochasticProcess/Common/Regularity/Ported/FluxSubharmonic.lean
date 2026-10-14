/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepSchauderFlux
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# FluxSubharmonic

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Subharmonic extension of the spherical flux calculus

This module contains only the subharmonic additions to the paper-side spherical
flux machinery. The harmonic definitions and mean-value lemmas are reused from
`OneStepSchauderFlux`.
-/

open scoped Real ContDiff Laplacian
open MeasureTheory Metric Set InnerProductSpace

namespace Algsuperdiff.StochasticProcess.Common.Regularity.Ported

open Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

noncomputable section

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

private theorem laplacian_zero_fun' : Δ (0 : 𝔼 → ℝ) = 0 := by
  rw [show (0 : 𝔼 → ℝ) = fun _ => (0 : ℝ) from rfl]
  funext z
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, iteratedFDeriv_fun_zero]
  simp

private theorem support_laplacian_subset' {ψ : 𝔼 → ℝ} :
    Function.support (Δ ψ) ⊆ tsupport ψ := by
  intro y hy
  by_contra hy'
  rw [Function.mem_support] at hy
  refine hy ?_
  have hev : ψ =ᶠ[nhds y] 0 := notMem_tsupport_iff_eventuallyEq.mp hy'
  have := (laplacian_congr_nhds hev).eq_of_nhds
  rw [this, laplacian_zero_fun']; rfl

theorem sphereMeasure_mul_integral_Ioi_weighted_sphereAverage_eq_laplacian [NeZero d]
    {u : 𝔼 → ℝ} (hu : ContDiff ℝ 2 u) {x : 𝔼}
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hψsupp : HasCompactSupport (fun w : 𝔼 ↦ φ (‖w - x‖ ^ 2))) :
    (sphereMeasure d).real univ *
        ∫ s in Ioi (0 : ℝ),
          s ^ (d - 1) *
              (4 * s ^ 2 * deriv (deriv φ) (s ^ 2) + 2 * (d : ℝ) * deriv φ (s ^ 2)) *
            sphereAverage x s u =
      ∫ y, Δ u y * φ (‖y - x‖ ^ 2) := by
  classical
  set ψ : 𝔼 → ℝ := fun w ↦ φ (‖w - x‖ ^ 2) with hψdef
  set M : ℝ → ℝ :=
    fun s ↦ 4 * s ^ 2 * deriv (deriv φ) (s ^ 2) + 2 * (d : ℝ) * deriv φ (s ^ 2) with hM
  have hψC2 : ContDiff ℝ 2 ψ :=
    (hφ.comp ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const))).of_le (by norm_cast)
  have hφ'C : ContDiff ℝ ∞ (deriv φ) := (contDiff_infty_iff_deriv.mp hφ).2
  have hd1 : Continuous (deriv φ) := hφ.continuous_deriv (by norm_cast)
  have hd2 : Continuous (deriv (deriv φ)) := hφ'C.continuous_deriv (by norm_cast)
  have hnsq : Continuous (fun w : 𝔼 ↦ ‖w - x‖ ^ 2) :=
    (continuous_norm.pow 2).comp (continuous_id.sub continuous_const)
  have hΔeq : Δ ψ = fun w ↦ 4 * ‖w - x‖ ^ 2 * deriv (deriv φ) (‖w - x‖ ^ 2)
      + 2 * (d : ℝ) * deriv φ (‖w - x‖ ^ 2) := by
    funext w
    rw [hψdef]
    exact laplacian_radial hφ x w
  have hΔcont : Continuous (Δ ψ) := by
    rw [hΔeq]
    exact ((continuous_const.mul hnsq).mul (hd2.comp hnsq)).add
      (continuous_const.mul (hd1.comp hnsq))
  have hΔsupp : HasCompactSupport (Δ ψ) := by
    exact hψsupp.of_isClosed_subset (isClosed_tsupport (Δ ψ))
      (closure_minimal support_laplacian_subset' (isClosed_tsupport ψ))
  set G : 𝔼 → ℝ := fun z ↦ u (x + z) * Δ ψ (x + z) with hG
  have hGcont : Continuous G :=
    (hu.continuous.comp (continuous_const.add continuous_id)).mul
      (hΔcont.comp (continuous_const.add continuous_id))
  have hGsupp : HasCompactSupport G := by
    have hΔtrans : HasCompactSupport (fun z ↦ Δ ψ (x + z)) :=
      hΔsupp.comp_homeomorph (Homeomorph.addLeft x)
    exact hΔtrans.mul_left
  have hGint : Integrable G := hGcont.integrable_of_hasCompactSupport hGsupp
  have htrans : (∫ z, G z) = ∫ y, u y * Δ ψ y := by
    have h := integral_add_left_eq_self (μ := (volume : Measure 𝔼))
      (fun y : 𝔼 ↦ u y * Δ ψ y) x
    simpa only [hG] using h
  have hgreen : (∫ y, u y * Δ ψ y) = ∫ y, Δ u y * ψ y :=
    integral_mul_laplacian_eq_integral_laplacian_mul hu hψC2 hψsupp
  have hpolar := integral_eq_integral_Ioi_sphere (G := G) hGint
  have hinner : ∀ s ∈ Ioi (0 : ℝ), (∫ ξ, G (s • (ξ : 𝔼)) ∂(sphereMeasure d))
      = (sphereMeasure d).real univ * (M s * sphereAverage x s u) := by
    intro s hs
    have hs0 : (0 : ℝ) < s := hs
    have hfun : (fun ξ : sphere (0 : 𝔼) 1 ↦ G (s • (ξ : 𝔼))) =
        fun ξ : sphere (0 : 𝔼) 1 ↦ u (x + s • (ξ : 𝔼)) * M s := by
      funext ξ
      simp only [hG]
      rw [show Δ ψ (x + s • (ξ : 𝔼)) = M s from by
        rw [hψdef]
        exact laplacian_radialTest_apply hφ x hs0 ξ]
    rw [hfun, integral_mul_const, integral_sphere_eq_measureReal_smul_sphereAverage,
      smul_eq_mul]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi (fun s hs ↦ by rw [hinner s hs])] at hpolar
  have hfactor : (∫ s in Ioi (0 : ℝ),
        s ^ (d - 1) • ((sphereMeasure d).real univ * (M s * sphereAverage x s u))) =
      (sphereMeasure d).real univ *
        ∫ s in Ioi (0 : ℝ), s ^ (d - 1) * M s * sphereAverage x s u := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun s _ ↦ ?_)
    rw [smul_eq_mul]
    ring
  rw [hfactor] at hpolar
  rw [← hpolar, htrans, hgreen]

/-! ### Support helpers -/

/-- A continuous integrable `f` that vanishes for `s > r` (with `0 < r < R`) has the same integral
over `(0, ∞)` and over the interval `[0, R]`. -/
private theorem intervalIntegral_eq_integral_Ioi_of_zero {f : ℝ → ℝ} {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hint : Integrable f)
    (hzero : ∀ s : ℝ, r < s → f s = 0) :
    ∫ s in (0 : ℝ)..R, f s = ∫ s in Ioi (0 : ℝ), f s := by
  have hle : (0 : ℝ) ≤ R := le_of_lt (hr.trans hrR)
  rw [intervalIntegral.integral_of_le hle]
  have hsplit : ∫ s in Ioi (0 : ℝ), f s
      = (∫ s in Ioc (0 : ℝ) R, f s) + ∫ s in Ioi R, f s := by
    rw [← setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      hint.integrableOn hint.integrableOn, Set.Ioc_union_Ioi_eq_Ioi hle]
  rw [hsplit, setIntegral_eq_zero_of_forall_eq_zero (t := Set.Ioi R)
    (fun s hs => hzero s (hrR.trans hs)), add_zero]

/-- **The radial profile of the test vanishes past `r`.**  If `tsupport (φ(‖· − x‖²)) ⊆ ball x r`,
then `φ t = 0` for every `t ≥ r²` (and `t ≥ 0`): otherwise a sphere point at
radius `√t ≥ r` would lie
in the support. -/
private theorem radialTest_eq_zero_of_ge [NeZero d] {φ : ℝ → ℝ} {x : 𝔼} {r : ℝ}
    (htsupp : tsupport (fun w : 𝔼 => φ (‖w - x‖ ^ 2)) ⊆ Metric.ball x r)
    {t : ℝ} (ht : 0 ≤ t) (htr : r ^ 2 ≤ t) : φ t = 0 := by
  by_contra hne
  obtain ⟨i⟩ : Nonempty (Fin d) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩⟩
  set e : 𝔼 := EuclideanSpace.single i (1 : ℝ) with he_def
  have he : ‖e‖ = 1 := by
    rw [he_def]
    simp
  set w : 𝔼 := x + Real.sqrt t • e with hw_def
  have hwx : ‖w - x‖ = Real.sqrt t := by
    rw [hw_def, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg t),
      he, mul_one]
  have hwsq : ‖w - x‖ ^ 2 = t := by rw [hwx, Real.sq_sqrt ht]
  have hmem : w ∈ tsupport (fun w : 𝔼 => φ (‖w - x‖ ^ 2)) := by
    refine subset_tsupport _ ?_
    rw [Function.mem_support]
    rw [hwsq]; exact hne
  have hball := htsupp hmem
  rw [Metric.mem_ball, dist_eq_norm, hwx] at hball
  have : t < r ^ 2 := by
    nlinarith only [hball, Real.sq_sqrt ht, Real.sqrt_nonneg t]
  exact (not_lt_of_ge htr) this

/-! ### The flux test identity -/

/-- **Flux test identity (integration by parts).**  For `u ∈ C²` harmonic on `Metric.ball x R` and a
radial test `ψ = φ(‖· − x‖²)` (`φ ∈ C^∞`, compactly supported inside
`Metric.ball x r`, `0 < r < R`),
  `∫₀^∞ (2 s φ'(s²)) · (s^{d−1} · sphereFlux x s u) ds = 0`.

This is `RadialLaplacian.hasDerivAt_weighted_radialProfile` integrated by parts against
`sphereAverage`, whose radial derivative is `‖S‖⁻¹ · sphereFlux`.  The test
`η(s) = 2 s φ'(s²)` ranges
over `C^∞_c((0, R))` as `φ` ranges over admissible radial profiles, so this is
the pairing consumed by
the fundamental lemma. -/
theorem integral_Ioi_test_sphereFlux_eq_neg_integral_laplacian [NeZero d]
    {u : 𝔼 → ℝ} (hu : ContDiff ℝ 2 u) {x : 𝔼} {R : ℝ}
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hψsupp : HasCompactSupport (fun w : 𝔼 ↦ φ (‖w - x‖ ^ 2)))
    {r : ℝ} (hr : 0 < r) (hrR : r < R)
    (htsupp : tsupport (fun w : 𝔼 ↦ φ (‖w - x‖ ^ 2)) ⊆ Metric.ball x r) :
    ∫ s in Ioi (0 : ℝ),
        2 * s * deriv φ (s ^ 2) * (s ^ (d - 1) * sphereFlux x s u) =
      -∫ y, Δ u y * φ (‖y - x‖ ^ 2) := by
  classical
  have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
  set σ : ℝ := (sphereMeasure d).real Set.univ with hσ_def
  set c : ℝ := σ⁻¹ with hc_def
  have hσ0 : σ ≠ 0 := by simpa only [hσ_def] using sphereMeasure_real_univ_ne_zero (d := d)
  have hd1c : Continuous (deriv φ) := hφ.continuous_deriv (by norm_cast)
  have hd2c : Continuous (deriv (deriv φ)) :=
    ((contDiff_infty_iff_deriv.mp hφ).2).continuous_deriv (by norm_cast)
  set U : ℝ → ℝ := fun s ↦ s ^ (d - 1) * (2 * s * deriv φ (s ^ 2)) with hU
  set U' : ℝ → ℝ :=
    fun s ↦ s ^ (d - 1) *
      (4 * s ^ 2 * deriv (deriv φ) (s ^ 2) + 2 * (d : ℝ) * deriv φ (s ^ 2)) with hU'
  set V : ℝ → ℝ := fun s ↦ sphereAverage x s u with hV
  set V' : ℝ → ℝ := fun s ↦ c * sphereFlux x s u with hV'
  have hUderiv : ∀ s, HasDerivAt U (U' s) s := fun s ↦
    hasDerivAt_weighted_radialProfile hφ hd1 s
  have hVderiv : ∀ s, HasDerivAt V (V' s) s := by
    intro s
    have h := hasDerivAt_sphereAverage hu1 x s
    rw [← sphereFlux_def, smul_eq_mul, ← hσ_def, ← hc_def] at h
    exact h
  have hU'c : Continuous U' := by
    rw [hU']
    exact (continuous_pow _).mul
      (((continuous_const.mul (continuous_pow 2)).mul (hd2c.comp (continuous_pow 2))).add
        (continuous_const.mul (hd1c.comp (continuous_pow 2))))
  have hV'c : Continuous V' := by
    rw [hV']
    exact continuous_const.mul (continuous_sphereFlux hu1 x)
  have hUdiff : Differentiable ℝ U := fun s ↦ (hUderiv s).differentiableAt
  have hUc : Continuous U := hUdiff.continuous
  have hVc : Continuous V := continuous_sphereAverage hu.continuous x
  have hφ'zero : ∀ s : ℝ, r < s → deriv φ (s ^ 2) = 0 := by
    intro s hs
    have hs2 : r ^ 2 < s ^ 2 := by nlinarith only [hs, hr]
    have hev : φ =ᶠ[nhds (s ^ 2)] 0 := by
      have hmem : Ioi (r ^ 2) ∈ nhds (s ^ 2) := Ioi_mem_nhds hs2
      filter_upwards [hmem] with t ht
      exact radialTest_eq_zero_of_ge htsupp (le_of_lt (lt_of_le_of_lt (sq_nonneg r) ht))
        (le_of_lt ht)
    rw [hev.deriv_eq]
    simp
  have hφ''zero : ∀ s : ℝ, r < s → deriv (deriv φ) (s ^ 2) = 0 := by
    intro s hs
    have hs2 : r ^ 2 < s ^ 2 := by nlinarith only [hs, hr]
    have hev : deriv φ =ᶠ[nhds (s ^ 2)] 0 := by
      have hmem : Ioi (r ^ 2) ∈ nhds (s ^ 2) := Ioi_mem_nhds hs2
      filter_upwards [hmem] with t ht
      have hev' : φ =ᶠ[nhds t] 0 := by
        have hmem' : Ioi (r ^ 2) ∈ nhds t := Ioi_mem_nhds ht
        filter_upwards [hmem'] with t' ht'
        exact radialTest_eq_zero_of_ge htsupp
          (le_of_lt (lt_of_le_of_lt (sq_nonneg r) ht')) (le_of_lt ht')
      rw [hev'.deriv_eq]
      simp
    rw [hev.deriv_eq]
    simp
  have hU'zero : ∀ s : ℝ, r < |s| → U' s = 0 := by
    intro s hs
    have h1 : deriv φ (s ^ 2) = 0 := by
      have h := hφ'zero |s| hs
      rwa [sq_abs] at h
    have h2 : deriv (deriv φ) (s ^ 2) = 0 := by
      have h := hφ''zero |s| hs
      rwa [sq_abs] at h
    simp only [hU']
    rw [h1, h2]
    ring
  have hUzero : ∀ s : ℝ, r < |s| → U s = 0 := by
    intro s hs
    have h1 : deriv φ (s ^ 2) = 0 := by
      have h := hφ'zero |s| hs
      rwa [sq_abs] at h
    simp only [hU]
    rw [h1]
    ring
  have hU'Vzero : ∀ s : ℝ, r < s → U' s * V s = 0 := by
    intro s hs
    rw [hU'zero s (by rw [abs_of_pos (lt_trans hr hs)]; exact hs), zero_mul]
  have hUV'zero : ∀ s : ℝ, r < s → U s * V' s = 0 := by
    intro s hs
    rw [hUzero s (by rw [abs_of_pos (lt_trans hr hs)]; exact hs), zero_mul]
  have hU'Vsupp : HasCompactSupport (fun s ↦ U' s * V s) := by
    apply HasCompactSupport.intro (K := Icc (-r) r) isCompact_Icc
    intro s hs
    rw [mem_Icc, not_and_or, not_le, not_le] at hs
    have habs : r < |s| := by
      rcases hs with hlt | hlt
      · rw [abs_of_neg (by linarith only [hlt, hr] : s < 0)]
        linarith only [hlt]
      · rw [abs_of_pos (by linarith only [hlt, hr] : (0 : ℝ) < s)]
        exact hlt
    simp only [hU'zero s habs, zero_mul]
  have hUV'supp : HasCompactSupport (fun s ↦ U s * V' s) := by
    apply HasCompactSupport.intro (K := Icc (-r) r) isCompact_Icc
    intro s hs
    rw [mem_Icc, not_and_or, not_le, not_le] at hs
    have habs : r < |s| := by
      rcases hs with hlt | hlt
      · rw [abs_of_neg (by linarith only [hlt, hr] : s < 0)]
        linarith only [hlt]
      · rw [abs_of_pos (by linarith only [hlt, hr] : (0 : ℝ) < s)]
        exact hlt
    simp only [hUzero s habs, zero_mul]
  have hU'Vint : Integrable (fun s ↦ U' s * V s) :=
    (hU'c.mul hVc).integrable_of_hasCompactSupport hU'Vsupp
  have hUV'int : Integrable (fun s ↦ U s * V' s) :=
    (hUc.mul hV'c).integrable_of_hasCompactSupport hUV'supp
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := U) (v := V) (u' := U') (v' := V') (a := 0) (b := R)
    (fun s _ ↦ hUderiv s) (fun s _ ↦ hVderiv s)
    (hU'c.intervalIntegrable 0 R) (hV'c.intervalIntegrable 0 R)
  have hUR : U R = 0 := hUzero R (by rw [abs_of_pos (lt_trans hr hrR)]; exact hrR)
  have hU0 : U 0 = 0 := by simp only [hU]; ring
  rw [hUR, hU0, zero_mul, zero_mul, sub_zero] at hIBP
  have hradGlobal :
      ∫ s in Ioi (0 : ℝ), U' s * V s =
        c * ∫ y, Δ u y * φ (‖y - x‖ ^ 2) := by
    have hrad :=
      sphereMeasure_mul_integral_Ioi_weighted_sphereAverage_eq_laplacian
        (d := d) hu hφ hψsupp
    have hshape :
        ∫ s in Ioi (0 : ℝ), U' s * V s =
          ∫ s in Ioi (0 : ℝ),
            s ^ (d - 1) *
                (4 * s ^ 2 * deriv (deriv φ) (s ^ 2) +
                  2 * (d : ℝ) * deriv φ (s ^ 2)) * sphereAverage x s u := by
      refine setIntegral_congr_fun measurableSet_Ioi (fun s _ ↦ ?_)
      simp only [hU', hV]
    rw [hshape]
    calc
      _ = c * (σ * ∫ s in Ioi (0 : ℝ),
          s ^ (d - 1) *
              (4 * s ^ 2 * deriv (deriv φ) (s ^ 2) +
                2 * (d : ℝ) * deriv φ (s ^ 2)) * sphereAverage x s u) := by
            rw [hc_def, inv_mul_cancel_left₀ hσ0]
      _ = c * ∫ y, Δ u y * φ (‖y - x‖ ^ 2) := by
            rw [hσ_def, hrad]
  have hrad : ∫ s in (0 : ℝ)..R, U' s * V s =
      c * ∫ y, Δ u y * φ (‖y - x‖ ^ 2) := by
    rw [intervalIntegral_eq_integral_Ioi_of_zero hr hrR hU'Vint hU'Vzero]
    exact hradGlobal
  rw [hrad] at hIBP
  rw [intervalIntegral_eq_integral_Ioi_of_zero hr hrR hUV'int hUV'zero] at hIBP
  have hpull : (∫ s in Ioi (0 : ℝ), U s * V' s) =
      c * ∫ s in Ioi (0 : ℝ),
        2 * s * deriv φ (s ^ 2) * (s ^ (d - 1) * sphereFlux x s u) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun s _ ↦ ?_)
    simp only [hU, hV']
    ring
  rw [hpull] at hIBP
  have hc0 : c ≠ 0 := inv_ne_zero hσ0
  have heq : c *
      (∫ s in Ioi (0 : ℝ),
        2 * s * deriv φ (s ^ 2) * (s ^ (d - 1) * sphereFlux x s u)) =
      c * (-∫ y, Δ u y * φ (‖y - x‖ ^ 2)) := by
    simpa [mul_neg] using hIBP
  exact mul_left_cancel₀ hc0 heq

private theorem fluxSubharmonic_comparisonBounds1 :
    ∀ {d : ℕ} {u : (EuclideanSpace ℝ (Fin d)) → ℝ} {x : (EuclideanSpace ℝ (Fin d))} {ρ : ℝ} (_ :
      Continuous fun (s : ℝ) => sphereFlux x s u),
      let f₀ : ℝ := sphereFlux x ρ u;
      ∀ (_ : f₀ < (0 : ℝ)) (δ : ℝ),
        let ε : ℝ := δ / (2 : ℝ);
        let a : ℝ := ρ - ε;
        let b : ℝ := ρ + ε;
        ∀ (_ : ∀ s ∈ Icc a b, (0 : ℝ) < sphereFlux x s u * f₀) (_ : (0 : ℝ) < a) (_ : (0 : ℝ) < b),
          let α : ℝ := a ^ (2 : ℕ);
            let β : ℝ := b ^ (2 : ℕ);
              let L : ℝ → ℝ := fun (t : ℝ) => (t - α) / (β - α);
              let φ : ℝ → ℝ := fun (t : ℝ) => (1 : ℝ) - (L t).smoothTransition;
              ∀ (_ : ContDiff ℝ ∞ φ) (_ : ∀ (t : ℝ), deriv φ t ≤ (0 : ℝ))
                (_ : ∀ (t : ℝ), t < α ∨ β < t → deriv φ t = (0 : ℝ)),
                let I' : ℝ → ℝ := fun (s : ℝ) =>
                  (2 : ℝ) * s * deriv φ (s ^ (2 : ℕ)) * (s ^ (d - (1 : ℕ)) * sphereFlux x s u);
                ∀ (_ : integral (volume.restrict (Ioi (0 : ℝ))) I' ≤ (0 : ℝ))
                  ,
                  let G : ℝ → ℝ := fun (s : ℝ) => -f₀ * I' s;
                   Continuous I' ∧ G =ᵐ[volume.restrict (Ioi
                    (0 : ℝ))] (0 : ℝ → ℝ) := by
  intro d u x _ hcont f₀ hf₀neg _ _ a b hsamesign ha0 hb0 calculationΑ β _ φ hφ_inf hφ_deriv_np
    hφ_deriv_out I' hfluxPair_le G
  have hαdef : calculationΑ = a ^ (2 : ℕ) := rfl
  have hβdef : β = b ^ (2 : ℕ) := rfl
  have hI'def : I' = fun (s : ℝ) => (2 : ℝ) * s * deriv φ (s ^ (2 : ℕ)) * (s ^ (d - (1 : ℕ)) *
                      sphereFlux x s u) := rfl
  have hGdef : G = fun (s : ℝ) => -f₀ * I' s := rfl
  have hGintle : ∫ s in Ioi (0 : ℝ), G s ≤ 0 := by
    simp only [hGdef]
    rw [integral_const_mul]
    exact mul_nonpos_of_nonneg_of_nonpos (by linarith only [hf₀neg]) hfluxPair_le
  have hd1c : Continuous (deriv φ) := hφ_inf.continuous_deriv (by norm_cast)
  have hI'cont : Continuous I' := by
    simp only [hI'def]
    exact (((continuous_const.mul continuous_id).mul (hd1c.comp (continuous_pow 2))).mul
      ((continuous_pow _).mul hcont))
  have hGcont : Continuous G := by
    simp only [hGdef]
    exact continuous_const.mul hI'cont
  have hGnn : ∀ s, 0 < s → 0 ≤ G s := by
    intro s hs
    by_cases hd : deriv φ (s ^ 2) = 0
    · have hz : G s = 0 := by simp only [hGdef, hI'def, hd]; ring
      exact le_of_eq hz.symm
    · have hmemcc : s ∈ Icc a b := by
        rw [mem_Icc]
        by_contra hcon
        rw [not_and_or, not_le, not_le] at hcon
        refine hd (hφ_deriv_out (s ^ 2) ?_)
        rcases hcon with hlt | hlt
        · left
          simp only [hαdef]
          nlinarith only [hlt, hs, ha0]
        · right
          simp only [hβdef]
          nlinarith only [hlt, hb0]
      have hsf : 0 < sphereFlux x s u * f₀ := hsamesign s hmemcc
      have hsf' : 0 < f₀ * sphereFlux x s u := by rw [mul_comm]; exact hsf
      have hEq : G s =
          (2 * s * s ^ (d - 1)) * (-(deriv φ (s ^ 2))) *
            (f₀ * sphereFlux x s u) := by
        simp only [hGdef, hI'def]
        ring
      rw [hEq]
      have h2s : (0 : ℝ) < 2 * s * s ^ (d - 1) := by
        exact mul_pos (by linarith only [hs]) (pow_pos hs (d - 1))
      exact mul_nonneg
        (mul_nonneg (le_of_lt h2s) (by linarith only [hφ_deriv_np (s ^ 2)]))
        (le_of_lt hsf')
  have hGsupp : HasCompactSupport G := by
    apply HasCompactSupport.intro (K := Icc (-b) b) isCompact_Icc
    intro s hs
    rw [mem_Icc, not_and_or, not_le, not_le] at hs
    have hout : β < s ^ 2 := by
      rcases hs with hlt | hlt
      · simp only [hβdef]
        nlinarith only [hlt, hb0]
      · simp only [hβdef]
        nlinarith only [hlt, hb0]
    simp only [hGdef, hI'def, hφ_deriv_out (s ^ 2) (Or.inr hout)]
    ring
  have hGint : Integrable G := hGcont.integrable_of_hasCompactSupport hGsupp
  have hGintnn : 0 ≤ ∫ s in Ioi (0 : ℝ), G s := by
    apply setIntegral_nonneg measurableSet_Ioi
    intro s hs
    exact hGnn s hs
  have hGint0 : ∫ s in Ioi (0 : ℝ), G s = 0 := le_antisymm hGintle hGintnn
  have hGae : G =ᵐ[volume.restrict (Ioi 0)] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae
      ((ae_restrict_iff' measurableSet_Ioi).mpr
        (Filter.Eventually.of_forall fun s hs ↦ hGnn s hs)) hGint.integrableOn).mp hGint0
  exact ⟨hI'cont, hGae⟩

/-- **Outward flux is nonnegative for a subharmonic function.** -/
theorem sphereFlux_nonneg_of_laplacian_nonneg [NeZero d]
    {u : 𝔼 → ℝ} (hu : ContDiff ℝ 2 u) {x : 𝔼} {R : ℝ}
    (hlap : ∀ y ∈ Metric.ball x R, 0 ≤ Δ u y)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρR : ρ < R) :
    0 ≤ sphereFlux x ρ u := by
  classical
  by_contra hnot
  have hneg : sphereFlux x ρ u < 0 := lt_of_not_ge hnot
  have hne : sphereFlux x ρ u ≠ 0 := ne_of_lt hneg
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
  have hcont : Continuous (fun s ↦ sphereFlux x s u) := continuous_sphereFlux hu1 x
  set f₀ : ℝ := sphereFlux x ρ u with hf0
  have hf₀neg : f₀ < 0 := by simpa only [hf0] using hneg
  have hsign_open : IsOpen {s : ℝ | 0 < sphereFlux x s u * f₀} :=
    isOpen_lt continuous_const (hcont.mul continuous_const)
  have hρmem : ρ ∈ {s : ℝ | 0 < sphereFlux x s u * f₀} ∩ Ioo 0 R := by
    refine ⟨?_, hρ0, hρR⟩
    simp only [Set.mem_ofPred_eq, ← hf0]
    exact mul_self_pos.mpr hne
  obtain ⟨δ, hδ0, hball⟩ :=
    Metric.isOpen_iff.mp (hsign_open.inter isOpen_Ioo) ρ hρmem
  set ε : ℝ := δ / 2 with hε
  have hε0 : 0 < ε := by positivity
  have hεδ : ε < δ := by rw [hε]; linarith only [hδ0]
  set a : ℝ := ρ - ε with ha
  set b : ℝ := ρ + ε with hb
  have hclosed : ∀ s ∈ Icc a b,
      s ∈ {s : ℝ | 0 < sphereFlux x s u * f₀} ∩ Ioo 0 R := by
    intro s hs
    rw [mem_Icc] at hs
    simp only [ha, hb] at hs
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    exact ⟨by linarith only [hs.1, hεδ], by linarith only [hs.2, hεδ]⟩
  have hsamesign : ∀ s ∈ Icc a b, 0 < sphereFlux x s u * f₀ :=
    fun s hs ↦ (hclosed s hs).1
  have hab : a < b := by simp only [ha, hb]; linarith only [hε0]
  have ha0 : 0 < a := (hclosed a (left_mem_Icc.2 (le_of_lt hab))).2.1
  have hbR : b < R := (hclosed b (right_mem_Icc.2 (le_of_lt hab))).2.2
  have hb0 : 0 < b := lt_trans ha0 hab
  set α : ℝ := a ^ 2 with hαdef
  set β : ℝ := b ^ 2 with hβdef
  have hβα : 0 < β - α := by
    simp only [hαdef, hβdef]
    nlinarith only [ha0, hab]
  set L : ℝ → ℝ := fun t ↦ (t - α) / (β - α) with hLdef
  set φ : ℝ → ℝ := fun t ↦ 1 - Real.smoothTransition (L t) with hφdef
  have hL_cd : ContDiff ℝ ∞ L := (contDiff_id.sub contDiff_const).div_const _
  have hφ_inf : ContDiff ℝ ∞ φ :=
    contDiff_const.sub (Real.smoothTransition.contDiff.comp hL_cd)
  have hL_mono : Monotone L := by
    intro s t hst
    simp only [hLdef]
    gcongr
  have hφ_anti : Antitone φ := by
    intro s t hst
    simp only [hφdef]
    have hmono := Real.smoothTransition.monotone (hL_mono hst)
    linarith only [hmono]
  have hφ_deriv_np : ∀ t, deriv φ t ≤ 0 := fun t ↦ hφ_anti.deriv_nonpos
  have hφ_nonneg : ∀ t, 0 ≤ φ t := by
    intro t
    simp only [hφdef]
    linarith only [Real.smoothTransition.le_one (L t)]
  have hφ_one : ∀ t, t ≤ α → φ t = 1 := by
    intro t ht
    simp only [hφdef, hLdef]
    rw [Real.smoothTransition.zero_of_nonpos
      (div_nonpos_iff.mpr (Or.inr ⟨by linarith only [ht], le_of_lt hβα⟩))]
    ring
  have hφ_zero : ∀ t, β ≤ t → φ t = 0 := by
    intro t ht
    simp only [hφdef, hLdef]
    rw [Real.smoothTransition.one_of_one_le ((one_le_div hβα).mpr (by linarith only [ht]))]
    ring
  have hφ_deriv_out : ∀ t, t < α ∨ β < t → deriv φ t = 0 := by
    intro t ht
    rcases ht with ht | ht
    · have hev : φ =ᶠ[nhds t] fun _ ↦ 1 := by
        filter_upwards [Iio_mem_nhds ht] with s hs
        exact hφ_one s (le_of_lt hs)
      rw [hev.deriv_eq]
      simp
    · have hev : φ =ᶠ[nhds t] fun _ ↦ 0 := by
        filter_upwards [Ioi_mem_nhds ht] with s hs
        exact hφ_zero s (le_of_lt hs)
      rw [hev.deriv_eq]
      simp
  set ψ : 𝔼 → ℝ := fun w ↦ φ (‖w - x‖ ^ 2) with hψdef
  set r' : ℝ := (b + R) / 2 with hr'def
  have hr'0 : 0 < r' := by rw [hr'def]; linarith only [hb0, hbR]
  have hr'R : r' < R := by rw [hr'def]; linarith only [hbR]
  have hbr' : b < r' := by rw [hr'def]; linarith only [hbR]
  have hsupp_sub : Function.support ψ ⊆ closedBall x b := by
    intro w hw
    by_contra hnotmem
    rw [mem_closedBall, dist_eq_norm, not_le] at hnotmem
    exact (Function.mem_support.mp hw)
      (hφ_zero _ (by
        simp only [hβdef]
        nlinarith only [hnotmem, hb0, norm_nonneg (w - x)]))
  have htsupp : tsupport ψ ⊆ Metric.ball x r' :=
    (closure_minimal hsupp_sub isClosed_closedBall).trans (closedBall_subset_ball hbr')
  have hψsupp : HasCompactSupport ψ :=
    (isCompact_closedBall x b).of_isClosed_subset (isClosed_tsupport ψ)
      (closure_minimal hsupp_sub isClosed_closedBall)
  have hfluxPair := integral_Ioi_test_sphereFlux_eq_neg_integral_laplacian
    hu hφ_inf hψsupp hr'0 hr'R htsupp
  have hlapIntegral : 0 ≤ ∫ y, Δ u y * φ (‖y - x‖ ^ 2) := by
    apply integral_nonneg
    intro y
    change 0 ≤ Δ u y * φ (‖y - x‖ ^ 2)
    by_cases hy : y ∈ Metric.ball x R
    · exact mul_nonneg (hlap y hy) (hφ_nonneg _)
    · have hφy : φ (‖y - x‖ ^ 2) = 0 := by
        by_contra hneφ
        have hysupp : y ∈ Function.support ψ := by
          rw [Function.mem_support]
          simpa only [hψdef] using hneφ
        have hyr' : y ∈ Metric.ball x r' := htsupp (subset_tsupport ψ hysupp)
        exact hy (Metric.ball_subset_ball hr'R.le hyr')
      rw [hφy, mul_zero]
  have hfluxPair_le :
      ∫ s in Ioi (0 : ℝ),
        2 * s * deriv φ (s ^ 2) * (s ^ (d - 1) * sphereFlux x s u) ≤ 0 := by
    rw [hfluxPair]
    exact neg_nonpos.mpr hlapIntegral
  set I' : ℝ → ℝ :=
    fun s ↦ 2 * s * deriv φ (s ^ 2) * (s ^ (d - 1) * sphereFlux x s u) with hI'def
  set G : ℝ → ℝ := fun s ↦ -f₀ * I' s with hGdef
  obtain ⟨hI'cont, hGae⟩ :=
    (show (Continuous I') ∧ (G =ᵐ[volume.restrict (Ioi 0)] 0) from
      @fluxSubharmonic_comparisonBounds1 (d) (u) (x) (ρ) (hcont) (hf₀neg) (δ) (hsamesign) (ha0)
        (hb0)   (hφ_inf) (hφ_deriv_np) (hφ_deriv_out) (hfluxPair_le)  )
  have hInull : volume ({s : ℝ | I' s ≠ 0} ∩ Ioi 0) = 0 := by
    have hIae : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Ioi 0 → I' s = 0 := by
      filter_upwards [(ae_restrict_iff' (μ := volume) measurableSet_Ioi).mp hGae]
        with s hsG hsmem
      have hG0 : -f₀ * I' s = 0 := hsG hsmem
      exact (mul_eq_zero.mp hG0).resolve_left (neg_ne_zero.mpr (by simpa only [hf0] using hne))
    rw [ae_iff] at hIae
    refine measure_mono_null ?_ hIae
    rintro s ⟨hs1, hs2⟩ hcontra
    exact hs1 (hcontra hs2)
  have hI0 : ∀ s ∈ Ioi (0 : ℝ), I' s = 0 := by
    intro s hs
    by_contra h
    have hopen : IsOpen ({s : ℝ | I' s ≠ 0} ∩ Ioi 0) :=
      (isOpen_ne.preimage hI'cont).inter isOpen_Ioi
    have hpos := hopen.measure_pos (μ := volume) ⟨s, h, hs⟩
    rw [hInull] at hpos
    exact lt_irrefl 0 hpos
  set p : ℝ → ℝ := fun s ↦ φ (s ^ 2) with hpdef
  have hp_diff : Differentiable ℝ p :=
    (hφ_inf.comp (contDiff_id.pow 2)).differentiable (by norm_cast)
  have hp_derivval : ∀ s, deriv p s = 2 * s * deriv φ (s ^ 2) := by
    intro s
    simp only [hpdef]
    exact deriv_radialProfile hφ_inf s
  have hp_deriv0 : ∀ s ∈ Icc a b, deriv p s = 0 := by
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le ha0 hs.1
    have hI's : I' s = 0 := hI0 s hs0
    have hsf : 0 < sphereFlux x s u * f₀ := hsamesign s hs
    have hsfne : sphereFlux x s u ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hsf
      exact lt_irrefl 0 hsf
    have hdφ : deriv φ (s ^ 2) = 0 := by
      have hfac :
          2 * s * deriv φ (s ^ 2) * (s ^ (d - 1) * sphereFlux x s u) = 0 := hI's
      have h1 : s ^ (d - 1) * sphereFlux x s u ≠ 0 := mul_ne_zero (by positivity) hsfne
      have h2 : 2 * s ≠ 0 := by positivity
      rcases mul_eq_zero.mp hfac with h | h
      · exact (mul_eq_zero.mp h).resolve_left h2
      · exact absurd h h1
    rw [hp_derivval, hdφ, mul_zero]
  have hp_const := constant_of_has_deriv_right_zero
    (f := p) (a := a) (b := b) hp_diff.continuous.continuousOn
    (fun s hs ↦ by
      have hda : HasDerivAt p 0 s := by
        have h := (hp_diff s).hasDerivAt
        rwa [hp_deriv0 s (Ico_subset_Icc_self hs)] at h
      exact hda.hasDerivWithinAt)
  have hpb : p b = p a := hp_const b (right_mem_Icc.2 (le_of_lt hab))
  have hpbz : p b = 0 := by simp only [hpdef]; exact hφ_zero (b ^ 2) (le_of_eq hβdef)
  have hpao : p a = 1 := by simp only [hpdef]; exact hφ_one (a ^ 2) (le_of_eq hαdef.symm)
  have : (0 : ℝ) = 1 := by rw [← hpbz, hpb, hpao]
  exact absurd this (by norm_num)

/-- Spherical averages of a smooth subharmonic function are nondecreasing in
the radius. -/
theorem sphereAverage_mono_of_laplacian_nonneg [NeZero d]
    {u : 𝔼 → ℝ} (hu : ContDiff ℝ 2 u) {x : 𝔼} {R : ℝ}
    (hlap : ∀ y ∈ Metric.ball x R, 0 ≤ Δ u y)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbR : b < R) :
    sphereAverage x a u ≤ sphereAverage x b u := by
  set F : ℝ → ℝ := fun r ↦ sphereAverage x r u with hF
  have hFdiff : Differentiable ℝ F := fun r ↦
    (hasDerivAt_sphereAverage (hu.of_le (by norm_num)) x r).differentiableAt
  have hmono : MonotoneOn F (Icc a b) :=
    monotoneOn_of_deriv_nonneg (convex_Icc a b) hFdiff.continuous.continuousOn
      hFdiff.differentiableOn fun r hr ↦ by
        rw [interior_Icc] at hr
        have hr0 : 0 < r := ha.trans hr.1
        have hrR : r < R := hr.2.trans_le (le_of_lt hbR)
        have hflux := sphereFlux_nonneg_of_laplacian_nonneg hu hlap hr0 hrR
        have hderiv := hasDerivAt_sphereAverage (hu.of_le (by norm_num)) x r
        rw [hderiv.deriv]
        exact smul_nonneg (by positivity) hflux
  exact hmono (left_mem_Icc.2 hab) (right_mem_Icc.2 hab) hab

end

end Algsuperdiff.StochasticProcess.Common.Regularity.Ported
