/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepSchauderWeakId
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# OneStepSchauderFlux

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The flux-vanishing crux and the mean value property

The three files merged here close the chain from harmonicity to the mean value
property:

* **flux vanishing** — for `u` harmonic on a neighbourhood of `closedBall x R`
  the spherical flux `∫_{∂B_r} ∂_ν u` vanishes for every `r < R`, obtained by
  testing the weak Laplacian identity against a radial cutoff and using the
  polar decomposition;
* **flux integration by parts** — the derivative of the sphere average is the
  normalized flux;
* **flux zero ⇒ constant sphere average**, and hence the mean value property
  `u(x) = ⨍_{∂B_r} u`, in the exact form the reproducing convolution needs.
-/

-- ==== flux vanishing ====
open scoped Real ContDiff Laplacian
open MeasureTheory Metric Set InnerProductSpace

namespace Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

noncomputable section

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- **Radiality of the test Laplacian on the sphere.**  For the radial test `ψ(w) = φ(‖w − x‖²)`
with `φ ∈ C^∞`, the Laplacian evaluated at the sphere point `x + r • ξ` (`ξ` a unit vector, `r > 0`)
equals the radial profile `m(r) = 4 r² φ''(r²) + 2 d φ'(r²)`, independently of the direction `ξ`.

This is the radiality fact (from `RadialLaplacian.laplacian_radial`) that lets the polar bridge pull
`m(r)` out of the sphere integral. -/
theorem laplacian_radialTest_apply {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (x : 𝔼) {r : ℝ} (hr : 0 < r)
    (ξ : sphere (0 : 𝔼) 1) :
    Δ (fun w => φ (‖w - x‖ ^ 2)) (x + r • (ξ : 𝔼))
      = 4 * r ^ 2 * deriv (deriv φ) (r ^ 2) + 2 * (d : ℝ) * deriv φ (r ^ 2) := by
  rw [laplacian_radial hφ x (x + r • (ξ : 𝔼))]
  have hnorm : ‖(x + r • (ξ : 𝔼)) - x‖ = r := by
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hr,
      mem_sphere_zero_iff_norm.mp ξ.2, mul_one]
  rw [hnorm]

/-- **The un-normalized spherical integral is the measure times the normalized average.**
`∫_S u(x + r ξ) dσ(ξ) = σ(S) · sphereAverage x r u`, from the definition of `sphereAverage` as the
measure average `⨍`. -/
theorem integral_sphere_eq_measureReal_smul_sphereAverage [NeZero d] (u : 𝔼 → ℝ) (x : 𝔼) (r : ℝ) :
    ∫ ξ, u (x + r • (ξ : 𝔼)) ∂(sphereMeasure d)
      = (sphereMeasure d).real Set.univ • sphereAverage x r u := by
  rw [sphereAverage_def, average_eq, smul_smul,
    mul_inv_cancel₀ sphereMeasure_real_univ_ne_zero, one_smul]

/-! ### Support of the Laplacian (helpers, re-derived natively) -/

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

/-! ### The radial weak identity — polar reduction of `∫ u · Δψ = 0` -/

/-- **Radial weak identity.**  For `u` harmonic on `Metric.ball x R` (and globally
`C²`) and a radial
test `ψ(w) = φ(‖w − x‖²)` (`φ ∈ C^∞`, compactly supported inside `Metric.ball x r`, `0 < r < R`),
the local weak identity `∫ u · Δψ = 0` (`CutoffLocalize`) reduces, via the general polar bridge
(piece 2) and the radial Laplacian profile (piece 1), to the **one-dimensional** vanishing

  `∫₀^∞ s^{d−1} · (4 s² φ''(s²) + 2 d φ'(s²)) · sphereAverage x s u ds = 0`.

This is the entry point of the du Bois-Reymond endgame: the integrand's weight
`s^{d−1} · (4 s² φ''(s²) + 2 d φ'(s²))` is the total derivative `(s^{d−1} p'(s))'`
(`RadialLaplacian.hasDerivAt_weighted_radialProfile`), so integrating by parts against
`sphereAverage x s u` transfers onto its radial derivative `‖S‖⁻¹ · sphereFlux`. -/
theorem integral_Ioi_weighted_sphereAverage_eq_zero [NeZero d]
    {u : 𝔼 → ℝ} (hu : ContDiff ℝ 2 u) {x : 𝔼} {R : ℝ}
    (hharm : HarmonicOnNhd u (Metric.ball x R))
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hψsupp : HasCompactSupport (fun w : 𝔼 => φ (‖w - x‖ ^ 2)))
    {r : ℝ} (hr : 0 < r) (hrR : r < R)
    (htsupp : tsupport (fun w : 𝔼 => φ (‖w - x‖ ^ 2)) ⊆ Metric.ball x r) :
    ∫ s in Ioi (0 : ℝ),
        s ^ (d - 1) * (4 * s ^ 2 * deriv (deriv φ) (s ^ 2) + 2 * (d : ℝ) * deriv φ (s ^ 2))
          * sphereAverage x s u = 0 := by
  classical
  set ψ : 𝔼 → ℝ := fun w => φ (‖w - x‖ ^ 2) with hψdef
  set M : ℝ → ℝ :=
    fun s => 4 * s ^ 2 * deriv (deriv φ) (s ^ 2) + 2 * (d : ℝ) * deriv φ (s ^ 2) with hM
  have hψC2 : ContDiff ℝ 2 ψ :=
    (hφ.comp ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const))).of_le (by norm_cast)
  -- continuity / support of `Δψ`
  have hφ'C : ContDiff ℝ ∞ (deriv φ) := (contDiff_infty_iff_deriv.mp hφ).2
  have hd1 : Continuous (deriv φ) := hφ.continuous_deriv (by norm_cast)
  have hd2 : Continuous (deriv (deriv φ)) := hφ'C.continuous_deriv (by norm_cast)
  have hnsq : Continuous (fun w : 𝔼 => ‖w - x‖ ^ 2) :=
    (continuous_norm.pow 2).comp (continuous_id.sub continuous_const)
  have hΔeq : Δ ψ = fun w => 4 * ‖w - x‖ ^ 2 * deriv (deriv φ) (‖w - x‖ ^ 2)
      + 2 * (d : ℝ) * deriv φ (‖w - x‖ ^ 2) := by
    funext w; rw [hψdef]; exact laplacian_radial hφ x w
  have hΔcont : Continuous (Δ ψ) := by
    rw [hΔeq]
    exact ((continuous_const.mul hnsq).mul (hd2.comp hnsq)).add
      (continuous_const.mul (hd1.comp hnsq))
  have hΔsupp : HasCompactSupport (Δ ψ) := by
    have hsub : tsupport (Δ ψ) ⊆ closedBall x r := by
      have h1 : tsupport (Δ ψ) ⊆ tsupport ψ :=
        closure_minimal support_laplacian_subset' (isClosed_tsupport ψ)
      exact h1.trans (htsupp.trans ball_subset_closedBall)
    exact (isCompact_closedBall x r).of_isClosed_subset (isClosed_tsupport (Δ ψ)) hsub
  -- the translated integrand and its integrability
  set G : 𝔼 → ℝ := fun z => u (x + z) * Δ ψ (x + z) with hG
  have hGcont : Continuous G :=
    (hu.continuous.comp (continuous_const.add continuous_id)).mul
      (hΔcont.comp (continuous_const.add continuous_id))
  have hGsupp : HasCompactSupport G := by
    have hΔtrans : HasCompactSupport (fun z => Δ ψ (x + z)) :=
      hΔsupp.comp_homeomorph (Homeomorph.addLeft x)
    exact hΔtrans.mul_left
  have hGint : Integrable G := hGcont.integrable_of_hasCompactSupport hGsupp
  -- weak identity, translated to the centre
  have hweak : ∫ y, u y * Δ ψ y = 0 :=
    integral_mul_laplacian_eq_zero_of_harmonicOn hr hrR hharm hψC2 hψsupp htsupp
  have htrans : (∫ z, G z) = 0 := by
    have h := integral_add_left_eq_self (μ := (volume : Measure 𝔼))
      (fun y : 𝔼 => u y * Δ ψ y) x
    rw [hweak] at h
    simpa only [hG] using h
  -- polar bridge
  have hpolar := integral_eq_integral_Ioi_sphere (G := G) hGint
  rw [htrans] at hpolar
  -- collapse the sphere integral using radiality of `Δψ`
  have hinner : ∀ s ∈ Ioi (0 : ℝ), (∫ ξ, G (s • (ξ : 𝔼)) ∂(sphereMeasure d))
      = (sphereMeasure d).real univ * (M s * sphereAverage x s u) := by
    intro s hs
    have hs0 : (0 : ℝ) < s := hs
    have hfun : (fun ξ : sphere (0 : 𝔼) 1 => G (s • (ξ : 𝔼)))
        = fun ξ : sphere (0 : 𝔼) 1 => u (x + s • (ξ : 𝔼)) * M s := by
      funext ξ
      simp only [hG]
      rw [show Δ ψ (x + s • (ξ : 𝔼)) = M s from by
        rw [hψdef]; exact laplacian_radialTest_apply hφ x hs0 ξ]
    rw [hfun, integral_mul_const, integral_sphere_eq_measureReal_smul_sphereAverage,
      smul_eq_mul]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi
    (fun s hs => by rw [hinner s hs])] at hpolar
  -- factor the constant `σ(S)` out of the radial integral
  have hfactor : (∫ s in Ioi (0 : ℝ),
        s ^ (d - 1) • ((sphereMeasure d).real univ * (M s * sphereAverage x s u)))
      = (sphereMeasure d).real univ *
          ∫ s in Ioi (0 : ℝ), s ^ (d - 1) * M s * sphereAverage x s u := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun s _ => ?_)
    rw [smul_eq_mul]; ring
  rw [hfactor] at hpolar
  have hI : (∫ s in Ioi (0 : ℝ), s ^ (d - 1) * M s * sphereAverage x s u) = 0 :=
    (mul_eq_zero.mp hpolar.symm).resolve_left sphereMeasure_real_univ_ne_zero
  simpa only [hM] using hI

end

end Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

-- ==== flux integration by parts ====
open scoped Real ContDiff Laplacian
open MeasureTheory Metric Set InnerProductSpace

namespace Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

noncomputable section

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

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
    have h : ‖EuclideanSpace.single i (1 : ℝ)‖ = ‖(1 : ℝ)‖ :=
      PiLp.norm_single (p := 2) (β := fun _ : Fin d => ℝ) i (1 : ℝ)
    rw [h, norm_one]
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
  linarith

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
theorem integral_Ioi_test_sphereFlux_eq_zero [NeZero d]
    {u : 𝔼 → ℝ} (hu : ContDiff ℝ 2 u) {x : 𝔼} {R : ℝ}
    (hharm : HarmonicOnNhd u (Metric.ball x R))
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hψsupp : HasCompactSupport (fun w : 𝔼 => φ (‖w - x‖ ^ 2)))
    {r : ℝ} (hr : 0 < r) (hrR : r < R)
    (htsupp : tsupport (fun w : 𝔼 => φ (‖w - x‖ ^ 2)) ⊆ Metric.ball x r) :
    ∫ s in Ioi (0 : ℝ), 2 * s * deriv φ (s ^ 2) * (s ^ (d - 1) * sphereFlux x s u) = 0 := by
  classical
  have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
  set c : ℝ := ((sphereMeasure d).real Set.univ)⁻¹ with hc_def
  have hc0 : c ≠ 0 := inv_ne_zero sphereMeasure_real_univ_ne_zero
  -- continuity of the derivatives of `φ`
  have hd1c : Continuous (deriv φ) := hφ.continuous_deriv (by norm_cast)
  have hd2c : Continuous (deriv (deriv φ)) :=
    ((contDiff_infty_iff_deriv.mp hφ).2).continuous_deriv (by norm_cast)
  -- the four IBP data
  set U : ℝ → ℝ := fun s => s ^ (d - 1) * (2 * s * deriv φ (s ^ 2)) with hU
  set U' : ℝ → ℝ :=
    fun s => s ^ (d - 1) * (4 * s ^ 2 * deriv (deriv φ) (s ^ 2) + 2 * (d : ℝ) * deriv φ (s ^ 2))
    with hU'
  set V : ℝ → ℝ := fun s => sphereAverage x s u with hV
  set V' : ℝ → ℝ := fun s => c * sphereFlux x s u with hV'
  have hUderiv : ∀ s, HasDerivAt U (U' s) s := fun s =>
    hasDerivAt_weighted_radialProfile hφ hd1 s
  have hVderiv : ∀ s, HasDerivAt V (V' s) s := by
    intro s
    have h := hasDerivAt_sphereAverage hu1 x s
    rw [← sphereFlux_def, smul_eq_mul, ← hc_def] at h
    exact h
  -- continuity of the integrand pieces
  have hU'c : Continuous U' := by
    rw [hU']
    exact (continuous_pow _).mul
      (((continuous_const.mul (continuous_pow 2)).mul (hd2c.comp (continuous_pow 2))).add
        (continuous_const.mul (hd1c.comp (continuous_pow 2))))
  have hV'c : Continuous V' := by
    rw [hV']; exact continuous_const.mul (continuous_sphereFlux hu1 x)
  have hUdiff : Differentiable ℝ U := fun s => (hUderiv s).differentiableAt
  have hUc : Continuous U := hUdiff.continuous
  have hVc : Continuous V := continuous_sphereAverage hu.continuous x
  -- vanishing of `deriv φ (s²)` and `deriv (deriv φ) (s²)` for `s > r`
  have hφ'zero : ∀ s : ℝ, r < s → deriv φ (s ^ 2) = 0 := by
    intro s hs
    have hs2 : r ^ 2 < s ^ 2 := by nlinarith only [hs, hr]
    have hev : φ =ᶠ[nhds (s ^ 2)] 0 := by
      have hmem : Ioi (r ^ 2) ∈ nhds (s ^ 2) := Ioi_mem_nhds hs2
      filter_upwards [hmem] with t ht
      exact radialTest_eq_zero_of_ge htsupp (le_of_lt (lt_of_le_of_lt (sq_nonneg r) ht))
        (le_of_lt ht)
    rw [hev.deriv_eq]; simp
  have hφ''zero : ∀ s : ℝ, r < s → deriv (deriv φ) (s ^ 2) = 0 := by
    intro s hs
    have hs2 : r ^ 2 < s ^ 2 := by nlinarith only [hs, hr]
    have hev : deriv φ =ᶠ[nhds (s ^ 2)] 0 := by
      have hmem : Ioi (r ^ 2) ∈ nhds (s ^ 2) := Ioi_mem_nhds hs2
      filter_upwards [hmem] with t ht
      have hev' : φ =ᶠ[nhds t] 0 := by
        have hmem' : Ioi (r ^ 2) ∈ nhds t := Ioi_mem_nhds ht
        filter_upwards [hmem'] with t' ht'
        exact radialTest_eq_zero_of_ge htsupp (le_of_lt (lt_of_le_of_lt (sq_nonneg r) ht'))
          (le_of_lt ht')
      rw [hev'.deriv_eq]; simp
    rw [hev.deriv_eq]; simp
  -- the profiles `U`, `U'` vanish for `|s| > r`
  have hU'zero : ∀ s : ℝ, r < |s| → U' s = 0 := by
    intro s hs
    have h1 : deriv φ (s ^ 2) = 0 := by
      have h := hφ'zero |s| hs; rwa [sq_abs] at h
    have h2 : deriv (deriv φ) (s ^ 2) = 0 := by
      have h := hφ''zero |s| hs; rwa [sq_abs] at h
    simp only [hU']; rw [h1, h2]; ring
  have hUzero : ∀ s : ℝ, r < |s| → U s = 0 := by
    intro s hs
    have h1 : deriv φ (s ^ 2) = 0 := by
      have h := hφ'zero |s| hs; rwa [sq_abs] at h
    simp only [hU]; rw [h1]; ring
  -- the two integrand products vanish for `s > r`
  have hU'Vzero : ∀ s : ℝ, r < s → U' s * V s = 0 := by
    intro s hs
    rw [hU'zero s (by rw [abs_of_pos (lt_trans hr hs)]; exact hs), zero_mul]
  have hUV'zero : ∀ s : ℝ, r < s → U s * V' s = 0 := by
    intro s hs
    rw [hUzero s (by rw [abs_of_pos (lt_trans hr hs)]; exact hs), zero_mul]
  -- compact support (hence integrability) of the two products
  have hU'Vsupp : HasCompactSupport (fun s => U' s * V s) := by
    apply HasCompactSupport.intro (K := Icc (-r) r) (isCompact_Icc)
    intro s hs
    rw [mem_Icc, not_and_or, not_le, not_le] at hs
    have habs : r < |s| := by
      rcases hs with hlt | hlt
      · rw [abs_of_neg (by linarith : s < 0)]; linarith
      · rw [abs_of_pos (by linarith : (0:ℝ) < s)]; exact hlt
    simp only [hU'zero s habs, zero_mul]
  have hUV'supp : HasCompactSupport (fun s => U s * V' s) := by
    apply HasCompactSupport.intro (K := Icc (-r) r) (isCompact_Icc)
    intro s hs
    rw [mem_Icc, not_and_or, not_le, not_le] at hs
    have habs : r < |s| := by
      rcases hs with hlt | hlt
      · rw [abs_of_neg (by linarith : s < 0)]; linarith
      · rw [abs_of_pos (by linarith : (0:ℝ) < s)]; exact hlt
    simp only [hUzero s habs, zero_mul]
  have hU'Vint : Integrable (fun s => U' s * V s) :=
    (hU'c.mul hVc).integrable_of_hasCompactSupport hU'Vsupp
  have hUV'int : Integrable (fun s => U s * V' s) :=
    (hUc.mul hV'c).integrable_of_hasCompactSupport hUV'supp
  -- integration by parts on `[0, R]`
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := U) (v := V) (u' := U') (v' := V') (a := 0) (b := R)
    (fun s _ => hUderiv s) (fun s _ => hVderiv s)
    (hU'c.intervalIntegrable 0 R) (hV'c.intervalIntegrable 0 R)
  -- boundary terms vanish
  have hUR : U R = 0 := hUzero R (by rw [abs_of_pos (lt_trans hr hrR)]; exact hrR)
  have hU0 : U 0 = 0 := by simp only [hU]; ring
  rw [hUR, hU0, zero_mul, zero_mul, sub_zero] at hIBP
  -- the `∫ U' V` term is the radial weak identity, hence `0`
  have hrad : ∫ s in (0 : ℝ)..R, U' s * V s = 0 := by
    rw [intervalIntegral_eq_integral_Ioi_of_zero hr hrR hU'Vint hU'Vzero]
    simp only [hU', hV]
    exact integral_Ioi_weighted_sphereAverage_eq_zero hu hharm hφ hψsupp hr hrR htsupp
  rw [hrad, sub_zero] at hIBP
  -- convert the `∫ U V'` term to the target
  rw [intervalIntegral_eq_integral_Ioi_of_zero hr hrR hUV'int hUV'zero] at hIBP
  -- factor `c` and cancel
  have hpull : (∫ s in Ioi (0 : ℝ), U s * V' s)
      = c * ∫ s in Ioi (0 : ℝ), 2 * s * deriv φ (s ^ 2) * (s ^ (d - 1) * sphereFlux x s u) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun s _ => ?_)
    simp only [hU, hV']; ring
  rw [hpull] at hIBP
  exact (mul_eq_zero.mp hIBP).resolve_left hc0

end

end Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

-- ==== vanishing flux ====
open scoped Real ContDiff Topology Laplacian
open MeasureTheory Metric Set InnerProductSpace

namespace Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

noncomputable section

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- **Flux vanishing for harmonic functions.**  If `u ∈ C²` is harmonic on
`Metric.ball x R`, then the
average radial flux `sphereFlux x ρ u` vanishes for every `ρ ∈ (0, R)`.

Proof by the monotone-cutoff contradiction described in the module docstring: a
decreasing smooth radial
cutoff makes the flux test identity's integrand single-signed, forcing the
radial average of `u` to be
locally constant across `ρ`, which is only consistent with zero flux. -/
theorem sphereFlux_eq_zero_of_harmonic [NeZero d]
    {u : 𝔼 → ℝ} (hu : ContDiff ℝ 2 u) {x : 𝔼} {R : ℝ}
    (hharm : HarmonicOnNhd u (Metric.ball x R))
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρR : ρ < R) :
    sphereFlux x ρ u = 0 := by
  classical
  by_contra hne
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
  have hcont : Continuous (fun s => sphereFlux x s u) := continuous_sphereFlux hu1 x
  set f₀ : ℝ := sphereFlux x ρ u with hf0
  -- an open window around `ρ` inside `(0, R)` where `sphereFlux · u` keeps the sign of `f₀`
  have hsign_open : IsOpen {s : ℝ | 0 < sphereFlux x s u * f₀} :=
    isOpen_lt continuous_const (hcont.mul continuous_const)
  have hρmem : ρ ∈ {s : ℝ | 0 < sphereFlux x s u * f₀} ∩ Ioo 0 R := by
    refine ⟨?_, hρ0, hρR⟩
    simp only [Set.mem_ofPred_eq, ← hf0]
    exact mul_self_pos.mpr hne
  obtain ⟨δ, hδ0, hball⟩ :=
    Metric.isOpen_iff.mp (hsign_open.inter isOpen_Ioo) ρ hρmem
  -- closed window `[a, b] ⊆ ball ρ δ`
  set ε : ℝ := δ / 2 with hε
  have hε0 : 0 < ε := by positivity
  have hεδ : ε < δ := by rw [hε]; linarith only [hδ0]
  set a : ℝ := ρ - ε with ha
  set b : ℝ := ρ + ε with hb
  have hclosed : ∀ s ∈ Icc a b, s ∈ {s : ℝ | 0 < sphereFlux x s u * f₀} ∩ Ioo 0 R := by
    intro s hs
    rw [mem_Icc] at hs
    simp only [ha, hb] at hs
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    refine ⟨by linarith only [hs.1, hεδ], by linarith only [hs.2, hεδ]⟩
  have hsamesign : ∀ s ∈ Icc a b, 0 < sphereFlux x s u * f₀ := fun s hs => (hclosed s hs).1
  have hab : a < b := by simp only [ha, hb]; linarith only [hε0]
  have ha0 : 0 < a := (hclosed a (left_mem_Icc.2 (le_of_lt hab))).2.1
  have hbR : b < R := (hclosed b (right_mem_Icc.2 (le_of_lt hab))).2.2
  have hb0 : 0 < b := lt_trans ha0 hab
  -- the cutoff profile `φ`
  set α : ℝ := a ^ 2 with hαdef
  set β : ℝ := b ^ 2 with hβdef
  have hβα : 0 < β - α := by
    simp only [hαdef, hβdef]; nlinarith only [ha0, hab]
  set L : ℝ → ℝ := fun t => (t - α) / (β - α) with hLdef
  set φ : ℝ → ℝ := fun t => 1 - Real.smoothTransition (L t) with hφdef
  -- smoothness
  have hL_cd : ContDiff ℝ ∞ L := (contDiff_id.sub contDiff_const).div_const _
  have hφ_inf : ContDiff ℝ ∞ φ :=
    contDiff_const.sub (Real.smoothTransition.contDiff.comp hL_cd)
  -- `L` monotone
  have hL_mono : Monotone L := by
    intro s t hst
    simp only [hLdef]
    gcongr
  -- `φ` antitone, hence `φ' ≤ 0`
  have hφ_anti : Antitone φ := by
    intro s t hst
    simp only [hφdef]
    have hmono := Real.smoothTransition.monotone (hL_mono hst)
    linarith only [hmono]
  have hφ_deriv_np : ∀ t, deriv φ t ≤ 0 := fun t => hφ_anti.deriv_nonpos
  -- `φ ≡ 1` for `t ≤ α`, `φ ≡ 0` for `t ≥ β`
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
  -- `φ' = 0` off `(α, β)`
  have hφ_deriv_out : ∀ t, t < α ∨ β < t → deriv φ t = 0 := by
    intro t ht
    rcases ht with ht | ht
    · have hev : φ =ᶠ[𝓝 t] fun _ => 1 := by
        filter_upwards [Iio_mem_nhds ht] with s hs
        exact hφ_one s (le_of_lt hs)
      rw [hev.deriv_eq]; simp
    · have hev : φ =ᶠ[𝓝 t] fun _ => 0 := by
        filter_upwards [Ioi_mem_nhds ht] with s hs
        exact hφ_zero s (le_of_lt hs)
      rw [hev.deriv_eq]; simp
  -- the radial test and its support
  set ψ : 𝔼 → ℝ := fun w => φ (‖w - x‖ ^ 2) with hψdef
  set r' : ℝ := (b + R) / 2 with hr'def
  have hr'0 : 0 < r' := by rw [hr'def]; linarith only [hb0, hbR]
  have hr'R : r' < R := by rw [hr'def]; linarith only [hbR]
  have hbr' : b < r' := by rw [hr'def]; linarith only [hbR]
  have hsupp_sub : Function.support ψ ⊆ closedBall x b := by
    intro w hw
    by_contra hnot
    rw [mem_closedBall, dist_eq_norm, not_le] at hnot
    exact (Function.mem_support.mp hw)
      (hφ_zero _ (by
        simp only [hβdef]; nlinarith only [hnot, hb0, norm_nonneg (w - x)]))
  have htsupp : tsupport ψ ⊆ Metric.ball x r' :=
    (closure_minimal hsupp_sub isClosed_closedBall).trans (closedBall_subset_ball hbr')
  have hψsupp : HasCompactSupport ψ :=
    (isCompact_closedBall x b).of_isClosed_subset (isClosed_tsupport ψ)
      (closure_minimal hsupp_sub isClosed_closedBall)
  -- the flux test identity
  have hIBP := integral_Ioi_test_sphereFlux_eq_zero hu hharm hφ_inf hψsupp hr'0 hr'R htsupp
  set I' : ℝ → ℝ := fun s => 2 * s * deriv φ (s ^ 2) * (s ^ (d - 1) * sphereFlux x s u) with hI'def
  -- `G = -f₀ · I'` is nonnegative on `(0, ∞)` with integral `0`
  set G : ℝ → ℝ := fun s => -f₀ * I' s with hGdef
  have hGint0 : ∫ s in Ioi (0 : ℝ), G s = 0 := by
    simp only [hGdef]
    rw [integral_const_mul, hIBP, mul_zero]
  have hd1c : Continuous (deriv φ) := hφ_inf.continuous_deriv (by norm_cast)
  have hI'cont : Continuous I' := by
    simp only [hI'def]
    exact (((continuous_const.mul continuous_id).mul (hd1c.comp (continuous_pow 2))).mul
      ((continuous_pow _).mul hcont))
  have hGcont : Continuous G := by simp only [hGdef]; exact continuous_const.mul hI'cont
  -- pointwise nonnegativity
  have hGnn : ∀ s, 0 < s → 0 ≤ G s := by
    intro s hs
    by_cases hd : deriv φ (s ^ 2) = 0
    · have hz : G s = 0 := by simp only [hGdef, hI'def, hd]; ring
      exact le_of_eq hz.symm
    · -- `deriv φ (s²) ≠ 0 ⟹ s ∈ [a, b]`
      have hmemcc : s ∈ Icc a b := by
        rw [mem_Icc]
        by_contra hcon
        rw [not_and_or, not_le, not_le] at hcon
        refine hd (hφ_deriv_out (s ^ 2) ?_)
        rcases hcon with hlt | hlt
        · left; simp only [hαdef]; nlinarith only [hlt, hs, ha0]
        · right; simp only [hβdef]; nlinarith only [hlt, hb0]
      have hsf : 0 < sphereFlux x s u * f₀ := hsamesign s hmemcc
      have hsf' : 0 < f₀ * sphereFlux x s u := by rw [mul_comm]; exact hsf
      have hEq : G s = (2 * s * s ^ (d - 1)) * (-(deriv φ (s ^ 2))) * (f₀ * sphereFlux x s u) := by
        simp only [hGdef, hI'def]; ring
      rw [hEq]
      have h2s : (0 : ℝ) < 2 * s * s ^ (d - 1) := by
        have hpow := pow_pos hs (d - 1)
        exact mul_pos (by linarith only [hs]) hpow
      exact mul_nonneg (mul_nonneg (le_of_lt h2s) (by linarith only [hφ_deriv_np (s ^ 2)]))
        (le_of_lt hsf')
  -- integrability of `G` (compact support)
  have hGsupp : HasCompactSupport G := by
    apply HasCompactSupport.intro (K := Icc (-b) b) isCompact_Icc
    intro s hs
    rw [mem_Icc, not_and_or, not_le, not_le] at hs
    have hout : β < s ^ 2 := by
      rcases hs with hlt | hlt
      · simp only [hβdef]; nlinarith only [hlt, hb0]
      · simp only [hβdef]; nlinarith only [hlt, hb0]
    simp only [hGdef, hI'def, hφ_deriv_out (s ^ 2) (Or.inr hout)]; ring
  have hGint : Integrable G := hGcont.integrable_of_hasCompactSupport hGsupp
  -- `G = 0` a.e. on `(0, ∞)`, hence `I' = 0` there
  have hGae : G =ᵐ[volume.restrict (Ioi 0)] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae
      ((ae_restrict_iff' measurableSet_Ioi).mpr
        (Filter.Eventually.of_forall fun s hs => hGnn s hs)) hGint.integrableOn).mp hGint0
  have hInull : volume ({s : ℝ | I' s ≠ 0} ∩ Ioi 0) = 0 := by
    have hIae : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Ioi 0 → I' s = 0 := by
      filter_upwards [(ae_restrict_iff' (μ := volume) measurableSet_Ioi).mp hGae]
        with s hsG hsmem
      have hG0 : -f₀ * I' s = 0 := hsG hsmem
      exact (mul_eq_zero.mp hG0).resolve_left (neg_ne_zero.mpr hne)
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
  -- `deriv (fun s => φ (s²)) = 0` on `[a, b]`, so it is constant there
  set p : ℝ → ℝ := fun s => φ (s ^ 2) with hpdef
  have hp_diff : Differentiable ℝ p :=
    (hφ_inf.comp (contDiff_id.pow 2)).differentiable (by norm_cast)
  have hp_derivval : ∀ s, deriv p s = 2 * s * deriv φ (s ^ 2) := by
    intro s; simp only [hpdef]; exact deriv_radialProfile hφ_inf s
  have hp_deriv0 : ∀ s ∈ Icc a b, deriv p s = 0 := by
    intro s hs
    have hs0 : 0 < s := lt_of_lt_of_le ha0 hs.1
    have hI's : I' s = 0 := hI0 s hs0
    have hsf : 0 < sphereFlux x s u * f₀ := hsamesign s hs
    have hsfne : sphereFlux x s u ≠ 0 := by
      intro h0; rw [h0, zero_mul] at hsf; exact lt_irrefl 0 hsf
    have hdφ : deriv φ (s ^ 2) = 0 := by
      have hfac : 2 * s * deriv φ (s ^ 2) * (s ^ (d - 1) * sphereFlux x s u) = 0 := hI's
      have h1 : s ^ (d - 1) * sphereFlux x s u ≠ 0 := mul_ne_zero (by positivity) hsfne
      have h2 : 2 * s ≠ 0 := by positivity
      rcases mul_eq_zero.mp hfac with h | h
      · exact (mul_eq_zero.mp h).resolve_left h2
      · exact absurd h h1
    rw [hp_derivval, hdφ, mul_zero]
  have hp_const := constant_of_has_deriv_right_zero
    (f := p) (a := a) (b := b) hp_diff.continuous.continuousOn
    (fun s hs => by
      have hda : HasDerivAt p 0 s := by
        have h := (hp_diff s).hasDerivAt
        rwa [hp_deriv0 s (Ico_subset_Icc_self hs)] at h
      exact hda.hasDerivWithinAt)
  have hpb : p b = p a := hp_const b (right_mem_Icc.2 (le_of_lt hab))
  have hpbz : p b = 0 := by simp only [hpdef]; exact hφ_zero (b ^ 2) (le_of_eq hβdef)
  have hpao : p a = 1 := by simp only [hpdef]; exact hφ_one (a ^ 2) (le_of_eq hαdef.symm)
  have : (0 : ℝ) = 1 := by rw [← hpbz, hpb, hpao]
  exact absurd this (by norm_num)

/-- **Spherical mean value property for harmonic functions.**  If `u ∈ C²` is harmonic on
`Metric.ball x R`, then its spherical average about `x` equals the center value at every radius in
`[0, R)`:  `sphereAverage x r u = u x`. -/
theorem sphereAverage_eq_center_of_harmonic [NeZero d]
    {u : 𝔼 → ℝ} (hu : ContDiff ℝ 2 u) {x : 𝔼} {R : ℝ}
    (hharm : HarmonicOnNhd u (Metric.ball x R)) :
    ∀ r ∈ Ico (0 : ℝ) R, sphereAverage x r u = u x :=
  sphereAverage_eq_center_of_flux_zero (hu.of_le (by norm_num)) x
    (fun r hr => sphereFlux_eq_zero_of_harmonic hu hharm hr.1 hr.2)

end

end Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

