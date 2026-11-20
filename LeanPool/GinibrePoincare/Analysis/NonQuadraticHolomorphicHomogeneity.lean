/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/NonQuadraticHolomorphicHomogeneity.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Analytic.CPolynomial
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Topology.MetricSpace.ProperSpace

/-! # Potential-independent holomorphic phase homogeneity -/

@[expose] public section
open Filter Set
open scoped Topology
namespace GinibrePoincare
noncomputable section

private def unitCircleRational (t : ℝ) : ℂ :=
  (1 + Complex.I * (t : ℂ)) / (1 - Complex.I * (t : ℂ))

private theorem unitCircleRational_denom_ne (t : ℝ) : (1 - Complex.I * (t : ℂ)) ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this

private theorem unitCircleRational_norm (t : ℝ) : ‖unitCircleRational t‖ = 1 := by
  have hn : ‖(1 + Complex.I * (t : ℂ))‖ = ‖(1 - Complex.I * (t : ℂ))‖ := by
    have hs : ‖(1 + Complex.I * (t : ℂ))‖ ^ 2 = ‖(1 - Complex.I * (t : ℂ))‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.sq_norm]
      simp [Complex.normSq, Complex.mul_re, Complex.mul_im]
    nlinarith [norm_nonneg (1 + Complex.I * (t : ℂ)), norm_nonneg (1 - Complex.I * (t : ℂ))]
  rw [unitCircleRational, norm_div, hn, div_self]
  exact norm_ne_zero_iff.mpr (unitCircleRational_denom_ne t)

private theorem unitCircleRational_ne_one {t : ℝ} (ht : t ≠ 0) : unitCircleRational t ≠ 1 := by
  intro h
  have he := (div_eq_one_iff_eq (unitCircleRational_denom_ne t)).mp h
  have hi := congrArg Complex.im he
  simp at hi
  exact ht (by linarith)

private theorem unitCircleRational_tendsto : Tendsto unitCircleRational (𝓝 0) (𝓝 1) := by
  have h : ContinuousAt unitCircleRational 0 :=
    (continuous_const.add (continuous_const.mul Complex.continuous_ofReal)).continuousAt.div
      (continuous_const.sub (continuous_const.mul Complex.continuous_ofReal)).continuousAt
      (unitCircleRational_denom_ne 0)
  simpa [unitCircleRational] using h.tendsto

/-- The unit circle has an explicit nontrivial sequence converging to one. -/
theorem frequently_unit_norm_near_one : ∃ᶠ u : ℂ in 𝓝[≠] 1, ‖u‖ = 1 := by
  let u : ℕ → ℂ := fun k => unitCircleRational (1 / ((k : ℝ) + 1))
  have ht : Tendsto u atTop (𝓝 1) := unitCircleRational_tendsto.comp
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hn : ∀ k, u k ≠ 1 := fun k => unitCircleRational_ne_one (by positivity)
  have hw : Tendsto u atTop (𝓝[≠] 1) := tendsto_nhdsWithin_iff.mpr
    ⟨ht, Eventually.of_forall hn⟩
  exact hw.frequently (Frequently.of_forall (fun k => unitCircleRational_norm _))

/-- An entire scalar function agreeing with a monomial on the unit circle
is exactly that monomial everywhere, independently of any weighted norm. -/
theorem entire_eq_monomial_of_unit_circle (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (d : ℕ) (c : ℂ) (hphase : ∀ u : ℂ, ‖u‖ = 1 → f u = u ^ d * c) :
    ∀ z : ℂ, f z = z ^ d * c := by
  have hg : Differentiable ℂ (fun z : ℂ => z ^ d * c) := differentiable_id.pow d |>.mul_const c
  have ha : AnalyticOnNhd ℂ f univ := fun z _ => hf.analyticAt z
  have hb : AnalyticOnNhd ℂ (fun z : ℂ => z ^ d * c) univ := fun z _ => hg.analyticAt z
  have he := ha.eqOn_of_preconnected_of_frequently_eq hb
    isPreconnected_univ (mem_univ (1 : ℂ))
    (frequently_unit_norm_near_one.mono (fun u hu => hphase u hu))
  exact fun z => he (mem_univ z)
/-- Unit-phase covariance of a genuinely entire function forces exact
homogeneity under every complex scalar, including zero. -/
theorem entire_phase_implies_complex_homogeneity
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (F : E → ℂ) (hF : Differentiable ℂ F) (d : ℕ)
    (hp : ∀ (u : ℂ) (z : E), ‖u‖ = 1 → F (u • z) = u ^ d * F z) :
    ∀ (u : ℂ) (z : E), F (u • z) = u ^ d * F z := by
  intro u z
  exact entire_eq_monomial_of_unit_circle (fun a : ℂ => F (a • z))
    (hF.comp (differentiable_id.smul_const z)) d (F z) (fun a ha => hp a z ha) u

private def monomialFormalSeries (d : ℕ) (c : ℂ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  fun k => if k = d then c • ContinuousMultilinearMap.mkPiAlgebraFin ℂ k ℂ else 0

private theorem monomial_hasFPowerSeriesAt (d : ℕ) (c : ℂ) :
    HasFPowerSeriesAt (fun z : ℂ => z ^ d * c) (monomialFormalSeries d c) 0 := by
  refine ⟨⊤, (HasFiniteFPowerSeriesOnBall.mk' (n := d + 1) ?_ ENNReal.zero_lt_top
      ?_).toHasFPowerSeriesOnBall⟩
  · intro k hk
    simp only [monomialFormalSeries, ite_eq_right (by omega : k ≠ d)]
  · intro z hz
    rw [Finset.sum_eq_single d]
    · simp [monomialFormalSeries, ContinuousMultilinearMap.mkPiAlgebraFin_apply, mul_comm]
    · intro k hk hkd
      simp [monomialFormalSeries, hkd]
    · intro hd
      exact False.elim (hd (Finset.mem_range.mpr (Nat.lt_succ_self d)))

/-- An entire phase eigenfunction analytic at the origin is exactly the
diagonal of its degree-d continuous multilinear Taylor coefficient. -/
theorem entire_phase_eq_homogeneous_taylor
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (F : E → ℂ) (hF : Differentiable ℂ F) (d : ℕ)
    (p : FormalMultilinearSeries ℂ E ℂ) (hseries : HasFPowerSeriesAt F p 0)
    (hp : ∀ (u : ℂ) (z : E), ‖u‖ = 1 → F (u • z) = u ^ d * F z) :
    ∀ z : E, F z = p d (fun _ => z) := by
  intro z
  let L : ℂ →L[ℂ] E := (ContinuousLinearMap.id ℂ ℂ).smulRight z
  have hc : HasFPowerSeriesAt (F ∘ L) (p.compContinuousLinearMap L) 0 := by
    apply HasFPowerSeriesAt.compContinuousLinearMap
    simpa using hseries
  have he : F ∘ L = fun a : ℂ => a ^ d * F z := by
    funext a
    exact entire_phase_implies_complex_homogeneity F hF d hp a z
  rw [he] at hc
  have hs := hc.eq_formalMultilinearSeries (monomial_hasFPowerSeriesAt d (F z))
  have hd := congrArg (fun q : FormalMultilinearSeries ℂ ℂ ℂ => q d (fun _ => 1)) hs
  simpa [FormalMultilinearSeries.compContinuousLinearMap,
      ContinuousMultilinearMap.compContinuousLinearMap_apply,
    L, monomialFormalSeries, ContinuousMultilinearMap.mkPiAlgebraFin_apply] using hd.symm

/-- The resulting finite homogeneous representation is independent of the
potential or any Gaussian basis. -/
theorem entire_phase_has_homogeneous_multilinear_representation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (F : E → ℂ) (hF : Differentiable ℂ F) (hA : AnalyticAt ℂ F 0) (d : ℕ)
    (hp : ∀ (u : ℂ) (z : E), ‖u‖ = 1 → F (u • z) = u ^ d * F z) :
    ∃ P : ContinuousMultilinearMap ℂ (fun _ : Fin d => E) ℂ,
      ∀ z : E, F z = P (fun _ => z) := by
  obtain ⟨p, hseries⟩ := hA
  exact ⟨p d, entire_phase_eq_homogeneous_taylor F hF d p hseries hp⟩

/-- Continuity and scalar homogeneity give a genuine global polynomial
growth bound in every proper complex normed space. -/
theorem continuous_homogeneous_polynomial_growth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [ProperSpace E]
    (F : E → ℂ) (hF : Continuous F) (d : ℕ)
    (hh : ∀ (u : ℂ) (z : E), F (u • z) = u ^ d * F z) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z, ‖F z‖ ≤ C * (1 + ‖z‖) ^ d := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : E) 1).exists_bound_of_continuousOn hF.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun z => ?_⟩
  let r : ℝ := 1 + ‖z‖
  have hr : 0 < r := by dsimp [r]; positivity
  let w : E := ((r : ℂ)⁻¹) • z
  have hw : w ∈ Metric.closedBall (0 : E) 1 := by
    rw [Metric.mem_closedBall, dist_zero_right]
    change ‖((r : ℂ)⁻¹) • z‖ ≤ 1
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    rw [inv_mul_le_iff₀ hr]
    dsimp [r]
    linarith
  have he : (r : ℂ) • w = z := by
    change (r : ℂ) • ((r : ℂ)⁻¹ • z) = z
    rw [smul_smul, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hr.ne'), one_smul]
  have hb : ‖F w‖ ≤ max C 0 := (hC w hw).trans (le_max_left _ _)
  rw [← he, hh, norm_mul, norm_pow]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  calc
    r ^ d * ‖F w‖ ≤ r ^ d * max C 0 := mul_le_mul_of_nonneg_left hb (pow_nonneg hr.le _)
    _ = max C 0 * (1 + ‖(r : ℂ) • w‖) ^ d := by rw [he]; exact mul_comm _ _

/-- Entire scalar functions cannot carry a strictly negative unit-phase
character. This is an analytic assertion independent of the measure. -/
theorem entire_negative_phase_eq_zero (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (k : ℕ) (hk : 0 < k)
    (hp : ∀ a : ℂ, ‖a‖ = 1 → f a = a ^ (-(k : ℤ)) * f 1) :
    ∀ z, f z = 0 := by
  have hg : Differentiable ℂ (fun z : ℂ => z ^ k * f z) := (differentiable_id.pow k).mul hf
  have hu (a : ℂ) (ha : ‖a‖ = 1) : a ^ k * f a = a ^ 0 * f 1 := by
    have hn : a ≠ 0 := by intro h; simp [h] at ha
    rw [hp a ha, ← mul_assoc, zpow_neg, zpow_natCast, mul_inv_cancel₀ (pow_ne_zero _ hn), one_mul,
        pow_zero, one_mul]
  have hgconst := entire_eq_monomial_of_unit_circle _ hg 0 (f 1) hu
  have hzero : f 1 = 0 := by
    have h := hgconst 0
    simpa [zero_pow hk.ne'] using h.symm
  have hfun := entire_eq_monomial_of_unit_circle f hf 0 0 (fun a ha => by rw [hp a ha, hzero]; simp)
  intro z
  simpa using hfun z

/-- A genuinely entire function on any complex normed space has no
strictly negative scalar phase, without any multivariate analytic API. -/
theorem entire_negative_phase_function_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (F : E → ℂ) (hF : Differentiable ℂ F) (k : ℕ) (hk : 0 < k)
    (hp : ∀ (a : ℂ) (z : E), ‖a‖ = 1 → F (a • z) = a ^ (-(k : ℤ)) * F z) :
    ∀ z, F z = 0 := by
  intro z
  have h := entire_negative_phase_eq_zero (fun a : ℂ => F (a • z))
    (hF.comp (differentiable_id.smul_const z)) k hk (fun a ha => by simpa using hp a z ha) 1
  simpa using h

end
end GinibrePoincare
