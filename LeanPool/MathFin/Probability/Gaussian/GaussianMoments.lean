/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho, Yang Ye
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Init
public import TauCeti.Probability.Distributions.Gaussian.Moments
public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
public import Mathlib.Topology.UniformSpace.Uniformizable

/-!
# Gaussian moments

Small, shared moment facts for real Gaussians used across the Brownian-motion
foundations (`BrownianMartingale`, `BrownianQuadraticVariation`, the L² quadratic
variation). Kept in one place so each identity is proved exactly once.

The fourth moment reuses Degenne's `(2n)`-th central-moment formula
(`ProbabilityTheory.centralMoment_two_mul_gaussianReal`) rather than re-deriving the
Gaussian integral — coherence with the upstream `brownian-motion` package.

## Main results

* `integral_sq_gaussianReal`, `integral_pow3_gaussianReal`, `integral_pow4_gaussianReal`,
  `integral_pow6_gaussianReal`: the second, third, fourth and sixth moments of `N(0, v)` are
  `v`, `0`, `3 v²` and `15 v³`.
* `integral_sq_sub_var_sq_gaussianReal`, `integral_sq_sub_var_gaussianReal`: for `N(0, v)`,
  `∫ (x² − v)² = 2 v²` and `∫ (x² − v) = 0`.
* `integral_sq_of_hasLaw_gaussianReal`: `X ~ N(m, v)` gives `𝔼[X²] = m² + v`.
* `hasLaw_increment`: for `s ≤ t`, the increment `B t − B s` of a pre-Brownian motion has law
  `N(0, t − s)`.
* `hasLaw_sum_range_gaussianReal`: a sum of `n` independent `N(m, v)` variables has law
  `N(n m, n v)`.
* `hasLaw_sub_div_of_gaussianReal`: if `X ~ N(μ, v)` with `v = s²`, `s > 0`, then
  `(X − μ)/s ~ N(0, 1)`.

## Tags

Gaussian moments, fourth moment, central moments, normal distribution, variance, MSC 60E05,
MSC 60J65
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- Second moment of a centered real Gaussian: `∫ x, x² ∂(gaussianReal 0 v) = v`.
For a mean-zero law the second moment is the variance (`variance_id_gaussianReal`). -/
lemma integral_sq_gaussianReal (v : ℝ≥0) :
    ∫ x, x ^ 2 ∂(gaussianReal 0 v) = (v : ℝ) := by
  have h_var : variance id (gaussianReal 0 v) = (v : ℝ) := variance_id_gaussianReal
  have h_mean : ∫ x, x ∂(gaussianReal 0 v) = 0 := integral_id_gaussianReal
  rw [variance_of_integral_eq_zero aemeasurable_id h_mean] at h_var
  exact h_var

/-- Third moment of a centered real Gaussian (odd moment, by density symmetry). -/
lemma integral_pow3_gaussianReal (v : ℝ≥0) :
    ∫ x, x ^ 3 ∂(gaussianReal 0 v) = 0 := by
  rcases eq_or_ne v 0 with rfl | hv
  · rw [gaussianReal_zero_var]
    simp
  · rw [integral_gaussianReal_eq_integral_smul hv]
    simp only [smul_eq_mul]
    have hmap : Measure.map (fun x : ℝ ↦ -x) (volume : Measure ℝ) = volume :=
      (Measure.measurePreserving_neg (μ := (volume : Measure ℝ))).map_eq
    have hpdfneg : ∀ x : ℝ, gaussianPDFReal 0 v (-x) = gaussianPDFReal 0 v x := by
      intro x
      simp only [gaussianPDFReal, sub_zero, neg_sq]
    have hsub : ∫ y, gaussianPDFReal 0 v y * y ^ 3 ∂volume
        = ∫ x, gaussianPDFReal 0 v (-x) * (-x) ^ 3 ∂volume := by
      have h1 : ∫ y, gaussianPDFReal 0 v y * y ^ 3 ∂volume
          = ∫ y, gaussianPDFReal 0 v y * y ^ 3
              ∂(Measure.map (fun x : ℝ ↦ -x) (volume : Measure ℝ)) := by
        rw [hmap]
      rw [h1]
      exact integral_map_equiv (MeasurableEquiv.neg (G := ℝ))
        (fun y : ℝ ↦ gaussianPDFReal 0 v y * y ^ 3)
    rw [hsub]
    have hcongr : ∫ x, gaussianPDFReal 0 v (-x) * (-x) ^ 3 ∂volume
        = -∫ x, gaussianPDFReal 0 v x * x ^ 3 ∂volume := by
      have hpt : ∀ x : ℝ, gaussianPDFReal 0 v (-x) * (-x) ^ 3
          = -(gaussianPDFReal 0 v x * x ^ 3) := by
        intro x
        rw [hpdfneg x]
        ring
      rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_neg]
    rw [hcongr]
    linarith

/-- Fourth moment of a centered real Gaussian: `∫ x, x⁴ ∂(gaussianReal 0 v) = 3 v²`
(the kurtosis identity `E[X⁴] = 3·Var²`, the source of the `2(Δt)²` variance of squared
Brownian increments). Via the `(2n)`-th central-moment formula
`centralMoment_two_mul_gaussianReal` at `n = 2` (`(2·2−1)!! = 3!! = 3`). -/
lemma integral_pow4_gaussianReal (v : ℝ≥0) :
    ∫ x, x ^ 4 ∂(gaussianReal 0 v) = 3 * (v : ℝ) ^ 2 := by
  simpa using TauCeti.Probability.integral_sub_pow_four_gaussianReal 0 v

/-- Sixth moment of a centered real Gaussian: `∫ x, x⁶ ∂(gaussianReal 0 v) = 15 v³`
(`E[X⁶] = 15·Var³`). It controls the `L²` size of the Itô–Taylor remainder
(`E[(ΔB)⁶] = 15(Δt)³`, so `‖|ΔB|³‖_{L²} = √15·(Δt)^{3/2}` sums to `O(n^{-1/2})`).
Via the `(2n)`-th central-moment formula `centralMoment_two_mul_gaussianReal` at
`n = 3` (`(2·3−1)!! = 5!! = 15`). -/
lemma integral_pow6_gaussianReal (v : ℝ≥0) :
    ∫ x, x ^ 6 ∂(gaussianReal 0 v) = 15 * (v : ℝ) ^ 3 := by
  simpa [Nat.doubleFactorial, mul_comm] using
    TauCeti.Probability.integral_sub_pow_two_mul_gaussianReal 0 v 3

/-- **Mean-square fluctuation of a squared centered Gaussian**: `∫ (x² − v)² ∂N(0,v) = 2v²`,
i.e. `Var(X²) = 2·Var(X)²` for `X ~ N(0,v)`. This is the kurtosis `E[X⁴] = 3v²` minus
`(E[X²])² = v²`. It is exactly the per-interval term `E[((ΔB)² − Δt)²] = 2(Δt)²` whose sum
gives the `2t²/n` rate of the L² quadratic variation. -/
lemma integral_sq_sub_var_sq_gaussianReal (v : ℝ≥0) :
    ∫ x, (x ^ 2 - (v : ℝ)) ^ 2 ∂(gaussianReal 0 v) = 2 * (v : ℝ) ^ 2 := by
  have hint2 : Integrable (fun x : ℝ ↦ x ^ 2) (gaussianReal 0 v) :=
    (memLp_id_gaussianReal (μ := 0) (v := v) 2).integrable_sq
  have hint4 : Integrable (fun x : ℝ ↦ x ^ 4) (gaussianReal 0 v) := by
    have h := (memLp_id_gaussianReal (μ := 0) (v := v) 4).integrable_norm_pow (p := 4) (by norm_num)
    simp only [id_eq, Real.norm_eq_abs] at h
    have hfe : (fun x : ℝ ↦ |x| ^ 4) = fun x : ℝ ↦ x ^ 4 :=
      funext fun x ↦ by rw [pow_abs, abs_of_nonneg (by positivity)]
    rwa [hfe] at h
  have hcm2 : Integrable (fun x : ℝ ↦ 2 * (v : ℝ) * x ^ 2) (gaussianReal 0 v) :=
    hint2.const_mul (2 * (v : ℝ))
  have hdiff : Integrable (fun a : ℝ ↦ a ^ 4 - 2 * (v : ℝ) * a ^ 2) (gaussianReal 0 v) :=
    hint4.sub hcm2
  have hexpand : ∀ x : ℝ, (x ^ 2 - (v : ℝ)) ^ 2 = x ^ 4 - 2 * (v : ℝ) * x ^ 2 + (v : ℝ) ^ 2 :=
    fun x ↦ by ring
  have huniv : (gaussianReal 0 v).real Set.univ = 1 := by
    rw [measureReal_def, measure_univ, ENNReal.toReal_one]
  rw [integral_congr_ae (Filter.Eventually.of_forall hexpand),
      integral_add hdiff (integrable_const _),
      integral_sub hint4 hcm2,
      integral_pow4_gaussianReal, integral_const_mul, integral_sq_gaussianReal, integral_const,
      huniv]
  simp only [smul_eq_mul]
  ring

/-- **A centered squared Gaussian has mean zero**: `∫ (x² − v) ∂N(0,v) = 0`, i.e.
`E[X² − Var] = 0` for `X ~ N(0,v)`. (`E[X²] = v`.) -/
lemma integral_sq_sub_var_gaussianReal (v : ℝ≥0) :
    ∫ x, (x ^ 2 - (v : ℝ)) ∂(gaussianReal 0 v) = 0 := by
  have hint2 : Integrable (fun x : ℝ ↦ x ^ 2) (gaussianReal 0 v) :=
    (memLp_id_gaussianReal (μ := 0) (v := v) 2).integrable_sq
  have huniv : (gaussianReal 0 v).real Set.univ = 1 := by
    rw [measureReal_def, measure_univ, ENNReal.toReal_one]
  rw [integral_sub hint2 (integrable_const _), integral_sq_gaussianReal, integral_const, huniv,
      one_smul, sub_self]

/-- The second moment of a Gaussian random variable: `X ~ N(m, v)` gives
`𝔼[X²] = m² + v` (`variance_eq_sub` on the law). -/
theorem integral_sq_of_hasLaw_gaussianReal {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} {X : Ω → ℝ} {m : ℝ} {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal m v) μ) : ∫ ω, X ω ^ 2 ∂μ = m ^ 2 + v := by
  have h := variance_eq_sub (memLp_id_gaussianReal' (μ := m) (v := v) 2 (by simp))
  simp only [variance_id_gaussianReal, Pi.pow_apply, id] at h
  rw [integral_id_gaussianReal] at h
  have hc := hX.integral_comp (f := fun x : ℝ ↦ x ^ 2) (by fun_prop)
  simp only [Function.comp_def] at hc
  rw [hc]
  linarith

/-! ### Brownian increments -/

/-- For `s ≤ t : ℝ≥0`, the increment `B t − B s` of a pre-Brownian motion has law
`gaussianReal 0 (t - s)`. Degenne's `hasLaw_sub` states the variance as `nndist`; this is the
same fact with the `ℝ≥0` subtraction the time-indexed towers actually carry, which is the only
reason the conversion keeps reappearing. -/
lemma hasLaw_increment {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) {s t : ℝ≥0} (hst : s ≤ t) :
    HasLaw (fun ω ↦ B t ω - B s ω) (gaussianReal 0 (t - s)) μ := by
  have hL := hB.hasLaw_sub t s
  have hv : nndist (t : ℝ) (s : ℝ) = (t - s : ℝ≥0) := by
    apply NNReal.coe_injective
    rw [coe_nndist, Real.dist_eq, NNReal.coe_sub hst,
      abs_of_nonneg (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hst))]
  rw [← hv]; exact hL

/-- A pre-Brownian increment `B t − B s` lies in `L²(μ)`, for any two times. -/
lemma memLp_increment {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (s t : ℝ≥0) :
    MemLp (fun ω ↦ B t ω - B s ω) 2 μ :=
  hB.isGaussianProcess.hasGaussianLaw_sub.memLp_two

/-! ### Sums and standardization of Gaussian variables -/

/-- A sum of `n` independent `N(m, v)` variables is `N(n·m, n·v)`. -/
theorem hasLaw_sum_range_gaussianReal {Ω : Type*} {mΩ : MeasurableSpace Ω} {Q : Measure Ω}
    {J : ℕ → Ω → ℝ} {m : ℝ} {v : ℝ≥0}
    (hJ : ∀ i, HasLaw (J i) (gaussianReal m v) Q) (hind : iIndepFun J Q) (n : ℕ) :
    HasLaw (∑ i ∈ Finset.range n, J i) (gaussianReal (n * m) (n * v)) Q := by
  have := (hJ 0).isProbabilityMeasure
  induction n with
  | zero =>
    simp only [Finset.sum_range_zero, Nat.cast_zero, zero_mul, gaussianReal_zero_var]
    exact hasLaw_dirac_of_ae_eq (ae_of_all _ fun _ ↦ rfl)
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h := (hind.indepFun_sum_range_succ₀ (fun i ↦ (hJ i).aemeasurable) n).hasLaw_add ih (hJ n)
    rw [gaussianReal_conv_gaussianReal] at h
    convert h using 2 <;> push_cast <;> ring

/-- Standardizing a Gaussian: if `X ∼ N(μ, s²)` with `s > 0`, then `(X − μ)/s ∼ N(0, 1)`. -/
theorem hasLaw_sub_div_of_gaussianReal {Ω : Type*} {mΩ : MeasurableSpace Ω} {Q : Measure Ω}
    {X : Ω → ℝ} {μ s : ℝ} {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal μ v) Q) (hs : 0 < s) (hv : (v : ℝ) = s ^ 2) :
    HasLaw (fun ω ↦ (X ω - μ) / s) (gaussianReal 0 1) Q := by
  have h := gaussianReal_const_mul (gaussianReal_sub_const hX μ) s⁻¹
  have hparam : gaussianReal (s⁻¹ * (μ - μ)) (.mk (s⁻¹ ^ 2) (sq_nonneg _) * v)
      = gaussianReal 0 1 := by
    congr 1
    · rw [sub_self, mul_zero]
    · ext
      rw [NNReal.coe_mul, NNReal.coe_mk, hv, NNReal.coe_one, inv_pow,
        inv_mul_cancel₀ (pow_pos hs 2).ne']
  rw [hparam] at h
  simpa only [div_eq_inv_mul] using h

end MathFin
