/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# A measure with vanishing distributional derivatives is a multiple of Lebesgue measure

Let `ν` be a finite measure on a finite-dimensional real normed space `E` with an additive Haar
measure `μ`, and suppose `∫ dψ(v) dν = 0` for every smooth compactly supported `ψ` with support in
the ball `B(x₀, 3r)` and every direction `v`.  Then there is a constant `c` with
`∫ ψ dν = c ∫ ψ dμ` for every smooth compactly supported `ψ` with support in `B(x₀, r)`
(`exists_integral_eq_const_mul`).

Proof.  (1) Translation invariance (`integral_comp_sub_eq`): `s ↦ ∫ ψ(x - s v) dν` has derivative
`-∫ dψ(x - s v)(v) dν = 0` (differentiation under the integral sign).  (2) Convolution symmetry
(`integral_mul_integral_comm`): by (1) and Fubini,
`(∫ ψ dν)(∫ ρ dμ) = ∫∫ ρ(y) ψ(x - y + x₀) dμ(y) dν(x)`, and the substitution `y ↦ x + x₀ - y`
exchanges the roles of `ψ` and `ρ`, so `(∫ ψ dν)(∫ ρ dμ) = (∫ ρ dν)(∫ ψ dμ)`.  (3) Take for `ρ` a
normalised bump.

This is the analytic core of step (S4) of the support theorem on the diagonal (TN.4 step B4.4,
`bou:diagonal-support`; `demailly-cadg:III.2.13`: `∂ν/∂xⱼ = 0` forces `ν` to be a constant
    multiple of
Lebesgue measure).
-/

@[expose] public section

noncomputable section

open Set Filter Topology MeasureTheory Metric
open scoped ContDiff

namespace SGPT.Foundations.Analysis.Pending.ZeroDerivativeMeasure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The hypothesis: `ν` has vanishing distributional derivatives on the open set `U`. -/
def HasZeroDerivOn (ν : Measure E) (U : Set E) : Prop :=
  ∀ ψ : E → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ U →
    ∀ v : E, ∫ x, fderiv ℝ ψ x v ∂ν = 0

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem tsupport_comp_sub (ψ : E → ℝ) (a : E) :
    tsupport (fun x => ψ (x - a)) ⊆ (fun z => z + a) '' tsupport ψ := by
  have h : (fun x => ψ (x - a)) = ψ ∘ (Homeomorph.subRight a) := rfl
  rw [h, tsupport_comp_eq_preimage]
  intro x hx
  exact ⟨x - a, hx, sub_add_cancel x a⟩

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem hasCompactSupport_comp_sub {ψ : E → ℝ} (hψc : HasCompactSupport ψ) (a : E) :
    HasCompactSupport (fun x => ψ (x - a)) :=
  hψc.comp_homeomorph (Homeomorph.subRight a)

/-- **Translation invariance.** -/
theorem integral_comp_sub_eq (ν : Measure E) [IsFiniteMeasure ν] {U : Set E}
    (hder : HasZeroDerivOn ν U) {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    {v : E} (hseg : ∀ s ∈ Icc (0 : ℝ) 1, tsupport (fun x => ψ (x - s • v)) ⊆ U) :
    ∫ x, ψ (x - v) ∂ν = ∫ x, ψ x ∂ν := by
  have hdψ : Continuous (fderiv ℝ ψ) := hψ.continuous_fderiv (by simp)
  obtain ⟨C, hC⟩ := hdψ.bounded_above_of_compact_support (hψc.fderiv (𝕜 := ℝ))
  set F : ℝ → ℝ := fun s => ∫ x, ψ (x - s • v) ∂ν with hF
  set F' : ℝ → E → ℝ := fun s x => fderiv ℝ ψ (x - s • v) (-v) with hF'
  have hpt : ∀ (s : ℝ) (x : E), HasDerivAt (fun s => ψ (x - s • v)) (F' s x) s := by
    intro s x
    have hg : HasDerivAt (fun s : ℝ => x - s • v) (-v) s := by
      simpa using ((hasDerivAt_id s).smul_const v).const_sub x
    exact ((hψ.differentiable (by simp)) _).hasFDerivAt.comp_hasDerivAt s hg
  have hderF : ∀ s, HasDerivAt F (∫ x, F' s x ∂ν) s := by
    intro s
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := fun _ => C * ‖v‖)
      (s := univ) univ_mem ?_ ?_ ?_ ?_ (integrable_const _) ?_).2
    · exact Eventually.of_forall fun s' =>
        (hψ.continuous.comp (continuous_id.sub continuous_const)).aestronglyMeasurable
    · exact (hψ.continuous.comp (continuous_id.sub
      continuous_const)).integrable_of_hasCompactSupport
        (hasCompactSupport_comp_sub hψc _)
    · exact ((hdψ.comp (continuous_id.sub continuous_const)).clm_apply
        continuous_const).aestronglyMeasurable
    · refine Eventually.of_forall fun x s' _ => ?_
      calc ‖F' s' x‖ ≤ ‖fderiv ℝ ψ (x - s' • v)‖ * ‖-v‖ := (fderiv ℝ ψ (x - s' • v)).le_opNorm _
        _ ≤ C * ‖v‖ := by
          rw [norm_neg]
          exact mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)
    · exact Eventually.of_forall fun x s' _ => hpt s' x
  have hzero : ∀ s ∈ Icc (0 : ℝ) 1, ∫ x, F' s x ∂ν = 0 := by
    intro s hs
    have hψs : ContDiff ℝ ∞ (fun x => ψ (x - s • v)) := hψ.comp (contDiff_id.sub contDiff_const)
    have h0 := hder _ hψs (hasCompactSupport_comp_sub hψc _) (hseg s hs) v
    have hfd : ∀ x, fderiv ℝ (fun x => ψ (x - s • v)) x = fderiv ℝ ψ (x - s • v) := fun x =>
      fderiv_comp_sub _
    simp only [hfd] at h0
    simp only [hF', map_neg, integral_neg, h0, neg_zero]
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope F (fun s => ∫ x, F' s x ∂ν) zero_lt_one
    (fun s _ => (hderF s).continuousAt.continuousWithinAt) (fun s _ => hderF s)
  rw [hzero c (Ioo_subset_Icc_self hc)] at hslope
  have h10 : F 1 = F 0 := by
    have := hslope.symm
    rw [sub_zero, div_one, sub_eq_zero] at this
    exact this
  simpa [hF] using h10

variable (μ : Measure E) [μ.IsAddHaarMeasure]

/-- `(∫ ψ dν)(∫ ρ dμ) = ∫∫ ρ(y) ψ(x - y + x₀) dμ(y) dν(x)`. -/
theorem integral_mul_eq_double (ν : Measure E) [IsFiniteMeasure ν] {x₀ : E} {r : ℝ}
    (hder : HasZeroDerivOn ν (ball x₀ (3 * r))) {ψ ρ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ ball x₀ r) (hρ : ContDiff ℝ ∞ ρ)
    (hρc : HasCompactSupport ρ) (hρs : tsupport ρ ⊆ ball x₀ r) :
    (∫ x, ψ x ∂ν) * ∫ y, ρ y ∂μ = ∫ x, ∫ y, ρ y * ψ (x - y + x₀) ∂μ ∂ν := by
  -- translation invariance for the shifts `y - x₀`, `y` in the support of `ρ`
  have htr : ∀ y ∈ ball x₀ r, ∫ x, ψ (x - y + x₀) ∂ν = ∫ x, ψ x ∂ν := by
    intro y hy
    have hshift : ∀ x, x - y + x₀ = x - (y - x₀) := fun x => by abel
    simp_rw [hshift]
    refine integral_comp_sub_eq ν hder hψ hψc fun s hs z hz => ?_
    obtain ⟨u, hu, rfl⟩ := tsupport_comp_sub ψ _ hz
    have hu' := hψs hu
    rw [mem_ball] at hy hu' ⊢
    have hs1 : ‖s • (y - x₀)‖ ≤ ‖y - x₀‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
      exact mul_le_of_le_one_left (norm_nonneg _) hs.2
    rw [dist_eq_norm] at hy hu' ⊢
    have : u + s • (y - x₀) - x₀ = (u - x₀) + s • (y - x₀) := by abel
    rw [this]
    calc ‖(u - x₀) + s • (y - x₀)‖ ≤ ‖u - x₀‖ + ‖s • (y - x₀)‖ := norm_add_le _ _
      _ < r + r := add_lt_add_of_lt_of_le hu' (hs1.trans hy.le)
      _ ≤ 3 * r := by
        have : 0 < r := (norm_nonneg _).trans_lt hu'
        linarith
  -- the pointwise identity in `y`
  have hpt : ∀ y, ρ y * ∫ x, ψ (x - y + x₀) ∂ν = ρ y * ∫ x, ψ x ∂ν := by
    intro y
    by_cases hy : ρ y = 0
    · rw [hy, zero_mul, zero_mul]
    · rw [htr y (hρs (subset_tsupport _ hy))]
  -- Fubini
  obtain ⟨Cψ, hCψ⟩ := hψ.continuous.bounded_above_of_compact_support hψc
  have hcont : Continuous (fun p : E × E => ρ p.1 * ψ (p.2 - p.1 + x₀)) :=
    (hρ.continuous.comp continuous_fst).mul
      (hψ.continuous.comp ((continuous_snd.sub continuous_fst).add continuous_const))
  have hint : Integrable (fun p : E × E => ρ p.1 * ψ (p.2 - p.1 + x₀)) (μ.prod ν) := by
    have hρi : Integrable ρ μ := hρ.continuous.integrable_of_hasCompactSupport hρc
    have hC0 : 0 ≤ Cψ := (norm_nonneg _).trans (hCψ 0)
    have hbd : Integrable (fun p : E × E => ‖ρ p.1‖ * Cψ) (μ.prod ν) :=
      (hρi.norm.mul_const Cψ).comp_fst ν |>.mono' (by fun_prop) (Eventually.of_forall fun _ => by
        simp [abs_of_nonneg hC0])
    refine hbd.mono' hcont.aestronglyMeasurable (Eventually.of_forall fun p => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hCψ _) (norm_nonneg _)
  rw [← integral_integral_swap hint]
  simp_rw [integral_const_mul, hpt, integral_mul_const]
  ring

/-- **Convolution symmetry**: `(∫ ψ dν)(∫ ρ dμ) = (∫ ρ dν)(∫ ψ dμ)`. -/
theorem integral_mul_integral_comm (ν : Measure E) [IsFiniteMeasure ν] {x₀ : E} {r : ℝ}
    (hder : HasZeroDerivOn ν (ball x₀ (3 * r))) {ψ ρ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ ball x₀ r) (hρ : ContDiff ℝ ∞ ρ)
    (hρc : HasCompactSupport ρ) (hρs : tsupport ρ ⊆ ball x₀ r) :
    (∫ x, ψ x ∂ν) * ∫ y, ρ y ∂μ = (∫ x, ρ x ∂ν) * ∫ y, ψ y ∂μ := by
  rw [integral_mul_eq_double μ ν hder hψ hψc hψs hρ hρc hρs,
    integral_mul_eq_double μ ν hder hρ hρc hρs hψ hψc hψs]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  change ∫ y, ρ y * ψ (x - y + x₀) ∂μ = ∫ y, ψ y * ρ (x - y + x₀) ∂μ
  have := integral_sub_left_eq_self (fun y => ρ y * ψ (x - y + x₀)) μ (x + x₀)
  rw [← this]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  rw [show x - (x + x₀ - y) + x₀ = y by abel, mul_comm]
  congr 2
  abel

/-- **A measure with vanishing distributional derivatives on `B(x₀, 3r)` is a constant multiple
of Haar measure on `B(x₀, r)`** (tested with smooth compactly supported functions). -/
theorem exists_integral_eq_const_mul (ν : Measure E) [IsFiniteMeasure ν] {x₀ : E} {r : ℝ}
    (hr : 0 < r) (hder : HasZeroDerivOn ν (ball x₀ (3 * r))) :
    ∃ c : ℝ, ∀ ψ : E → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ ball x₀ r →
      ∫ x, ψ x ∂ν = c * ∫ x, ψ x ∂μ := by
  let b : ContDiffBump x₀ := ⟨r / 4, r / 2, by positivity, by linarith⟩
  have hb : ContDiff ℝ ∞ (b.normed μ) := b.contDiff_normed
  have hbc : HasCompactSupport (b.normed μ) := b.hasCompactSupport_normed
  have hbs : tsupport (b.normed μ) ⊆ ball x₀ r := by
    rw [b.tsupport_normed_eq]
    exact closedBall_subset_ball (by simp only [b]; linarith)
  refine ⟨∫ x, b.normed μ x ∂ν, fun ψ hψ hψc hψs => ?_⟩
  have h := integral_mul_integral_comm μ ν hder hψ hψc hψs hb hbc hbs
  rw [b.integral_normed, mul_one] at h
  exact h

end SGPT.Foundations.Analysis.Pending.ZeroDerivativeMeasure
