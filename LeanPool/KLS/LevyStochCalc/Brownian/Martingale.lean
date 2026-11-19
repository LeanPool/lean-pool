/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-12 by the KLS formalization project: ported to Lean v4.33.0 and
-- Mathlib db584cd. The changes are listed in vendor/README.md and vendor/port.patch.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import LeanPool.KLS.LevyStochCalc.Brownian.Continuity
public import LeanPool.KLS.LevyStochCalc.Martingale.RightCont
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Probability.ConditionalExpectation

/-!
# Natural filtration, martingale property, quadratic variation

Brownian motion `W` generates the *natural filtration*

  `ℱ_t := σ(W_s : s ≤ t)`,

w.r.t. which `W` is a martingale, and has *quadratic variation*

  `⟨W⟩_t = t`.

The quadratic-variation identity `(dW)² = dt` is the cornerstone of the Itô
formula; without it the second-order Taylor term in the diffusion case would
not produce the `½ σ² f''` correction.

## References

* Karatzas–Shreve, *Brownian Motion and Stochastic Calculus*, 1991, §1.5 + §3.1.
* User's dissertation, ch02 §"Probability-space prerequisites", lines 22-23.

## Proof structure

1. Construct `naturalFiltration W` via `MeasureTheory.Filtration.natural`.
2. Adaptedness is automatic via `Filtration.stronglyAdapted_natural`.
3. Conditional-expectation identity: `𝔼[W_t | ℱ_s] = W_s` reduces to
   `𝔼[W_t − W_s | ℱ_s] = 0`. This requires:
   * **σ-algebra independence**: `σ(W_t − W_s) ⊥⊥ ℱ_s` under `P`. This is the
     structure field `BrownianMotion.joint_increment_independent`, read through
     the description of `naturalFiltration W` at `s` as `⨆ j ∈ Set.Iic s, σ(W_j)`;
     it is stronger than the derived pairwise statement
     `BrownianMotion.increment_independent`.
   * **Mean zero of increment**: `𝔼[W_t − W_s] = ∫ x, x ∂(gaussianReal 0 ⟨t-s⟩) = 0`
     by `ProbabilityTheory.integral_id_gaussianReal`.
   * **`condExp_indep_eq`**: independence + measurability ⇒ `𝔼[X | ℱ] = 𝔼[X]` a.s.

## Downstream modules

The conditional-expectation identities for Brownian increments live in
`LevyStochCalc.Brownian.MartingaleCondExp`, the martingale property and the quadratic variation
`⟨W⟩_t = t` in `LevyStochCalc.Brownian.MartingaleQuadVar`, and their counterparts for the
right-continuous augmentation of the natural filtration in
`LevyStochCalc.Brownian.MartingaleRightCont`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Brownian.Martingale

universe u

section Moments
variable {Ω : Type u} [MeasurableSpace Ω]

/-- The *natural filtration* of a Brownian motion `W`. -/
noncomputable def naturalFiltration
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P) :
    MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω› :=
  MeasureTheory.Filtration.natural W.W (fun t => (W.measurable_eval t).stronglyMeasurable)

/-- **Integrability of a Brownian-motion value at any `s : ℝ`.** Uses the
Gaussian distribution of `W_s` (for `s ≥ 0`) or the `negative_zero` extension
(for `s < 0`). -/
lemma brownianMotion_integrable
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (s : ℝ) :
    MeasureTheory.Integrable (W.W s) P := by
  by_cases hs_neg : s < 0
  · -- s < 0: W_s = 0 a.s.
    refine ⟨(W.measurable_eval s).aestronglyMeasurable, ?_⟩
    rw [MeasureTheory.hasFiniteIntegral_iff_eNorm]
    have h_nn : ∀ᵐ ω ∂P, ‖W.W s ω‖ₑ = 0 := by
      filter_upwards [W.negative_zero s hs_neg] with ω hω
      rw [hω]; simp
    rw [MeasureTheory.lintegral_congr_ae h_nn]
    simp
  push Not at hs_neg
  -- s ≥ 0
  have hs := hs_neg
  by_cases hs_zero : s = 0
  · subst hs_zero
    refine ⟨(W.measurable_eval 0).aestronglyMeasurable, ?_⟩
    rw [MeasureTheory.hasFiniteIntegral_iff_eNorm]
    have h_nn : ∀ᵐ ω ∂P, ‖W.W 0 ω‖ₑ = 0 := by
      filter_upwards [W.initial_zero] with ω hω
      rw [hω]; simp
    rw [MeasureTheory.lintegral_congr_ae h_nn]
    simp
  · have hs_pos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs_zero)
    have h_eq : (fun ω => W.W s ω) =ᵐ[P] fun ω => W.W s ω - W.W 0 ω := by
      filter_upwards [W.initial_zero] with ω hω
      rw [hω]; ring
    have h_map : P.map (fun ω => W.W s ω)
        = ProbabilityTheory.gaussianReal 0 ⟨s, hs⟩ := by
      rw [MeasureTheory.Measure.map_congr h_eq]
      have := W.increment_gaussian (le_refl 0) hs_pos
      simpa using this
    have h_int_id : MeasureTheory.Integrable (id : ℝ → ℝ)
        (ProbabilityTheory.gaussianReal 0 ⟨s, hs⟩) :=
      MeasureTheory.memLp_one_iff_integrable.mp
        (ProbabilityTheory.memLp_id_gaussianReal' 1 (by simp))
    have := (MeasureTheory.integrable_map_measure (g := (id : ℝ → ℝ))
      (by fun_prop : MeasureTheory.AEStronglyMeasurable id _)
      (W.measurable_eval s).aemeasurable).mp (h_map ▸ h_int_id)
    simpa using this

/-- **`W_s` is in `L²` for any `s : ℝ`.** Pushforward to `gaussianReal 0 v` +
`IsGaussian.memLp_id`, with the `negative_zero` field for `s < 0`. -/
lemma brownianMotion_memLp_2
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (s : ℝ) :
    MeasureTheory.MemLp (W.W s) 2 P := by
  by_cases hs_neg : s < 0
  · -- s < 0: W_s = 0 a.s.
    rw [MeasureTheory.memLp_iff,
      MeasureTheory.eLpNorm_eq_lintegral_rpow_eNorm_toReal (by norm_num) (by simp)
        (W.measurable_eval s).aestronglyMeasurable]
    have h_zero : ∀ᵐ ω ∂P, ‖W.W s ω‖ₑ ^ ((2 : ℝ≥0∞).toReal) = 0 := by
      filter_upwards [W.negative_zero s hs_neg] with ω hω
      rw [hω]; simp
    rw [MeasureTheory.lintegral_congr_ae h_zero]
    simp
  push Not at hs_neg
  have hs := hs_neg
  by_cases hs_zero : s = 0
  · subst hs_zero
    rw [MeasureTheory.memLp_iff,
      MeasureTheory.eLpNorm_eq_lintegral_rpow_eNorm_toReal (by norm_num) (by simp)
        (W.measurable_eval 0).aestronglyMeasurable]
    have h_zero : ∀ᵐ ω ∂P, ‖W.W 0 ω‖ₑ ^ ((2 : ℝ≥0∞).toReal) = 0 := by
      filter_upwards [W.initial_zero] with ω hω
      rw [hω]; simp
    rw [MeasureTheory.lintegral_congr_ae h_zero]
    simp
  · have hs_pos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs_zero)
    have h_eq : (fun ω => W.W s ω) =ᵐ[P] fun ω => W.W s ω - W.W 0 ω := by
      filter_upwards [W.initial_zero] with ω hω
      rw [hω]; ring
    have h_map : P.map (fun ω => W.W s ω)
        = ProbabilityTheory.gaussianReal 0 ⟨s, hs⟩ := by
      rw [MeasureTheory.Measure.map_congr h_eq]
      have := W.increment_gaussian (le_refl 0) hs_pos
      simpa using this
    have h_memLp_id : MeasureTheory.MemLp (id : ℝ → ℝ) 2
        (ProbabilityTheory.gaussianReal 0 ⟨s, hs⟩) :=
      ProbabilityTheory.memLp_id_gaussianReal' 2 (by simp)
    rw [show (W.W s : Ω → ℝ) = id ∘ W.W s from rfl]
    rw [← h_map] at h_memLp_id
    exact (MeasureTheory.memLp_map_measure_iff (by fun_prop)
      (W.measurable_eval s).aemeasurable).mp h_memLp_id

/-- **Integrability of `(W_s)^2` at any `s : ℝ`.** Uses the Gaussian
distribution of `W_s` (for `s ≥ 0`) or the `negative_zero` extension. -/
lemma brownianMotion_sq_integrable
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (s : ℝ) :
    MeasureTheory.Integrable (fun ω => (W.W s ω)^2) P := by
  by_cases hs_neg : s < 0
  · -- s < 0
    refine ⟨((W.measurable_eval s).pow_const 2).aestronglyMeasurable, ?_⟩
    rw [MeasureTheory.hasFiniteIntegral_iff_eNorm]
    have h_nn : ∀ᵐ ω ∂P, ‖(W.W s ω)^2‖ₑ = 0 := by
      filter_upwards [W.negative_zero s hs_neg] with ω hω
      rw [hω]; simp
    rw [MeasureTheory.lintegral_congr_ae h_nn]
    simp
  push Not at hs_neg
  have hs := hs_neg
  by_cases hs_zero : s = 0
  · subst hs_zero
    refine ⟨((W.measurable_eval 0).pow_const 2).aestronglyMeasurable, ?_⟩
    rw [MeasureTheory.hasFiniteIntegral_iff_eNorm]
    have h_nn : ∀ᵐ ω ∂P, ‖(W.W 0 ω)^2‖ₑ = 0 := by
      filter_upwards [W.initial_zero] with ω hω
      rw [hω]; simp
    rw [MeasureTheory.lintegral_congr_ae h_nn]
    simp
  · have hs_pos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs_zero)
    have h_eq : (fun ω => W.W s ω) =ᵐ[P] fun ω => W.W s ω - W.W 0 ω := by
      filter_upwards [W.initial_zero] with ω hω
      rw [hω]; ring
    have h_map : P.map (fun ω => W.W s ω)
        = ProbabilityTheory.gaussianReal 0 ⟨s, hs⟩ := by
      rw [MeasureTheory.Measure.map_congr h_eq]
      have := W.increment_gaussian (le_refl 0) hs_pos
      simpa using this
    -- Integrability of x^2 under gaussianReal 0 ⟨s, hs⟩
    have h_int_sq : MeasureTheory.Integrable (fun x : ℝ => x^2)
        (ProbabilityTheory.gaussianReal 0 ⟨s, hs⟩) := by
      have h_memLp : MeasureTheory.MemLp (id : ℝ → ℝ) 2
          (ProbabilityTheory.gaussianReal 0 ⟨s, hs⟩) :=
        ProbabilityTheory.memLp_id_gaussianReal' 2 (by simp)
      have h := h_memLp.integrable_norm_pow (p := 2) (by norm_num)
      convert h using 1
      ext x
      change x^2 = ‖x‖^2
      rw [Real.norm_eq_abs, sq_abs]
    -- Pull back via map
    have := (MeasureTheory.integrable_map_measure
      (g := fun x : ℝ => x^2)
      (by fun_prop : MeasureTheory.AEStronglyMeasurable (fun x : ℝ => x^2) _)
      (W.measurable_eval s).aemeasurable).mp (h_map ▸ h_int_sq)
    simpa [Function.comp_def] using this

end Moments

end LevyStochCalc.Brownian.Martingale
