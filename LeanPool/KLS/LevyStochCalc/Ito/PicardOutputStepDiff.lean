/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import LeanPool.KLS.LevyStochCalc.Ito.PicardOutputWeighting

/-!
# The contraction estimate for the Picard step

The Picard step is the sum of its drift, diffusion and jump components, so the three
per-component difference bounds combine, through `‖a + b + c‖² ≤ 3(‖a‖² + ‖b‖² + ‖c‖²)`,
into a single per-time second-moment bound for the difference of two steps by the energy of
the difference of the two frozen paths. Weighting that bound back into the Bielecki norm
gives a contraction factor that tends to `0` as the rate `β` grows.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]
variable {n d : ℕ} {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]

section Weighting

omit [MeasurableSpace E] [MeasureTheory.IsProbabilityMeasure P] in
/-- **Combining three per-time bounds with a common right-hand side.** For a process that splits
as a sum of three, `‖a + b + c‖² ≤ 3(‖a‖² + ‖b‖² + ‖c‖²)` turns three separate second-moment
bounds into one, with the constants added and tripled. -/
theorem lintegral_sq_sum3_le {U₁ U₂ U₃ : Ω → (Fin n → ℝ)} {c₁ c₂ c₃ R : ℝ≥0∞}
    (hm₁ : ∀ i : Fin n, Measurable fun ω => (‖U₁ ω i‖₊ : ℝ≥0∞) ^ 2)
    (hm₂ : ∀ i : Fin n, Measurable fun ω => (‖U₂ ω i‖₊ : ℝ≥0∞) ^ 2)
    (hm₃ : ∀ i : Fin n, Measurable fun ω => (‖U₃ ω i‖₊ : ℝ≥0∞) ^ 2)
    (h₁ : ∫⁻ ω, ∑ i, (‖U₁ ω i‖₊ : ℝ≥0∞) ^ 2 ∂P ≤ c₁ * R)
    (h₂ : ∫⁻ ω, ∑ i, (‖U₂ ω i‖₊ : ℝ≥0∞) ^ 2 ∂P ≤ c₂ * R)
    (h₃ : ∫⁻ ω, ∑ i, (‖U₃ ω i‖₊ : ℝ≥0∞) ^ 2 ∂P ≤ c₃ * R) :
    ∫⁻ ω, ∑ i, (‖U₁ ω i + U₂ ω i + U₃ ω i‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ 3 * (c₁ + c₂ + c₃) * R := by
  have hM₁ : Measurable fun ω => ∑ i, (‖U₁ ω i‖₊ : ℝ≥0∞) ^ 2 :=
    Finset.measurable_sum _ fun i _ => hm₁ i
  have hM₂ : Measurable fun ω => ∑ i, (‖U₂ ω i‖₊ : ℝ≥0∞) ^ 2 :=
    Finset.measurable_sum _ fun i _ => hm₂ i
  have hM₃ : Measurable fun ω => ∑ i, (‖U₃ ω i‖₊ : ℝ≥0∞) ^ 2 :=
    Finset.measurable_sum _ fun i _ => hm₃ i
  have hsum : ∀ ω : Ω, ∑ i, (‖U₁ ω i + U₂ ω i + U₃ ω i‖₊ : ℝ≥0∞) ^ 2
      ≤ 3 * (∑ i, (‖U₁ ω i‖₊ : ℝ≥0∞) ^ 2) + 3 * (∑ i, (‖U₂ ω i‖₊ : ℝ≥0∞) ^ 2)
        + 3 * (∑ i, (‖U₃ ω i‖₊ : ℝ≥0∞) ^ 2) := by
    intro ω
    refine le_trans (Finset.sum_le_sum fun i _ => sq_nnnorm_add3_le _ _ _) (le_of_eq ?_)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum,
      Finset.mul_sum]
  have hM1' : Measurable fun ω : Ω => 3 * (∑ i, (‖U₁ ω i‖₊ : ℝ≥0∞) ^ 2) := hM₁.const_mul 3
  have hM2' : Measurable fun ω : Ω => 3 * (∑ i, (‖U₂ ω i‖₊ : ℝ≥0∞) ^ 2) := hM₂.const_mul 3
  have hM12 : Measurable fun ω : Ω =>
      3 * (∑ i, (‖U₁ ω i‖₊ : ℝ≥0∞) ^ 2) + 3 * (∑ i, (‖U₂ ω i‖₊ : ℝ≥0∞) ^ 2) := hM1'.add hM2'
  refine (lintegral_mono hsum).trans ?_
  rw [MeasureTheory.lintegral_add_left hM12,
    MeasureTheory.lintegral_add_left hM1',
    MeasureTheory.lintegral_const_mul' _ _ (by simp : (3 : ℝ≥0∞) ≠ ⊤),
    MeasureTheory.lintegral_const_mul' _ _ (by simp : (3 : ℝ≥0∞) ≠ ⊤),
    MeasureTheory.lintegral_const_mul' _ _ (by simp : (3 : ℝ≥0∞) ≠ ⊤)]
  calc 3 * (∫⁻ ω, ∑ i, (‖U₁ ω i‖₊ : ℝ≥0∞) ^ 2 ∂P)
        + 3 * (∫⁻ ω, ∑ i, (‖U₂ ω i‖₊ : ℝ≥0∞) ^ 2 ∂P)
        + 3 * (∫⁻ ω, ∑ i, (‖U₃ ω i‖₊ : ℝ≥0∞) ^ 2 ∂P)
      ≤ 3 * (c₁ * R) + 3 * (c₂ * R) + 3 * (c₃ * R) :=
        add_le_add (add_le_add (mul_le_mul' le_rfl h₁) (mul_le_mul' le_rfl h₂))
          (mul_le_mul' le_rfl h₃)
    _ = 3 * (c₁ + c₂ + c₃) * R := by ring

omit [MeasurableSpace Ω] [MeasureTheory.IsProbabilityMeasure P] in
/-- The `μ` clause of `IsLipschitz`, read on a single coordinate. -/
theorem mu_lip_componentwise {ν : MeasureTheory.Measure E}
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E) {L : ℝ}
    (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (s : ℝ) (x₁ x₂ : Fin n → ℝ) (i : Fin n) :
    |coeffs.μ s x₁ i - coeffs.μ s x₂ i| ≤ L * ‖x₁ - x₂‖ := by
  refine le_trans ?_ (hLip.2.1 s x₁ x₂)
  simpa [Real.norm_eq_abs, Pi.sub_apply] using
    norm_le_pi_norm (coeffs.μ s x₁ - coeffs.μ s x₂) i

omit [MeasurableSpace E] [MeasureTheory.IsProbabilityMeasure P] in
/-- The two shapes of the coordinate second moment agree. -/
theorem lintegral_ofReal_sum_sq_eq (U : Ω → (Fin n → ℝ)) :
    ∫⁻ ω, ENNReal.ofReal (∑ i, (U ω i) ^ 2) ∂P
      = ∫⁻ ω, ∑ i, (‖U ω i‖₊ : ℝ≥0∞) ^ 2 ∂P := by
  refine lintegral_congr fun ω => ?_
  rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
  exact (Finset.sum_congr rfl fun i _ => sq_coe_nnnorm_real (U ω i)).symm

/-- The Picard step is the sum of its three components, coordinatewise. -/
theorem picardStep_apply_eq
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    {ν : MeasureTheory.Measure E} [MeasureTheory.SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (X : ℝ → Ω → (Fin n → ℝ)) (x₀ : Fin n → ℝ)
    (h_σ_meas : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (X s ω) i j)))
    (h_σ_progMeas : ∀ i : Fin n, ∀ j : Fin d,
      Probability.ProgressivelyMeasurable ℱ (fun ω s => coeffs.σ s (X s ω) i j))
    (h_σ_sq : ∀ i : Fin n, ∀ j : Fin d, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h_γ_meas : ∀ i : Fin n,
      Measurable (fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i))
    (h_γ_progMeas : ∀ i : Fin n,
      Probability.MarkedProgressivelyMeasurable ℱ (fun ω s e => coeffs.γ s (X s ω) e i))
    (h_γ_sq : ∀ i : Fin n, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
        (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (t : ℝ) (ω : Ω) (i : Fin n) :
    picardStep W N ℱ hℱW hℱN coeffs X x₀ h_σ_meas h_σ_progMeas h_σ_sq
        h_γ_meas h_γ_progMeas h_γ_sq t ω i
      = picardStepDrift coeffs X x₀ t ω i
        + picardStepDiffusion W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq t ω i
        + picardStepJump N ℱ hℱN coeffs X h_γ_meas h_γ_progMeas h_γ_sq t ω i := rfl

/-- **Slice measurability of the Picard step.** At each fixed time the step is measurable in the
sample point; joint measurability in `(t, ω)` is a property of the modification, not of the step
itself. -/
theorem measurable_picardStep_slice
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    {ν : MeasureTheory.Measure E} [MeasureTheory.SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (X : ℝ → Ω → (Fin n → ℝ)) (x₀ : Fin n → ℝ)
    (h_σ_meas : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (X s ω) i j)))
    (h_σ_progMeas : ∀ i : Fin n, ∀ j : Fin d,
      Probability.ProgressivelyMeasurable ℱ (fun ω s => coeffs.σ s (X s ω) i j))
    (h_σ_sq : ∀ i : Fin n, ∀ j : Fin d, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h_γ_meas : ∀ i : Fin n,
      Measurable (fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i))
    (h_γ_progMeas : ∀ i : Fin n,
      Probability.MarkedProgressivelyMeasurable ℱ (fun ω s e => coeffs.γ s (X s ω) e i))
    (h_γ_sq : ∀ i : Fin n, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
        (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (h_μ_meas : ∀ i : Fin n,
      Measurable (Function.uncurry fun ω s => coeffs.μ s (X s ω) i))
    (t : ℝ) (i : Fin n) :
    Measurable fun ω => picardStep W N ℱ hℱW hℱN coeffs X x₀ h_σ_meas h_σ_progMeas h_σ_sq
      h_γ_meas h_γ_progMeas h_γ_sq t ω i := by
  have heq : (fun ω => picardStep W N ℱ hℱW hℱN coeffs X x₀ h_σ_meas h_σ_progMeas h_σ_sq
        h_γ_meas h_γ_progMeas h_γ_sq t ω i)
      = fun ω => picardStepDrift coeffs X x₀ t ω i
        + picardStepDiffusion W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq t ω i
        + picardStepJump N ℱ hℱN coeffs X h_γ_meas h_γ_progMeas h_γ_sq t ω i := by
    funext ω
    exact picardStep_apply_eq W N ℱ hℱW hℱN coeffs X x₀ h_σ_meas h_σ_progMeas h_σ_sq
      h_γ_meas h_γ_progMeas h_γ_sq t ω i
  rw [heq]
  exact ((measurable_picardStep_drift coeffs X x₀ i (h_μ_meas i) t).add
    (measurable_picardStep_diffusion W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq i t)).add
    (measurable_picardStep_jump N ℱ hℱN coeffs X h_γ_meas h_γ_progMeas h_γ_sq i t)

/-- The Picard step starts at `x₀`: at time `0` both stochastic components vanish almost surely
and the drift window is a null set. -/
theorem ae_picardStep_zero
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    {ν : MeasureTheory.Measure E} [MeasureTheory.SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (X : ℝ → Ω → (Fin n → ℝ)) (x₀ : Fin n → ℝ)
    (h_σ_meas : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (X s ω) i j)))
    (h_σ_progMeas : ∀ i : Fin n, ∀ j : Fin d,
      Probability.ProgressivelyMeasurable ℱ (fun ω s => coeffs.σ s (X s ω) i j))
    (h_σ_sq : ∀ i : Fin n, ∀ j : Fin d, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h_γ_meas : ∀ i : Fin n,
      Measurable (fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i))
    (h_γ_progMeas : ∀ i : Fin n,
      Probability.MarkedProgressivelyMeasurable ℱ (fun ω s e => coeffs.γ s (X s ω) e i))
    (h_γ_sq : ∀ i : Fin n, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
        (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤) :
    ∀ᵐ ω ∂P, ∀ i : Fin n,
      picardStep W N ℱ hℱW hℱN coeffs X x₀ h_σ_meas h_σ_progMeas h_σ_sq
        h_γ_meas h_γ_progMeas h_γ_sq 0 ω i = x₀ i := by
  have hdrift : ∀ (ω : Ω) (i : Fin n), picardStepDrift coeffs X x₀ 0 ω i = x₀ i := by
    intro ω i
    have hzero : (∫ s in Set.Icc (0 : ℝ) 0, coeffs.μ s (X s ω) i ∂volume) = 0 :=
      MeasureTheory.setIntegral_measure_zero _ (by simp)
    change x₀ i + (∫ s in Set.Icc (0 : ℝ) 0, coeffs.μ s (X s ω) i ∂volume) = x₀ i
    rw [hzero, add_zero]
  have hσ : ∀ᵐ ω ∂P, ∀ p : Fin n × Fin d,
      LevyStochCalc.Brownian.Ito.stochasticIntegral (W.W p.2) ℱ (hℱW p.2)
        (fun ω' s => coeffs.σ s (X s ω') p.1 p.2)
        (h_σ_meas p.1 p.2) (h_σ_progMeas p.1 p.2) (h_σ_sq p.1 p.2) 0 ω = 0 :=
    MeasureTheory.ae_all_iff.mpr fun p =>
      LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_ae_zero_of_nonpos (W.W p.2) ℱ
        (hℱW p.2) (fun ω' s => coeffs.σ s (X s ω') p.1 p.2)
        (h_σ_meas p.1 p.2) (h_σ_progMeas p.1 p.2) (h_σ_sq p.1 p.2) le_rfl
  have hγ : ∀ᵐ ω ∂P, ∀ i : Fin n,
      picardStepJump N ℱ hℱN coeffs X h_γ_meas h_γ_progMeas h_γ_sq 0 ω i = 0 := by
    refine MeasureTheory.ae_all_iff.mpr fun i => ?_
    filter_upwards [LevyStochCalc.Poisson.Compensated.stochasticIntegral_ae_eq_process N ℱ hℱN
        (fun ω s e => coeffs.γ s (X s ω) e i) (h_γ_meas i) (h_γ_progMeas i) (h_γ_sq i) 0,
      LevyStochCalc.Poisson.Compensated.process_ae_zero_of_nonpos N ℱ hℱN
        (fun ω s e => coeffs.γ s (X s ω) e i) (h_γ_meas i) (h_γ_progMeas i) (h_γ_sq i)
        le_rfl] with ω h1 h2
    change LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN
      (fun ω' s e => coeffs.γ s (X s ω') e i) (h_γ_meas i) (h_γ_progMeas i) (h_γ_sq i) 0 ω = 0
    rw [h1, h2]
    rfl
  filter_upwards [hσ, hγ] with ω hσω hγω i
  rw [picardStep_apply_eq W N ℱ hℱW hℱN coeffs X x₀ h_σ_meas h_σ_progMeas h_σ_sq
    h_γ_meas h_γ_progMeas h_γ_sq 0 ω i, hdrift ω i, hγω i, add_zero]
  have hdiff : picardStepDiffusion W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq 0 ω i = 0 := by
    change (∑ j : Fin d, LevyStochCalc.Brownian.Ito.stochasticIntegral (W.W j) ℱ (hℱW j)
      (fun ω' s => coeffs.σ s (X s ω') i j)
      (h_σ_meas i j) (h_σ_progMeas i j) (h_σ_sq i j) 0 ω) = 0
    exact Finset.sum_eq_zero fun j _ => hσω (i, j)
  rw [hdiff, add_zero]

-- `picardStep` and the two stochastic-integral components unfold to `Finset` sums over `Fin d`
-- and to the `L²`-limit integrals; the statement below repeats those terms verbatim on both
-- sides, so unfolding them during unification only costs time. Sealed as in `Ito/Picard.lean`.
attribute [local irreducible] picardStep picardStepDiffusion picardStepJump
attribute [local irreducible]
  LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral
attribute [local irreducible] LevyStochCalc.Brownian.Ito.stochasticIntegral

-- The statement names the full three-component Picard term twice, once along each path, and
-- elaborating the second application exceeds the default budget even with the components sealed.
private theorem lintegral_window_nnnorm_le_sum (measure : Measure Ω) (Z : ℝ → Ω → Fin n → ℝ)
  (t : ℝ) :
    (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, (‖Z s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂measure)
      ≤ ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, ∑ i, (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂measure :=
  lintegral_mono fun ω => lintegral_mono fun s => sq_coe_nnnorm_le_sum (Z s ω)

/-- **The per-time contraction estimate for the Picard step**, with every hypothesis of its three
components discharged from `IsLipschitz`. -/
theorem lintegral_sq_picardStep_diff_le
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    {ν : MeasureTheory.Measure E} [MeasureTheory.SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (X Y : ℝ → Ω → (Fin n → ℝ)) (x₀ : Fin n → ℝ)
    (h_σ_meas_X : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (X s ω) i j)))
    (h_σ_progMeas_X : ∀ i : Fin n, ∀ j : Fin d,
      Probability.ProgressivelyMeasurable ℱ (fun ω s => coeffs.σ s (X s ω) i j))
    (h_σ_sq_X : ∀ i : Fin n, ∀ j : Fin d, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h_γ_meas_X : ∀ i : Fin n,
      Measurable (fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i))
    (h_γ_progMeas_X : ∀ i : Fin n,
      Probability.MarkedProgressivelyMeasurable ℱ (fun ω s e => coeffs.γ s (X s ω) e i))
    (h_γ_sq_X : ∀ i : Fin n, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
        (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (h_σ_meas_Y : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (Y s ω) i j)))
    (h_σ_progMeas_Y : ∀ i : Fin n, ∀ j : Fin d,
      Probability.ProgressivelyMeasurable ℱ (fun ω s => coeffs.σ s (Y s ω) i j))
    (h_σ_sq_Y : ∀ i : Fin n, ∀ j : Fin d, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coeffs.σ s (Y s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h_γ_meas_Y : ∀ i : Fin n,
      Measurable (fun p : Ω × ℝ × E => coeffs.γ p.2.1 (Y p.2.1 p.1) p.2.2 i))
    (h_γ_progMeas_Y : ∀ i : Fin n,
      Probability.MarkedProgressivelyMeasurable ℱ (fun ω s e => coeffs.γ s (Y s ω) e i))
    (h_γ_sq_Y : ∀ i : Fin n, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
        (‖coeffs.γ s (Y s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (hμX : ∀ i : Fin n, Measurable (Function.uncurry fun ω s => coeffs.μ s (X s ω) i))
    (hμY : ∀ i : Fin n, Measurable (Function.uncurry fun ω s => coeffs.μ s (Y s ω) i))
    (hXYm : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => ‖X s ω - Y s ω‖))
    (hμXsq : ∀ i : Fin n, ∀ b : ℝ, 0 < b → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
      (‖coeffs.μ s (X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hμYsq : ∀ i : Fin n, ∀ b : ℝ, 0 < b → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
      (‖coeffs.μ s (Y s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hXYsq : ∀ b : ℝ, 0 < b → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
      (‖X s ω - Y s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 < t) :
    let stepX : ℝ → Ω → Fin n → ℝ :=
      picardStep (P := P) (ν := ν) W N ℱ hℱW hℱN coeffs X x₀
        h_σ_meas_X h_σ_progMeas_X h_σ_sq_X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X
    let stepY : ℝ → Ω → Fin n → ℝ :=
      picardStep (P := P) (ν := ν) W N ℱ hℱW hℱN coeffs Y x₀
        h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y
    ∫⁻ ω, ∑ i : Fin n, (‖stepX t ω i - stepY t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ 3 * (ENNReal.ofReal ((n : ℝ) * L ^ 2 * t)
              + ENNReal.ofReal ((n : ℝ) * ((d : ℝ) * L ^ 2))
              + ENNReal.ofReal ((n : ℝ) * L ^ 2))
          * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
              (∑ i, (‖X s ω i - Y s ω i‖₊ : ℝ≥0∞) ^ 2) ∂volume ∂P := by
  dsimp only
  have hbridgeR := lintegral_window_nnnorm_le_sum P (fun s ω => X s ω - Y s ω) t
  have hbochner : (∫⁻ ω, ENNReal.ofReal
        (∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2 ∂volume) ∂P)
      ≤ ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
          (∑ i, (‖X s ω i - Y s ω i‖₊ : ℝ≥0∞) ^ 2) ∂volume ∂P :=
    lintegral_mono (lintegral_window_norm_le_sum (Z := fun s ω => X s ω - Y s ω) t)
  have hsplit : ∀ (ω : Ω) (i : Fin n),
      picardStep (P := P) (ν := ν) (n := n) (d := d)
            W N ℱ hℱW hℱN coeffs X x₀ h_σ_meas_X h_σ_progMeas_X h_σ_sq_X
          h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω i
        - picardStep (P := P) (ν := ν) (n := n) (d := d)
            W N ℱ hℱW hℱN coeffs Y x₀ h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y
            h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω i
      = (picardStepDrift coeffs X x₀ t ω i - picardStepDrift coeffs Y x₀ t ω i)
        + (picardStepDiffusion W ℱ hℱW coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω i
            - picardStepDiffusion W ℱ hℱW coeffs Y h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω i)
        + (picardStepJump N ℱ hℱN coeffs X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω i
            - picardStepJump N ℱ hℱN coeffs Y h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω i) := by
    intro ω i
    rw [picardStep_apply_eq W N ℱ hℱW hℱN coeffs X x₀ h_σ_meas_X h_σ_progMeas_X h_σ_sq_X
      h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω i,
      picardStep_apply_eq W N ℱ hℱW hℱN coeffs Y x₀ h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y
        h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω i]
    ring
  rw [lintegral_congr fun ω => Finset.sum_congr rfl fun i _ => by rw [hsplit ω i]]
  refine lintegral_sq_sum3_le
    (U₁ := fun ω i => picardStepDrift coeffs X x₀ t ω i
      - picardStepDrift coeffs Y x₀ t ω i)
    (U₂ := fun ω i =>
      picardStepDiffusion W ℱ hℱW coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω i
        - picardStepDiffusion W ℱ hℱW coeffs Y h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω i)
    (U₃ := fun ω i =>
      picardStepJump N ℱ hℱN coeffs X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω i
        - picardStepJump N ℱ hℱN coeffs Y h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω i)
    (fun i => ((((measurable_picardStep_drift coeffs X x₀ i (hμX i) t).sub
      (measurable_picardStep_drift coeffs Y x₀ i (hμY i) t)).nnNorm).coe_nnreal_ennreal).pow_const
        2)
    (fun i => ((((measurable_picardStep_diffusion W ℱ hℱW coeffs X h_σ_meas_X h_σ_progMeas_X
      h_σ_sq_X i t).sub (measurable_picardStep_diffusion W ℱ hℱW coeffs Y h_σ_meas_Y
        h_σ_progMeas_Y h_σ_sq_Y i t)).nnNorm).coe_nnreal_ennreal).pow_const 2)
    (fun i => ((((measurable_picardStep_jump N ℱ hℱN coeffs X h_γ_meas_X h_γ_progMeas_X
      h_γ_sq_X i t).sub (measurable_picardStep_jump N ℱ hℱN coeffs Y h_γ_meas_Y
        h_γ_progMeas_Y h_γ_sq_Y i t)).nnNorm).coe_nnreal_ennreal).pow_const 2)
    ?_ ?_ ?_
  · rw [← lintegral_ofReal_sum_sq_eq]
    exact (drift_diff_lintegral_sq_bound coeffs hLip.1 (mu_lip_componentwise coeffs hLip) X Y x₀
      hμX hμY hXYm hμXsq hμYsq hXYsq ht.le).trans (mul_le_mul' le_rfl hbochner)
  · exact (diffusion_diff_lintegral_sq_bound W ℱ hℱW coeffs hLip.1 hLip.2.2.1 X Y
      h_σ_meas_X h_σ_meas_Y h_σ_progMeas_X h_σ_progMeas_Y h_σ_sq_X h_σ_sq_Y ht).trans
      (mul_le_mul' le_rfl hbridgeR)
  · exact (jump_diff_lintegral_sq_bound N ℱ hℱN coeffs hLip X Y h_γ_meas_X h_γ_progMeas_X
      h_γ_sq_X h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y ht).trans (mul_le_mul' le_rfl hbridgeR)

/-- The Bielecki contraction estimate for the Picard step, with rate
`√(3n(L²T + dL² + L²) / 2β)`. -/
theorem bieleckiNorm_picardStep_diff_le
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    {ν : MeasureTheory.Measure E} [MeasureTheory.SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (X Y : ℝ → Ω → (Fin n → ℝ)) (x₀ : Fin n → ℝ)
    (h_σ_meas_X : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (X s ω) i j)))
    (h_σ_progMeas_X : ∀ i : Fin n, ∀ j : Fin d,
      Probability.ProgressivelyMeasurable ℱ (fun ω s => coeffs.σ s (X s ω) i j))
    (h_σ_sq_X : ∀ i : Fin n, ∀ j : Fin d, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h_γ_meas_X : ∀ i : Fin n,
      Measurable (fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i))
    (h_γ_progMeas_X : ∀ i : Fin n,
      Probability.MarkedProgressivelyMeasurable ℱ (fun ω s e => coeffs.γ s (X s ω) e i))
    (h_γ_sq_X : ∀ i : Fin n, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
        (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (h_σ_meas_Y : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (Y s ω) i j)))
    (h_σ_progMeas_Y : ∀ i : Fin n, ∀ j : Fin d,
      Probability.ProgressivelyMeasurable ℱ (fun ω s => coeffs.σ s (Y s ω) i j))
    (h_σ_sq_Y : ∀ i : Fin n, ∀ j : Fin d, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coeffs.σ s (Y s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h_γ_meas_Y : ∀ i : Fin n,
      Measurable (fun p : Ω × ℝ × E => coeffs.γ p.2.1 (Y p.2.1 p.1) p.2.2 i))
    (h_γ_progMeas_Y : ∀ i : Fin n,
      Probability.MarkedProgressivelyMeasurable ℱ (fun ω s e => coeffs.γ s (Y s ω) e i))
    (h_γ_sq_Y : ∀ i : Fin n, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
        (‖coeffs.γ s (Y s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (hμX : ∀ i : Fin n, Measurable (Function.uncurry fun ω s => coeffs.μ s (X s ω) i))
    (hμY : ∀ i : Fin n, Measurable (Function.uncurry fun ω s => coeffs.μ s (Y s ω) i))
    (hXYm : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => ‖X s ω - Y s ω‖))
    (hμXsq : ∀ i : Fin n, ∀ b : ℝ, 0 < b → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
      (‖coeffs.μ s (X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hμYsq : ∀ i : Fin n, ∀ b : ℝ, 0 < b → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
      (‖coeffs.μ s (Y s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hXYsq : ∀ b : ℝ, 0 < b → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
      (‖X s ω - Y s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hZm : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => X s ω - Y s ω))
    {β : ℝ} (hβ : 0 < β) {T : ℝ} (hT : 0 < T) :
    bieleckiNorm (P := P) β T (fun t ω i =>
        picardStep (P := P) (ν := ν) (n := n) (d := d)
            W N ℱ hℱW hℱN coeffs X x₀ h_σ_meas_X h_σ_progMeas_X h_σ_sq_X
            h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω i
          - picardStep (P := P) (ν := ν) (n := n) (d := d)
            W N ℱ hℱW hℱN coeffs Y x₀ h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y
              h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω i)
      ≤ (ENNReal.ofReal
            ((3 * ((n : ℝ) * L ^ 2 * T + (n : ℝ) * ((d : ℝ) * L ^ 2) + (n : ℝ) * L ^ 2))
              / (2 * β))) ^ ((1 : ℝ) / 2)
        * bieleckiNorm (P := P) β T (fun t ω i => X t ω i - Y t ω i) := by
  have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hdn : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hCnn : (0 : ℝ)
      ≤ 3 * ((n : ℝ) * L ^ 2 * T + (n : ℝ) * ((d : ℝ) * L ^ 2) + (n : ℝ) * L ^ 2) := by
    have h1 : (0 : ℝ) ≤ (n : ℝ) * L ^ 2 * T := by positivity
    have h2 : (0 : ℝ) ≤ (n : ℝ) * ((d : ℝ) * L ^ 2) := by positivity
    have h3 : (0 : ℝ) ≤ (n : ℝ) * L ^ 2 := by positivity
    linarith
  refine bieleckiNorm_le_of_perTime hβ hCnn _ _ hZm fun t ht => ?_
  rw [lintegral_ofReal_sum_sq_eq]
  rcases ht.1.lt_or_eq with ht0 | ht0
  · refine (lintegral_sq_picardStep_diff_le W N ℱ hℱW hℱN coeffs hLip X Y x₀
      h_σ_meas_X h_σ_progMeas_X h_σ_sq_X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X
      h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y
      hμX hμY hXYm hμXsq hμYsq hXYsq ht0).trans (mul_le_mul' ?_ le_rfl)
    have hstep : ENNReal.ofReal ((n : ℝ) * L ^ 2 * t)
        ≤ ENNReal.ofReal ((n : ℝ) * L ^ 2 * T) := by
      refine ENNReal.ofReal_le_ofReal ?_
      have : (0 : ℝ) ≤ (n : ℝ) * L ^ 2 := by positivity
      nlinarith [ht.2, this]
    calc 3 * (ENNReal.ofReal ((n : ℝ) * L ^ 2 * t)
            + ENNReal.ofReal ((n : ℝ) * ((d : ℝ) * L ^ 2)) + ENNReal.ofReal ((n : ℝ) * L ^ 2))
        ≤ 3 * (ENNReal.ofReal ((n : ℝ) * L ^ 2 * T)
            + ENNReal.ofReal ((n : ℝ) * ((d : ℝ) * L ^ 2)) + ENNReal.ofReal ((n : ℝ) * L ^ 2)) :=
          mul_le_mul' le_rfl (add_le_add (add_le_add hstep le_rfl) le_rfl)
      _ = ENNReal.ofReal
            (3 * ((n : ℝ) * L ^ 2 * T + (n : ℝ) * ((d : ℝ) * L ^ 2) + (n : ℝ) * L ^ 2)) := by
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3),
            ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_ofNat]
  · have hzero : ∀ᵐ ω ∂P, ∑ i : Fin n,
        (‖picardStep (P := P) (ν := ν) (n := n) (d := d)
            W N ℱ hℱW hℱN coeffs X x₀ h_σ_meas_X h_σ_progMeas_X h_σ_sq_X
              h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω i
            - picardStep (P := P) (ν := ν) (n := n) (d := d)
            W N ℱ hℱW hℱN coeffs Y x₀ h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y
                h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω i‖₊ : ℝ≥0∞) ^ 2 = 0 := by
      filter_upwards [ae_picardStep_zero W N ℱ hℱW hℱN coeffs X x₀ h_σ_meas_X h_σ_progMeas_X
          h_σ_sq_X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X,
        ae_picardStep_zero W N ℱ hℱW hℱN coeffs Y x₀ h_σ_meas_Y h_σ_progMeas_Y
          h_σ_sq_Y h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y] with ω hX hY
      simp [← ht0, hX, hY]
    rw [lintegral_congr_ae hzero, MeasureTheory.lintegral_zero]
    exact zero_le

end Weighting

end LevyStochCalc.Ito.Picard
