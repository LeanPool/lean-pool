/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import LeanPool.KLS.LevyStochCalc.Brownian.ItoLinear
public import LeanPool.KLS.LevyStochCalc.Brownian.ItoAlgebra
public import LeanPool.KLS.LevyStochCalc.Brownian.ItoZero

/-!
# Linearity of the Itô integral over finite sums

Additivity and scaling give the negation, the difference and the sum over a finite index set.
The finite sum is stated existentially in the admissibility data of the summed integrand, which
the induction produces along with the identity.

## Main statements

* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_neg`
* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_sub`
* `LevyStochCalc.Brownian.Ito.exists_stochasticIntegralBrownian_finsetSum`
-/

@[expose] public section

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
/-- The square-integrability of an integrand transfers along an equality of integrands. -/
theorem energy_lt_top_congr {F₁ F₂ : Ω → ℝ → ℝ} (h : F₁ = F₂)
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖F₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖F₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  subst h
  exact hq

variable (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)

include hℱ in
/-- **The Itô integral negates with its integrand.** -/
theorem stochasticIntegralBrownian_neg {H : Ω → ℝ → ℝ}
    (hm : Measurable (Function.uncurry H)) (hp : Probability.ProgressivelyMeasurable ℱ H)
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hmn : Measurable (Function.uncurry fun ω s => -H ω s))
    (hpn : Probability.ProgressivelyMeasurable ℱ fun ω s => -H ω s)
    (hqn : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖-H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    stochasticIntegralBrownian W ℱ hℱ (fun ω s => -H ω s) hmn hpn hqn T
      =ᵐ[P] fun ω => -stochasticIntegralBrownian W ℱ hℱ H hm hp hq T ω := by
  have hfun : (fun (ω : Ω) (s : ℝ) => -H ω s) = fun ω s => (-1 : ℝ) * H ω s := by
    funext ω s
    ring
  have hmc : Measurable (Function.uncurry fun ω s => (-1 : ℝ) * H ω s) := hfun ▸ hmn
  have hpc : Probability.ProgressivelyMeasurable ℱ fun ω s => (-1 : ℝ) * H ω s := hfun ▸ hpn
  have hqc : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖(-1 : ℝ) * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := energy_lt_top_congr hfun hqn
  rw [stochasticIntegralBrownian_congr_fun W ℱ hℱ hfun hmn hpn hqn hmc hpc hqc T]
  filter_upwards [stochasticIntegralBrownian_const_mul W ℱ hℱ hm hp hq (-1) hmc hpc hqc hT]
    with ω hω
  rw [hω]
  ring

include hℱ in
/-- **The Itô integral is additive in its integrand, in the subtractive form.** -/
theorem stochasticIntegralBrownian_sub {H₁ H₂ : Ω → ℝ → ℝ}
    (hm₁ : Measurable (Function.uncurry H₁)) (hm₂ : Measurable (Function.uncurry H₂))
    (hp₁ : Probability.ProgressivelyMeasurable ℱ H₁)
    (hp₂ : Probability.ProgressivelyMeasurable ℱ H₂)
    (hq₁ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hq₂ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hms : Measurable (Function.uncurry fun ω s => H₁ ω s - H₂ ω s))
    (hps : Probability.ProgressivelyMeasurable ℱ fun ω s => H₁ ω s - H₂ ω s)
    (hqs : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₁ ω s - H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    stochasticIntegralBrownian W ℱ hℱ (fun ω s => H₁ ω s - H₂ ω s) hms hps hqs T
      =ᵐ[P] fun ω => stochasticIntegralBrownian W ℱ hℱ H₁ hm₁ hp₁ hq₁ T ω
        - stochasticIntegralBrownian W ℱ hℱ H₂ hm₂ hp₂ hq₂ T ω := by
  have hnegfun : (fun (ω : Ω) (s : ℝ) => -H₂ ω s) = fun ω s => (0 : ℝ) - H₂ ω s := by
    funext ω s
    ring
  have hmn : Measurable (Function.uncurry fun ω s => -H₂ ω s) := hm₂.neg
  have hpn : Probability.ProgressivelyMeasurable ℱ fun ω s => -H₂ ω s := by
    have hz : Probability.ProgressivelyMeasurable ℱ fun (_ : Ω) (_ : ℝ) => (0 : ℝ) :=
      Probability.progressivelyMeasurable_zero ℱ
    exact hnegfun ▸ hz.sub hp₂
  have hqn : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖-H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
    intro T' hT'
    have hcongr : ∀ (ω : Ω) (s : ℝ), (‖-H₂ ω s‖₊ : ℝ≥0∞) ^ 2 = (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 := by
      intro ω s
      simp
    calc ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', (‖-H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
        = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P :=
          lintegral_congr fun ω => lintegral_congr fun s => hcongr ω s
      _ < ⊤ := hq₂ T' hT'
  have hsubfun : (fun (ω : Ω) (s : ℝ) => H₁ ω s - H₂ ω s)
      = fun ω s => H₁ ω s + -H₂ ω s := by
    funext ω s
    ring
  have hma : Measurable (Function.uncurry fun ω s => H₁ ω s + -H₂ ω s) := hsubfun ▸ hms
  have hpa : Probability.ProgressivelyMeasurable ℱ fun ω s => H₁ ω s + -H₂ ω s := hsubfun ▸ hps
  have hqa : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₁ ω s + -H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := energy_lt_top_congr hsubfun hqs
  rw [stochasticIntegralBrownian_congr_fun W ℱ hℱ hsubfun hms hps hqs hma hpa hqa T]
  filter_upwards [stochasticIntegralBrownian_add W ℱ hℱ hm₁ hmn hp₁ hpn hq₁ hqn hma hpa hqa hT,
    stochasticIntegralBrownian_neg W ℱ hℱ hm₂ hp₂ hq₂ hmn hpn hqn hT] with ω hadd hneg
  rw [hadd, hneg]
  ring

include hℱ in
/-- **The Itô integral of a finite sum of integrands is the sum of their integrals.** -/
theorem exists_stochasticIntegralBrownian_finsetSum {ι : Type*}
    (H : ι → Ω → ℝ → ℝ) (hm : ∀ i, Measurable (Function.uncurry (H i)))
    (hp : ∀ i, Probability.ProgressivelyMeasurable ℱ (H i))
    (hq : ∀ (i : ι) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H i ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (J : Finset ι) {T : ℝ} (hT : 0 < T) :
    ∃ (hms : Measurable (Function.uncurry fun ω u => ∑ i ∈ J, H i ω u))
      (hps : Probability.ProgressivelyMeasurable ℱ fun ω u => ∑ i ∈ J, H i ω u)
      (hqs : ∀ T', 0 < T' → ∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) T',
        (‖∑ i ∈ J, H i ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤),
      stochasticIntegralBrownian W ℱ hℱ (fun ω u => ∑ i ∈ J, H i ω u) hms hps hqs T
        =ᵐ[P] fun ω => ∑ i ∈ J,
          stochasticIntegralBrownian W ℱ hℱ (H i) (hm i) (hp i) (hq i) T ω := by
  classical
  induction J using Finset.induction with
  | empty =>
    have hfun : (fun (ω : Ω) (u : ℝ) => ∑ i ∈ (∅ : Finset ι), H i ω u)
        = fun (_ : Ω) (_ : ℝ) => (0 : ℝ) := by
      funext ω u
      simp
    have hmz : Measurable (Function.uncurry fun (_ : Ω) (_ : ℝ) => (0 : ℝ)) := measurable_const
    have hpz : Probability.ProgressivelyMeasurable ℱ fun (_ : Ω) (_ : ℝ) => (0 : ℝ) :=
      Probability.progressivelyMeasurable_zero ℱ
    have hqz : ∀ T', 0 < T' → ∫⁻ ω, ∫⁻ _u in Set.Icc (0 : ℝ) T',
        (‖(0 : ℝ)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
      intro T' _
      simp
    have hqz' := energy_lt_top_congr (P := P) hfun.symm hqz
    refine ⟨hfun ▸ hmz, hfun ▸ hpz, hqz', ?_⟩
    rw [stochasticIntegralBrownian_congr_fun W ℱ hℱ hfun (hfun ▸ hmz) (hfun ▸ hpz) hqz'
      hmz hpz hqz T]
    filter_upwards [stochasticIntegralBrownian_ae_zero W ℱ hℱ hmz hpz hqz T] with ω hω
    simpa using hω
  | insert a J ha ih =>
    obtain ⟨hms, hps, hqs, hae⟩ := ih
    have hfun : (fun (ω : Ω) (u : ℝ) => ∑ i ∈ insert a J, H i ω u)
        = fun ω u => H a ω u + ∑ i ∈ J, H i ω u := by
      funext ω u
      exact Finset.sum_insert ha
    have hma : Measurable (Function.uncurry fun ω u => H a ω u + ∑ i ∈ J, H i ω u) :=
      (hm a).add hms
    have hpa : Probability.ProgressivelyMeasurable ℱ
        fun ω u => H a ω u + ∑ i ∈ J, H i ω u := (hp a).add hps
    have hqa : ∀ T', 0 < T' → ∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) T',
        (‖H a ω u + ∑ i ∈ J, H i ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
      lintegral_energy_lt_top_of_bound (fun ω u => sq_nnnorm_add_le_two_mul _ _) (hm a) hms
        (hq a) hqs
    have hqi := energy_lt_top_congr (P := P) hfun.symm hqa
    refine ⟨hfun ▸ hma, hfun ▸ hpa, hqi, ?_⟩
    rw [stochasticIntegralBrownian_congr_fun W ℱ hℱ hfun (hfun ▸ hma) (hfun ▸ hpa) hqi
      hma hpa hqa T]
    filter_upwards [stochasticIntegralBrownian_add W ℱ hℱ (hm a) hms (hp a) hps (hq a) hqs
      hma hpa hqa hT, hae] with ω hadd hsum
    rw [hadd, hsum, Finset.sum_insert ha]

end LevyStochCalc.Brownian.Ito
