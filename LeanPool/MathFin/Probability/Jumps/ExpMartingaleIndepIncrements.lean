/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Init
public import Mathlib.Probability.ConditionalExpectation
public import Mathlib.Probability.Martingale.Basic

/-!
# The exponential martingale of a process with independent increments

Let a real process `X` be adapted to a filtration `𝓕`, with each increment `X_t − X_s` (`s ≤ t`)
independent of `𝓕_s` and with exponential moment `𝔼[e^{X_t − X_s}] = e^{ψ(t) − ψ(s)}` for a
deterministic `ψ`, and with each `e^{X_t}` integrable. Then `t ↦ e^{X_t − ψ(t)}` is an
`𝓕`-martingale. The increment factor
`e^{ψ(s) − ψ(t)}·e^{X_t − X_s}` is independent of `𝓕_s`, so its conditional expectation is its
mean, `1` (`condExp_indep_eq`); the factor `e^{X_s − ψ(s)}` is known at time `s` and comes out of
the conditional expectation (`condExp_mul_of_stronglyMeasurable_left`).

For a Lévy process started at `0`, `ψ(t) = t·log 𝔼[e^{X_1}]` is linear in `t`. The Wald
martingale of Brownian motion is the case `αX`, `ψ(t) = α²t/2`, and is derived from this lemma
(`IsFilteredPreBrownian.waldExponential_isMartingale`,
`Probability/Brownian/BrownianMartingale.lean`);
`Models/Jumps/JumpDiffusionProcess.lean` applies it to the log-price of a jump-diffusion.

## Main results

* `condExp_exp_eq_of_indep_increment`: `𝔼[e^{X_t} | 𝓕_s] = e^{X_s}·𝔼[e^{X_t − X_s}]` for an
  increment independent of `𝓕_s`.
* `martingale_exp_sub_of_indep_increments`: `t ↦ e^{X_t − ψ(t)}` is an `𝓕`-martingale when each
  increment is independent of the past with `𝔼[e^{X_t − X_s}] = e^{ψ(t) − ψ(s)}` and each
  `e^{X_t}` is integrable.

## References

* [Cont and Tankov, *Financial Modelling with Jump Processes*][ContTankov2004]
* [Y. F. Saporito, *Stochastic Processes*][Saporito], Remark 5.1.6

## Tags

exponential martingale, Lévy process, independent increments, Wald martingale, jump-diffusion,
MSC 60G51, MSC 60G44
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory

variable {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P] [Preorder ι]
  {𝓕 : Filtration ι mΩ} {X : ι → Ω → ℝ}

/-- **The conditional exponential moment of a later value.** If the increment `X_t − X_s` is
independent of `𝓕_s`, then `𝔼[e^{X_t} | 𝓕_s] = e^{X_s}·𝔼[e^{X_t − X_s}]`: the factor `e^{X_s}` is
known at time `s` and comes out, and the increment factor is replaced by its mean. -/
theorem condExp_exp_eq_of_indep_increment {s t : ι} (hX : StronglyAdapted 𝓕 X)
    (hindep : Indep (MeasurableSpace.comap (fun ω ↦ X t ω - X s ω) inferInstance) (𝓕 s) P)
    (hint : Integrable (fun ω ↦ Real.exp (X t ω)) P)
    (hD_int : Integrable (fun ω ↦ Real.exp (X t ω - X s ω)) P) :
    P[fun ω ↦ Real.exp (X t ω) | 𝓕 s]
      =ᵐ[P] fun ω ↦ Real.exp (X s ω) * ∫ ω', Real.exp (X t ω' - X s ω') ∂P := by
  have hD : Measurable fun ω ↦ X t ω - X s ω :=
    ((hX t).mono (𝓕.le t)).measurable.sub ((hX s).mono (𝓕.le s)).measurable
  have hsplit : (fun ω ↦ Real.exp (X t ω))
      = (fun ω ↦ Real.exp (X s ω)) * fun ω ↦ Real.exp (X t ω - X s ω) := by
    funext ω
    change Real.exp (X t ω) = Real.exp (X s ω) * Real.exp (X t ω - X s ω)
    rw [← Real.exp_add]
    congr 1
    ring
  -- the increment factor is independent of `𝓕_s`: its conditional expectation is its mean
  have hD_cond : P[fun ω ↦ Real.exp (X t ω - X s ω) | 𝓕 s]
      =ᵐ[P] fun _ ↦ ∫ ω', Real.exp (X t ω' - X s ω') ∂P := by
    have hm : StronglyMeasurable[MeasurableSpace.comap (fun ω ↦ X t ω - X s ω) inferInstance]
        fun ω ↦ Real.exp (X t ω - X s ω) :=
      (Real.continuous_exp.measurable.comp (Measurable.of_comap_le le_rfl)).stronglyMeasurable
    exact condExp_indep_eq hD.comap_le (𝓕.le s) hm hindep
  -- `e^{X_s}` is known at time `s` and comes out
  have hpull := condExp_mul_of_stronglyMeasurable_left
    (Real.continuous_exp.comp_stronglyMeasurable (hX s)) (by rw [← hsplit]; exact hint) hD_int
  rw [hsplit]
  filter_upwards [hpull, hD_cond] with ω h1 h2
  rw [h1, Pi.mul_apply, h2]

/-- **The exponential martingale of a process with independent increments.** If `X` is adapted
to `𝓕`, each increment `X_t − X_s` (`s ≤ t`) is independent of `𝓕_s` with
`𝔼[e^{X_t − X_s}] = e^{ψ(t) − ψ(s)}`, and each `e^{X_t}` is integrable, then `t ↦ e^{X_t − ψ(t)}`
is an `𝓕`-martingale: by `condExp_exp_eq_of_indep_increment`,
`𝔼[e^{X_t − ψ(t)} | 𝓕_s] = e^{−ψ(t)}e^{X_s}e^{ψ(t) − ψ(s)} = e^{X_s − ψ(s)}`. -/
theorem martingale_exp_sub_of_indep_increments {ψ : ι → ℝ} (hX : StronglyAdapted 𝓕 X)
    (hindep : ∀ s t, s ≤ t →
      Indep (MeasurableSpace.comap (fun ω ↦ X t ω - X s ω) inferInstance) (𝓕 s) P)
    (hint : ∀ t, Integrable (fun ω ↦ Real.exp (X t ω)) P)
    (hmean : ∀ s t, s ≤ t → ∫ ω, Real.exp (X t ω - X s ω) ∂P = Real.exp (ψ t - ψ s)) :
    Martingale (fun t ω ↦ Real.exp (X t ω - ψ t)) 𝓕 P := by
  refine ⟨fun t ↦ Real.continuous_exp.comp_stronglyMeasurable
    ((hX t).sub stronglyMeasurable_const), fun s t hst ↦ ?_⟩
  have hfun : (fun ω ↦ Real.exp (X t ω - ψ t)) = Real.exp (-ψ t) • fun ω ↦ Real.exp (X t ω) := by
    funext ω
    rw [Pi.smul_apply, smul_eq_mul, ← Real.exp_add, neg_add_eq_sub]
  have hsmul : P[Real.exp (-ψ t) • fun ω ↦ Real.exp (X t ω) | 𝓕 s]
      =ᵐ[P] Real.exp (-ψ t) • P[fun ω ↦ Real.exp (X t ω) | 𝓕 s] :=
    condExp_smul _ _ _
  have hcond := condExp_exp_eq_of_indep_increment hX (hindep s t hst) (hint t)
    (Integrable.of_integral_ne_zero (by rw [hmean s t hst]; exact (Real.exp_pos _).ne'))
  change P[fun ω ↦ Real.exp (X t ω - ψ t) | 𝓕 s] =ᵐ[P] fun ω ↦ Real.exp (X s ω - ψ s)
  rw [hfun]
  filter_upwards [hsmul, hcond] with ω h1 h2
  rw [h1, Pi.smul_apply, h2, hmean s t hst, smul_eq_mul, ← mul_assoc, ← Real.exp_add,
    ← Real.exp_add]
  congr 1
  ring

end MathFin
