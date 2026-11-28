/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Init
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Probability.Martingale.Centering
public import Mathlib.Probability.Martingale.OptionalSampling
public import Mathlib.Topology.Separation.CompletelyRegular

/-!
# Optional sampling inequality for submartingales (bounded stopping times)

Mathlib's `Martingale.stoppedValue_ae_eq_condExp_of_le` is the optional
sampling **equality** for martingales: for stopping times `σ ≤ τ` with `τ`
bounded, `f_σ =ᵐ μ[f_τ | ℱ_σ]`. For submartingales it provides only the
**expectation-form** inequality (`Submartingale.expected_stoppedValue_mono`).
The conditional-expectation inequality for submartingales is

  `stoppedValue f σ ≤ᵐ[μ] μ[stoppedValue f τ | ℱ_σ]`

The proof uses the Doob decomposition to combine the optional sampling
equality with the monotonicity of the compensator
`f = M + A` (Mathlib's `martingalePart` / `predictablePart`, used directly; their
existence-and-uniqueness statement is `Probability/Discrete/DoobDecomposition.lean`):

* the martingale part transports across stopping times by Mathlib's
  *equality* (`M_σ =ᵐ μ[M_τ | ℱ_σ]`);
* the compensator `A` of a submartingale is a.s. *nondecreasing*
  (Mathlib's `Submartingale.monotone_predictablePart` — its increments are
  `μ[f_{k+1} − f_k | ℱ_k] ≥ᵐ 0`, which is exactly the submartingale
  property), so `A_σ ≤ A_τ` pathwise and `condExp_mono` gives the
  inequality on the compensator side.

Adding the two statements yields the conditional inequality.

## Main results

* `submartingale_optional_sampling`: the optional sampling inequality
  `f_σ ≤ᵐ μ[f_τ | ℱ_σ]` for bounded stopping times `σ ≤ τ`.

`Probability/Discrete/SnellDoobDecomposition.lean` applies it to the finite-horizon Snell envelope
`snellEnvelope` (`Probability/Discrete/SnellEnvelope.lean`) at `X = univ`:
`𝔼[Z_τ | 𝓕_σ] ≤ U_σ` for stopping times `σ ≤ τ ≤ N`.

Degenne's discrete-time `Submartingale.stoppedValue_min_ae_le_condExp_nat`
proves the conditional inequality by the same decomposition. It uses `τ ⊓ σ`,
an almost-sure bound on `τ`, and a general ordered codomain.

## References

* R. Degenne, `BrownianMotion/StochasticIntegral/OptionalSampling.lean` at commit
  `497e5e2a`, the discrete-time conditional inequality.
* [Y. F. Saporito, *Stochastic Processes*][Saporito], Theorem 2.3.6, background on
  the unconditional expectation equality for a martingale at one stopping time.

## Tags

optional sampling theorem, optional stopping, submartingale, Doob decomposition,
bounded stopping times, compensator, MSC 60G42, MSC 60G40
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Filter

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
  {ℱ : Filtration ℕ m0} {f : ℕ → Ω → ℝ} {τ σ : Ω → ℕ∞} {n : ℕ}

/-- **Conditional optional sampling inequality** (Degenne, discrete time). For a
submartingale `f` and stopping times `σ ≤ τ` with `τ ≤ n` bounded,

  `stoppedValue f σ ≤ᵐ[μ] μ[stoppedValue f τ | ℱ_σ]`.

Derivation: Doob-decompose `f = martingalePart + predictablePart`. The
martingale part satisfies Mathlib's optional sampling *equality*; the
compensator is a.s. nondecreasing (Mathlib's
`Submartingale.monotone_predictablePart`), so its stopped values compare
pathwise and `condExp_mono` transports the
comparison. Summing the two statements gives the theorem. -/
theorem submartingale_optional_sampling [SigmaFiniteFiltration μ ℱ]
    (hf : Submartingale f ℱ μ)
    (hτ : IsStoppingTime ℱ τ) (hσ : IsStoppingTime ℱ σ)
    (hσ_le_τ : σ ≤ τ) (hτ_le : ∀ ω, τ ω ≤ n)
    [SigmaFinite (μ.trim hσ.measurableSpace_le)] :
    stoppedValue f σ ≤ᵐ[μ] μ[stoppedValue f τ | hσ.measurableSpace] := by
  have hσ_le : ∀ ω, σ ω ≤ n := fun ω ↦ (hσ_le_τ ω).trans (hτ_le ω)
  -- the two halves of the Doob decomposition
  have hM : Martingale (martingalePart f ℱ μ) ℱ μ :=
    martingale_martingalePart hf.1 hf.integrable
  -- stopped values split exactly along the decomposition
  have h_split : ∀ ρ : Ω → ℕ∞, stoppedValue f ρ
      = stoppedValue (martingalePart f ℱ μ) ρ
        + stoppedValue (predictablePart f ℱ μ) ρ := fun ρ ↦ by
    funext ω
    simp only [stoppedValue, Pi.add_apply, martingalePart, Pi.sub_apply,
      sub_add_cancel]
  -- integrability of all stopped values in play
  have hMτ_int : Integrable (stoppedValue (martingalePart f ℱ μ) τ) μ :=
    hM.submartingale.integrable_stoppedValue hτ hτ_le
  have hMσ_int : Integrable (stoppedValue (martingalePart f ℱ μ) σ) μ :=
    hM.submartingale.integrable_stoppedValue hσ hσ_le
  have hAτ_int : Integrable (stoppedValue (predictablePart f ℱ μ) τ) μ := by
    have h := (hf.integrable_stoppedValue hτ hτ_le).sub hMτ_int
    have h_eq : stoppedValue f τ - stoppedValue (martingalePart f ℱ μ) τ
        = stoppedValue (predictablePart f ℱ μ) τ := by
      rw [h_split τ, add_sub_cancel_left]
    rwa [h_eq] at h
  have hAσ_int : Integrable (stoppedValue (predictablePart f ℱ μ) σ) μ := by
    have h := (hf.integrable_stoppedValue hσ hσ_le).sub hMσ_int
    have h_eq : stoppedValue f σ - stoppedValue (martingalePart f ℱ μ) σ
        = stoppedValue (predictablePart f ℱ μ) σ := by
      rw [h_split σ, add_sub_cancel_left]
    rwa [h_eq] at h
  -- martingale half: optional sampling EQUALITY (Mathlib)
  have hM_eq : stoppedValue (martingalePart f ℱ μ) σ
      =ᵐ[μ] μ[stoppedValue (martingalePart f ℱ μ) τ | hσ.measurableSpace] :=
    hM.stoppedValue_ae_eq_condExp_of_le hτ hσ hσ_le_τ hτ_le
  -- compensator half: pathwise monotone, then condExp_mono
  have h_untopA_mono : ∀ ω, (σ ω).untopA ≤ (τ ω).untopA := by
    intro ω
    have hτ_ne : τ ω ≠ ⊤ := fun h ↦ by
      have hle := hτ_le ω
      rw [h] at hle
      exact WithTop.not_top_le_coe n hle
    have hσ_ne : σ ω ≠ ⊤ := fun h ↦ hτ_ne (top_le_iff.1 (h ▸ hσ_le_τ ω))
    obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.1 hσ_ne
    obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.1 hτ_ne
    have hab : a ≤ b := by
      have h := hσ_le_τ ω
      rw [← ha, ← hb] at h
      exact WithTop.coe_le_coe.1 h
    rw [← ha, ← hb]
    simpa only [WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe] using hab
  have hA_le : stoppedValue (predictablePart f ℱ μ) σ
      ≤ᵐ[μ] stoppedValue (predictablePart f ℱ μ) τ := by
    filter_upwards [hf.monotone_predictablePart] with ω hω
    exact hω (h_untopA_mono ω)
  have hAσ_meas : StronglyMeasurable[hσ.measurableSpace]
      (stoppedValue (predictablePart f ℱ μ) σ) :=
    (measurable_stoppedValue
      (stronglyAdapted_predictablePart'.isStronglyProgressive_of_discrete) hσ
      ).stronglyMeasurable
  have hAσ_eq : μ[stoppedValue (predictablePart f ℱ μ) σ | hσ.measurableSpace]
      = stoppedValue (predictablePart f ℱ μ) σ :=
    condExp_of_stronglyMeasurable hσ.measurableSpace_le hAσ_meas hAσ_int
  have hA_condExp_le :
      μ[stoppedValue (predictablePart f ℱ μ) σ | hσ.measurableSpace]
        ≤ᵐ[μ] μ[stoppedValue (predictablePart f ℱ μ) τ | hσ.measurableSpace] :=
    condExp_mono hAσ_int hAτ_int hA_le
  -- assemble: f_σ = M_σ + A_σ ≤ᵐ μ[M_τ|ℱ_σ] + μ[A_τ|ℱ_σ] =ᵐ μ[f_τ|ℱ_σ]
  have h_condExp_split : μ[stoppedValue f τ | hσ.measurableSpace]
      =ᵐ[μ] μ[stoppedValue (martingalePart f ℱ μ) τ | hσ.measurableSpace]
        + μ[stoppedValue (predictablePart f ℱ μ) τ | hσ.measurableSpace] := by
    rw [h_split τ]
    exact condExp_add hMτ_int hAτ_int _
  rw [h_split σ]
  filter_upwards [hM_eq, hA_condExp_le, h_condExp_split] with ω hMω hAω hsplitω
  have hAσω : stoppedValue (predictablePart f ℱ μ) σ ω
      = μ[stoppedValue (predictablePart f ℱ μ) σ | hσ.measurableSpace] ω := by
    rw [hAσ_eq]
  simp only [Pi.add_apply] at hsplitω ⊢
  rw [hsplitω, hMω, hAσω]
  exact add_le_add le_rfl hAω

end MathFin
