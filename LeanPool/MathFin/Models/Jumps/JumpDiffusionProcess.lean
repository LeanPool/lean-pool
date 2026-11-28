/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.Jumps.JumpDiffusionCanonical
public import LeanPool.MathFin.Probability.Jumps.ExpMartingaleIndepIncrements

/-!
# The jump-diffusion price process

The other jump-diffusion files model only the price at maturity. Here the log-price is a process
`X` on `[0, ∞)`, adapted to a filtration `𝓕`, starting at `0`, whose increment `X_t − X_s` over
`[s, t]` is independent of `𝓕_s` and has the law of a jump-diffusion log-return over `t − s`: a
drift `b(t − s)`, a Gaussian part of variance `σ²(t − s)` and a compound-Poisson part with
`Poisson(Λ(t − s))` jumps of law `ν` (`JumpDiffusionProcess`); here `Λ` is a jump rate. The
increments are those of a Lévy process with these characteristics; no path regularity is assumed.
Without jumps, Brownian motion with drift is such a process
(`IsFilteredPreBrownian.jumpDiffusionProcess`); with jumps its existence is not proved.

The log-return over `τ` has the moment-generating function `e^{κ(θ)τ}` at every `θ` with
`∫ e^{θx} dν < ∞`, where `κ(θ) = bθ + σ²θ²/2 + Λ(∫ e^{θx} dν − 1)` is the Laplace exponent
(`jumpDiffusionExponent`). On the canonical model it is the Gaussian moment-generating function
times the compound-Poisson one (`JumpDiffusionHyp.mgf_logReturn`, `compoundPoisson_mgf_of_indepFun`
from `Probability/Jumps/CompoundPoissonMGF.lean`), by independence; in Mathlib's terms `κ(θ)τ` is
the cumulant generating function (`cgf_id_jumpDiffusionIncrementLaw`).

The price `S_t = S₀e^{X_t}` discounted at the rate `r` is a martingale exactly at the compensated
drift `b = r − σ²/2 − Λ(𝔼[e^J] − 1)` (`JumpDiffusionProcess.martingale_iff`). The increment's
exponential moment is `e^{(b + σ²/2 + Λ(𝔼[e^J] − 1))(t − s)}`
(`integral_exp_jumpDiffusionIncrementLaw`, the case `θ = 1`), so the exponential martingale of
independent increments (`martingale_exp_sub_of_indep_increments`) gives the "if"; conversely a
martingale has constant mean, and the mean at time `1` is `S₀e^{b + σ²/2 + Λ(𝔼[e^J] − 1) − r}`.

## Main definitions

* `jumpDiffusionLogReturn`: the log-return over a time `τ` on the canonical space
  `ℝ × ℕ × (ℕ → ℝ)`, built from the drift `bτ`, the Gaussian part `σ√τ·ω₁` and the jumps.
* `jumpDiffusionIncrementLaw`: the law of that log-return over `τ`, with drift `b`, volatility `σ`,
  jump rate `Λ` and jump law `ν`.
* `jumpDiffusionExponent`: the Laplace exponent `κ(θ) = bθ + σ²θ²/2 + Λ(∫ e^{θx} dν − 1)`.
* `JumpDiffusionProcess`: a log-price process adapted to a filtration, starting at `0`, whose
  increment over `[s, t]` is independent of `𝓕_s` and has the jump-diffusion log-return law over
  `t − s`.

## Main results

* `integral_exp_const_mul_jumpDiffusionIncrementLaw`, `mgf_id_jumpDiffusionIncrementLaw`,
  `cgf_id_jumpDiffusionIncrementLaw`: for `θ` with `∫ e^{θx} dν < ∞`, its moment-generating
  function is `e^{κ(θ)τ}`.
* `integrableExpSet_id_subset_jumpDiffusionIncrementLaw`,
  `zero_mem_interior_integrableExpSet_jumpDiffusionIncrementLaw`,
  `cgf_id_jumpDiffusionIncrementLaw_eventuallyEq`: the jumps' exponential moments pass to the
  log-return, and near `0` its cumulant generating function is `κ(θ)τ`.
* `hasDerivAt_jumpDiffusionExponent`: `κ'(θ) = b + σ²θ + ΛM'(θ)`, with `M` the jump law's
  moment-generating function.
* `integral_exp_jumpDiffusionIncrementLaw_of_compensated`: at the compensated drift the forward is
  the mean, `∫ eʸ = e^{rτ}`.
* `JumpDiffusionProcess.hasLaw`: `X_t` has the log-return law over `t`.
* `JumpDiffusionProcess.martingale_iff`: for `S₀ ≠ 0` and integrable `e^J`, the discounted price
  is a martingale if and only if the drift is compensated, `b = r − σ²/2 − Λ(𝔼[e^J] − 1)`.

## References

* [Cont and Tankov, *Financial Modelling with Jump Processes*][ContTankov2004]
* [R. C. Merton, *Option pricing when underlying stock returns are discontinuous*][Merton1976]

## Tags

jump-diffusion process, independent increments, Lévy process, filtered log-price, Merton model,
MSC 60G51, MSC 91G20
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

/-! ### The increment law -/

namespace JumpDiffusionHyp

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {Q : Measure Ω} {Λ : ℝ≥0} {Z : Ω → ℝ}
  {N : Ω → ℕ} {J : ℕ → Ω → ℝ}

/-- **The moment-generating function of a jump-diffusion log-return.** For `θ` with
`𝔼[e^{θJ}] < ∞`, `𝔼[e^{θ(bT + σ√T·Z + ∑_{i<N} Jᵢ)}] = e^{(bθ + σ²θ²/2)T + Λ(𝔼[e^{θJ}] − 1)}`. The
drift contributes `e^{θbT}`; the Gaussian part its moment-generating function `e^{σ²θ²T/2}`
(`mgf_gaussianReal`); and, independently of it (`IndepFun.mgf_add'`), the compound-Poisson part
its moment-generating function `e^{Λ(𝔼[e^{θJ}] − 1)}` (`compoundPoisson_mgf_of_indepFun`, the
aggregate-loss MGF of `Probability/Jumps/CompoundPoissonMGF.lean`). -/
lemma mgf_logReturn (h : JumpDiffusionHyp Q Λ Z N J) {θ : ℝ}
    (hJ : Integrable (fun ω ↦ rexp (θ * J 0 ω)) Q) (b σ : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    mgf (fun ω ↦ b * T + σ * Real.sqrt T * Z ω + ∑ i ∈ Finset.range (N ω), J i ω) Q θ
      = rexp ((b * θ + σ ^ 2 * θ ^ 2 / 2) * T + Λ * (mgf (J 0) Q θ - 1)) := by
  have hind : IndepFun (fun ω ↦ σ * Real.sqrt T * Z ω)
      (fun ω ↦ ∑ i ∈ Finset.range (N ω), J i ω) Q :=
    h.Z_indep_jumps.comp (measurable_const_mul (σ * Real.sqrt T)) measurable_sum_range_prod
  have hS : AEMeasurable (fun ω ↦ ∑ i ∈ Finset.range (N ω), J i ω) Q :=
    measurable_sum_range_prod.comp_aemeasurable
      (h.N_law.aemeasurable.prodMk h.aemeasurable_jumps)
  have hsplit : (fun ω ↦ b * T + σ * Real.sqrt T * Z ω + ∑ i ∈ Finset.range (N ω), J i ω)
      = fun ω ↦ b * T + ((fun ω ↦ σ * Real.sqrt T * Z ω)
          + fun ω ↦ ∑ i ∈ Finset.range (N ω), J i ω) ω := by
    funext ω
    simp only [Pi.add_apply]
    ring
  rw [hsplit, mgf_const_add, hind.mgf_add' (h.Z_law.aemeasurable.const_mul _).aestronglyMeasurable
      hS.aestronglyMeasurable, mgf_const_mul, mgf_gaussianReal h.Z_law,
    compoundPoisson_mgf_of_indepFun Λ θ J h.N_law h.J_indep h.J_ident h.N_indep_J hJ,
    ← Real.exp_add, ← Real.exp_add]
  congr 1
  simp only [mul_pow, Real.sq_sqrt hT, NNReal.coe_one]
  ring

/-- `JumpDiffusionHyp.mgf_logReturn` as an integral. -/
lemma integral_exp_mul_logReturn (h : JumpDiffusionHyp Q Λ Z N J) {θ : ℝ}
    (hJ : Integrable (fun ω ↦ rexp (θ * J 0 ω)) Q) (b σ : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    ∫ ω, rexp (θ * (b * T + σ * Real.sqrt T * Z ω + ∑ i ∈ Finset.range (N ω), J i ω)) ∂Q
      = rexp ((b * θ + σ ^ 2 * θ ^ 2 / 2) * T + Λ * (∫ ω, rexp (θ * J 0 ω) ∂Q - 1)) :=
  h.mgf_logReturn hJ b σ hT

end JumpDiffusionHyp

/-- The jump-diffusion log-return over a time `τ` on the canonical space `ℝ × ℕ × (ℕ → ℝ)`: the
drift `bτ`, the Gaussian part `σ√τ·ω₁` and the jumps `∑_{i<ω₂} ω₃ᵢ`. -/
noncomputable def jumpDiffusionLogReturn (b σ : ℝ) (τ : ℝ≥0) (ω : ℝ × ℕ × (ℕ → ℝ)) : ℝ :=
  b * τ + σ * Real.sqrt τ * ω.1 + ∑ i ∈ Finset.range ω.2.1, ω.2.2 i

/-- The log-return is measurable on the canonical space. -/
lemma measurable_jumpDiffusionLogReturn (b σ : ℝ) (τ : ℝ≥0) :
    Measurable (jumpDiffusionLogReturn b σ τ) :=
  (measurable_const.add (measurable_const.mul measurable_fst)).add
    (measurable_sum_range_prod.comp measurable_snd)

/-- The law of a jump-diffusion log-return over a time `τ`: the drift `bτ`, a Gaussian part
`σ√τ·Z` and a compound-Poisson part, a `Poisson(Λτ)` number of independent jumps of law `ν`, all
independent. It is the law of `jumpDiffusionLogReturn` under the canonical model
`jumpDiffusionMeasure (Λτ) ν`. -/
noncomputable def jumpDiffusionIncrementLaw (b σ : ℝ) (Λ : ℝ≥0) (ν : Measure ℝ) (τ : ℝ≥0) :
    Measure ℝ :=
  (jumpDiffusionMeasure (Λ * τ) ν).map (jumpDiffusionLogReturn b σ τ)

instance isProbabilityMeasure_jumpDiffusionIncrementLaw (b σ : ℝ) (Λ : ℝ≥0) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (τ : ℝ≥0) :
    IsProbabilityMeasure (jumpDiffusionIncrementLaw b σ Λ ν τ) :=
  inferInstanceAs
    (IsProbabilityMeasure ((jumpDiffusionMeasure (Λ * τ) ν).map (jumpDiffusionLogReturn b σ τ)))

/-- **The Laplace exponent of a jump-diffusion**, `κ(θ) = bθ + σ²θ²/2 + Λ(∫ e^{θx} dν − 1)`. For
`θ` with `∫ e^{θx} dν < ∞` it is the cumulant generating function of the log-return per unit
time: `𝔼[e^{θY}] = e^{κ(θ)τ}` (`integral_exp_const_mul_jumpDiffusionIncrementLaw`,
`cgf_id_jumpDiffusionIncrementLaw`). Where `∫ e^{θx} dν = ∞` the Bochner integral is `0` by
convention and `κ(θ)` is not a cumulant. -/
noncomputable def jumpDiffusionExponent (b σ : ℝ) (Λ : ℝ≥0) (ν : Measure ℝ) (θ : ℝ) : ℝ :=
  b * θ + σ ^ 2 * θ ^ 2 / 2 + Λ * (∫ x, rexp (θ * x) ∂ν - 1)

/-- **The exponential moments of the jump-diffusion increment law.** For `θ` with
`∫ e^{θx} dν < ∞`, `∫ e^{θy} dμ_τ(y) = e^{κ(θ)τ}`, with `μ_τ` the log-return law over `τ`. On the
canonical model this is `JumpDiffusionHyp.mgf_logReturn`: the Gaussian moment-generating function
times the compound-Poisson one. -/
theorem integral_exp_const_mul_jumpDiffusionIncrementLaw (b σ : ℝ) (Λ : ℝ≥0) {ν : Measure ℝ}
    [IsProbabilityMeasure ν] {θ : ℝ} (hν : Integrable (fun x ↦ rexp (θ * x)) ν) (τ : ℝ≥0) :
    ∫ y, rexp (θ * y) ∂(jumpDiffusionIncrementLaw b σ Λ ν τ)
      = rexp (jumpDiffusionExponent b σ Λ ν θ * τ) := by
  rw [jumpDiffusionIncrementLaw, integral_map
    (measurable_jumpDiffusionLogReturn b σ τ).aemeasurable
    (measurable_const_mul θ).exp.aestronglyMeasurable]
  unfold jumpDiffusionLogReturn
  rw [(jumpDiffusionHyp_canonical (Λ * τ) ν).1.integral_exp_mul_logReturn
      (integrable_exp_mul_canonical_jump hν) b σ (NNReal.coe_nonneg τ),
    integral_exp_mul_canonical_jump (Λ * τ) ν θ, jumpDiffusionExponent, NNReal.coe_mul]
  congr 1
  ring

/-- The log-return law has the exponential moment of order `θ` when the jump law does: its
integral is positive. -/
lemma integrable_exp_mul_jumpDiffusionIncrementLaw (b σ : ℝ) (Λ : ℝ≥0) {ν : Measure ℝ}
    [IsProbabilityMeasure ν] {θ : ℝ} (hν : Integrable (fun x ↦ rexp (θ * x)) ν) (τ : ℝ≥0) :
    Integrable (fun y ↦ rexp (θ * y)) (jumpDiffusionIncrementLaw b σ Λ ν τ) :=
  Integrable.of_integral_ne_zero (by
    rw [integral_exp_const_mul_jumpDiffusionIncrementLaw b σ Λ hν τ]
    exact (Real.exp_pos _).ne')

/-- The moment-generating function of the log-return law, in Mathlib's terms:
`mgf id μ_τ θ = e^{κ(θ)τ}`. -/
lemma mgf_id_jumpDiffusionIncrementLaw (b σ : ℝ) (Λ : ℝ≥0) {ν : Measure ℝ}
    [IsProbabilityMeasure ν] {θ : ℝ} (hν : Integrable (fun x ↦ rexp (θ * x)) ν) (τ : ℝ≥0) :
    mgf id (jumpDiffusionIncrementLaw b σ Λ ν τ) θ = rexp (jumpDiffusionExponent b σ Λ ν θ * τ) :=
  integral_exp_const_mul_jumpDiffusionIncrementLaw b σ Λ hν τ

/-- **`κ` is the cumulant generating function per unit time**: `cgf id μ_τ θ = κ(θ)τ` (Mathlib's
`cgf`), for `θ` with `∫ e^{θx} dν < ∞`. -/
lemma cgf_id_jumpDiffusionIncrementLaw (b σ : ℝ) (Λ : ℝ≥0) {ν : Measure ℝ}
    [IsProbabilityMeasure ν] {θ : ℝ} (hν : Integrable (fun x ↦ rexp (θ * x)) ν) (τ : ℝ≥0) :
    cgf id (jumpDiffusionIncrementLaw b σ Λ ν τ) θ = jumpDiffusionExponent b σ Λ ν θ * τ := by
  rw [cgf, mgf_id_jumpDiffusionIncrementLaw b σ Λ hν τ, Real.log_exp]

/-- **The exponential moment of the jump-diffusion increment law**:
`∫ e^x d(law over τ) = e^{(b + σ²/2 + Λ(𝔼[e^J] − 1))τ}` when `𝔼[e^J] < ∞` under the jump law `ν`;
the case `θ = 1` of `integral_exp_const_mul_jumpDiffusionIncrementLaw`. -/
theorem integral_exp_jumpDiffusionIncrementLaw (b σ : ℝ) (Λ : ℝ≥0) {ν : Measure ℝ}
    [IsProbabilityMeasure ν] (hν : Integrable rexp ν) (τ : ℝ≥0) :
    ∫ x, rexp x ∂(jumpDiffusionIncrementLaw b σ Λ ν τ)
      = rexp ((b + σ ^ 2 / 2 + Λ * (∫ x, rexp x ∂ν - 1)) * τ) := by
  simpa only [jumpDiffusionExponent, one_mul, mul_one, one_pow] using
    integral_exp_const_mul_jumpDiffusionIncrementLaw b σ Λ (ν := ν) (θ := 1)
      (by simpa only [one_mul] using hν) τ

/-- The exponential of the log-return is integrable when `𝔼[e^J] < ∞`
(`integrable_exp_mul_jumpDiffusionIncrementLaw` at `θ = 1`). -/
lemma integrable_exp_jumpDiffusionIncrementLaw (b σ : ℝ) (Λ : ℝ≥0) {ν : Measure ℝ}
    [IsProbabilityMeasure ν] (hν : Integrable rexp ν) (τ : ℝ≥0) :
    Integrable rexp (jumpDiffusionIncrementLaw b σ Λ ν τ) := by
  simpa only [one_mul] using integrable_exp_mul_jumpDiffusionIncrementLaw b σ Λ (ν := ν) (θ := 1)
    (by simpa only [one_mul] using hν) τ

/-- **At the compensated drift the forward is the mean**: when `b = r − σ²/2 − Λ(𝔼[e^J] − 1)` and
`𝔼[e^J] < ∞`, `∫ eʸ d(law over τ) = e^{rτ}` (`integral_exp_jumpDiffusionIncrementLaw`). -/
lemma integral_exp_jumpDiffusionIncrementLaw_of_compensated {b r σ : ℝ} {Λ : ℝ≥0}
    {ν : Measure ℝ} [IsProbabilityMeasure ν] (hν : Integrable rexp ν)
    (hb : b = r - σ ^ 2 / 2 - Λ * (∫ x, rexp x ∂ν - 1)) (τ : ℝ≥0) :
    ∫ x, rexp x ∂(jumpDiffusionIncrementLaw b σ Λ ν τ) = rexp (r * τ) := by
  rw [integral_exp_jumpDiffusionIncrementLaw b σ Λ hν τ, hb]
  congr 1
  ring

/-- **The jumps' exponential moments pass to the log-return**: wherever `∫ e^{θx} dν < ∞`, also
`∫ e^{θy} < ∞` under the log-return law (`integrable_exp_mul_jumpDiffusionIncrementLaw`). -/
lemma integrableExpSet_id_subset_jumpDiffusionIncrementLaw (b σ : ℝ) (Λ : ℝ≥0) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (τ : ℝ≥0) :
    integrableExpSet id ν ⊆ integrableExpSet id (jumpDiffusionIncrementLaw b σ Λ ν τ) :=
  fun θ hθ ↦ integrable_exp_mul_jumpDiffusionIncrementLaw (ν := ν) (θ := θ) b σ Λ hθ τ

/-- **A moment-generating function finite near `0` passes from the jumps to the log-return**
(`integrableExpSet_id_subset_jumpDiffusionIncrementLaw`). -/
lemma zero_mem_interior_integrableExpSet_jumpDiffusionIncrementLaw (b σ : ℝ) (Λ : ℝ≥0)
    {ν : Measure ℝ} [IsProbabilityMeasure ν] (hν : 0 ∈ interior (integrableExpSet id ν))
    (τ : ℝ≥0) : 0 ∈ interior (integrableExpSet id (jumpDiffusionIncrementLaw b σ Λ ν τ)) :=
  interior_mono (integrableExpSet_id_subset_jumpDiffusionIncrementLaw b σ Λ ν τ) hν

open Filter Topology in
/-- **Near `0` the cumulant generating function of the log-return is `κ(θ)τ`**
(`cgf_id_jumpDiffusionIncrementLaw`, wherever the jump law has the exponential moment). -/
lemma cgf_id_jumpDiffusionIncrementLaw_eventuallyEq (b σ : ℝ) (Λ : ℝ≥0) {ν : Measure ℝ}
    [IsProbabilityMeasure ν] (hν : 0 ∈ interior (integrableExpSet id ν)) (τ : ℝ≥0) :
    cgf id (jumpDiffusionIncrementLaw b σ Λ ν τ) =ᶠ[𝓝 0]
      fun θ ↦ jumpDiffusionExponent b σ Λ ν θ * τ := by
  filter_upwards [mem_interior_iff_mem_nhds.1 hν] with θ hθ
    using cgf_id_jumpDiffusionIncrementLaw (ν := ν) (θ := θ) b σ Λ hθ τ

/-- With every exponential moment of the jump law, the Laplace exponent is continuous: Mathlib's
`continuous_mgf` for the jump part. -/
lemma continuous_jumpDiffusionExponent (b σ : ℝ) (Λ : ℝ≥0) {ν : Measure ℝ}
    (hν : ∀ u, Integrable (fun x ↦ rexp (u * x)) ν) :
    Continuous (jumpDiffusionExponent b σ Λ ν) := by
  have h : Continuous (mgf id ν) := continuous_mgf hν
  exact (by fun_prop : Continuous fun θ ↦ b * θ + σ ^ 2 * θ ^ 2 / 2 + Λ * (mgf id ν θ - 1))

/-- **The derivative of the Laplace exponent**: where the jump law has exponential moments,
`κ'(θ) = b + σ²θ + ΛM'(θ)`, with `M` the moment-generating function of the jump law (Mathlib's
`differentiableAt_mgf`). -/
lemma hasDerivAt_jumpDiffusionExponent (b σ : ℝ) (Λ : ℝ≥0) {ν : Measure ℝ} {θ : ℝ}
    (hθ : θ ∈ interior (integrableExpSet id ν)) :
    HasDerivAt (jumpDiffusionExponent b σ Λ ν) (b + σ ^ 2 * θ + Λ * deriv (mgf id ν) θ) θ := by
  have hsq : HasDerivAt (fun θ : ℝ ↦ θ ^ 2) (2 * θ) θ := by simpa using hasDerivAt_pow 2 θ
  exact ((((hasDerivAt_id' θ).const_mul b).fun_add ((hsq.const_mul (σ ^ 2)).div_const 2)).fun_add
    (((differentiableAt_mgf hθ).hasDerivAt.sub_const 1).const_mul (Λ : ℝ))).congr_deriv (by ring)

/-- **The compensated drift is `κ(1) = r`**: `b = r − σ²/2 − Λ(∫ eˣ dν − 1)` exactly when the
Laplace exponent at `1` is the rate. It is the form in which the discounted-price criterion
(`JumpDiffusionProcess.martingale_iff_exponent_one`) and the Esscher condition
(`compensated_tilted_iff`) read the drift. -/
lemma compensated_iff_exponent_one (b σ r : ℝ) (Λ : ℝ≥0) (ν : Measure ℝ) :
    b = r - σ ^ 2 / 2 - Λ * (∫ x, rexp x ∂ν - 1) ↔ jumpDiffusionExponent b σ Λ ν 1 = r := by
  rw [jumpDiffusionExponent]
  simp only [one_mul, mul_one, one_pow]
  constructor <;> intro h <;> linarith

/-! ### The process -/

/-- **A jump-diffusion log-price process.** `X` is adapted to the filtration `𝓕`, starts at `0`,
and each increment `X_t − X_s` (`s ≤ t`) is independent of `𝓕_s` and has the law of a
jump-diffusion log-return over `t − s` (`jumpDiffusionIncrementLaw`): drift `b(t − s)`, a
Gaussian part of variance `σ²(t − s)`, and a compound-Poisson part with `Poisson(Λ(t − s))` jumps
of law `ν`. The price is `S_t = S₀e^{X_t}`. The structure is a hypothesis: it is satisfied
without jumps (`IsFilteredPreBrownian.jumpDiffusionProcess`), and its existence with jumps is not
proved. -/
structure JumpDiffusionProcess {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    (𝓕 : Filtration ℝ≥0 mΩ) (X : ℝ≥0 → Ω → ℝ) (b σ : ℝ) (Λ : ℝ≥0) (ν : Measure ℝ) : Prop where
  adapted : StronglyAdapted 𝓕 X
  zero : ∀ᵐ ω ∂P, X 0 ω = 0
  indep : ∀ s t, s ≤ t →
    Indep (MeasurableSpace.comap (fun ω ↦ X t ω - X s ω) inferInstance) (𝓕 s) P
  law : ∀ s t, s ≤ t →
    HasLaw (fun ω ↦ X t ω - X s ω) (jumpDiffusionIncrementLaw b σ Λ ν (t - s)) P

namespace JumpDiffusionProcess

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ} {b σ : ℝ} {Λ : ℝ≥0} {ν : Measure ℝ}

/-- A jump-diffusion lives on a probability space: the law of each increment is a probability
measure. -/
lemma isProbabilityMeasure (h : JumpDiffusionProcess P 𝓕 X b σ Λ ν) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure P :=
  (h.law 0 0 le_rfl).isProbabilityMeasure

/-- The increment over `[s, t]` has exponential moment
`e^{(b + σ²/2 + Λ(𝔼[e^J] − 1))(t − s)}`. -/
lemma integral_exp_increment (h : JumpDiffusionProcess P 𝓕 X b σ Λ ν) [IsProbabilityMeasure ν]
    (hν : Integrable rexp ν) {s t : ℝ≥0} (hst : s ≤ t) :
    ∫ ω, rexp (X t ω - X s ω) ∂P
      = rexp ((b + σ ^ 2 / 2 + Λ * (∫ x, rexp x ∂ν - 1)) * (t - s : ℝ≥0)) := by
  rw [← integral_exp_jumpDiffusionIncrementLaw b σ Λ hν (t - s)]
  exact (h.law s t hst).integral_comp measurable_exp.aestronglyMeasurable

/-- **The law of `X_t`** is the log-return law over `t`: `X_t = X_t − X_0` almost surely. -/
lemma hasLaw (h : JumpDiffusionProcess P 𝓕 X b σ Λ ν) (t : ℝ≥0) :
    HasLaw (X t) (jumpDiffusionIncrementLaw b σ Λ ν t) P := by
  have h0 := h.law 0 t (zero_le : (0 : ℝ≥0) ≤ t)
  rw [tsub_zero] at h0
  refine h0.congr ?_
  filter_upwards [h.zero] with ω hω
  rw [hω, sub_zero]

/-- `𝔼[e^{X_t}] = e^{(b + σ²/2 + Λ(𝔼[e^J] − 1))t}`, the exponential moment of the law of `X_t`
(`hasLaw`). -/
lemma integral_exp (h : JumpDiffusionProcess P 𝓕 X b σ Λ ν) [IsProbabilityMeasure ν]
    (hν : Integrable rexp ν) (t : ℝ≥0) :
    ∫ ω, rexp (X t ω) ∂P = rexp ((b + σ ^ 2 / 2 + Λ * (∫ x, rexp x ∂ν - 1)) * t) := by
  rw [← integral_exp_jumpDiffusionIncrementLaw b σ Λ hν t]
  exact (h.hasLaw t).integral_comp measurable_exp.aestronglyMeasurable

/-- `e^{X_t}` is integrable: its integral is positive (`integral_exp`). -/
lemma integrable_exp (h : JumpDiffusionProcess P 𝓕 X b σ Λ ν) [IsProbabilityMeasure ν]
    (hν : Integrable rexp ν) (t : ℝ≥0) : Integrable (fun ω ↦ rexp (X t ω)) P :=
  Integrable.of_integral_ne_zero (by rw [h.integral_exp hν t]; exact (Real.exp_pos _).ne')

/-- **The discounted jump-diffusion price is a martingale exactly at the compensated drift.** For
a jump law with `𝔼[e^J] < ∞` and `S₀ ≠ 0`, `t ↦ e^{−rt}S₀e^{X_t}` is an `𝓕`-martingale if and
only if `b = r − σ²/2 − Λ(𝔼[e^J] − 1)`. -/
theorem martingale_iff (h : JumpDiffusionProcess P 𝓕 X b σ Λ ν) [IsProbabilityMeasure ν]
    (hν : Integrable rexp ν) {S_0 : ℝ} (hS_0 : S_0 ≠ 0) (r : ℝ) :
    Martingale (fun (t : ℝ≥0) ω ↦ rexp (-r * t) * (S_0 * rexp (X t ω))) 𝓕 P ↔
      b = r - σ ^ 2 / 2 - Λ * (∫ x, rexp x ∂ν - 1) := by
  have := h.isProbabilityMeasure
  constructor
  · -- a martingale has constant mean; at time `1` it is `S₀e^{b + σ²/2 + Λ(𝔼[e^J] − 1) − r}`
    intro hM
    have hmean : ∫ ω, rexp (-r * ((0 : ℝ≥0) : ℝ)) * (S_0 * rexp (X 0 ω)) ∂P
        = ∫ ω, rexp (-r * ((1 : ℝ≥0) : ℝ)) * (S_0 * rexp (X 1 ω)) ∂P :=
      (integral_congr_ae (hM.condExp_ae_eq zero_le_one)).symm.trans (integral_condExp (𝓕.le 0))
    have h0 : ∫ ω, rexp (-r * ((0 : ℝ≥0) : ℝ)) * (S_0 * rexp (X 0 ω)) ∂P = S_0 := by
      have hS : (fun ω ↦ rexp (-r * ((0 : ℝ≥0) : ℝ)) * (S_0 * rexp (X 0 ω))) =ᵐ[P]
          fun _ ↦ S_0 := by
        filter_upwards [h.zero] with ω hω
        simp [hω]
      rw [integral_congr_ae hS, integral_const, probReal_univ, one_smul]
    have h1 : ∫ ω, rexp (-r * ((1 : ℝ≥0) : ℝ)) * (S_0 * rexp (X 1 ω)) ∂P
        = S_0 * rexp (b + σ ^ 2 / 2 + Λ * (∫ x, rexp x ∂ν - 1) - r) := by
      rw [integral_const_mul, integral_const_mul, h.integral_exp hν 1, mul_left_comm,
        ← Real.exp_add, NNReal.coe_one]
      congr 2
      ring
    rw [h0, h1] at hmean
    have := (Real.exp_eq_one_iff _).1 ((mul_eq_left₀ hS_0).1 hmean.symm)
    linarith
  · -- at the compensated drift the increment exponentials have mean `e^{r(t − s)}`
    intro hb
    have hfun : (fun (t : ℝ≥0) ω ↦ rexp (-r * t) * (S_0 * rexp (X t ω)))
        = S_0 • fun (t : ℝ≥0) ω ↦ rexp (X t ω - r * t) := by
      funext t ω
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [mul_left_comm, ← Real.exp_add]
      congr 2
      ring
    rw [hfun]
    refine Martingale.smul S_0 (martingale_exp_sub_of_indep_increments
      (ψ := fun t : ℝ≥0 ↦ r * (t : ℝ)) h.adapted h.indep (h.integrable_exp hν)
      fun s t hst ↦ ?_)
    show ∫ ω, rexp (X t ω - X s ω) ∂P = rexp (r * t - r * s)
    rw [h.integral_exp_increment hν hst, NNReal.coe_sub hst, hb]
    congr 1
    ring

end JumpDiffusionProcess

end MathFin
