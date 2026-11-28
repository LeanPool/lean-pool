/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.Jumps.JumpDiffusionMixing
public import Mathlib.Probability.Independence.InfinitePi

/-!
# The canonical jump-diffusion model

`JumpDiffusionHyp` lists what the jump-diffusion results assume of a probability space: a
standard normal diffusion sample `Z`, a jump count `N ∼ Poisson(Λ)` and i.i.d. log-jump sizes
`Jᵢ`, with the count independent of the diffusion sample and the sizes, and the diffusion sample
independent of the sizes. Here `Λ` is the expected number of jumps to maturity (`λT` for a jump
rate `λ`). This file shows that the assumptions can be met for every `Λ` and every jump law `ν`:
on `ℝ × ℕ × (ℕ → ℝ)` with the product of `N(0, 1)`, `Poisson(Λ)` and the infinite product `ν^ℕ`
(`jumpDiffusionMeasure`), the coordinates satisfy them (`jumpDiffusionHyp_canonical`). So the
`JumpDiffusionHyp` theorems are not vacuous; their remaining hypotheses on the model are
conditions on `Λ` and `ν`, such as `∫ eˣ dν < ∞` (`integrable_exp_canonical_jump`). With Gaussian
jumps the same model is Merton's (`JumpDiffusionHyp.call_eq_mertonCallPrice`).

It also shows that the call depends on the model only through `Λ` and the law of the jumps. On
any probability space satisfying `JumpDiffusionHyp`, the jump sizes are i.i.d., so their sequence
has law `ν^ℕ`, with `ν` the law of `J₀`, and for `𝔼[e^{J₀}] < ∞` and `S₀, K, σ, T > 0` the call
is

  `∫ n, ∫ x, C_BS(S₀e^{−κ + ∑_{i<n} xᵢ}) dν^ℕ(x) dPoisson(Λ)(n)`

(`JumpDiffusionHyp.call_eq_integral_infinitePi`), Merton's formula for a general jump law with
the expectation over the jump sizes written against their law.

## Main definitions

* `jumpDiffusionMeasure`: the canonical law on `ℝ × ℕ × (ℕ → ℝ)`, the product of `N(0, 1)`,
  `Poisson(Λ)` and the i.i.d. product `ν^ℕ`: a diffusion sample, a jump count and the log-jump
  sizes.

## Main results

* `jumpDiffusionHyp_canonical`: the coordinates of `ℝ × ℕ × (ℕ → ℝ)` under
  `N(0, 1) ⊗ Poisson(Λ) ⊗ ν^ℕ` satisfy `JumpDiffusionHyp`, and each jump size has law `ν`.
* `JumpDiffusionHyp.call_eq_integral_infinitePi`: the call as an integral against `Poisson(Λ)`
  and `ν^ℕ`.

## References

* [Cont and Tankov, *Financial Modelling with Jump Processes*][ContTankov2004]
* [R. C. Merton, *Option pricing when underlying stock returns are discontinuous*][Merton1976]

## Tags

jump-diffusion model, Poisson jump count, compound Poisson, log-jump sizes, Merton model,
independence hypotheses, MSC 91G20, MSC 60G51, JEL G13
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

/-- The canonical jump-diffusion law on `ℝ × ℕ × (ℕ → ℝ)`: a standard normal diffusion sample,
a `Poisson(Λ)` jump count and a sequence of log-jump sizes, i.i.d. of law `ν`, all independent. -/
noncomputable def jumpDiffusionMeasure (Λ : ℝ≥0) (ν : Measure ℝ) : Measure (ℝ × ℕ × (ℕ → ℝ)) :=
  (gaussianReal 0 1).prod ((poissonMeasure Λ).prod (Measure.infinitePi fun _ : ℕ ↦ ν))

instance isProbabilityMeasure_jumpDiffusionMeasure (Λ : ℝ≥0) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] : IsProbabilityMeasure (jumpDiffusionMeasure Λ ν) := by
  unfold jumpDiffusionMeasure
  infer_instance

/-- **The jump-diffusion model exists**, for every expected jump count `Λ` and every jump law `ν`:
under `jumpDiffusionMeasure Λ ν` the coordinates (the diffusion sample, the jump count and the
log-jump sizes) satisfy `JumpDiffusionHyp`, and each jump size has law `ν`. -/
theorem jumpDiffusionHyp_canonical (Λ : ℝ≥0) (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    JumpDiffusionHyp (jumpDiffusionMeasure Λ ν) Λ (fun ω ↦ ω.1) (fun ω ↦ ω.2.1)
        (fun i ω ↦ ω.2.2 i) ∧
      ∀ i, HasLaw (fun ω : ℝ × ℕ × (ℕ → ℝ) ↦ ω.2.2 i) ν (jumpDiffusionMeasure Λ ν) := by
  have hsnd : MeasurePreserving (fun ω : ℝ × ℕ × (ℕ → ℝ) ↦ ω.2) (jumpDiffusionMeasure Λ ν)
      ((poissonMeasure Λ).prod (Measure.infinitePi fun _ : ℕ ↦ ν)) :=
    measurePreserving_snd
  have hsizes : MeasurePreserving (fun ω : ℝ × ℕ × (ℕ → ℝ) ↦ ω.2.2) (jumpDiffusionMeasure Λ ν)
      (Measure.infinitePi fun _ : ℕ ↦ ν) :=
    measurePreserving_snd.comp hsnd
  have hJm (i : ℕ) : Measurable fun ω : ℝ × ℕ × (ℕ → ℝ) ↦ ω.2.2 i :=
    (measurable_pi_apply i).comp (measurable_snd.comp measurable_snd)
  have hJ (i : ℕ) : HasLaw (fun ω : ℝ × ℕ × (ℕ → ℝ) ↦ ω.2.2 i) ν (jumpDiffusionMeasure Λ ν) :=
    ((measurePreserving_eval_infinitePi (fun _ : ℕ ↦ ν) i).comp hsizes).hasLaw
  -- the diffusion sample is independent of the count and the sizes together
  have hZ : (fun ω : ℝ × ℕ × (ℕ → ℝ) ↦ ω.1) ⟂ᵢ[jumpDiffusionMeasure Λ ν]
      fun ω ↦ (ω.2.1, ω.2.2) :=
    indepFun_prod (μ := gaussianReal 0 1)
      (ν := (poissonMeasure Λ).prod (Measure.infinitePi fun _ : ℕ ↦ ν)) measurable_id
      measurable_id
  -- the count is independent of the sizes: their joint law is the product of their laws
  have hNJ : (fun ω : ℝ × ℕ × (ℕ → ℝ) ↦ ω.2.1) ⟂ᵢ[jumpDiffusionMeasure Λ ν] fun ω ↦ ω.2.2 :=
    (indepFun_iff_hasLaw_prodMk_prod (measurePreserving_fst.comp hsnd).hasLaw
      hsizes.hasLaw).2 hsnd.hasLaw
  refine ⟨⟨(measurePreserving_fst (μ := gaussianReal 0 1)).hasLaw,
    (measurePreserving_fst.comp hsnd).hasLaw, ?_, fun i ↦ (hJ i).identDistrib (hJ 0),
    hZ.comp measurable_id measurable_snd,
    indepFun_prodMk_of_indepFun_prodMk measurable_fst.aemeasurable
      (measurable_fst.comp measurable_snd).aemeasurable
      (measurable_snd.comp measurable_snd).aemeasurable hZ hNJ⟩, hJ⟩
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map hJm]
  refine hsizes.map_eq.trans ?_
  congr 1
  funext i
  exact (hJ i).map_eq.symm

/-- On the canonical model the first log-jump size has exponential moment `∫ e^{θx} dν` at every
`θ`: it has law `ν`. -/
lemma integral_exp_mul_canonical_jump (Λ : ℝ≥0) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (θ : ℝ) :
    ∫ ω, rexp (θ * ω.2.2 0) ∂(jumpDiffusionMeasure Λ ν) = ∫ x, rexp (θ * x) ∂ν :=
  ((jumpDiffusionHyp_canonical Λ ν).2 0).integral_comp
    (measurable_const_mul θ).exp.aestronglyMeasurable

/-- On the canonical model `e^{θJ₀}` is integrable when `e^{θx}` is integrable under the jump
law. -/
lemma integrable_exp_mul_canonical_jump {Λ : ℝ≥0} {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {θ : ℝ} (hν : Integrable (fun x ↦ rexp (θ * x)) ν) :
    Integrable (fun ω : ℝ × ℕ × (ℕ → ℝ) ↦ rexp (θ * ω.2.2 0)) (jumpDiffusionMeasure Λ ν) := by
  have hJ := (jumpDiffusionHyp_canonical Λ ν).2 0
  rw [← hJ.map_eq] at hν
  exact (integrable_map_measure (measurable_const_mul θ).exp.aestronglyMeasurable
    hJ.aemeasurable).1 hν

/-- On the canonical model the first log-jump size has exponential moment `∫ eˣ dν`
(`integral_exp_mul_canonical_jump` at `θ = 1`). -/
lemma integral_exp_canonical_jump (Λ : ℝ≥0) (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    ∫ ω, rexp (ω.2.2 0) ∂(jumpDiffusionMeasure Λ ν) = ∫ x, rexp x ∂ν := by
  simpa only [one_mul] using integral_exp_mul_canonical_jump Λ ν 1

/-- On the canonical model `e^{J₀}` is integrable when `eˣ` is integrable under the jump law
(`integrable_exp_mul_canonical_jump` at `θ = 1`). -/
lemma integrable_exp_canonical_jump {Λ : ℝ≥0} {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : Integrable rexp ν) :
    Integrable (fun ω : ℝ × ℕ × (ℕ → ℝ) ↦ rexp (ω.2.2 0)) (jumpDiffusionMeasure Λ ν) := by
  simpa only [one_mul] using
    integrable_exp_mul_canonical_jump (Λ := Λ) (ν := ν) (θ := 1) (by simpa only [one_mul] using hν)

namespace JumpDiffusionHyp

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {Q : Measure Ω} {Λ : ℝ≥0} {Z : Ω → ℝ}
  {N : Ω → ℕ} {J : ℕ → Ω → ℝ}

/-- The jump sizes of a jump-diffusion form an i.i.d. sequence: their joint law is `ν^ℕ`, with
`ν` the law of `J₀`. -/
lemma map_jumps (h : JumpDiffusionHyp Q Λ Z N J) :
    Q.map (fun ω i ↦ J i ω) = Measure.infinitePi fun _ : ℕ ↦ Q.map (J 0) := by
  rw [h.J_indep.map_fun_eq_infinitePi_map₀' h.aemeasurable_J]
  congr 1
  funext i
  exact (h.J_ident i).map_eq

/-- **The call depends only on `Λ` and the jump law.** For a jump-diffusion whose jump
sizes have law `ν = Q.map (J 0)`, the discounted expected call payoff is the integral, against
`Poisson(Λ)` for the count and `ν^ℕ` for the jump sizes, of the Black–Scholes price at the spot
`S₀e^{−κ + ∑_{i<n} xᵢ}`: Merton's formula for a general jump law (`call_poisson_mixture`) with
the expectation over the jump sizes written against their law (`map_jumps`). -/
theorem call_eq_integral_infinitePi (h : JumpDiffusionHyp Q Λ Z N J)
    (hJ : Integrable (fun ω ↦ rexp (J 0 ω)) Q) {S_0 K r σ T : ℝ} (hS_0 : 0 < S_0) (hK : 0 < K)
    (hσ : 0 < σ) (hT : 0 < T) (κ : ℝ) :
    ∫ ω, rexp (-r * T)
        * max (jumpDiffusionTerminal S_0 r σ T κ (Z ω) (N ω) (fun i ↦ J i ω) - K) 0 ∂Q
      = ∫ n, ∫ x, bsV K r σ (S_0 * rexp (-κ + ∑ i ∈ Finset.range n, x i)) T
          ∂(Measure.infinitePi fun _ : ℕ ↦ Q.map (J 0)) ∂(poissonMeasure Λ) := by
  rw [h.call_poisson_mixture hJ hS_0 hK hσ hT κ, ← h.map_jumps]
  refine integral_congr_ae (ae_of_all _ fun n ↦ ?_)
  have hg : Measurable fun x : ℕ → ℝ ↦ bsV K r σ (S_0 * rexp (-κ + ∑ i ∈ Finset.range n, x i)) T :=
    (measurable_bsV_spot K r σ T).comp (by fun_prop)
  exact (integral_map h.aemeasurable_jumps
    hg.aestronglyMeasurable).symm

end JumpDiffusionHyp

end MathFin
