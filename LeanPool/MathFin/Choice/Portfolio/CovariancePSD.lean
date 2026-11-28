/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Choice.Portfolio.MarkowitzNAsset
public import Mathlib.Probability.Moments.Variance

/-!
# Covariance kernels are positive semidefinite (the self-dot variance identity)

`MarkowitzNAsset.lean` proves `portfolioVarN_nonneg_of_psd` *given* a PSD
hypothesis on the kernel. This file discharges that hypothesis from first
principles for the kernel that finance actually uses: the covariance kernel
`σ_{ij} = cov(R_i, R_j)` of genuine square-integrable random returns.

The whole argument is the **self-dot identity**: Mathlib's `variance_sum'`
("the variance of a sum is the double sum of covariances") read backwards,
with `covariance_smul_left`/`covariance_smul_right` peeling the weights,
collapses the Markowitz double sum onto a single variance,

  `∑_{i,j} w_i w_j · cov(R_i, R_j) = cov(∑ w_i R_i, ∑ w_j R_j) = Var(∑ w_i R_i)`,

and a variance is non-negative. The quadratic form is non-negative *because it
IS a variance* — that is why covariance matrices are PSD.

## Main results

* `portfolioVarN_covariance_eq_variance`: the Markowitz quadratic form with the
  genuine covariance kernel equals the variance of the portfolio return.
* `covariance_kernel_psd`: the covariance kernel satisfies the PSD hypothesis
  of `portfolioVarN_nonneg_of_psd` — derived, not assumed.
* `portfolioVarN_covariance_nonneg`: the capstone non-negativity.

## References

* [K. Bodie and Marcus, *Investments*][BodieKaneMarcus], Ch 7
* [H. Markowitz, *Portfolio selection*][Markowitz1952]

## Tags

covariance matrix, positive semidefinite, portfolio variance, Markowitz, variance of a sum,
quadratic form, MSC 91G10, MSC 62H05, JEL G11
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
  {ι : Type*}

/-- **Self-dot variance identity**: the n-asset Markowitz quadratic form, evaluated
at the *genuine* covariance kernel `σ_{ij} = cov(R_i, R_j)` of square-integrable
random returns, is exactly the variance of the portfolio return `∑ wᵢ Rᵢ`:

  `portfolioVarN s w (cov(R_·, R_·)) = Var[∑ i ∈ s, wᵢ • Rᵢ]`.

Mathlib's `variance_sum'` unfolds the portfolio variance into the double sum
of covariances; the `smul` lemmas peel the weights. No PSD assumption appears
anywhere. -/
theorem portfolioVarN_covariance_eq_variance
    (s : Finset ι) (w : ι → ℝ) (R : ι → Ω → ℝ)
    (hR : ∀ i ∈ s, MemLp (R i) 2 μ) :
    portfolioVarN s w (fun i j ↦ cov[R i, R j; μ]) =
      Var[∑ i ∈ s, w i • R i; μ] := by
  have hwR : ∀ i ∈ s, MemLp (w i • R i) 2 μ := fun i hi ↦ (hR i hi).const_smul (w i)
  rw [variance_sum' hwR]
  unfold portfolioVarN
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  rw [covariance_smul_left, covariance_smul_right]
  ring

/-- **Covariance kernels are PSD** — the hypothesis of
`portfolioVarN_nonneg_of_psd`, discharged from first principles: for any
weights `v`, the quadratic form `∑∑ vᵢ vⱼ cov(Rᵢ, Rⱼ)` is the variance of
`∑ vᵢ Rᵢ`, hence non-negative. -/
theorem covariance_kernel_psd
    (s : Finset ι) (R : ι → Ω → ℝ)
    (hR : ∀ i ∈ s, MemLp (R i) 2 μ) :
    ∀ v : ι → ℝ, 0 ≤ ∑ i ∈ s, ∑ j ∈ s, v i * v j * cov[R i, R j; μ] := by
  intro v
  have h := portfolioVarN_covariance_eq_variance s v R hR
  unfold portfolioVarN at h
  rw [h]
  exact variance_nonneg _ μ

/-- **N-asset portfolio variance non-negativity from random returns**: with the
genuine covariance kernel of square-integrable returns, the Markowitz portfolio
variance is non-negative — because it *is* the variance `Var[∑ wᵢ Rᵢ] ≥ 0`. -/
theorem portfolioVarN_covariance_nonneg
    (s : Finset ι) (w : ι → ℝ) (R : ι → Ω → ℝ)
    (hR : ∀ i ∈ s, MemLp (R i) 2 μ) :
    0 ≤ portfolioVarN s w (fun i j ↦ cov[R i, R j; μ]) :=
  portfolioVarN_nonneg_of_psd s w _ (covariance_kernel_psd s R hR)

end MathFin
