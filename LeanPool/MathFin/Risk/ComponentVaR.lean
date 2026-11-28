/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye, Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Choice.Portfolio.RiskParityFOC
public import LeanPool.MathFin.Risk.GaussianRiskMarkowitz

/-!
# Component and marginal Value-at-Risk (the Euler allocation)

For a zero-mean Gaussian portfolio loss with positions `x : ι → ℝ` and covariance kernel `σ`, the
parametric VaR is `VaR = α · √(x'Σx)` for a quantile multiplier `α` (e.g. `α = Φ⁻¹(level)`, as in
`Risk/Gaussian.lean`). Here `portfolioVaRN` is *defined* as that expression. The
Gaussian quantile identity behind it is `valueAtRisk_portfolio_gaussian_eq_portfolioVaRN`: for a
Gaussian vector `X` of risk-factor changes, `VaR_α(∑ wᵢXᵢ)` is the mean `∑ wᵢ E Xᵢ` plus
`portfolioVaRN` at the multiplier `Φ⁻¹(α)` and the covariance kernel of `X`
(`valueAtRisk_portfolio_gaussian`, `Risk/GaussianRiskMarkowitz.lean`). Since
`x ↦ √(x'Σx)` is positively homogeneous of degree 1, Euler's theorem predicts
`∑ᵢ xᵢ · ∂VaR/∂xᵢ = VaR`. Here the marginal VaR is *defined* by the textbook
closed form `α(Σx)ᵢ/√(x'Σx)`. For symmetric `σ` and positive portfolio variance these are the
partial derivatives of `portfolioVaRN`: its derivative along any direction `d` is
`∑ᵢ dᵢ · marginalVaRᵢ` (`hasDerivAt_portfolioVaRN`). With this definition the component VaR
`xᵢ · marginalVaRᵢ` is `α/√(x'Σx)` times the risk contribution `xᵢ(Σx)ᵢ` of
`Choice/Portfolio/RiskParityFOC.lean`, and the Euler identity reduces to
`sum_riskContribution_eq_variance`.

## Main definitions

* `portfolioVaRN`: the parametric portfolio VaR `α · √(x'Σx)`, with `x'Σx` the `portfolioVarN`
  of positions `x` against the kernel `σ`.
* `marginalVaR`: the marginal VaR `α (Σx)ᵢ / √(x'Σx)`, defined as this closed form.
* `componentVaR`: the component VaR `xᵢ · marginalVaR i`.

## Main results

* `sum_componentVaR_eq_portfolioVaRN`: the Euler allocation `∑ᵢ CVaRᵢ = VaR`, stated for
  `0 < x'Σx` (strictly positive portfolio variance).
* `hasDerivAt_portfolioVaRN`: for symmetric `σ` and `0 < x'Σx`, the derivative of `portfolioVaRN`
  along any direction `d` is `∑ᵢ dᵢ · marginalVaRᵢ`.
* `valueAtRisk_portfolio_gaussian_eq_portfolioVaRN`: the VaR of a Gaussian portfolio loss is its
  mean plus `portfolioVaRN` at `Φ⁻¹(α)`.
* `sum_componentVaR_eq_valueAtRisk_sub`: the component VaRs at `Φ⁻¹(α)` allocate the VaR of a
  Gaussian portfolio loss in excess of its mean.

## References

* [A. J. McNeil, R. Frey and P. Embrechts, *Quantitative Risk Management: Concepts, Techniques and
  Tools*][McNeilFreyEmbrechts], Corollary 8.43
* [D. Tasche, *Capital allocation to business units and sub-portfolios: the Euler
  principle*][Tasche2008]

## Tags

component VaR, marginal VaR, Euler allocation, parametric VaR, risk contribution, delta-normal VaR,
MSC 91G70, JEL G32
-/

@[expose] public section

namespace MathFin

section Euler

variable {ι : Type*} (s : Finset ι) (x : ι → ℝ) (σ : ι → ι → ℝ) (α : ℝ)

/-- Parametric portfolio VaR `α · √(x'Σx)`, with `x'Σx` the N-asset portfolio variance of
`Choice/Portfolio/MarkowitzNAsset.lean`. -/
noncomputable def portfolioVaRN : ℝ := α * Real.sqrt (portfolioVarN s x σ)

/-- **Marginal VaR**: *defined* as the textbook closed form `α·(Σx)ᵢ/√(x'Σx)`, with
`(Σx)ᵢ = marginalVariance s σ x i`. For symmetric `σ` and positive portfolio variance it is the
partial derivative of `portfolioVaRN` in `xᵢ` (`hasDerivAt_portfolioVaRN`). -/
noncomputable def marginalVaR (i : ι) : ℝ :=
  α * marginalVariance s σ x i / Real.sqrt (portfolioVarN s x σ)

/-- **Component VaR**: `CVaRᵢ = xᵢ · marginalVaRᵢ`, i.e. `α/√(x'Σx)` times the risk contribution
`riskContribution s σ x i = xᵢ(Σx)ᵢ`. -/
noncomputable def componentVaR (i : ι) : ℝ := x i * marginalVaR s x σ α i

/-- **Euler allocation of VaR**: the component VaRs sum to the portfolio VaR, `∑ᵢ CVaRᵢ = VaR`,
whenever the portfolio variance is (strictly) positive. This is the identity Euler's theorem
predicts for the degree-1-homogeneous map `x ↦ α√(x'Σx)`; since `marginalVaR` is defined by its
closed form, the proof is the algebra `∑ᵢ xᵢ(Σx)ᵢ = x'Σx` (`sum_riskContribution_eq_variance`). -/
theorem sum_componentVaR_eq_portfolioVaRN (hvar : 0 < portfolioVarN s x σ) :
    ∑ i ∈ s, componentVaR s x σ α i = portfolioVaRN s x σ α := by
  have hsqrt : Real.sqrt (portfolioVarN s x σ) ≠ 0 := (Real.sqrt_pos.mpr hvar).ne'
  unfold componentVaR marginalVaR portfolioVaRN
  have hsum :
      ∑ i ∈ s, x i * (α * marginalVariance s σ x i / Real.sqrt (portfolioVarN s x σ)) =
        α * (∑ i ∈ s, riskContribution s σ x i) / Real.sqrt (portfolioVarN s x σ) := by
    rw [Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    unfold riskContribution
    ring
  have hsq : Real.sqrt (portfolioVarN s x σ) * Real.sqrt (portfolioVarN s x σ) =
      portfolioVarN s x σ := Real.mul_self_sqrt hvar.le
  rw [hsum, sum_riskContribution_eq_variance,
    div_eq_iff hsqrt, mul_assoc, hsq]

/-- **The portfolio variance along a line** `x + t d` is the quadratic
`Var(x) + t · ∑ᵢⱼ (dᵢxⱼ + xᵢdⱼ)σᵢⱼ + t² Var(d)`. -/
lemma portfolioVarN_add_mul (d : ι → ℝ) (t : ℝ) :
    portfolioVarN s (fun k ↦ x k + t * d k) σ =
      portfolioVarN s x σ + t * ∑ i ∈ s, ∑ j ∈ s, (d i * x j + x i * d j) * σ i j +
        t ^ 2 * portfolioVarN s d σ := by
  simp only [portfolioVarN, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring

/-- For a symmetric kernel the linear coefficient of `portfolioVarN_add_mul` is twice
`∑ᵢ dᵢ (Σx)ᵢ`. -/
lemma sum_sum_add_mul_eq_two_mul (hσ : ∀ i ∈ s, ∀ j ∈ s, σ i j = σ j i) (d : ι → ℝ) :
    ∑ i ∈ s, ∑ j ∈ s, (d i * x j + x i * d j) * σ i j =
      2 * ∑ i ∈ s, d i * marginalVariance s σ x i := by
  have h2 : ∑ i ∈ s, ∑ j ∈ s, x i * d j * σ i j = ∑ i ∈ s, ∑ j ∈ s, d i * x j * σ i j := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i hi ↦ Finset.sum_congr rfl fun j hj ↦ by
      rw [hσ j hj i hi]; ring
  calc ∑ i ∈ s, ∑ j ∈ s, (d i * x j + x i * d j) * σ i j
      = ∑ i ∈ s, ∑ j ∈ s, d i * x j * σ i j + ∑ i ∈ s, ∑ j ∈ s, x i * d j * σ i j := by
        simp only [add_mul, Finset.sum_add_distrib]
    _ = 2 * ∑ i ∈ s, ∑ j ∈ s, d i * x j * σ i j := by rw [h2, two_mul]
    _ = 2 * ∑ i ∈ s, d i * marginalVariance s σ x i := by
        congr 1
        exact Finset.sum_congr rfl fun i _ ↦ by
          rw [marginalVariance, Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ ↦ by ring

/-- **The marginal VaRs are the partial derivatives of the parametric VaR**: for a symmetric
kernel and a positive portfolio variance, the derivative of `portfolioVaRN` at `x` along any
direction `d` is `∑ᵢ dᵢ · marginalVaRᵢ`. -/
theorem hasDerivAt_portfolioVaRN (hσ : ∀ i ∈ s, ∀ j ∈ s, σ i j = σ j i)
    (hvar : 0 < portfolioVarN s x σ) (d : ι → ℝ) :
    HasDerivAt (fun t ↦ portfolioVaRN s (fun k ↦ x k + t * d k) σ α)
      (∑ i ∈ s, d i * marginalVaR s x σ α i) 0 := by
  set S := ∑ i ∈ s, d i * marginalVariance s σ x i with hS
  have hfun : (fun t ↦ portfolioVarN s (fun k ↦ x k + t * d k) σ) =
      fun t ↦ portfolioVarN s x σ + t * (2 * S) + t ^ 2 * portfolioVarN s d σ := by
    funext t
    rw [portfolioVarN_add_mul, sum_sum_add_mul_eq_two_mul s x σ hσ]
  have hpoly : HasDerivAt (fun t ↦ portfolioVarN s (fun k ↦ x k + t * d k) σ) (2 * S) 0 := by
    rw [hfun]
    exact ((((hasDerivAt_id' (x := (0 : ℝ))).mul_const (2 * S)).const_add _).add
      ((hasDerivAt_pow 2 (0 : ℝ)).mul_const _)).congr_deriv (by simp)
  have h0 : portfolioVarN s (fun k ↦ x k + 0 * d k) σ = portfolioVarN s x σ := by simp
  have hsqrt := (hpoly.sqrt (by rw [h0]; exact hvar.ne')).const_mul α
  rw [h0] at hsqrt
  refine hsqrt.congr_deriv ?_
  simp only [marginalVaR, hS, Finset.mul_sum, Finset.sum_div]
  field_simp

end Euler

/-! ### Gaussian portfolio losses -/

section Gaussian

open MeasureTheory ProbabilityTheory Set

variable {ι : Type*} [Fintype ι] {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X : ι → Ω → ℝ} {α : ℝ}

/-- **The parametric VaR is the VaR of a Gaussian portfolio loss above its mean**: for a
Gaussian vector `X` of risk-factor changes and `α ∈ (0, 1)`,
`VaR_α(∑ wᵢXᵢ) = ∑ wᵢ E Xᵢ + portfolioVaRN` at the multiplier `Φ⁻¹(α)` and the covariance kernel
of `X`. -/
theorem valueAtRisk_portfolio_gaussian_eq_portfolioVaRN
    (hX : HasGaussianLaw (fun ω ↦ (X · ω)) P) (w : ι → ℝ) (hα : α ∈ Ioo 0 1) :
    valueAtRisk (fun ω ↦ ∑ i, w i * X i ω) P α =
      ∑ i, w i * P[X i] +
        portfolioVaRN Finset.univ w (fun i j ↦ cov[X i, X j; P]) (PhiInv α) := by
  rw [valueAtRisk_portfolio_gaussian hX w hα, portfolioVaRN, mul_comm (PhiInv α)]

/-- **Euler allocation of a Gaussian VaR**: for a Gaussian vector `X`, weights `w` with positive
portfolio variance and `α ∈ (0, 1)`, the component VaRs at the multiplier `Φ⁻¹(α)` sum to the VaR
of the portfolio loss in excess of its mean: `∑ᵢ CVaRᵢ = VaR_α(∑ wᵢXᵢ) − ∑ wᵢ E Xᵢ`. -/
theorem sum_componentVaR_eq_valueAtRisk_sub
    (hX : HasGaussianLaw (fun ω ↦ (X · ω)) P) (w : ι → ℝ) (hα : α ∈ Ioo 0 1)
    (hvar : 0 < portfolioVarN Finset.univ w fun i j ↦ cov[X i, X j; P]) :
    ∑ i, componentVaR Finset.univ w (fun i j ↦ cov[X i, X j; P]) (PhiInv α) i =
      valueAtRisk (fun ω ↦ ∑ i, w i * X i ω) P α - ∑ i, w i * P[X i] := by
  rw [sum_componentVaR_eq_portfolioVaRN _ _ _ _ hvar,
    valueAtRisk_portfolio_gaussian_eq_portfolioVaRN hX w hα, add_sub_cancel_left]

end Gaussian

end MathFin
