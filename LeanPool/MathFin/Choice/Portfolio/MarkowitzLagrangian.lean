/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Choice.Portfolio.CAPMEquilibrium
public import LeanPool.MathFin.Choice.Portfolio.ConvexQPKKT
public import LeanPool.MathFin.Choice.Portfolio.CovariancePSD
public import LeanPool.MathFin.Choice.Portfolio.TangentPortfolio

/-!
# N-asset Markowitz from constrained-variance Lagrangian (first principles)

The 2-asset Sharpe-ratio file (`Choice/Portfolio/SharpeFOCDerivation.lean`)
derives the cross-product FOC `r₂(Σw)₁ = r₁(Σw)₂` from `d(Sh²)/dw = 0`.
This file extends the first-principles derivation to N assets, but for the
*constrained variance minimization* formulation —
which is the textbook Markowitz statement and gives the canonical
Lagrangian FOC `Σw = lam_1 · 1 + lam_2 · μ`.

## The problem

Minimize `(1/2) · w^T Σ w` (portfolio variance) subject to

  * `1^T w = 1` (budget constraint),
  * `μ^T w = m` (expected-return target).

## The Lagrangian

`L(w, lam_1, lam_2) := (1/2) · w^T Σ w − lam_1 · (1^T w − 1) − lam_2 · (μ^T w − m)`.

## The FOC (textbook derivation)

`∂L/∂w_i = (Σw)_i − lam_1 − lam_2 · μ_i = 0`,    i.e.,    `Σw = lam_1 · 1 + lam_2 · μ`.

This says the marginal variance vector lies in the 2-d span of the
constraint normals — the canonical "two-fund separation" structural fact.

## Variational characterisation

A portfolio `w` is a **constrained variance critical point** if for every
admissible perturbation `δw` (orthogonal to budget and expected-return
normals, i.e., `1^T δw = 0` and `μ^T δw = 0`),

  `(Σw)^T δw = 0`.

For symmetric `Σ` this is the vanishing of `d/dt [(1/2) (w + t δw)^T Σ (w + t δw)] |_{t=0}`:
`quadratic_form_perturb_linear_coeff` identifies `(Σw)^T δw` as the linear coefficient of
that polynomial in `t` (no derivative statement is proved).

## Main definitions

* `IsConstrainedVarianceCriticalPoint`: `w` is a critical point of `(1/2) wᵀ Σ w` under the
  budget constraint `1ᵀ w = 1` and the return constraint `μᵀ w = m`, in the variational form:
  `(Σw)ᵀ δw = 0` for every perturbation `δw` orthogonal to `1` and `μ`.

## Main results

* `isCriticalPoint_of_lagrangian_FOC` (forward direction): if `Σw = lam_1 ·
  1 + lam_2 · μ` componentwise, then `w` is a constrained-variance critical
  point. *Proof*: direct algebra — substitute the FOC, use the
  perturbation's orthogonality to the constraint normals.
* `variance_objective_eq_self_dot` / `quadratic_form_perturb_linear_coeff`:
  the variance objective as a self-dot, and the explicit linear coefficient
  `(Σw) · δw` of a perturbation of `(1/2) wᵀΣw` for symmetric `Σ` — the
  directional-derivative content underlying the FOC.
* `portfolioVarN_le_of_lagrangian_FOC`: for positive semidefinite `Σ`, a portfolio
  meeting both constraints and the Lagrangian FOC has the least variance among all
  portfolios meeting the same constraints — the KKT sufficiency theorem
  `kkt_sufficient_of_eq` (`Choice/Portfolio/ConvexQPKKT.lean`) for the QP `min ½ wᵀΣw`.
* `posSemidef_covariance`, `variance_le_of_lagrangian_FOC`: the same for the covariance
  matrix of square-integrable random returns, whose positive semidefiniteness is derived
  (`covariance_kernel_psd`), stated for the variance of the portfolio return itself.
* `isTangentPortfolioN_and_portfolioVarN_le`: a portfolio with `Σw = λ(μ − r_f)` is a tangent
  portfolio and has the least variance at its budget and expected return.
* `portfolioVarN_minVarWeightTwo_le`: the closed-form two-asset weight minimises `portfolioVarN`.
* Two assets: `portfolioVarN_covTwo` and `portfolioVarTwo_eq_variance` identify the closed form
  `portfolioVarTwo` (`Choice/Portfolio/Markowitz.lean`) with the quadratic form `portfolioVarN` and
  with
  `Var[w R₁ + (1 − w) R₂]`; `marginalVariance_minVarWeightTwo` shows that at the minimum-variance
  weight each asset's marginal variance equals `V_min` (for `D ≠ 0`), so
  (`isConstrainedVarianceCriticalPoint_minVarWeightTwo`) that weight satisfies the budget-only
  Lagrangian FOC with multiplier `V_min`.

## What is *not* in this file

Necessity — "every constrained minimiser (or critical point) satisfies the Lagrangian
FOC for some multipliers" — is not proved. It requires showing `Σw ∈ span{1, μ}`, which by
the orthogonal-complement characterization is equivalent to
`Σw ⊥ {δw : 1·δw = 0 ∧ μ·δw = 0}`; in finite dimensions this needs
`Submodule.orthogonalComplement` machinery. The file proves the converse direction: every
weight satisfying the Lagrangian equations is a critical point and, for positive
semidefinite `Σ`, a global minimiser.

## Why this is "first principles"

`Choice/Portfolio/Markowitz.lean` states the two-asset minimum-variance weight in closed form and
`Choice/Portfolio/MarkowitzNAsset.lean` the n-asset variance identities. This file derives the
optimality of Lagrangian-FOC weights from the constrained variance-minimization problem,
for N assets with budget and target-return constraints (the standard textbook setup).

## References

* [K. Bodie and Marcus, *Investments*][BodieKaneMarcus], ch. 7
* [Boyd and Vandenberghe, *Convex Optimization*][BoydVandenberghe2004], §5.5.3
* [H. Markowitz, *Portfolio selection*][Markowitz1952]
* [R. C. Merton, *An analytic derivation of the efficient portfolio frontier*][Merton1972], §II

## Tags

Markowitz, mean-variance optimization, Lagrangian, first-order condition, two-fund separation,
minimum variance, constrained optimization, MSC 91G10, MSC 90C25, JEL G11
-/

@[expose] public section

namespace MathFin

open Finset

/-- **Constrained-variance critical-point property** (variational form):
`w` is a critical point of `(1/2) w^T Σ w` subject to `1^T w = 1` and
`μ^T w = m` if, for every admissible perturbation `δw` (orthogonal to
both constraint normals), the directional derivative `(Σw) · δw` vanishes. -/
def IsConstrainedVarianceCriticalPoint {ι : Type*} (s : Finset ι)
    (Sg : ι → ι → ℝ) (μ w : ι → ℝ) : Prop :=
  ∀ δw : ι → ℝ,
    (∑ i ∈ s, δw i) = 0 →
    (∑ i ∈ s, μ i * δw i) = 0 →
    (∑ i ∈ s, marginalVariance s Sg w i * δw i) = 0

/-- **Forward direction of the Lagrangian FOC characterisation**: if there
exist scalars `lam_1, lam_2` such that `(Σw)_i = lam_1 + lam_2 · μ_i` for every
asset `i ∈ s`, then `w` is a constrained-variance critical point.

The "Lagrangian FOC" `Σw = lam_1 · 1 + lam_2 · μ` is the textbook
characterisation of efficient portfolios. Only this direction (FOC ⟹ critical
point) is proved here, together with FOC ⟹ global minimum for positive
semidefinite `Σ` (`portfolioVarN_le_of_lagrangian_FOC`); that every
variance-minimising portfolio satisfies the FOC is not proved.

Proof: substitute the FOC into the directional-derivative sum and use the
perturbation's orthogonality to the constraint normals (`∑ δw = 0` kills
the `lam_1` term, `∑ μ δw = 0` kills the `lam_2 μ` term). -/
theorem isCriticalPoint_of_lagrangian_FOC
    {ι : Type*} (s : Finset ι) (Sg : ι → ι → ℝ) (μ w : ι → ℝ)
    (lam_1 lam_2 : ℝ)
    (h_FOC : ∀ i ∈ s, marginalVariance s Sg w i = lam_1 + lam_2 * μ i) :
    IsConstrainedVarianceCriticalPoint s Sg μ w := by
  intro δw h_sum_zero h_mu_zero
  -- ∑ (Σw)_i · δw_i = ∑ (lam_1 + lam_2 μ_i) · δw_i
  --                 = lam_1 · ∑ δw_i + lam_2 · ∑ μ_i δw_i
  --                 = lam_1 · 0 + lam_2 · 0 = 0
  have h_subst : ∑ i ∈ s, marginalVariance s Sg w i * δw i =
                 ∑ i ∈ s, (lam_1 + lam_2 * μ i) * δw i := by
    refine Finset.sum_congr rfl ?_
    intros i hi
    rw [h_FOC i hi]
  rw [h_subst]
  -- ∑ (lam_1 + lam_2 μ i) · δw i = lam_1 · ∑ δw + lam_2 · ∑ μ δw
  have h_split : ∑ i ∈ s, (lam_1 + lam_2 * μ i) * δw i =
                 lam_1 * (∑ i ∈ s, δw i) + lam_2 * (∑ i ∈ s, μ i * δw i) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ ↦ by ring)
  rw [h_split, h_sum_zero, h_mu_zero]
  ring

/-- **Self-dot identity for the variance objective**: `(1/2) w^T Σ w` (the
variance objective, up to constant 1/2) equals `(1/2) · ∑_i w_i · (Σw)_i`.
This is the same self-dot identity used in `Choice/Portfolio/SharpeFOCDerivation.lean`,
restated for N assets. -/
lemma variance_objective_eq_self_dot
    {ι : Type*} (s : Finset ι) (Sg : ι → ι → ℝ) (w : ι → ℝ) :
    (1 / 2 : ℝ) * portfolioVarN s w Sg =
      (1 / 2 : ℝ) * ∑ i ∈ s, w i * marginalVariance s Sg w i := by
  rw [portfolioVarN_eq_sum_mul_marginalVariance]

/-- **Directional derivative of the variance objective at `w` in direction
`δw`**, for *symmetric* `Sg`:

  `d/dt [(1/2) (w + t δw)^T Σ (w + t δw)] |_{t=0} = (Σw)^T δw`.

This is the calculus content underlying the FOC. Proof: expand the
quadratic in `t`, the linear coefficient is `(1/2) · [(δw)^T Σ w + w^T Σ δw]`,
which for symmetric `Σ` equals `(Σw)^T δw`.

(No `HasDerivAt` statement is proved: the identity below is the linear
coefficient of the polynomial `t ↦ ½ (w + t δw)ᵀ Σ (w + t δw)`, stated
algebraically.) -/
lemma quadratic_form_perturb_linear_coeff
    {ι : Type*} (s : Finset ι) (Sg : ι → ι → ℝ) (w δw : ι → ℝ)
    (h_symm : ∀ i ∈ s, ∀ j ∈ s, Sg i j = Sg j i) :
    (1 / 2 : ℝ) *
      ((∑ i ∈ s, ∑ j ∈ s, Sg i j * δw i * w j) +
       (∑ i ∈ s, ∑ j ∈ s, Sg i j * w i * δw j)) =
      ∑ i ∈ s, marginalVariance s Sg w i * δw i := by
  -- The cross-terms: ∑_{ij} Sg(i,j) (δw_i w_j + w_i δw_j)
  -- By symmetry Sg(i,j) = Sg(j,i), this equals 2 ∑_{ij} Sg(i,j) δw_i w_j
  -- (after relabelling). Then (1/2) · 2 = 1, giving ∑_i δw_i (Σw)_i.
  have h_swap : ∑ i ∈ s, ∑ j ∈ s, Sg i j * w i * δw j =
                ∑ i ∈ s, ∑ j ∈ s, Sg i j * δw i * w j := by
    -- Swap the indices using symmetry of Sg
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intros i hi
    refine Finset.sum_congr rfl ?_
    intros j hj
    rw [h_symm i hi j hj]
    ring
  rw [h_swap]
  unfold marginalVariance
  rw [show (1 / 2 : ℝ) * ((∑ i ∈ s, ∑ j ∈ s, Sg i j * δw i * w j) +
            (∑ i ∈ s, ∑ j ∈ s, Sg i j * δw i * w j)) =
        ∑ i ∈ s, ∑ j ∈ s, Sg i j * δw i * w j from by ring]
  -- ∑_i ∑_j Sg(i,j) δw_i w_j = ∑_i δw_i · (∑_j Sg(i,j) w_j) = ∑_i δw_i · (Σw)_i
  rw [show ∑ i ∈ s, ∑ j ∈ s, Sg i j * δw i * w j =
        ∑ i ∈ s, δw i * (∑ j ∈ s, Sg i j * w j) from
      Finset.sum_congr rfl (fun i _ ↦ by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun j _ ↦ by ring))]
  refine Finset.sum_congr rfl (fun i _ ↦ by ring)

/-- **Sufficient condition for tangency from the Lagrangian FOC**:
specialising to the case `lam_1 = 0` (no budget constraint, only expected-
return constraint), the FOC becomes `Σw = lam_2 · μ`, recovering the
cross-product tangent characterisation `IsTangentPortfolioN` from
`Choice/Portfolio/TangentPortfolio.lean`. -/
theorem isTangent_of_lagrangian_no_budget
    {ι : Type*} (s : Finset ι) (μ w : ι → ℝ) (Sg : ι → ι → ℝ)
    (lam_2 : ℝ)
    (h : ∀ i ∈ s, marginalVariance s Sg w i = lam_2 * μ i) :
    IsTangentPortfolioN s μ Sg w := by
  intro i hi j hj
  unfold marginalVariance at h
  rw [h i hi, h j hj]
  ring

/-! ### Global optimality of the Lagrangian FOC (KKT sufficiency) -/

section Global

open Matrix MeasureTheory ProbabilityTheory

variable {ι : Type*} [Fintype ι]

/-- On a finite asset set the marginal-variance vector is the matrix–vector product. -/
lemma marginalVariance_univ (Sg : Matrix ι ι ℝ) (w : ι → ℝ) :
    marginalVariance Finset.univ Sg w = Sg *ᵥ w := rfl

/-- On a finite asset set the portfolio variance is the quadratic form `w ⬝ᵥ (Σ *ᵥ w)`. -/
lemma portfolioVarN_univ (Sg : Matrix ι ι ℝ) (w : ι → ℝ) :
    portfolioVarN Finset.univ w Sg = w ⬝ᵥ (Sg *ᵥ w) :=
  portfolioVarN_eq_sum_mul_marginalVariance Finset.univ Sg w

/-- **The Lagrangian FOC is sufficient for minimum variance.** Let `Σ` be positive
semidefinite and let `w` meet the budget `∑ wᵢ = 1` and the return target `∑ wᵢ μᵢ = m`.
If `(Σw)ᵢ = λ₁ + λ₂ μᵢ` for every asset, then `w` has the least variance among all
portfolios meeting the same two constraints.

This is `kkt_sufficient_of_eq` for the QP `min ½ wᵀΣw` with the equality constraints
`1 ⬝ᵥ w = 1`, `μ ⬝ᵥ w = m` and multipliers `(λ₁, λ₂)`. Only sufficiency is proved: that
every minimiser satisfies the FOC is not. -/
theorem portfolioVarN_le_of_lagrangian_FOC {Sg : Matrix ι ι ℝ} (hSg : Sg.PosSemidef)
    {μ w : ι → ℝ} {m lam₁ lam₂ : ℝ}
    (hw₁ : ∑ i, w i = 1) (hwμ : portfolioReturn Finset.univ w μ = m)
    (h_FOC : ∀ i, marginalVariance Finset.univ Sg w i = lam₁ + lam₂ * μ i)
    {v : ι → ℝ} (hv₁ : ∑ i, v i = 1) (hvμ : portfolioReturn Finset.univ v μ = m) :
    portfolioVarN Finset.univ w Sg ≤ portfolioVarN Finset.univ v Sg := by
  have hfeas (x : ι → ℝ) (h₁ : ∑ i, x i = 1) (hμ : portfolioReturn Finset.univ x μ = m) :
      ∀ k, ![fun _ ↦ (1 : ℝ), μ] k ⬝ᵥ x = ![1, m] k := by
    intro k
    fin_cases k
    · simpa [dotProduct] using h₁
    · simpa [dotProduct, portfolioReturn, mul_comm] using hμ
  have hstat : 0 + Sg *ᵥ w = ∑ k, ![lam₁, lam₂] k • ![fun _ ↦ (1 : ℝ), μ] k := by
    rw [zero_add, ← marginalVariance_univ]
    funext i
    simp [Finset.sum_apply, Fin.sum_univ_two, h_FOC]
  have key := kkt_sufficient_of_eq hSg (hfeas w hw₁ hwμ) hstat v (hfeas v hv₁ hvμ)
  simp only [qpObj, zero_dotProduct, zero_add] at key
  rw [portfolioVarN_univ, portfolioVarN_univ]
  linarith

omit [Fintype ι] in
/-- **Covariance matrices are positive semidefinite** (in Mathlib's `Matrix.PosSemidef`
sense): the covariance matrix of square-integrable returns is symmetric
(`covariance_comm`) and its quadratic form is the variance of `∑ vᵢ Rᵢ`
(`covariance_kernel_psd`). -/
theorem posSemidef_covariance [Finite ι] {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsFiniteMeasure P] (R : ι → Ω → ℝ) (hR : ∀ i, MemLp (R i) 2 P) :
    (Matrix.of fun i j ↦ cov[R i, R j; P]).PosSemidef := by
  cases nonempty_fintype ι
  refine PosSemidef.of_dotProduct_mulVec_nonneg (IsHermitian.ext fun i j ↦ by
    simp only [of_apply, star_trivial]; exact covariance_comm _ _) fun v ↦ ?_
  refine (covariance_kernel_psd Finset.univ R (fun i _ ↦ hR i) v).trans_eq ?_
  simp only [Pi.star_apply, star_trivial, dotProduct, mulVec, of_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring

/-- **Markowitz for random returns.** For square-integrable returns `R`, a portfolio `w`
meeting the budget and the return target whose covariances with the assets satisfy the
Lagrangian FOC `∑ⱼ cov(Rᵢ, Rⱼ) wⱼ = λ₁ + λ₂ μᵢ` minimises the variance of the portfolio
return `∑ wᵢ Rᵢ` among all portfolios meeting the same constraints. The positive
semidefiniteness that `portfolioVarN_le_of_lagrangian_FOC` needs is derived
(`posSemidef_covariance`), not assumed. Sufficiency only. -/
theorem variance_le_of_lagrangian_FOC {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsFiniteMeasure P] (R : ι → Ω → ℝ) (hR : ∀ i, MemLp (R i) 2 P)
    {μ w : ι → ℝ} {m lam₁ lam₂ : ℝ}
    (hw₁ : ∑ i, w i = 1) (hwμ : portfolioReturn Finset.univ w μ = m)
    (h_FOC : ∀ i, marginalVariance Finset.univ (fun i j ↦ cov[R i, R j; P]) w i =
      lam₁ + lam₂ * μ i)
    {v : ι → ℝ} (hv₁ : ∑ i, v i = 1) (hvμ : portfolioReturn Finset.univ v μ = m) :
    Var[∑ i, w i • R i; P] ≤ Var[∑ i, v i • R i; P] := by
  have hR' : ∀ i ∈ Finset.univ, MemLp (R i) 2 P := fun i _ ↦ hR i
  rw [← portfolioVarN_covariance_eq_variance _ w R hR',
    ← portfolioVarN_covariance_eq_variance _ v R hR']
  exact portfolioVarN_le_of_lagrangian_FOC (posSemidef_covariance R hR) hw₁ hwμ h_FOC
    hv₁ hvμ

/-- **The tangent portfolio is mean–variance efficient.** If `Σw = λ(μ − r_f)` and `∑ wᵢ = 1`,
then `w` is a tangent portfolio, and it has the least variance among the portfolios with the same
budget and expected return: the tangency condition is the Lagrangian condition with multipliers
`(−λ r_f, λ)`. Positive semidefiniteness of `Σ` is a hypothesis. -/
theorem isTangentPortfolioN_and_portfolioVarN_le {Sg : Matrix ι ι ℝ} (hSg : Sg.PosSemidef)
    {μ w : ι → ℝ} {rf lam : ℝ} (hw₁ : ∑ i, w i = 1)
    (h : ∀ i, marginalVariance Finset.univ Sg w i = lam * (μ i - rf)) :
    IsTangentPortfolioN Finset.univ (fun i ↦ μ i - rf) Sg w ∧
      ∀ v : ι → ℝ, ∑ i, v i = 1 →
        portfolioReturn Finset.univ v μ = portfolioReturn Finset.univ w μ →
        portfolioVarN Finset.univ w Sg ≤ portfolioVarN Finset.univ v Sg :=
  ⟨isTangent_of_proportional _ _ _ _ lam fun i _ ↦ h i,
    fun _ hv₁ hvμ ↦ portfolioVarN_le_of_lagrangian_FOC (lam₁ := -(lam * rf)) (lam₂ := lam)
      hSg hw₁ rfl (fun i ↦ by rw [h i]; ring) hv₁ hvμ⟩

end Global

/-! ### Two assets: the closed form as an instance -/

section TwoAsset

open Matrix MeasureTheory ProbabilityTheory

/-- The two-asset `portfolioVarN` with the covariance matrix `covTwo` and weights
`(w, 1 − w)` is the closed form `portfolioVarTwo` of `Choice/Portfolio/Markowitz.lean`. -/
lemma portfolioVarN_covTwo (σ₁ σ₂ ρ w : ℝ) :
    portfolioVarN Finset.univ ![w, 1 - w] (covTwo σ₁ σ₂ ρ) = portfolioVarTwo σ₁ σ₂ ρ w := by
  rw [portfolioVarN_univ, portfolioVarTwo_eq_dotProduct]

/-- **The two-asset variance formula is the variance of the portfolio return.** For
square-integrable returns with `Var[R₁] = σ₁²`, `Var[R₂] = σ₂²` and `cov[R₁, R₂] = ρσ₁σ₂`,
`portfolioVarTwo σ₁ σ₂ ρ w = Var[w R₁ + (1 − w) R₂]`: the closed form of
`Choice/Portfolio/Markowitz.lean` is derived from the covariance kernel
(`portfolioVarN_covariance_eq_variance`), not posited. -/
theorem portfolioVarTwo_eq_variance {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsFiniteMeasure P] {R₁ R₂ : Ω → ℝ} (h₁ : MemLp R₁ 2 P) (h₂ : MemLp R₂ 2 P)
    {σ₁ σ₂ ρ : ℝ} (hv₁ : Var[R₁; P] = σ₁ ^ 2) (hv₂ : Var[R₂; P] = σ₂ ^ 2)
    (hc : cov[R₁, R₂; P] = ρ * σ₁ * σ₂) (w : ℝ) :
    portfolioVarTwo σ₁ σ₂ ρ w = Var[w • R₁ + (1 - w) • R₂; P] := by
  have hR : ∀ i ∈ (Finset.univ : Finset (Fin 2)), MemLp (![R₁, R₂] i) 2 P := by
    intro i _
    fin_cases i
    · exact h₁
    · exact h₂
  have h := portfolioVarN_covariance_eq_variance Finset.univ ![w, 1 - w] ![R₁, R₂] hR
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  rw [← h, portfolioVarN, portfolioVarTwo]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    covariance_self h₁.aestronglyMeasurable.aemeasurable,
    covariance_self h₂.aestronglyMeasurable.aemeasurable, covariance_comm R₂ R₁, hv₁, hv₂, hc]
  ring

/-- **The minimum-variance mix equalises marginal variances.** At the two-asset
minimum-variance weight `w* = minVarWeightTwo`, each asset's marginal variance `(Σw*)ᵢ` —
its covariance with the portfolio — equals the minimum variance `V_min`. -/
theorem marginalVariance_minVarWeightTwo {σ₁ σ₂ ρ : ℝ} (hD : minVarDenom σ₁ σ₂ ρ ≠ 0)
    (i : Fin 2) :
    marginalVariance Finset.univ (covTwo σ₁ σ₂ ρ)
        ![minVarWeightTwo σ₁ σ₂ ρ, 1 - minVarWeightTwo σ₁ σ₂ ρ] i =
      minPortfolioVarTwo σ₁ σ₂ ρ := by
  have hw : minVarWeightTwo σ₁ σ₂ ρ * minVarDenom σ₁ σ₂ ρ = σ₂ ^ 2 - ρ * σ₁ * σ₂ :=
    div_mul_cancel₀ _ hD
  have hV : minPortfolioVarTwo σ₁ σ₂ ρ * minVarDenom σ₁ σ₂ ρ =
      σ₁ ^ 2 * σ₂ ^ 2 * (1 - ρ ^ 2) :=
    div_mul_cancel₀ _ hD
  have hDdef : minVarDenom σ₁ σ₂ ρ = σ₁ ^ 2 - 2 * ρ * σ₁ * σ₂ + σ₂ ^ 2 := rfl
  rw [marginalVariance_univ]
  fin_cases i
  · simp only [mulVec, dotProduct, covTwo, Fin.zero_eta, Fin.isValue, of_apply,
      cons_val', cons_val_fin_one, cons_val_zero, Fin.sum_univ_two, cons_val_one]
    refine mul_right_cancel₀ hD ?_
    linear_combination (σ₁ ^ 2 - ρ * σ₁ * σ₂) * hw + ρ * σ₁ * σ₂ * hDdef - hV
  · simp only [mulVec, dotProduct, covTwo, Fin.mk_one, Fin.isValue, of_apply,
      cons_val', cons_val_fin_one, cons_val_one, Fin.sum_univ_two, cons_val_zero]
    refine mul_right_cancel₀ hD ?_
    linear_combination (ρ * σ₁ * σ₂ - σ₂ ^ 2) * hw + σ₂ ^ 2 * hDdef - hV

/-- **The two-asset minimum-variance weight satisfies the Lagrangian FOC** with budget
multiplier `V_min` (and no return constraint, `μ = 0`), so it is a critical point of the
variance under the budget constraint (`isCriticalPoint_of_lagrangian_FOC`). -/
theorem isConstrainedVarianceCriticalPoint_minVarWeightTwo {σ₁ σ₂ ρ : ℝ}
    (hD : minVarDenom σ₁ σ₂ ρ ≠ 0) :
    IsConstrainedVarianceCriticalPoint Finset.univ (covTwo σ₁ σ₂ ρ) 0
      ![minVarWeightTwo σ₁ σ₂ ρ, 1 - minVarWeightTwo σ₁ σ₂ ρ] :=
  isCriticalPoint_of_lagrangian_FOC _ _ 0 _ (minPortfolioVarTwo σ₁ σ₂ ρ) 0 fun i _ ↦ by
    rw [marginalVariance_minVarWeightTwo hD, zero_mul, add_zero]

/-- **The closed-form two-asset weight minimises the portfolio variance.** When
`D = σ₁² − 2ρσ₁σ₂ + σ₂² > 0`, the weights `(w*, 1 − w*)` have the least `portfolioVarN` under
`covTwo` among all two-asset budgets `(w, 1 − w)`. -/
theorem portfolioVarN_minVarWeightTwo_le {σ₁ σ₂ ρ : ℝ} (hD : 0 < minVarDenom σ₁ σ₂ ρ) (w : ℝ) :
    portfolioVarN Finset.univ ![minVarWeightTwo σ₁ σ₂ ρ, 1 - minVarWeightTwo σ₁ σ₂ ρ]
        (covTwo σ₁ σ₂ ρ) ≤ portfolioVarN Finset.univ ![w, 1 - w] (covTwo σ₁ σ₂ ρ) := by
  rw [portfolioVarN_covTwo, portfolioVarN_covTwo, portfolioVarTwo_at_minVarWeight hD.ne']
  exact portfolioVarTwo_ge_min hD w

end TwoAsset

end MathFin
