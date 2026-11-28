/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Choice.Portfolio.BlackLitterman
public import LeanPool.MathFin.Choice.Portfolio.ConvexQPKKT
public import Mathlib.Logic.Equiv.PartialEquiv

/-!
# N-dimensional Black-Litterman posterior (matrix form)

The pre-existing `Choice/Portfolio/BlackLitterman.lean` derives the 1-D Bayesian
update for a single asset with a single direct view. This file extends to
the **N-asset / m-view matrix** formulation, the standard form used in
production.

## Setup

* `π : Fin n → ℝ` — prior mean of expected returns.
* `Sg_inv : Matrix (Fin n) (Fin n) ℝ` — prior *precision* (inverse covariance).
* `Q : Fin m → ℝ` — view vector (target values).
* `P : Matrix (Fin m) (Fin n) ℝ` — view-selection matrix (which linear
  combinations of `μ` the views talk about).
* `Om_inv : Matrix (Fin m) (Fin m) ℝ` — view *precision* (inverse covariance
  of view noise).

## Posterior identities

In the Gaussian prior/view model, the Bayesian-conjugate update gives

  `posterior_precision = Sg_inv + Pᵀ · Om_inv · P`,             (additive precision)
  `posterior_precision · μ_post = Sg_inv · π + Pᵀ · Om_inv · Q`. (normal equation)

The Gaussian conditioning behind these identities is not formalized: this file takes
the normal equation as the definition of the posterior mean (`IsBLPosteriorMean`).
When posterior precision is invertible, the posterior mean has the explicit
form

  `μ_post = (posterior_precision)⁻¹ · (Sg_inv · π + Pᵀ · Om_inv · Q)`.

This file proves: (a) the explicit form satisfies the normal equation,
(b) the solution to the normal equation is *unique* (when precision is
invertible), and (c) for positive semidefinite precisions, every solution of the
normal equation minimises the **mixed-estimation loss** of Theil and Goldberger,

  `½ (μ − π)ᵀ Sg_inv (μ − π) + ½ (Pμ − Q)ᵀ Om_inv (Pμ − Q)`,

the generalized-least-squares fit of `μ` to the prior and the views together — by
the KKT sufficiency theorem of `Choice/Portfolio/ConvexQPKKT.lean` with no constraints.

## Characterisations

The 1-D `BlackLitterman.lean` stated the posterior as a closed form and
verified three equivalent forms (symmetric, precision-weighted, harmonic-
variance). This file characterises the N-dim posterior as the **unique solution
of a linear system** — the natural way to characterise it without ad-hoc
inverses, and the way it is used in practice (LU/Cholesky solve rather
than explicit inversion) — and as a **minimiser of the mixed-estimation loss**.

## Connection to the 1-D module

At `n = 1`, `m = 1`, `P = (1)`, `Sg_inv = (1/s0sq)`, `Om_inv = (1/s1sq)` the
normal equation below reduces to the scalar Bayesian update behind
`posteriorMean1d` (`Choice/Portfolio/BlackLitterman.lean`); `isBLPosteriorMean_one_dim`
makes this precise (the scalar `posteriorMean1d` is the BL posterior mean at
`n = 1`), and the matrix form here is its N-asset generalisation.

## Main definitions

* `blPosteriorPrecision`: the posterior precision `Sg_inv + Pᵀ·Om_inv·P`.
* `blPrecisionWeightedMean`: the right-hand side `Sg_inv·π + Pᵀ·Om_inv·Q` of the normal equation.
* `IsBLPosteriorMean`: `μ_post` solves the Black-Litterman normal equation.
* `blPosteriorMean`: the explicit solution, the inverse of the posterior precision applied to
  the precision-weighted mean (when the posterior precision is invertible).
* `blLoss`: the Theil-Goldberger mixed-estimation loss, half the prior-precision-weighted squared
  distance from `π` plus half the view-precision-weighted squared distance of `P·μ` from `Q`.

## Main results

* `blPosteriorMean_satisfies_normal_eq`: when the posterior precision is invertible, the explicit
  form `blPosteriorMean` satisfies the normal equation `IsBLPosteriorMean`.
* `IsBLPosteriorMean.unique`: solution to the normal equation is unique
  (when posterior precision is invertible); dot-notation `h.unique`.
* `blLoss_eq_qpObj`: for symmetric `Sg_inv` and `Om_inv`, the mixed-estimation loss `blLoss` is
  the convex QP objective `qpObj` with Hessian the posterior precision, up to a constant.
* `IsBLPosteriorMean.blLoss_le`: a solution of the normal equation minimises `blLoss`
  when `Sg_inv` and `Om_inv` are positive semidefinite.

## References

* [Black and Litterman, *Global portfolio optimization*][BlackLitterman1992]
* [Theil and Goldberger, *On pure and mixed statistical estimation in
  economics*][TheilGoldberger1961]

## Tags

Black-Litterman model, posterior precision, mixed estimation, Theil-Goldberger, normal equation,
investor views, generalized least squares, MSC 91G10, MSC 62F10, JEL G11
-/

@[expose] public section

namespace MathFin

open Matrix

/-- **N-dim BL posterior precision**: additive Bayesian update of precision.
`posterior_precision = prior_precision + view_precision`, where the view
precision is `Pᵀ · Om_inv · P` (the information about `μ` provided by the
linear views). -/
def blPosteriorPrecision {n m : ℕ}
    (Sg_inv : Matrix (Fin n) (Fin n) ℝ)
    (P : Matrix (Fin m) (Fin n) ℝ)
    (Om_inv : Matrix (Fin m) (Fin m) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Sg_inv + Pᵀ * Om_inv * P

/-- **N-dim BL precision-weighted mean RHS**: `Sg_inv · π + Pᵀ · Om_inv · Q`.
This is the RHS of the BL normal equation. -/
def blPrecisionWeightedMean {n m : ℕ}
    (π : Fin n → ℝ) (Q : Fin m → ℝ)
    (Sg_inv : Matrix (Fin n) (Fin n) ℝ)
    (P : Matrix (Fin m) (Fin n) ℝ)
    (Om_inv : Matrix (Fin m) (Fin m) ℝ) :
    Fin n → ℝ :=
  Sg_inv *ᵥ π + (Pᵀ * Om_inv) *ᵥ Q

/-- **N-dim BL posterior mean as the normal-equation solution** (variational
characterisation). A vector `μ_post : Fin n → ℝ` is a BL posterior mean iff
it satisfies

  `(Sg_inv + Pᵀ · Om_inv · P) · μ_post = Sg_inv · π + Pᵀ · Om_inv · Q`.

This characterisation does not require the precision to be invertible — it
is well-defined for any precision (the existence of a solution requires
the RHS to be in the column span of the LHS; uniqueness requires
invertibility). -/
def IsBLPosteriorMean {n m : ℕ}
    (μ_post π : Fin n → ℝ) (Q : Fin m → ℝ)
    (Sg_inv : Matrix (Fin n) (Fin n) ℝ)
    (P : Matrix (Fin m) (Fin n) ℝ)
    (Om_inv : Matrix (Fin m) (Fin m) ℝ) : Prop :=
  (blPosteriorPrecision Sg_inv P Om_inv).mulVec μ_post =
    blPrecisionWeightedMean π Q Sg_inv P Om_inv

/-- **Explicit form of the N-dim BL posterior mean** (when posterior
precision is invertible): apply the inverse to the precision-weighted mean. -/
noncomputable def blPosteriorMean {n m : ℕ}
    (π : Fin n → ℝ) (Q : Fin m → ℝ)
    (Sg_inv : Matrix (Fin n) (Fin n) ℝ)
    (P : Matrix (Fin m) (Fin n) ℝ)
    (Om_inv : Matrix (Fin m) (Fin m) ℝ) :
    Fin n → ℝ :=
  (blPosteriorPrecision Sg_inv P Om_inv)⁻¹ *ᵥ
    blPrecisionWeightedMean π Q Sg_inv P Om_inv

/-- **Explicit form satisfies the normal equation** (when posterior precision
is invertible). -/
theorem blPosteriorMean_satisfies_normal_eq {n m : ℕ}
    (π : Fin n → ℝ) (Q : Fin m → ℝ)
    (Sg_inv : Matrix (Fin n) (Fin n) ℝ)
    (P : Matrix (Fin m) (Fin n) ℝ)
    (Om_inv : Matrix (Fin m) (Fin m) ℝ)
    [Invertible (blPosteriorPrecision Sg_inv P Om_inv)] :
    IsBLPosteriorMean (blPosteriorMean π Q Sg_inv P Om_inv) π Q Sg_inv P Om_inv := by
  unfold IsBLPosteriorMean blPosteriorMean
  rw [Matrix.mulVec_mulVec]
  rw [Matrix.mul_inv_of_invertible]
  rw [Matrix.one_mulVec]

/-- **Uniqueness of the BL posterior mean** (when posterior precision is
invertible): any solution to the normal equation equals the explicit form. -/
theorem IsBLPosteriorMean.unique {n m : ℕ}
    {μ_post π : Fin n → ℝ} {Q : Fin m → ℝ}
    {Sg_inv : Matrix (Fin n) (Fin n) ℝ}
    {P : Matrix (Fin m) (Fin n) ℝ}
    {Om_inv : Matrix (Fin m) (Fin m) ℝ}
    [Invertible (blPosteriorPrecision Sg_inv P Om_inv)]
    (h : IsBLPosteriorMean μ_post π Q Sg_inv P Om_inv) :
    μ_post = blPosteriorMean π Q Sg_inv P Om_inv := by
  unfold IsBLPosteriorMean at h
  unfold blPosteriorMean
  rw [← h]
  rw [Matrix.mulVec_mulVec]
  rw [Matrix.inv_mul_of_invertible]
  rw [Matrix.one_mulVec]

/-- **n = 1 recovers the scalar posterior**: at `n = m = 1`, `P = 1`,
`Sg_inv = (1/s0sq)`, `Om_inv = (1/s1sq)`, the scalar `posteriorMean1d` is the
BL posterior mean — the 1-D case of the matrix normal equation, showing the
N-asset form specialises to `Choice/Portfolio/BlackLitterman`. -/
theorem isBLPosteriorMean_one_dim (π₀ Q₀ s0sq s1sq : ℝ) (h₀ : 0 < s0sq) (h₁ : 0 < s1sq) :
    IsBLPosteriorMean ![posteriorMean1d π₀ Q₀ s0sq s1sq] ![π₀] ![Q₀]
        (!![1 / s0sq]) (1 : Matrix (Fin 1) (Fin 1) ℝ) (!![1 / s1sq]) := by
  have h₀' : s0sq ≠ 0 := h₀.ne'
  have h₁' : s1sq ≠ 0 := h₁.ne'
  unfold IsBLPosteriorMean blPosteriorPrecision blPrecisionWeightedMean posteriorMean1d
  funext i
  fin_cases i
  simp [Matrix.mulVec, dotProduct, Matrix.add_apply, Matrix.transpose_one,
    Matrix.cons_val_fin_one, Matrix.of_apply]
  field_simp
  ring

/-- **Black–Litterman mixed-estimation loss** (Theil–Goldberger): half the
prior-precision-weighted squared distance of `μ` from the prior mean `π`, plus half the
view-precision-weighted squared residual of the views `P μ − Q`. -/
noncomputable def blLoss {n m : ℕ} (π : Fin n → ℝ) (Q : Fin m → ℝ)
    (Sg_inv : Matrix (Fin n) (Fin n) ℝ) (P : Matrix (Fin m) (Fin n) ℝ)
    (Om_inv : Matrix (Fin m) (Fin m) ℝ) (μ : Fin n → ℝ) : ℝ :=
  (1 / 2) * ((μ - π) ⬝ᵥ (Sg_inv *ᵥ (μ - π))) +
    (1 / 2) * ((P *ᵥ μ - Q) ⬝ᵥ (Om_inv *ᵥ (P *ᵥ μ - Q)))

/-- For symmetric precisions, the mixed-estimation loss is the convex QP objective
`qpObj` with linear term `−(Sg_inv π + Pᵀ Om_inv Q)` and Hessian the posterior precision
`Sg_inv + Pᵀ Om_inv P`, plus a constant: expanding the two quadratics, the cross terms
are collected by symmetry and `(Pμ) ⬝ (Om_inv x) = μ ⬝ (Pᵀ Om_inv x)`. -/
lemma blLoss_eq_qpObj {n m : ℕ} (π : Fin n → ℝ) (Q : Fin m → ℝ)
    {Sg_inv : Matrix (Fin n) (Fin n) ℝ} (hS : Sg_inv.IsSymm) (P : Matrix (Fin m) (Fin n) ℝ)
    {Om_inv : Matrix (Fin m) (Fin m) ℝ} (hO : Om_inv.IsSymm) (μ : Fin n → ℝ) :
    blLoss π Q Sg_inv P Om_inv μ =
      qpObj (-blPrecisionWeightedMean π Q Sg_inv P Om_inv)
          (blPosteriorPrecision Sg_inv P Om_inv) μ +
        ((1 / 2) * (π ⬝ᵥ (Sg_inv *ᵥ π)) + (1 / 2) * (Q ⬝ᵥ (Om_inv *ᵥ Q))) := by
  have hPOP : (P *ᵥ μ) ⬝ᵥ (Om_inv *ᵥ (P *ᵥ μ)) = μ ⬝ᵥ ((Pᵀ * Om_inv * P) *ᵥ μ) := by
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec μ Pᵀ, vecMul_transpose]
  have hPOQ : (P *ᵥ μ) ⬝ᵥ (Om_inv *ᵥ Q) = ((Pᵀ * Om_inv) *ᵥ Q) ⬝ᵥ μ := by
    rw [← mulVec_mulVec, dotProduct_comm _ μ, dotProduct_mulVec μ Pᵀ, vecMul_transpose]
  simp only [blLoss, qpObj, blPrecisionWeightedMean, blPosteriorPrecision, mulVec_sub,
    sub_dotProduct, dotProduct_sub, add_mulVec, dotProduct_add, add_dotProduct, neg_dotProduct]
  rw [dotProduct_mulVec_symm_comm hO Q (P *ᵥ μ), hPOQ, hPOP,
    dotProduct_mulVec_symm_comm hS π μ, dotProduct_comm (Sg_inv *ᵥ π) μ]
  ring

/-- **The Black–Litterman posterior mean minimises the mixed-estimation loss.** If
`μ_post` solves the normal equation and the prior and view precisions are positive
semidefinite, then `blLoss μ_post ≤ blLoss μ` for every `μ`: the posterior mean is the
generalized-least-squares fit of `μ` to the prior and the views (Theil–Goldberger mixed
estimation). Proof: `blLoss_eq_qpObj` and the unconstrained case (`κ = Fin 0`) of
`kkt_sufficient_of_eq`, whose stationarity condition is the normal equation; the
posterior precision `Sg_inv + Pᵀ Om_inv P` is positive semidefinite as a sum of
positive semidefinite matrices. -/
theorem IsBLPosteriorMean.blLoss_le {n m : ℕ} {μ_post π : Fin n → ℝ} {Q : Fin m → ℝ}
    {Sg_inv : Matrix (Fin n) (Fin n) ℝ} {P : Matrix (Fin m) (Fin n) ℝ}
    {Om_inv : Matrix (Fin m) (Fin m) ℝ} (h : IsBLPosteriorMean μ_post π Q Sg_inv P Om_inv)
    (hS : Sg_inv.PosSemidef) (hO : Om_inv.PosSemidef) (μ : Fin n → ℝ) :
    blLoss π Q Sg_inv P Om_inv μ_post ≤ blLoss π Q Sg_inv P Om_inv μ := by
  have hS' : Sg_inv.IsSymm := isHermitian_iff_isSymm.mp hS.isHermitian
  have hO' : Om_inv.IsSymm := isHermitian_iff_isSymm.mp hO.isHermitian
  have hA : (blPosteriorPrecision Sg_inv P Om_inv).PosSemidef := by
    simpa [blPosteriorPrecision, conjTranspose_eq_transpose_of_trivial] using
      hS.add (hO.conjTranspose_mul_mul_same P)
  rw [blLoss_eq_qpObj π Q hS' P hO', blLoss_eq_qpObj π Q hS' P hO', add_le_add_iff_right]
  refine kkt_sufficient_of_eq (a := fun _ : Fin 0 ↦ 0) (b := fun _ ↦ 0) (ν := fun _ ↦ 0) hA
    (fun k ↦ k.elim0) ?_ μ fun k ↦ k.elim0
  simp only [Finset.univ_eq_empty, Finset.sum_empty, neg_add_eq_zero]
  exact Eq.symm h

end MathFin
