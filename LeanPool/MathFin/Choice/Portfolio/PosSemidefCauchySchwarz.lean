/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Choice.Portfolio.ConvexQPKKT

/-!
# Cauchy–Schwarz for positive semidefinite forms, and the mean–standard-deviation tradeoff

The Cauchy–Schwarz inequality for the semi-inner product `⟨u, v⟩ = u ⬝ᵥ (Sig *ᵥ v)` induced by
a positive semidefinite matrix `Sig` over `ι → ℝ`, and its application to the tradeoff form of
the Markowitz mean–variance problem.

* `posSemidef_cauchySchwarz`: for `Sig` positive semidefinite,
  `|x ⬝ᵥ (Sig *ᵥ y)| ≤ √(x ⬝ᵥ (Sig *ᵥ x)) · √(y ⬝ᵥ (Sig *ᵥ y))`. The form is degenerate when
  `Sig` is singular, and the bound holds all the same. It is Mathlib's
  Cauchy–Schwarz for bilinear forms nonnegative on the diagonal, applied to `Matrix.toBilin'`.
* `pricedReturn_le_of_kkt`: if `x1` satisfies the KKT stationarity, dual-feasibility and
  complementary-slackness conditions of the risk-penalized QP
  `min -μ ⬝ᵥ x + (t₁/2) · x ⬝ᵥ (Sig *ᵥ x)` (with `Sig` PSD and `t₁ ≥ 0`; the KKT machinery is
  that of `MathFin.Choice.Portfolio.ConvexQPKKT`), then `x1` maximizes the mean–standard-deviation
  objective `μ ⬝ᵥ y - t₁·√(x1 ⬝ᵥ (Sig *ᵥ x1)) · √(y ⬝ᵥ (Sig *ᵥ y))` over every feasible `y`.
  Stationarity, rearranged to `μ = t₁ • Sig *ᵥ x1 + ∑ u k • a k`, turns the return gap into
  `t₁ · (Q - X)` plus the complementary-slackness terms (nonpositive at any feasible `y`, by
  `kkt_complementary_term_nonneg`), and Cauchy–Schwarz bounds the bilinear term `Q`.

KKT necessity (that an optimal solution is a KKT point) is not proved; the module certifies
candidates, as `MathFin.Choice.Portfolio.ConvexQPKKT` does.

## Main definitions

* `pricedReturn`: the return `μ ⬝ᵥ y` minus the charge
  `t₁ · √(x1 ⬝ᵥ (Sig *ᵥ x1)) · √(y ⬝ᵥ (Sig *ᵥ y))`, with the price of risk calibrated on the
  benchmark `x1`.

## Main results

* `posSemidef_cauchySchwarz`: for a positive semidefinite matrix `Sig`,
  `|x ⬝ᵥ (Sig *ᵥ y)| ≤ √(x ⬝ᵥ (Sig *ᵥ x)) · √(y ⬝ᵥ (Sig *ᵥ y))`.
* `pricedReturn_le_of_kkt`: a point `x1` satisfying the KKT stationarity, dual-feasibility and
  complementary-slackness conditions of the risk-penalized quadratic program (with `Sig`
  positive semidefinite and `t₁ ≥ 0`) maximizes `pricedReturn` over every feasible `y`. It
  certifies a candidate; KKT necessity is not proved.

## References

* [Boyd and Vandenberghe, *Convex Optimization*][BoydVandenberghe2004]
* [H. Markowitz, *Portfolio selection*][Markowitz1952]

## Tags

Cauchy-Schwarz inequality, mean-standard deviation tradeoff, positive semidefinite form, Markowitz,
KKT conditions, risk aversion, MSC 91G10, MSC 90C25, JEL G11
-/

@[expose] public section

namespace MathFin

open Matrix

variable {ι : Type*} [Fintype ι] {Sig : Matrix ι ι ℝ}

/-- **Cauchy–Schwarz for a positive semidefinite bilinear form**: for `Sig` PSD,

`|x ⬝ᵥ (Sig *ᵥ y)| ≤ √(x ⬝ᵥ (Sig *ᵥ x)) · √(y ⬝ᵥ (Sig *ᵥ y))`.

The form `⟨u, v⟩ = u ⬝ᵥ (Sig *ᵥ v)` is a semi-inner product only (degenerate when `Sig` is
singular). This is Mathlib's Cauchy–Schwarz for a bilinear form that is nonnegative on the
diagonal (`LinearMap.BilinForm.apply_mul_apply_le_of_forall_zero_le`), applied to
`Matrix.toBilin' Sig`, with symmetry of `Sig` matching the two cross terms. -/
theorem posSemidef_cauchySchwarz (hpsd : Sig.PosSemidef) (x y : ι → ℝ) :
    |x ⬝ᵥ (Sig *ᵥ y)| ≤
      Real.sqrt (x ⬝ᵥ (Sig *ᵥ x)) * Real.sqrt (y ⬝ᵥ (Sig *ᵥ y)) := by
  classical
  have hB (u v : ι → ℝ) : Matrix.toBilin' Sig u v = u ⬝ᵥ (Sig *ᵥ v) :=
    Matrix.toBilin'_apply' Sig u v
  have hs (u : ι → ℝ) : 0 ≤ Matrix.toBilin' Sig u u := by
    rw [hB]; simpa using hpsd.dotProduct_mulVec_nonneg u
  have hCS := LinearMap.BilinForm.apply_mul_apply_le_of_forall_zero_le (Matrix.toBilin' Sig) hs x y
  rw [hB, hB, hB, hB,
    dotProduct_mulVec_symm_comm (isHermitian_iff_isSymm.mp hpsd.isHermitian) y x] at hCS
  rw [← Real.sqrt_mul (hs x |>.trans_eq (hB x x)), ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (by nlinarith [hCS])

/-- The **priced return** of `y` at the price of risk `t₁ · √(x1 ⬝ᵥ (Sig *ᵥ x1))`
calibrated on the benchmark `x1`: the return `μ ⬝ᵥ y` minus the charge
`t₁ · √(x1 ⬝ᵥ (Sig *ᵥ x1)) · √(y ⬝ᵥ (Sig *ᵥ y))` — the price `t₁ · √(x1 ⬝ᵥ (Sig *ᵥ x1))`
per unit of the holder's own risk `√(y ⬝ᵥ (Sig *ᵥ y))`. Maximizing it over a
feasible set is the risk-adjusted (tradeoff) form of portfolio selection. -/
noncomputable def pricedReturn (μ : ι → ℝ) (t₁ : ℝ) (Sig : Matrix ι ι ℝ)
    (x1 y : ι → ℝ) : ℝ :=
  μ ⬝ᵥ y - t₁ * Real.sqrt (x1 ⬝ᵥ (Sig *ᵥ x1)) * Real.sqrt (y ⬝ᵥ (Sig *ᵥ y))

/-- **A mean–variance KKT point maximizes the mean–standard-deviation objective** at the price of
risk `t₁·√(x1'Σx1)`: if `x1` satisfies the KKT stationarity, dual feasibility and
complementary-slackness conditions of the risk-penalized QP
`min −μ ⬝ᵥ x + (t₁/2) · x ⬝ᵥ (Sig *ᵥ x)`, with `Sig` positive semidefinite and `t₁ ≥ 0`, then
for every feasible competitor `y`

`pricedReturn μ t₁ Sig x1 y ≤ pricedReturn μ t₁ Sig x1 x1`.

Stationarity, rearranged to `μ = t₁ • Sig *ᵥ x1 + ∑ u k • a k`, turns the return gap into
`t₁ · (Q − X)` plus the complementary-slackness terms (nonpositive at any feasible `y`), and
Cauchy–Schwarz for the PSD form bounds `Q`. `x1`'s own primal feasibility is not assumed:
complementary slackness alone forces `u k = 0` at every `k` where `a k ⬝ᵥ x1 > b k`, as for
`kkt_sufficient` in `MathFin.Choice.Portfolio.ConvexQPKKT`. -/
theorem pricedReturn_le_of_kkt {κ : Type*} [Fintype κ]
    {μ : ι → ℝ} (hpsd : Sig.PosSemidef) {t₁ : ℝ} (ht₁ : 0 ≤ t₁)
    {a : κ → ι → ℝ} {b : κ → ℝ} {x1 : ι → ℝ} {u : κ → ℝ}
    (hu_nonneg : ∀ k, 0 ≤ u k)
    (hstat : -μ + t₁ • Sig *ᵥ x1 = -∑ k, u k • a k)
    (hcs : ∀ k, u k * (a k ⬝ᵥ x1 - b k) = 0)
    {y : ι → ℝ} (hfeasy : ∀ k, a k ⬝ᵥ y ≤ b k) :
    pricedReturn μ t₁ Sig x1 y ≤ pricedReturn μ t₁ Sig x1 x1 := by
  have hC : Sig.IsSymm := isHermitian_iff_isSymm.mp hpsd.isHermitian
  have hX : 0 ≤ x1 ⬝ᵥ (Sig *ᵥ x1) := by
    simpa using hpsd.dotProduct_mulVec_nonneg x1
  -- unfold the priced returns; at the benchmark itself the charge is `t₁ · X`
  simp only [pricedReturn]
  conv_rhs => rw [mul_assoc]
  rw [Real.mul_self_sqrt hX]
  -- stationarity dot-product identity against any vector `z`
  have hstatdot : ∀ z : ι → ℝ,
      μ ⬝ᵥ z = t₁ * (x1 ⬝ᵥ (Sig *ᵥ z)) + ∑ k, u k * (a k ⬝ᵥ z) := by
    intro z
    have h2 : z ⬝ᵥ (-μ + t₁ • Sig *ᵥ x1) = z ⬝ᵥ (-∑ k, u k • a k) := by rw [hstat]
    rw [dotProduct_add, dotProduct_neg, dotProduct_comm z μ, dotProduct_smul,
      dotProduct_mulVec_symm_comm hC z x1, dotProduct_neg, dotProduct_sum] at h2
    have h3 : ∀ k, z ⬝ᵥ (u k • a k) = u k * (a k ⬝ᵥ z) := by
      intro k
      rw [dotProduct_smul, dotProduct_comm z (a k)]
      simp only [smul_eq_mul]
    simp only [h3, smul_eq_mul] at h2
    linarith
  have hstaty := hstatdot y
  have hstatx := hstatdot x1
  -- return gap = t₁ (Q − X) + the complementary-slackness terms
  have hgap : μ ⬝ᵥ y - μ ⬝ᵥ x1
      = t₁ * (x1 ⬝ᵥ (Sig *ᵥ y) - x1 ⬝ᵥ (Sig *ᵥ x1))
        + (∑ k, u k * (a k ⬝ᵥ y) - ∑ k, u k * (a k ⬝ᵥ x1)) := by
    rw [hstaty, hstatx]
    ring
  have hcsle : 0 ≤ ∑ k, u k * (a k ⬝ᵥ x1 - a k ⬝ᵥ y) :=
    kkt_complementary_term_nonneg hu_nonneg hcs hfeasy
  have hsumsplit : ∑ k, u k * (a k ⬝ᵥ y) - ∑ k, u k * (a k ⬝ᵥ x1)
      = -∑ k, u k * (a k ⬝ᵥ x1 - a k ⬝ᵥ y) := by
    rw [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ ↦ by ring
  -- Cauchy–Schwarz bounds the bilinear term; assemble
  have hQle : x1 ⬝ᵥ (Sig *ᵥ y)
      ≤ Real.sqrt (x1 ⬝ᵥ (Sig *ᵥ x1)) * Real.sqrt (y ⬝ᵥ (Sig *ᵥ y)) :=
    (le_abs_self _).trans (posSemidef_cauchySchwarz hpsd x1 y)
  have e1 : t₁ * (x1 ⬝ᵥ (Sig *ᵥ y)) ≤ t₁ * (Real.sqrt (x1 ⬝ᵥ (Sig *ᵥ x1))
      * Real.sqrt (y ⬝ᵥ (Sig *ᵥ y))) := mul_le_mul_of_nonneg_left hQle ht₁
  have e3 : t₁ * (x1 ⬝ᵥ (Sig *ᵥ y) - x1 ⬝ᵥ (Sig *ᵥ x1))
      = t₁ * (x1 ⬝ᵥ (Sig *ᵥ y)) - t₁ * (x1 ⬝ᵥ (Sig *ᵥ x1)) := by ring
  linarith [hgap, hsumsplit, hcsle, e1, e3]

end MathFin
