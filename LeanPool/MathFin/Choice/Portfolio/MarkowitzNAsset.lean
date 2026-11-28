/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Choice.Portfolio.Markowitz
public import Mathlib.Logic.Equiv.PartialEquiv

/-!
# N-asset Markowitz portfolio variance (sum form)

Closed-form algebraic identities for the n-asset portfolio variance as an
explicit Finset double sum:

  `Var(w) = ∑_{i, j ∈ s} w_i · w_j · σ_{ij}`.

We avoid the matrix-algebra layer (`Matrix.mulVec`, `Matrix.PosDef`) and work
directly with sums — this keeps the file lightweight while still covering the
core textbook identities.

## Main definitions

* `portfolioVarN`: the `n`-asset portfolio variance `∑_{i,j ∈ s} wᵢ wⱼ σᵢⱼ`, a double sum over a
  finite index set `s` against a kernel `σ`.

## Main results

* `portfolioVarN_smul`: scaling `Var(c · w) = c² · Var(w)`.
* `portfolioVarN_diag`: when `σ` is diagonal (`σ_{ij} = 0` for `i ≠ j`),
  `Var(w) = ∑ w_i² · σ_{ii}`.
* `portfolioVarN_equal_weights_iid`: equal-weights / iid case gives
  `Var(c · 1) = c² · n · σ²` (a diversification scaling identity).
* `portfolioVarN_nonneg_of_psd`: if the kernel `σ` defines a non-negative
  quadratic form, then `Var(w) ≥ 0`.
* `portfolioVarN_two_asset_compat`: when the index set has cardinality 2,
  the double sum is the two-asset `portfolioVarTwo` of `Markowitz.lean`.

## References

* [K. Bodie and Marcus, *Investments*][BodieKaneMarcus], Ch 7; Ch 7.2; Ch 7.3; Ch 7.4

## Tags

Markowitz, portfolio variance, covariance matrix, n-asset portfolio, diversification, MSC 91G10,
JEL G11
-/

@[expose] public section

namespace MathFin

/-- N-asset portfolio variance: `Var(w) = ∑_{i,j} w_i · w_j · σ_{ij}`. -/
noncomputable def portfolioVarN
    {ι : Type*} (s : Finset ι) (w : ι → ℝ) (σ : ι → ι → ℝ) : ℝ :=
  ∑ i ∈ s, ∑ j ∈ s, w i * w j * σ i j

/-- **Quadratic scaling**: `Var(c · w) = c² · Var(w)`. -/
lemma portfolioVarN_smul {ι : Type*} (s : Finset ι)
    (w : ι → ℝ) (σ : ι → ι → ℝ) (c : ℝ) :
    portfolioVarN s (fun i ↦ c * w i) σ = c ^ 2 * portfolioVarN s w σ := by
  unfold portfolioVarN
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j _
  ring

/-- **Diagonal covariance**: when `σ_{ij} = 0` for `i ≠ j`, the portfolio
variance collapses to `∑ w_i² · σ_{ii}`. -/
lemma portfolioVarN_diag {ι : Type*} (s : Finset ι)
    (w : ι → ℝ) (σ : ι → ι → ℝ)
    (h_diag : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → σ i j = 0) :
    portfolioVarN s w σ = ∑ i ∈ s, w i ^ 2 * σ i i := by
  classical
  unfold portfolioVarN
  refine Finset.sum_congr rfl ?_
  intro i hi
  have h_inner : ∀ j ∈ s, w i * w j * σ i j =
      if j = i then w i ^ 2 * σ i i else 0 := by
    intro j hj
    by_cases hij : j = i
    · subst hij; simp [sq]
    · have : σ i j = 0 := h_diag i hi j hj (fun h ↦ hij h.symm)
      rw [this]; simp [hij]
  rw [Finset.sum_congr rfl h_inner]
  rw [Finset.sum_ite_eq' s i]
  simp [hi]

/-- **Diversification under iid assets**: equal weights `c` across an index set
`s` of cardinality `n`, with zero cross-covariances and common variance `σ²`,
gives `Var(c · 1) = c² · n · σ²`. -/
lemma portfolioVarN_equal_weights_iid {ι : Type*}
    (s : Finset ι) (c σ_sq : ℝ)
    (kernel : ι → ι → ℝ)
    (h_diag : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → kernel i j = 0)
    (h_var : ∀ i ∈ s, kernel i i = σ_sq) :
    portfolioVarN s (fun _ ↦ c) kernel = c ^ 2 * s.card * σ_sq := by
  rw [portfolioVarN_diag s _ kernel h_diag]
  have h_eq : ∀ i ∈ s, c ^ 2 * kernel i i = c ^ 2 * σ_sq :=
    fun i hi ↦ by rw [h_var i hi]
  rw [Finset.sum_congr rfl h_eq, Finset.sum_const, nsmul_eq_mul]
  ring

/-- **Non-negativity from PSD kernel**: if `σ` defines a non-negative quadratic
form (`∀ v, ∑∑ v_i v_j σ_{ij} ≥ 0`), then `Var(w) ≥ 0`. -/
lemma portfolioVarN_nonneg_of_psd
    {ι : Type*} (s : Finset ι) (w : ι → ℝ) (σ : ι → ι → ℝ)
    (h_psd : ∀ v : ι → ℝ, 0 ≤ ∑ i ∈ s, ∑ j ∈ s, v i * v j * σ i j) :
    0 ≤ portfolioVarN s w σ := h_psd w

/-- **Two-asset compatibility**: for an index set `{0, 1} ⊆ Fin 2` with weights
`w 0 = w` and `w 1 = 1 − w` and the covariance kernel
`σ 0 0 = σ₁², σ 1 1 = σ₂², σ 0 1 = σ 1 0 = ρ · σ₁ · σ₂`, the n-asset variance
is the two-asset `portfolioVarTwo σ₁ σ₂ ρ w` of `Markowitz.lean`. -/
lemma portfolioVarN_two_asset_compat (w σ₁ σ₂ ρ : ℝ) :
    portfolioVarN (Finset.univ : Finset (Fin 2))
        (fun i ↦ if i = 0 then w else 1 - w)
        (fun i j ↦
          if i = 0 ∧ j = 0 then σ₁ ^ 2
          else if i = 1 ∧ j = 1 then σ₂ ^ 2
          else ρ * σ₁ * σ₂) =
      portfolioVarTwo σ₁ σ₂ ρ w := by
  unfold portfolioVarN portfolioVarTwo
  rw [show (Finset.univ : Finset (Fin 2)) = {0, 1} from rfl]
  simp [Finset.sum_insert, Finset.mem_singleton, Finset.sum_singleton]
  ring

end MathFin
