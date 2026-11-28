/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Choice.Portfolio.CovariancePSD
public import Mathlib.Algebra.Order.Chebyshev

/-!
# The equicorrelation matrix: when is a common correlation admissible?

The `d × d` **equicorrelation matrix** has ones on the diagonal and a common correlation `ρ`
everywhere else (`equicorrelationMatrix`). It is the correlation matrix of every exchangeable
model: equally rated obligors in a credit portfolio, the assets of a single-factor model, the
daily losses behind the square-root-of-time rule. The question of QRM Exercise 6.26 is which `ρ`
can occur at all. The answer is

  `(1 − ρ)·I + ρ·J` is positive semidefinite `↔ −1/(d − 1) ≤ ρ ≤ 1`

(`posSemidef_equicorrelationMatrix_iff`). Perfect positive dependence is always admissible, but
perfect negative dependence is not: in three or more dimensions, three variables cannot be
pairwise perfectly anticorrelated.

The proof reads the quadratic form as a Markowitz portfolio variance. For weights `w`,
`wᵀ (equicorrelation) w = (1 − ρ) ∑ wᵢ² + ρ (∑ wᵢ)²` (`portfolioVarN_equicorrelation`).

* Sufficiency is the Cauchy–Schwarz bound `(∑ wᵢ)² ≤ d ∑ wᵢ²`, the same inequality behind the
  Herfindahl lower bound.
* Necessity tests two portfolios. The equal-weight portfolio gives `d (1 + (d − 1) ρ) ≥ 0`. The
  long–short pair `eᵢ − eⱼ` gives `2 (1 − ρ) ≥ 0`.

Mathlib's `Matrix.PosSemidef` quadratic form `x ⬝ᵥ (M *ᵥ x)` and the library's sum-form
`portfolioVarN` are identified by `dotProduct_mulVec_eq_portfolioVarN`, so the matrix statement
and the portfolio statement are the same theorem.

The probabilistic reading (`neg_inv_le_and_le_one_of_covariance`) follows from
`Choice/Portfolio/CovariancePSD.lean`. Square-integrable variables with a common positive variance
and a common pairwise covariance `ρ σ²` have a PSD covariance kernel, and that kernel is `σ²` times
the equicorrelation matrix. So their common correlation satisfies `−1/(d − 1) ≤ ρ ≤ 1`.

## Main definitions

* `equicorrelationMatrix`: the `n × n` matrix with `1` on the diagonal and the common
  correlation `ρ` off it, `(1 − ρ)·I + ρ·J`.

## Main results

* `dotProduct_mulVec_eq_portfolioVarN`: Mathlib's matrix quadratic form is the Markowitz double
  sum.
* `portfolioVarN_equicorrelation`: `wᵀ E w = (1 − ρ) ∑ wᵢ² + ρ (∑ wᵢ)²`.
* `posSemidef_equicorrelationMatrix_iff`: for `d ≥ 2`, PSD `↔ −1/(d − 1) ≤ ρ ≤ 1` (QRM Ex. 6.26).
* `portfolioVarN_equicorrelation_equal_weights`: the equal-weight variance `ρ + (1 − ρ)/d`, the
  diversification floor of QRM Ex. 6.16.
* `portfolioVarN_covariance_eq_mul_equicorrelation`: an equicorrelated covariance kernel is `σ²`
  times the equicorrelation matrix.
* `neg_inv_le_and_le_one_of_covariance`: the bound for a common correlation of random variables.

## References

* [*QRM Exercise Book*][QRMExerciseBook], Ex. 6.26

## Tags

equicorrelation matrix, common correlation, exchangeable model, admissible correlation,
positive semidefinite, diversification, MSC 91G10, MSC 62H05, JEL G11
-/

@[expose] public section

namespace MathFin

open Finset Matrix MeasureTheory ProbabilityTheory

variable {n : Type*} [Fintype n] [DecidableEq n] {ρ : ℝ}

/-- The **equicorrelation matrix**: `1` on the diagonal and the common correlation `ρ` off it,
i.e. `(1 − ρ)·I + ρ·J`. -/
def equicorrelationMatrix (n : Type*) [DecidableEq n] (ρ : ℝ) : Matrix n n ℝ :=
  Matrix.of fun i j ↦ if i = j then 1 else ρ

omit [Fintype n] in
/-- The equicorrelation matrix is symmetric, hence Hermitian over `ℝ`. -/
lemma isHermitian_equicorrelationMatrix : (equicorrelationMatrix n ρ).IsHermitian :=
  IsHermitian.ext fun i j ↦ by simp [equicorrelationMatrix, eq_comm]

omit [DecidableEq n] in
/-- Mathlib's matrix quadratic form `x ⬝ᵥ (M *ᵥ x)` is the Markowitz double sum
`portfolioVarN univ x M = ∑ᵢ ∑ⱼ xᵢ xⱼ Mᵢⱼ`. -/
lemma dotProduct_mulVec_eq_portfolioVarN (M : Matrix n n ℝ) (x : n → ℝ) :
    x ⬝ᵥ (M *ᵥ x) = portfolioVarN univ x M := by
  simp only [dotProduct, mulVec, portfolioVarN, mul_sum]
  exact sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ by ring

/-- **Portfolio variance against an equicorrelated kernel**:
`∑ᵢ ∑ⱼ wᵢ wⱼ Eᵢⱼ = (1 − ρ) ∑ wᵢ² + ρ (∑ wᵢ)²`. -/
lemma portfolioVarN_equicorrelation (w : n → ℝ) :
    portfolioVarN univ w (equicorrelationMatrix n ρ) =
      (1 - ρ) * ∑ i, w i ^ 2 + ρ * (∑ i, w i) ^ 2 := by
  have hterm (i j : n) : w i * w j * equicorrelationMatrix n ρ i j =
      ρ * (w i * w j) + (1 - ρ) * (if i = j then w i * w j else 0) := by
    by_cases hij : i = j <;> simp [equicorrelationMatrix, hij] <;> ring
  simp only [portfolioVarN, hterm, sum_add_distrib, ← mul_sum, sum_ite_eq, mem_univ, ite_true,
    sq, sum_mul_sum]
  ring

/-- **Admissible common correlations** (QRM Exercise 6.26): for `d ≥ 2` the equicorrelation
matrix is positive semidefinite exactly when `−1/(d − 1) ≤ ρ ≤ 1`. -/
theorem posSemidef_equicorrelationMatrix_iff (hn : 2 ≤ Fintype.card n) :
    (equicorrelationMatrix n ρ).PosSemidef ↔ -1 / ((Fintype.card n : ℝ) - 1) ≤ ρ ∧ ρ ≤ 1 := by
  set d : ℝ := (Fintype.card n : ℝ)
  have hd : 1 < d := by simp only [d]; exact_mod_cast hn
  have hform (x : n → ℝ) : star x ⬝ᵥ (equicorrelationMatrix n ρ *ᵥ x) =
      (1 - ρ) * ∑ i, x i ^ 2 + ρ * (∑ i, x i) ^ 2 := by
    rw [star_trivial, dotProduct_mulVec_eq_portfolioVarN, portfolioVarN_equicorrelation]
  rw [posSemidef_iff_dotProduct_mulVec, div_le_iff₀ (by linarith)]
  simp only [hform, isHermitian_equicorrelationMatrix, true_and]
  constructor
  · intro h
    obtain ⟨i, j, hij⟩ := Fintype.exists_pair_of_one_lt_card (α := n) (by omega)
    -- the equal-weight portfolio: `d (1 + (d − 1) ρ) ≥ 0`
    have h1 := h fun _ ↦ 1
    -- the long–short pair `eᵢ − eⱼ`: `2 (1 − ρ) ≥ 0`
    have h2 := h (Pi.single i 1 - Pi.single j 1)
    have hsq : ∑ k, (Pi.single i 1 - Pi.single j 1 : n → ℝ) k ^ 2 = 2 := by
      have hk (k : n) : (Pi.single i 1 - Pi.single j 1 : n → ℝ) k ^ 2 =
          (Pi.single i 1 : n → ℝ) k + (Pi.single j 1 : n → ℝ) k := by
        by_cases hki : k = i <;> by_cases hkj : k = j <;> simp_all [Pi.single_apply]
      simp only [hk, sum_add_distrib, sum_pi_single', mem_univ, ite_true]
      norm_num
    simp only [one_pow, sum_const, card_univ, nsmul_eq_mul, mul_one] at h1
    rw [hsq] at h2
    simp only [Pi.sub_apply, sum_sub_distrib, sum_pi_single', mem_univ, ite_true, sub_self,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero] at h2
    change 0 ≤ (1 - ρ) * d + ρ * d ^ 2 at h1
    refine ⟨?_, by linarith⟩
    nlinarith
  · rintro ⟨h1, h2⟩ x
    have hcs : (∑ i, x i) ^ 2 ≤ d * ∑ i, x i ^ 2 := by
      simpa [d] using sq_sum_le_card_mul_sum_sq (s := univ) (f := x)
    have hsq : 0 ≤ ∑ i, x i ^ 2 := sum_nonneg fun i _ ↦ sq_nonneg (x i)
    rcases le_or_gt 0 ρ with hρ | hρ
    · exact add_nonneg (mul_nonneg (by linarith) hsq) (mul_nonneg hρ (sq_nonneg _))
    · nlinarith [mul_le_mul_of_nonpos_left hcs hρ.le,
        mul_nonneg (by linarith : 0 ≤ 1 + ρ * (d - 1)) hsq]

/-- **The diversification floor** (QRM Exercise 6.16): with a common correlation `ρ`, the equally
weighted portfolio of `d` assets has kernel variance `ρ + (1 − ρ)/d`. Adding assets removes only
the idiosyncratic part `(1 − ρ)/d`; the common part `ρ` stays. -/
lemma portfolioVarN_equicorrelation_equal_weights [Nonempty n] :
    portfolioVarN univ (fun _ ↦ (Fintype.card n : ℝ)⁻¹) (equicorrelationMatrix n ρ) =
      ρ + (1 - ρ) / Fintype.card n := by
  have hd : (Fintype.card n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  rw [portfolioVarN_equicorrelation]
  simp only [sum_const, card_univ, nsmul_eq_mul]
  field_simp
  ring

/-- A covariance kernel with a common variance `σ²` and a common pairwise covariance `ρ σ²` is
`σ²` times the equicorrelation matrix, so its Markowitz form is `σ²` times the equicorrelation
form. -/
lemma portfolioVarN_covariance_eq_mul_equicorrelation {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} (X : n → Ω → ℝ) (hX : ∀ i, AEMeasurable (X i) μ) {σ2 : ℝ}
    (hvar : ∀ i, Var[X i; μ] = σ2) (hcov : ∀ i j, i ≠ j → cov[X i, X j; μ] = ρ * σ2)
    (w : n → ℝ) :
    portfolioVarN univ w (fun i j ↦ cov[X i, X j; μ]) =
      σ2 * portfolioVarN univ w (equicorrelationMatrix n ρ) := by
  have hkernel (i j : n) : cov[X i, X j; μ] = σ2 * equicorrelationMatrix n ρ i j := by
    by_cases hij : i = j
    · subst hij
      simp [equicorrelationMatrix, covariance_self, hX, hvar]
    · simp [equicorrelationMatrix, hij, hcov i j hij, mul_comm]
  simp only [hkernel, portfolioVarN, mul_sum]
  exact sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ by ring

omit [DecidableEq n] in
/-- **A common correlation of random variables obeys the equicorrelation bound**: if
square-integrable `X₁, …, X_d` (`d ≥ 2`) have a common variance `σ² > 0` and a common pairwise
covariance `ρ σ²`, then `−1/(d − 1) ≤ ρ ≤ 1`. Their covariance kernel is `σ²` times the
equicorrelation matrix, and a covariance kernel is PSD (`covariance_kernel_psd`). -/
theorem neg_inv_le_and_le_one_of_covariance {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] (X : n → Ω → ℝ) (hX : ∀ i, MemLp (X i) 2 μ) {σ2 : ℝ} (hσ2 : 0 < σ2)
    (hvar : ∀ i, Var[X i; μ] = σ2) (hcov : ∀ i j, i ≠ j → cov[X i, X j; μ] = ρ * σ2)
    (hn : 2 ≤ Fintype.card n) :
    -1 / ((Fintype.card n : ℝ) - 1) ≤ ρ ∧ ρ ≤ 1 := by
  classical
  refine (posSemidef_equicorrelationMatrix_iff hn).1 <|
    posSemidef_iff_dotProduct_mulVec.2 ⟨isHermitian_equicorrelationMatrix, fun x ↦ ?_⟩
  have hpsd : 0 ≤ portfolioVarN univ x fun i j ↦ cov[X i, X j; μ] :=
    covariance_kernel_psd univ X (fun i _ ↦ hX i) x
  rw [portfolioVarN_covariance_eq_mul_equicorrelation X
    (fun i ↦ (hX i).aestronglyMeasurable.aemeasurable) hvar hcov] at hpsd
  rw [star_trivial, dotProduct_mulVec_eq_portfolioVarN]
  exact (mul_nonneg_iff_of_pos_left hσ2).1 hpsd

end MathFin
