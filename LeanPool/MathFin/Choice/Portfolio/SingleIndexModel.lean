/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye, Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Choice.Portfolio.MarkowitzNAsset
public import LeanPool.MathFin.Choice.Portfolio.CovariancePSD
public import LeanPool.MathFin.Choice.Portfolio.CAPM

/-!
# Single-index covariance structure and its large-`N` limit

Sharpe's single-index model writes each asset's return as `Rᵢ = βᵢ·R_M + εᵢ`, with idiosyncratic
shocks `εᵢ` uncorrelated across assets and with the market. The implied covariance kernel is
`Σ = ββ'σ_M² + D_ε` (`D_ε` diagonal). The passage from the return model to this kernel is
`covariance_singleIndex`: for square-integrable `R_M` and `εᵢ`, with the shocks uncorrelated with
the market and with each other, `cov(Rᵢ, Rⱼ)` is the kernel with `D_ε(i) = Var[εᵢ]`, by
bilinearity of covariance. With the self-dot identity of `Choice/Portfolio/CovariancePSD.lean` this
gives
the variance of the random portfolio return (`variance_singleIndex_portfolio`), and the loading
`βᵢ` is the CAPM beta `cov(Rᵢ, R_M)/Var[R_M]` of `Choice/Portfolio/CAPM.lean` (`beta_singleIndex`).
On the kernel itself, with `Choice/Portfolio/MarkowitzNAsset.lean`'s sum-form portfolio variance:

  `Var(Rp) = (w'β)² σ_M² + w'D_εw`,

in which, for nonnegative, uniformly bounded idiosyncratic variances and the equal-weight
portfolio, the idiosyncratic term tends to `0` as `n → ∞`: idiosyncratic risk diversifies away.
The limit is stated for the idiosyncratic term alone; that `Var(Rp)` minus the systematic term
`(β_p σ_M)²` tends to `0` follows with `portfolioVarN_singleIndex_eq` but is not stated.

## Main definitions

* `singleIndexKernel`: the single-index covariance kernel
  `σᵢⱼ = βᵢβⱼσ_M² + 1[i=j]·D_ε(i)`.

## Main results

* `portfolioVarN_singleIndex_eq`: `Var(Rp) = (∑ wᵢβᵢ)² σ_M² + ∑ wᵢ² D_ε(i)`.
* `idiosyncraticTerm_equalWeight_le`: for equal weights `1/n` and idiosyncratic variances
  bounded by `M`, the idiosyncratic term is at most `M / n`.
* `tendsto_idiosyncraticTerm_equalWeight_zero`: hence, for nonnegative variances bounded by `M`,
  it tends to `0` as `n → ∞` (idiosyncratic risk diversifies away under equal weighting).
* `covariance_singleIndex`: the covariance of the return model is `singleIndexKernel`.
* `variance_singleIndex_portfolio`: `Var[∑ wᵢRᵢ] = (∑ wᵢβᵢ)² Var[R_M] + ∑ wᵢ² Var[εᵢ]`.
* `beta_singleIndex`: the CAPM beta of asset `i` is `βᵢ`.

## References

* [Sharpe, *A simplified model for portfolio analysis*][Sharpe1963]
* [Sharpe, *Capital asset prices*][Sharpe1964]

## Tags

single-index model, Sharpe's index model, idiosyncratic risk, systematic risk, diversification,
market model, beta, MSC 91G10, MSC 62P05, JEL G11
-/

@[expose] public section

namespace MathFin

open Filter Topology

variable {ι : Type*} (s : Finset ι) (w β : ι → ℝ) (σM : ℝ) (Dε : ι → ℝ)

/-- The single-index covariance kernel `σᵢⱼ = βᵢβⱼσ_M² + 1[i=j]·D_ε(i)`. -/
def singleIndexKernel [DecidableEq ι] (i j : ι) : ℝ :=
  β i * β j * σM ^ 2 + if i = j then Dε i else 0

/-- `portfolioVarN` is additive in the covariance kernel: `Var` of a sum-kernel is the sum of the
`Var`s. Pure linearity of the double `Finset.sum`. -/
lemma portfolioVarN_add_kernel (f g : ι → ι → ℝ) :
    portfolioVarN s w (fun i j ↦ f i j + g i j) = portfolioVarN s w f + portfolioVarN s w g := by
  unfold portfolioVarN
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ ↦ by ring

/-- The rank-one ("market") kernel's portfolio variance is `σ_M² · (∑ wᵢβᵢ)²`: the double sum over
a rank-one kernel `βᵢβⱼ` factors into the product of two copies of the same single sum. -/
lemma portfolioVarN_rankOne_eq :
    portfolioVarN s w (fun i j ↦ β i * β j * σM ^ 2) = σM ^ 2 * (∑ i ∈ s, w i * β i) ^ 2 := by
  unfold portfolioVarN
  have heq : ∑ i ∈ s, ∑ j ∈ s, w i * w j * (β i * β j * σM ^ 2) =
      (∑ i ∈ s, w i * β i * σM) * ∑ j ∈ s, w j * β j * σM :=
    (Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ show
        w i * w j * (β i * β j * σM ^ 2) = (w i * β i * σM) * (w j * β j * σM) by ring).trans
      (Finset.sum_mul_sum s s (fun i ↦ w i * β i * σM) (fun j ↦ w j * β j * σM)).symm
  have hX : (∑ i ∈ s, w i * β i * σM) = σM * ∑ i ∈ s, w i * β i := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ ↦ by ring
  rw [heq, hX]
  ring

/-- **Single-index portfolio variance**: `Var(Rp) = (∑ wᵢβᵢ)² σ_M² + ∑ wᵢ² D_ε(i)`. -/
theorem portfolioVarN_singleIndex_eq [DecidableEq ι] :
    portfolioVarN s w (singleIndexKernel β σM Dε) =
      (∑ i ∈ s, w i * β i) ^ 2 * σM ^ 2 + ∑ i ∈ s, w i ^ 2 * Dε i := by
  unfold singleIndexKernel
  rw [portfolioVarN_add_kernel s w, portfolioVarN_rankOne_eq,
    portfolioVarN_diag s w _ fun i _ j _ hij ↦ ite_eq_right hij]
  simp
  ring

/-- **Idiosyncratic-term bound under equal weighting**: with weights `1/n` on an index set of
cardinality `n` and idiosyncratic variances bounded by `M`, the idiosyncratic term is at most
`M / n`. -/
lemma idiosyncraticTerm_equalWeight_le {n : ℕ} (M : ℝ)
    (hM : ∀ i ∈ s, Dε i ≤ M) (hcard : s.card = n) :
    ∑ i ∈ s, ((1 : ℝ) / n) ^ 2 * Dε i ≤ M / n := by
  have hbound : ∑ i ∈ s, ((1 : ℝ) / n) ^ 2 * Dε i ≤ ∑ _i ∈ s, ((1 : ℝ) / n) ^ 2 * M :=
    Finset.sum_le_sum fun i hi ↦
      mul_le_mul_of_nonneg_left (hM i hi) (sq_nonneg _)
  have heq : ∑ _i ∈ s, ((1 : ℝ) / n) ^ 2 * M = M / n := by
    rw [Finset.sum_const, hcard, nsmul_eq_mul]
    field_simp
  rwa [heq] at hbound

/-- **Diversification**: the idiosyncratic term under equal weighting on an index set of
cardinality `n` tends to `0` as `n → ∞`, for nonnegative idiosyncratic variances uniformly bounded
by `M` — idiosyncratic risk diversifies away. The statement is about the idiosyncratic term
alone; the systematic term `(β_p σ_M)²` that remains in `portfolioVarN_singleIndex_eq` does not
enter it. -/
theorem tendsto_idiosyncraticTerm_equalWeight_zero
    (t : ℕ → Finset ι) (D : ℕ → ι → ℝ) (M : ℝ)
    (hM : ∀ n, ∀ i ∈ t n, D n i ≤ M) (hMnn : ∀ n, ∀ i ∈ t n, 0 ≤ D n i)
    (hcard : ∀ n, (t n).card = n) :
    Tendsto (fun n ↦ ∑ i ∈ t n, ((1 : ℝ) / n) ^ 2 * D n i) atTop (𝓝 0) := by
  have hlo (n : ℕ) : 0 ≤ ∑ i ∈ t n, ((1 : ℝ) / n) ^ 2 * D n i :=
    Finset.sum_nonneg fun i hi ↦ mul_nonneg (sq_nonneg _) (hMnn n i hi)
  have hhi (n : ℕ) : ∑ i ∈ t n, ((1 : ℝ) / n) ^ 2 * D n i ≤ M / n :=
    idiosyncraticTerm_equalWeight_le (t n) (D n) M (hM n) (hcard n)
  exact squeeze_zero hlo hhi (tendsto_const_div_atTop_nhds_zero_nat M)

/-! ### From the return model to the kernel -/

section ReturnModel

open MeasureTheory ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {RM : Ω → ℝ} {ε : ι → Ω → ℝ}

/-- **The single-index kernel is the covariance of the return model.** Let
`Rᵢ = βᵢ R_M + εᵢ` with square-integrable market return `R_M` and shocks `εᵢ`, the shocks
uncorrelated with the market and with each other, and `Var[R_M] = σ_M²`. Then
`cov(Rᵢ, Rⱼ) = βᵢβⱼσ_M² + 1[i = j]·Var[εᵢ]`: the kernel `singleIndexKernel` with the shock
variances on the diagonal. Bilinearity of covariance (`covariance_add_left`,
`covariance_smul_left`, …) and the zero cross-covariances. -/
theorem covariance_singleIndex [DecidableEq ι] (hRM : MemLp RM 2 P)
    (hε : ∀ i, MemLp (ε i) 2 P) (hRMε : ∀ i, cov[RM, ε i; P] = 0)
    (hεε : ∀ i j, i ≠ j → cov[ε i, ε j; P] = 0) (hσM : Var[RM; P] = σM ^ 2) (i j : ι) :
    cov[β i • RM + ε i, β j • RM + ε j; P] =
      singleIndexKernel β σM (fun k ↦ Var[ε k; P]) i j := by
  rw [covariance_add_left (hRM.const_smul _) (hε i) ((hRM.const_smul _).add (hε j)),
    covariance_add_right (hRM.const_smul _) (hRM.const_smul _) (hε j),
    covariance_add_right (hε i) (hRM.const_smul _) (hε j)]
  simp only [covariance_smul_left, covariance_smul_right,
    covariance_self hRM.aestronglyMeasurable.aemeasurable, hσM, hRMε,
    covariance_comm (ε i) RM]
  simp only [singleIndexKernel]
  split_ifs with hij
  · subst hij
    rw [covariance_self (hε i).aestronglyMeasurable.aemeasurable]
    ring
  · rw [hεε i j hij]
    ring

/-- **Single-index portfolio variance from the return model.** Under the hypotheses of
`covariance_singleIndex`, the variance of the portfolio return `∑ wᵢ Rᵢ` is
`(∑ wᵢβᵢ)² σ_M² + ∑ wᵢ² Var[εᵢ]`. The self-dot identity
`portfolioVarN_covariance_eq_variance` turns the variance into the quadratic form of the
covariance kernel, which `covariance_singleIndex` identifies and
`portfolioVarN_singleIndex_eq` evaluates. -/
theorem variance_singleIndex_portfolio (hRM : MemLp RM 2 P)
    (hε : ∀ i, MemLp (ε i) 2 P) (hRMε : ∀ i, cov[RM, ε i; P] = 0)
    (hεε : ∀ i j, i ≠ j → cov[ε i, ε j; P] = 0) (hσM : Var[RM; P] = σM ^ 2) :
    Var[∑ i ∈ s, w i • (β i • RM + ε i); P] =
      (∑ i ∈ s, w i * β i) ^ 2 * σM ^ 2 + ∑ i ∈ s, w i ^ 2 * Var[ε i; P] := by
  classical
  rw [← portfolioVarN_covariance_eq_variance s w (fun i ↦ β i • RM + ε i)
    fun i _ ↦ (hRM.const_smul _).add (hε i)]
  simp_rw [covariance_singleIndex β σM hRM hε hRMε hεε hσM]
  exact portfolioVarN_singleIndex_eq s w β σM _

/-- **The single-index loading is the CAPM beta.** Under the return model, the CAPM beta
`cov(Rᵢ, R_M) / Var[R_M]` (`beta`, `Choice/Portfolio/CAPM.lean`) of asset `i` is its loading `βᵢ`,
provided the market variance is nonzero. -/
theorem beta_singleIndex (hRM : MemLp RM 2 P) (hε : ∀ i, MemLp (ε i) 2 P)
    (hRMε : ∀ i, cov[RM, ε i; P] = 0) (hvar : Var[RM; P] ≠ 0) (i : ι) :
    MathFin.beta cov[β i • RM + ε i, RM; P] Var[RM; P] = β i := by
  unfold MathFin.beta
  rw [covariance_add_left (hRM.const_smul _) (hε i) hRM, covariance_smul_left,
    covariance_self hRM.aestronglyMeasurable.aemeasurable, covariance_comm (ε i) RM, hRMε,
    add_zero, mul_div_assoc, div_self hvar, mul_one]

end ReturnModel

end MathFin
