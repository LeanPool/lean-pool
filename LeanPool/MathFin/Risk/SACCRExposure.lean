/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye, Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Choice.Portfolio.CovariancePSD

/-!
# Basel SA-CCR: exposure at default and effective notional aggregation

The Basel III **Standardised Approach for Counterparty Credit Risk** (SA-CCR, BCBS 279)
computes the exposure at default of a derivatives netting set as

  `EAD = α · (RC + PFE)`,

where `RC` is the replacement cost, `PFE` is the potential future exposure add-on, and the
regulator fixes `α = 1.4`. Here `RC` and `PFE` enter as free real numbers: their construction
from supervisory factors (the replacement cost, the PFE multiplier, the asset-class add-ons) is not
formalized, apart from the two-bucket interest-rate effective notional below. We record the
formula and its one structural fact: `EAD` is nondecreasing in `RC` and in `PFE`, jointly, for any
fixed `α ≥ 0`, so netting or hedging that lowers one component without raising the other can only
lower (never raise) the capital exposure.

The other SA-CCR building block with algebraic content is the **effective notional** of an
interest-rate hedging set. SA-CCR splits the trades of one currency into three maturity buckets
(under one year, one to five years, over five years) with signed bucket effective notionals
`D₁, D₂, D₃`, and aggregates them as

  `EffectiveNotional = √(D₁² + D₂² + D₃² + 1.4·D₁·D₂ + 1.4·D₂·D₃ + 0.6·D₁·D₃)`,

that is, with correlation `0.7` between adjacent buckets and `0.3` between the first and the third
(Basel Framework CRE52.57). This is `effNotionalIR`, and it never exceeds `|D₁| + |D₂| + |D₃|`
(`effNotionalIR_le_abs_add`). With one bucket empty it is

  `effNotionalPair ρ d₁ d₂ = √(d₁² + d₂² + 2ρ·d₁·d₂)`

at `ρ = 0.7` (third bucket empty, `effNotionalIR_third_zero`) or `ρ = 0.3` (middle bucket empty,
`effNotionalIR_second_zero`). The two-bucket form is the same quadratic form
as the standard deviation of a sum of two correlated risks. It is not the single-factor
aggregation that SA-CCR uses for the credit, equity and commodity classes,
`√((Σₖ ρₖ·Aₖ)² + Σₖ (1 − ρₖ²)·Aₖ²)` over entity-level add-ons `Aₖ`, whose two-entity cross term
with equal `ρ` is `2ρ²·A₁·A₂`. We prove that `effNotionalPair` collapses to `|d₁ + d₂|` at `ρ = 1`
(full correlation, no diversification benefit) and to `√(d₁² + d₂²)` at `ρ = 0`, that it never
exceeds `|d₁| + |d₂|` for `ρ ∈ [-1, 1]` (no *negative* diversification: recognising offset across
buckets never gives more than adding the absolute bucket notionals), and that for `ρ ≥ 0` and both
notionals nonnegative, growing `d₁` never shrinks the aggregate (`effNotionalPair_mono_left`; the
formula is symmetric in `d₁, d₂`, so the same holds for `d₂` by relabelling; that version is not
stated).

**The effective notional is a standard deviation.** Its radicand is the Markowitz quadratic form
`∑ᵢⱼ DᵢDⱼρᵢⱼ` (`portfolioVarN`, `Choice/Portfolio/MarkowitzNAsset.lean`) of the bucket notionals
under the
supervisory correlation matrix `saccrIRCorrelation` (`effNotionalIR_eq_sqrt_portfolioVarN`). So if
the three bucket risk factors `Zᵢ` have unit variances and the supervisory correlations as
covariances, `effNotionalIR` is the standard deviation of the hedging-set exposure `∑ Dᵢ Zᵢ`
(`effNotionalIR_eq_sqrt_variance`, through `portfolioVarN_covariance_eq_variance` of
`Choice/Portfolio/CovariancePSD.lean`). The supervisory matrix is positive semidefinite: the
radicand is a sum of squares, nonnegative for every hedging set, so the square root never truncates
(`effNotionalIR_radicand_nonneg`, `effNotionalIR_sq`). The bound "never more than adding the
absolute notionals" holds for every kernel with entries in `[-1, 1]`
(`sqrt_portfolioVarN_le_sum_abs`), and both `effNotionalIR_le_abs_add` and
`effNotionalPair_le_abs_add` are proved as its instances. The bucket risk factors themselves are
not part of the Basel formula; the theorem says which variance the formula computes.

## Main definitions

* `saccrEAD`: `α · (RC + PFE)`.
* `effNotionalIR`: the CRE52.57 interest-rate effective notional of three maturity buckets.
* `effNotionalPair`: the two-bucket aggregation `√(d₁² + d₂² + 2ρ·d₁·d₂)` at a general `ρ`.
* `saccrIRCorrelation`: the CRE52.57 correlation matrix of the three maturity buckets.

## Main results

* `saccrEAD_mono_rc`, `saccrEAD_mono_pfe`: `EAD` is monotone in `RC` and in `PFE` for `α ≥ 0`.
* `saccrEAD_mono`: `EAD` is jointly monotone in `(RC, PFE)` for `α ≥ 0`.
* `effNotionalPair_nonneg`: the aggregated notional is nonnegative.
* `effNotionalPair_eq_abs_add_of_corr_one`: at `ρ = 1`, `effNotionalPair = |d₁ + d₂|`.
* `effNotionalPair_eq_hypot_of_corr_zero`: at `ρ = 0`, `effNotionalPair = √(d₁² + d₂²)`.
* `effNotionalPair_le_abs_add`: for `ρ ∈ [-1, 1]`, the aggregation never exceeds `|d₁| + |d₂|` (no
  negative diversification).
* `effNotionalPair_mono_left`: for `ρ ≥ 0` and `d₂ ≥ 0`, the aggregation is monotone in `d₁` on
  `[0, ∞)`.
* `effNotionalIR_le_abs_add`: the three-bucket effective notional never exceeds
  `|D₁| + |D₂| + |D₃|`.
* `effNotionalIR_third_zero`, `effNotionalIR_second_zero`: with one bucket empty it is
  `effNotionalPair` at `0.7` or `0.3`.
* `sqrt_portfolioVarN_le_sum_abs`: for a kernel with entries in `[-1, 1]`, the square root of the
  quadratic form never exceeds the sum of the absolute weights.
* `effNotionalIR_eq_sqrt_portfolioVarN`, `effNotionalPair_eq_sqrt_portfolioVarN`: the effective
  notionals as square roots of Markowitz quadratic forms.
* `effNotionalIR_eq_sqrt_variance`: the effective notional is the standard deviation of the
  hedging-set exposure under unit-variance factors with the supervisory correlations.
* `effNotionalIR_radicand_nonneg`, `effNotionalIR_sq`: the supervisory correlation matrix is
  positive semidefinite, and the effective notional squares to its radicand.

## References

* [Basel Committee on Banking Supervision, *The standardised approach for measuring counterparty
  credit risk exposures*][BCBS279] (the EAD formula and the interest-rate effective
  notional).
* [Basel Committee on Banking Supervision, *The Basel Framework*, CRE52][BaselFrameworkCRE52],
  CRE52.57.

## Tags

SA-CCR, exposure at default, counterparty credit risk, Basel III, effective notional,
replacement cost, potential future exposure, MSC 91G40, MSC 91G70, JEL G28, JEL G32
-/

@[expose] public section

namespace MathFin

open Real

/-! ## Exposure at default -/

/-- The Basel SA-CCR exposure-at-default formula `EAD = α · (RC + PFE)`, where `RC` is the
replacement cost and `PFE` the potential future exposure add-on. The regulator fixes
`α = 1.4` (`saccrAlpha`), but we keep it as a parameter since the only mathematical content is
the arithmetic combination, not the specific constant. -/
noncomputable def saccrEAD (α RC PFE : ℝ) : ℝ := α * (RC + PFE)

/-- The regulatory value of `α` fixed by Basel SA-CCR (BCBS 279). -/
noncomputable def saccrAlpha : ℝ := 1.4

/-- `saccrAlpha` is positive, so `saccrEAD saccrAlpha` inherits the monotonicity lemmas below at
the regulatory value of `α`. -/
theorem saccrAlpha_pos : 0 < saccrAlpha := by norm_num [saccrAlpha]

/-- `EAD` is monotone increasing in the replacement cost `RC`, for any fixed `α ≥ 0`. -/
theorem saccrEAD_mono_rc {α : ℝ} (hα : 0 ≤ α) {PFE : ℝ} :
    Monotone (fun RC ↦ saccrEAD α RC PFE) := by
  intro RC₁ RC₂ h
  simp only [saccrEAD]
  gcongr

/-- `EAD` is monotone increasing in the PFE add-on, for any fixed `α ≥ 0`. -/
theorem saccrEAD_mono_pfe {α : ℝ} (hα : 0 ≤ α) {RC : ℝ} :
    Monotone (fun PFE ↦ saccrEAD α RC PFE) := by
  intro PFE₁ PFE₂ h
  simp only [saccrEAD]
  gcongr

/-- `EAD` is jointly monotone: raising `RC` and/or `PFE` never lowers the exposure, for
`α ≥ 0`. -/
theorem saccrEAD_mono {α : ℝ} (hα : 0 ≤ α) {RC₁ RC₂ PFE₁ PFE₂ : ℝ}
    (hRC : RC₁ ≤ RC₂) (hPFE : PFE₁ ≤ PFE₂) :
    saccrEAD α RC₁ PFE₁ ≤ saccrEAD α RC₂ PFE₂ := by
  unfold saccrEAD
  gcongr

/-! ## Effective notional aggregation

SA-CCR aggregates the signed maturity-bucket effective notionals of an interest-rate hedging set
with correlation `0.7` between adjacent buckets and `0.3` between the first and the third
(CRE52.57, `effNotionalIR` at the end of this section). `effNotionalPair` below is the
two-bucket quadratic form for a general correlation `ρ`; at `ρ = 0.7` or `ρ = 0.3` it is that
aggregation with one bucket empty (`effNotionalIR_third_zero`, `effNotionalIR_second_zero`). -/

/-- The two-bucket aggregation `√(d₁² + d₂² + 2ρ·d₁·d₂)` of signed bucket effective notionals
`d₁, d₂` at correlation `ρ`. At `ρ = 0.7` (adjacent buckets) or `ρ = 0.3` (the first and third)
it is the interest-rate effective notional `effNotionalIR` of Basel Framework CRE52.57 for a
hedging set with the remaining bucket empty (`effNotionalIR_third_zero`,
`effNotionalIR_second_zero`). -/
noncomputable def effNotionalPair (ρ d₁ d₂ : ℝ) : ℝ := √(d₁ ^ 2 + d₂ ^ 2 + 2 * ρ * d₁ * d₂)

theorem effNotionalPair_nonneg (ρ d₁ d₂ : ℝ) : 0 ≤ effNotionalPair ρ d₁ d₂ :=
  Real.sqrt_nonneg _

/-- At full correlation `ρ = 1` the aggregation collapses to `|d₁ + d₂|`: no diversification
benefit, the signed bucket notionals simply add. -/
theorem effNotionalPair_eq_abs_add_of_corr_one (d₁ d₂ : ℝ) :
    effNotionalPair 1 d₁ d₂ = |d₁ + d₂| := by
  unfold effNotionalPair
  rw [show d₁ ^ 2 + d₂ ^ 2 + 2 * 1 * d₁ * d₂ = (d₁ + d₂) ^ 2 by ring]
  exact Real.sqrt_sq_eq_abs _

/-- At zero correlation the aggregation is the Euclidean (independent-risk) combination. -/
theorem effNotionalPair_eq_hypot_of_corr_zero (d₁ d₂ : ℝ) :
    effNotionalPair 0 d₁ d₂ = √(d₁ ^ 2 + d₂ ^ 2) := by
  unfold effNotionalPair; ring_nf

/-- `effNotionalPair` is monotone in `d₁` on `[0, ∞)`, for `ρ ≥ 0` and `d₂ ≥ 0`: increasing a
nonnegative bucket notional `d₁` never decreases the aggregate when the correlation and the other
notional are both nonnegative. -/
theorem effNotionalPair_mono_left {ρ : ℝ} (hρ : 0 ≤ ρ) {d₂ : ℝ} (hd₂ : 0 ≤ d₂) :
    MonotoneOn (fun d₁ ↦ effNotionalPair ρ d₁ d₂) (Set.Ici (0 : ℝ)) := by
  intro d₁ hd₁ d₁' hd₁' h
  simp only [Set.mem_Ici] at hd₁ hd₁'
  unfold effNotionalPair
  apply Real.sqrt_le_sqrt
  nlinarith [mul_nonneg (mul_nonneg hρ hd₂) (sub_nonneg.mpr h), mul_le_mul h h hd₁ (hd₁.trans h)]

/-- **The SA-CCR interest-rate effective notional** of a hedging set (Basel Framework CRE52.57):
`√(D₁² + D₂² + D₃² + 1.4·D₁·D₂ + 1.4·D₂·D₃ + 0.6·D₁·D₃)` for the signed effective notionals
`D₁, D₂, D₃` of its three maturity buckets (under one year, one to five years, over five years).
The bucket notionals themselves (supervisory duration, delta, maturity factor) are inputs. -/
noncomputable def effNotionalIR (D₁ D₂ D₃ : ℝ) : ℝ :=
  √(D₁ ^ 2 + D₂ ^ 2 + D₃ ^ 2 + 7 / 5 * D₁ * D₂ + 7 / 5 * D₂ * D₃ + 3 / 5 * D₁ * D₃)

/-- With the third bucket empty, the SA-CCR effective notional is `effNotionalPair` at the
adjacent-bucket correlation `0.7`. -/
theorem effNotionalIR_third_zero (D₁ D₂ : ℝ) :
    effNotionalIR D₁ D₂ 0 = effNotionalPair (7 / 10) D₁ D₂ := by
  unfold effNotionalIR effNotionalPair
  congr 1
  ring

/-- With the middle bucket empty, the SA-CCR effective notional is `effNotionalPair` at the
first-to-third-bucket correlation `0.3`. -/
theorem effNotionalIR_second_zero (D₁ D₃ : ℝ) :
    effNotionalIR D₁ 0 D₃ = effNotionalPair (3 / 10) D₁ D₃ := by
  unfold effNotionalIR effNotionalPair
  congr 1
  ring

/-! ## The effective notional as a standard deviation -/

/-- **No negative diversification for a correlation-bounded kernel**: if every entry of the kernel
`c` on `s` lies in `[-1, 1]`, the square root of the quadratic form `∑ᵢⱼ wᵢwⱼcᵢⱼ` never exceeds
`∑ᵢ |wᵢ|`, because each term is at most `|wᵢ||wⱼ|`. -/
theorem sqrt_portfolioVarN_le_sum_abs {ι : Type*} (s : Finset ι) (w : ι → ℝ) {c : ι → ι → ℝ}
    (hc : ∀ i ∈ s, ∀ j ∈ s, |c i j| ≤ 1) :
    √(portfolioVarN s w c) ≤ ∑ i ∈ s, |w i| := by
  unfold portfolioVarN
  rw [Real.sqrt_le_left (Finset.sum_nonneg fun i _ ↦ abs_nonneg (w i)), sq, Finset.sum_mul_sum]
  refine Finset.sum_le_sum fun i hi ↦ Finset.sum_le_sum fun j hj ↦ ?_
  calc w i * w j * c i j ≤ |w i * w j * c i j| := le_abs_self _
    _ = |w i| * |w j| * |c i j| := by rw [abs_mul, abs_mul]
    _ ≤ |w i| * |w j| * 1 := mul_le_mul_of_nonneg_left (hc i hi j hj) (by positivity)
    _ = |w i| * |w j| := mul_one _

/-- The supervisory correlations between the three maturity buckets of an interest-rate hedging
set (Basel Framework CRE52.57): `1` on the diagonal, `0.7` between adjacent buckets and `0.3`
between the first and the third. -/
noncomputable def saccrIRCorrelation : Fin 3 → Fin 3 → ℝ :=
  ![![1, 7 / 10, 3 / 10], ![7 / 10, 1, 7 / 10], ![3 / 10, 7 / 10, 1]]

/-- **The effective notional is the square root of a Markowitz quadratic form**: `effNotionalIR`
is `√(∑ᵢⱼ DᵢDⱼρᵢⱼ)` with the supervisory correlations `ρ = saccrIRCorrelation`. -/
theorem effNotionalIR_eq_sqrt_portfolioVarN (D : Fin 3 → ℝ) :
    effNotionalIR (D 0) (D 1) (D 2) = √(portfolioVarN Finset.univ D saccrIRCorrelation) := by
  simp only [effNotionalIR, portfolioVarN, saccrIRCorrelation, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  congr 1
  ring

/-- The two-bucket aggregation is the square root of the quadratic form of the correlation
matrix `!![1, ρ; ρ, 1]`. -/
theorem effNotionalPair_eq_sqrt_portfolioVarN (ρ d₁ d₂ : ℝ) :
    effNotionalPair ρ d₁ d₂ = √(portfolioVarN Finset.univ ![d₁, d₂] ![![1, ρ], ![ρ, 1]]) := by
  simp only [effNotionalPair, portfolioVarN, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  congr 1
  ring

/-- For a correlation `ρ ∈ [-1, 1]` (which contains Basel's `0.7` and `0.3`), the aggregated
notional never exceeds the sum of the absolute bucket notionals: there is no *negative*
diversification from this formula. This is `sqrt_portfolioVarN_le_sum_abs` at the kernel
`!![1, ρ; ρ, 1]`. The bound fails outside `[-1, 1]`, e.g. `ρ = -5`, `d₁ = 1`, `d₂ = -1` gives
`effNotionalPair = √12 > 2`. -/
theorem effNotionalPair_le_abs_add {ρ : ℝ} (hρ1 : -1 ≤ ρ) (hρ2 : ρ ≤ 1) (d₁ d₂ : ℝ) :
    effNotionalPair ρ d₁ d₂ ≤ |d₁| + |d₂| := by
  have h := sqrt_portfolioVarN_le_sum_abs Finset.univ ![d₁, d₂] (c := ![![1, ρ], ![ρ, 1]])
    (by norm_num [Fin.forall_fin_succ, abs_le, hρ1, hρ2])
  rw [← effNotionalPair_eq_sqrt_portfolioVarN] at h
  simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] using h

/-- **No negative diversification across the three buckets**: the SA-CCR interest-rate effective
notional never exceeds the sum of the absolute bucket notionals. This is
`sqrt_portfolioVarN_le_sum_abs` at the supervisory correlations, whose entries lie in `[0, 1]`. -/
theorem effNotionalIR_le_abs_add (D₁ D₂ D₃ : ℝ) :
    effNotionalIR D₁ D₂ D₃ ≤ |D₁| + |D₂| + |D₃| := by
  have h := sqrt_portfolioVarN_le_sum_abs Finset.univ ![D₁, D₂, D₃] (c := saccrIRCorrelation)
    (by norm_num [Fin.forall_fin_succ, saccrIRCorrelation, Matrix.cons_val_two, abs_le])
  rw [← effNotionalIR_eq_sqrt_portfolioVarN] at h
  simpa only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] using h

section Variance

open MeasureTheory ProbabilityTheory

/-- **The effective notional is the standard deviation of the hedging-set exposure**: if the
three bucket risk factors `Zᵢ` are square-integrable with covariances equal to the supervisory
correlations (unit variances, `0.7` between adjacent buckets, `0.3` between the first and the
third), then `effNotionalIR D₀ D₁ D₂ = sd(∑ᵢ Dᵢ Zᵢ)`. This is
`portfolioVarN_covariance_eq_variance` at the supervisory kernel. -/
theorem effNotionalIR_eq_sqrt_variance {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {Z : Fin 3 → Ω → ℝ} (hZ : ∀ i, MemLp (Z i) 2 μ)
    (hcov : ∀ i j, cov[Z i, Z j; μ] = saccrIRCorrelation i j) (D : Fin 3 → ℝ) :
    effNotionalIR (D 0) (D 1) (D 2) = √Var[∑ i, D i • Z i; μ] := by
  have hk : (fun i j ↦ cov[Z i, Z j; μ]) = saccrIRCorrelation := funext₂ hcov
  rw [effNotionalIR_eq_sqrt_portfolioVarN, ← hk,
    portfolioVarN_covariance_eq_variance _ D Z fun i _ ↦ hZ i]

end Variance

/-- **The supervisory correlation matrix is positive semidefinite**: the radicand of
`effNotionalIR` is nonnegative for every hedging set. It is the sum of squares
`(D₁ + 0.7 D₂ + 0.3 D₃)² + (51 D₂ + 49 D₃)²/5100 + (112/255) D₃²`. -/
theorem effNotionalIR_radicand_nonneg (D₁ D₂ D₃ : ℝ) :
    0 ≤ D₁ ^ 2 + D₂ ^ 2 + D₃ ^ 2 + 7 / 5 * D₁ * D₂ + 7 / 5 * D₂ * D₃ + 3 / 5 * D₁ * D₃ := by
  nlinarith [sq_nonneg (D₁ + 7 / 10 * D₂ + 3 / 10 * D₃), sq_nonneg (51 * D₂ + 49 * D₃),
    sq_nonneg D₃]

/-- The square of the effective notional is its radicand: no truncation at zero. -/
theorem effNotionalIR_sq (D₁ D₂ D₃ : ℝ) :
    effNotionalIR D₁ D₂ D₃ ^ 2 =
      D₁ ^ 2 + D₂ ^ 2 + D₃ ^ 2 + 7 / 5 * D₁ * D₂ + 7 / 5 * D₂ * D₃ + 3 / 5 * D₁ * D₃ :=
  Real.sq_sqrt (effNotionalIR_radicand_nonneg D₁ D₂ D₃)

end MathFin
