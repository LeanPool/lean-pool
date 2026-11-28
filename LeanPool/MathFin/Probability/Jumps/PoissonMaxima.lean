/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Jumps.PoissonPgf
public import LeanPool.MathFin.Probability.Laws.GeneralizedPareto
public import Mathlib.Order.CompletePartialOrder

/-!
# The maximum of a Poisson number of losses

Over a fixed period a Poisson(`λ`) number `N` of losses occurs, with iid severities `Y₀, Y₁, …`
of distribution function `G`, independent of `N`. The largest loss stays below `x` exactly
when none of the `N` losses exceeds `x`, and

  `P(max_{i<N} Yᵢ ≤ x) = E[G(x)^N] = exp(−λ (1 − G(x)))`

(`measureReal_forall_lt_le_of_poisson`). The empty maximum (`N = 0`) counts as staying below
every level. The proof conditions on `N`: independence turns the event into
`∑ₙ P(N = n) G(x)ⁿ`, which is the Poisson probability generating function
(`Probability/Jumps/PoissonPgf.lean`).

Conceptually this is Poisson thinning (`Probability/Jumps/PoissonThinning.lean`). Marking each loss
as an exceedance of `x` with probability `Gbar(x) = 1 − G(x)` splits the Poisson count, and the
exceedances form a Poisson(`λ Gbar(x)`) count. The event is "no exceedance", so its probability is
the zero-probability of that count (`measureReal_forall_lt_le_eq_poisson_zero`). This equality
of probabilities is all that is proved here; that the exceedance count itself has the thinned
Poisson law is not derived.

For generalized Pareto severities the maximum has a **generalized extreme value** law, exactly,
with no limit taken (MFE Exercise 5.26): for `x ≥ 0`,

  `P(max_{i<N} Yᵢ ≤ x) = H_ξ((x − μ)/σ)`,  `σ = β λ^ξ`,  `μ = β(λ^ξ − 1)/ξ`  (`μ = β log λ`
  for `ξ = 0`)

(`measureReal_poisson_max_gpd`, `measureReal_poisson_max_gpd_zero`). This is the Poisson–GPD
model behind the peaks-over-threshold method: a Poisson number of GPD exceedances produces GEV
block maxima, with the normalizing constants of GEV max-stability evaluated at the real rate `λ`
instead of an integer block size. For `x < 0` the probability is `P(N = 0) = e^{−λ}`, the mass
of the empty maximum, and the GEV identity does not hold there.

## Main results

* `measureReal_forall_lt_le_of_poisson`: `P(max_{i<N} Yᵢ ≤ x) = exp(−λ(1 − G(x)))`.
* `measureReal_forall_lt_le_eq_poisson_zero`: the same probability as `P(Poisson(λ Gbar(x)) = 0)`.
* `exp_neg_mul_gpdTail`, `exp_neg_mul_gpdTail_zero`: `exp(−λ Gbar_{ξ,β}(x))` is a GEV distribution
  function on `x ≥ 0`.
* `measureReal_poisson_max_gpd`, `measureReal_poisson_max_gpd_zero`: MFE Exercise 5.26.

## References

* [*QRM Exercise Book*][QRMExerciseBook], Ex. 5.26

## Tags

maximum of Poisson losses, peaks over threshold, generalized Pareto distribution,
generalized extreme value, extreme value theory, block maxima, compound Poisson loss, MSC 60G55,
MSC 91G70, JEL G32
-/

@[expose] public section

namespace MathFin

open Real MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal Nat

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {N : Ω → ℕ} {Y : ℕ → Ω → ℝ}
  {r : ℝ≥0}

/-- **The maximum of a Poisson number of iid losses.** If `N ∼ Poisson(λ)` is independent of the
iid sequence `(Yᵢ)` with law `μ`, then
`P(Yᵢ ≤ x for all i < N) = exp(−λ (1 − G(x)))` with `G = cdf μ`. -/
theorem measureReal_forall_lt_le_of_poisson {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hN : HasLaw N (poissonMeasure r) P) (hNm : Measurable N) (hYm : ∀ i, Measurable (Y i))
    (hY : ∀ i, HasLaw (Y i) μ P) (hind : iIndepFun Y P)
    (hNY : IndepFun N (fun ω i ↦ Y i ω) P) (x : ℝ) :
    P.real {ω | ∀ i < N ω, Y i ω ≤ x} = exp (-((r : ℝ) * (1 - cdf μ x))) := by
  -- the event, sorted by the value of `N`
  set S : ℕ → Set (ℕ → ℝ) := fun n ↦ {y | ∀ i < n, y i ≤ x} with hS
  have hSm (n : ℕ) : MeasurableSet (S n) := by
    have : S n = ⋂ i ∈ Finset.range n, (fun y : ℕ → ℝ ↦ y i) ⁻¹' Iic x := by
      ext y
      simp [hS]
    rw [this]
    exact Finset.measurableSet_biInter _ fun i _ ↦ measurable_pi_apply i measurableSet_Iic
  have hevent : {ω | ∀ i < N ω, Y i ω ≤ x} =
      ⋃ n, N ⁻¹' {n} ∩ (fun ω i ↦ Y i ω) ⁻¹' S n := by
    ext ω
    simp [hS]
  -- each piece factorizes: `P(N = n) · P(Yᵢ ≤ x, i < n) = P(N = n) · G(x)ⁿ`
  have hpiece (n : ℕ) : P (N ⁻¹' {n} ∩ (fun ω i ↦ Y i ω) ⁻¹' S n) =
      ENNReal.ofReal (rexp (-(r : ℝ)) * (r : ℝ) ^ n / n ! * cdf μ x ^ n) := by
    rw [hNY.measure_inter_preimage_eq_mul _ _ (measurableSet_singleton n) (hSm n)]
    have hN1 : P (N ⁻¹' {n}) = ENNReal.ofReal (rexp (-(r : ℝ)) * (r : ℝ) ^ n / n !) := by
      rw [← Measure.map_apply hNm (measurableSet_singleton n), hN.map_eq,
        poissonMeasure_singleton]
    have hS' : (fun ω i ↦ Y i ω) ⁻¹' S n = ⋂ i ∈ Finset.range n, Y i ⁻¹' Iic x := by
      ext ω
      simp [hS]
    have hY1 (i : ℕ) : P (Y i ⁻¹' Iic x) = ENNReal.ofReal (cdf μ x) := by
      rw [← Measure.map_apply (hYm i) measurableSet_Iic, (hY i).map_eq, ofReal_cdf]
    rw [hN1, hS', hind.measure_inter_preimage_eq_mul (Finset.range n)
        fun i _ ↦ measurableSet_Iic, Finset.prod_congr rfl fun i _ ↦ hY1 i, Finset.prod_const,
      Finset.card_range, ← ENNReal.ofReal_pow (cdf_nonneg μ x),
      ← ENNReal.ofReal_mul (by positivity)]
  have hdisj : Pairwise (Function.onFun Disjoint
      fun n ↦ N ⁻¹' {n} ∩ (fun ω i ↦ Y i ω) ⁻¹' S n) := fun m n hmn ↦
    Disjoint.mono inter_subset_left inter_subset_left
      ((disjoint_singleton.2 hmn).preimage N)
  have hsum := PoissonPgf.hasSum_poisson_weights_mul_pow r (cdf μ x)
  rw [measureReal_def, hevent, measure_iUnion hdisj fun n ↦
      (hNm (measurableSet_singleton n)).inter
        ((Measurable.of_eval hYm : Measurable fun ω i ↦ Y i ω) (hSm n)),
    tsum_congr hpiece, ← ENNReal.ofReal_tsum_of_nonneg
      (fun n ↦ mul_nonneg (by positivity) (pow_nonneg (cdf_nonneg μ x) n)) hsum.summable,
    hsum.tsum_eq, ENNReal.toReal_ofReal (exp_pos _).le]
  congr 1
  ring

/-- **No exceedance is a Poisson zero.** The probability that none of the `N ∼ Poisson(λ)` losses
exceeds `x` is the probability that a Poisson count of mean `λ Gbar(x)` vanishes: the exceedances of
`x` thin the loss count with retention probability `Gbar(x) = 1 − G(x)`. -/
theorem measureReal_forall_lt_le_eq_poisson_zero {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hN : HasLaw N (poissonMeasure r) P) (hNm : Measurable N) (hYm : ∀ i, Measurable (Y i))
    (hY : ∀ i, HasLaw (Y i) μ P) (hind : iIndepFun Y P)
    (hNY : IndepFun N (fun ω i ↦ Y i ω) P) (x : ℝ) :
    P.real {ω | ∀ i < N ω, Y i ω ≤ x} =
      (poissonMeasure (r * (1 - cdf μ x).toNNReal)).real {0} := by
  rw [measureReal_forall_lt_le_of_poisson hN hNm hYm hY hind hNY, poissonMeasure_real_singleton,
    NNReal.coe_mul, Real.coe_toNNReal _ (sub_nonneg.2 (cdf_le_one μ x))]
  simp

/-! ### Generalized Pareto severities give a GEV maximum -/

/-- For `ξ ≠ 0`, `λ > 0` and `x ≥ 0`, `exp(−λ Gbar_{ξ,β}(x)) = H_ξ((x − μ)/σ)` with `σ = β λ^ξ` and
`μ = β(λ^ξ − 1)/ξ`. -/
theorem exp_neg_mul_gpdTail {ξ β : ℝ} (hξ : ξ ≠ 0) (hβ : 0 < β) {l : ℝ} (hl : 0 < l) {x : ℝ}
    (hx : 0 ≤ x) :
    exp (-(l * gpdTail ξ β x)) =
      gevCDF ξ ((x - β * (l ^ ξ - 1) / ξ) / (β * l ^ ξ)) := by
  have hβ0 : β ≠ 0 := hβ.ne'
  have hs : 0 < l ^ ξ := rpow_pos_of_pos hl ξ
  have hs0 : l ^ ξ ≠ 0 := hs.ne'
  -- the GEV argument is the GPD support variable rescaled by `λ^{−ξ}`
  have hkey : 1 + ξ * ((x - β * (l ^ ξ - 1) / ξ) / (β * l ^ ξ)) =
      (1 + ξ * (x / β)) / l ^ ξ := by
    field_simp
    ring
  by_cases hsupp : 0 < 1 + ξ * (x / β)
  · have hpos : 0 < 1 + ξ * ((x - β * (l ^ ξ - 1) / ξ) / (β * l ^ ξ)) := by
      rw [hkey]
      exact div_pos hsupp hs
    rw [gpdTail_of_nonneg hξ hx hsupp.le, gevCDF_of_pos hξ hpos, hkey,
      div_rpow hsupp.le hs.le, ← rpow_mul hl.le, show ξ * (-1 / ξ) = -1 by field_simp,
      rpow_neg_one, div_inv_eq_mul, mul_comm l]
  · have hle : 1 + ξ * (x / β) ≤ 0 := not_lt.1 hsupp
    have hneg : ξ < 0 := by
      by_contra! h
      have : 0 ≤ ξ * (x / β) := mul_nonneg h (div_nonneg hx hβ.le)
      linarith
    have hnp : 1 + ξ * ((x - β * (l ^ ξ - 1) / ξ) / (β * l ^ ξ)) ≤ 0 := by
      rw [hkey]
      exact div_nonpos_of_nonpos_of_nonneg hle hs.le
    rw [gpdTail_of_endpoint_le hξ hx hle, mul_zero, neg_zero, exp_zero,
      gevCDF_of_nonpos hξ hnp, ite_eq_right (not_lt.2 hneg.le)]

/-- For `ξ = 0`, `λ > 0` and `x ≥ 0`, `exp(−λ e^{−x/β}) = H_0((x − β log λ)/β)`. -/
theorem exp_neg_mul_gpdTail_zero {β : ℝ} (hβ : 0 < β) {l : ℝ} (hl : 0 < l) {x : ℝ}
    (hx : 0 ≤ x) : exp (-(l * gpdTail 0 β x)) = gevCDF 0 ((x - β * log l) / β) := by
  have hβ0 : β ≠ 0 := hβ.ne'
  rw [gpdTail_zero_shape hx, gevCDF_zero,
    show -((x - β * log l) / β) = log l + -(x / β) by
      rw [sub_div, mul_div_cancel_left₀ _ hβ0]; ring,
    exp_add, exp_log hl]

/-- **MFE Exercise 5.26.** If `N ∼ Poisson(λ)`, `λ > 0`, is independent of iid `GPD(ξ, β)` losses
`(Yᵢ)` with `ξ ≠ 0`, the largest loss has a generalized extreme value law on `[0, ∞)`:
`P(max_{i<N} Yᵢ ≤ x) = H_ξ((x − μ)/σ)` with `σ = β λ^ξ` and `μ = β(λ^ξ − 1)/ξ`. -/
theorem measureReal_poisson_max_gpd {ξ β : ℝ} (hξ : ξ ≠ 0) (hβ : 0 < β) (hr : 0 < r)
    (hN : HasLaw N (poissonMeasure r) P) (hNm : Measurable N) (hYm : ∀ i, Measurable (Y i))
    (hY : ∀ i, HasLaw (Y i) (gpdMeasure ξ β) P) (hind : iIndepFun Y P)
    (hNY : IndepFun N (fun ω i ↦ Y i ω) P) {x : ℝ} (hx : 0 ≤ x) :
    P.real {ω | ∀ i < N ω, Y i ω ≤ x} =
      gevCDF ξ ((x - β * ((r : ℝ) ^ ξ - 1) / ξ) / (β * (r : ℝ) ^ ξ)) := by
  rw [measureReal_forall_lt_le_of_poisson hN hNm hYm hY hind hNY, cdf_gpdMeasure hβ, gpdCDF,
    sub_sub_cancel, exp_neg_mul_gpdTail hξ hβ (NNReal.coe_pos.2 hr) hx]

/-- **MFE Exercise 5.26, exponential case.** If `N ∼ Poisson(λ)`, `λ > 0`, is independent of iid
exponential losses `GPD(0, β)`, the largest loss has a Gumbel law on `[0, ∞)`:
`P(max_{i<N} Yᵢ ≤ x) = H_0((x − β log λ)/β)`. -/
theorem measureReal_poisson_max_gpd_zero {β : ℝ} (hβ : 0 < β) (hr : 0 < r)
    (hN : HasLaw N (poissonMeasure r) P) (hNm : Measurable N) (hYm : ∀ i, Measurable (Y i))
    (hY : ∀ i, HasLaw (Y i) (gpdMeasure 0 β) P) (hind : iIndepFun Y P)
    (hNY : IndepFun N (fun ω i ↦ Y i ω) P) {x : ℝ} (hx : 0 ≤ x) :
    P.real {ω | ∀ i < N ω, Y i ω ≤ x} = gevCDF 0 ((x - β * log r) / β) := by
  rw [measureReal_forall_lt_le_of_poisson hN hNm hYm hY hind hNY, cdf_gpdMeasure hβ, gpdCDF,
    sub_sub_cancel, exp_neg_mul_gpdTail_zero hβ (NNReal.coe_pos.2 hr) hx]

end MathFin
