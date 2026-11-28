/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aleksey Salkutsan, Yang Ye
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Choice.Performance.Ratios

/-!
# Downside performance metrics

Finite-state Omega ratio, maximum drawdown of a finite price path, and the
positive-scaling invariance of the Calmar ratio.

## Main definitions

* `FiniteReturnModel`: a finite return model, nonnegative probability weights of total mass one.
* `finiteExpectedReturn`: the expected return of a finite return model.
* `omegaUpside`, `omegaDownside`: the expected gain above and the expected shortfall below a
  threshold.
* `omegaRatio`: the Omega ratio at a threshold in a finite state space.
* `maximumDrawdown`: the largest decline of a finite price path below its running peak.
* `calmarRatio`: the annual return divided by the maximum drawdown.

## Main results

* `omega_upside_sub_downside`: expected upside minus expected downside is the mean excess return.
* `omegaRatio_nonneg`: the finite-state Omega ratio is nonnegative.
* `omegaRatio_threshold_identity`: when the expected downside is nonzero,
  `omegaRatio − 1 = (𝔼[R] − threshold) / omegaDownside`.
* `sub_le_maximumDrawdown`: every chronological peak-to-trough decline `E s − E t`, `s ≤ t`, is at
  most `maximumDrawdown E`.
* `maximumDrawdown_nonneg`, `maximumDrawdown_scale`: nonnegativity, and positive homogeneity for
  scaling by `c ≥ 0`.
* `calmarRatio_scale_invariant`: the Calmar ratio is unchanged by a common scaling `c > 0`.
* `downsideMetrics_bundle`: one conjunction collecting the Omega, drawdown and Calmar facts.

## References

* [Keating and Shadwick (2002)][KeatingShadwick2002]
* [Young (1991)][Young1991]

## Tags

Omega ratio, maximum drawdown, Calmar ratio, downside risk, performance measurement, MSC 91G10,
JEL G11
-/

@[expose] public section

namespace MathFin

open scoped BigOperators

/-- A finite return model with nonnegative probability weights of total mass one. -/
structure FiniteReturnModel (ι : Type*) [Fintype ι] where
  /-- Probability weight assigned to a state. -/
  weight : ι → ℝ
  /-- Return realized in a state. -/
  outcome : ι → ℝ
  weight_nonneg : ∀ i, 0 ≤ weight i
  weight_sum_one : ∑ i, weight i = 1

/-- Expected return of a finite return model. -/
def finiteExpectedReturn {ι : Type*} [Fintype ι] (m : FiniteReturnModel ι) : ℝ :=
  ∑ i, m.weight i * m.outcome i

/-- Expected gain above a threshold. -/
def omegaUpside {ι : Type*} [Fintype ι] (m : FiniteReturnModel ι) (threshold : ℝ) : ℝ :=
  ∑ i, m.weight i * max (m.outcome i - threshold) 0

/-- Expected shortfall below a threshold. -/
def omegaDownside {ι : Type*} [Fintype ι]
    (m : FiniteReturnModel ι) (threshold : ℝ) : ℝ :=
  ∑ i, m.weight i * max (threshold - m.outcome i) 0

/-- Omega ratio at a threshold in a finite state space. -/
noncomputable def omegaRatio {ι : Type*} [Fintype ι]
    (m : FiniteReturnModel ι) (threshold : ℝ) : ℝ :=
  omegaUpside m threshold / omegaDownside m threshold

/-- Expected upside minus expected downside equals mean excess return. -/
theorem omega_upside_sub_downside {ι : Type*} [Fintype ι]
    (m : FiniteReturnModel ι) (threshold : ℝ) :
    omegaUpside m threshold - omegaDownside m threshold =
      finiteExpectedReturn m - threshold := by
  unfold omegaUpside omegaDownside finiteExpectedReturn
  rw [← Finset.sum_sub_distrib]
  calc
    (∑ i, (m.weight i * max (m.outcome i - threshold) 0 -
        m.weight i * max (threshold - m.outcome i) 0)) =
        ∑ i, m.weight i * (m.outcome i - threshold) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [← mul_sub]
          congr 1
          simpa only [neg_sub] using max_zero_sub_max_neg_zero_eq_self (m.outcome i - threshold)
    _ = ∑ i, (m.weight i * m.outcome i - threshold * m.weight i) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ = (∑ i, m.weight i * m.outcome i) - threshold * (∑ i, m.weight i) := by
          rw [Finset.sum_sub_distrib, Finset.mul_sum]
    _ = (∑ i, m.weight i * m.outcome i) - threshold := by
          rw [m.weight_sum_one, mul_one]

/-- The finite-state Omega ratio is nonnegative. -/
theorem omegaRatio_nonneg {ι : Type*} [Fintype ι]
    (m : FiniteReturnModel ι) (threshold : ℝ) :
    0 ≤ omegaRatio m threshold := by
  unfold omegaRatio omegaUpside omegaDownside
  apply div_nonneg
  · exact Finset.sum_nonneg fun i _ =>
      mul_nonneg (m.weight_nonneg i) (le_max_right _ _)
  · exact Finset.sum_nonneg fun i _ =>
      mul_nonneg (m.weight_nonneg i) (le_max_right _ _)

/-- Threshold identity for the Omega ratio when expected downside is nonzero. -/
theorem omegaRatio_threshold_identity {ι : Type*} [Fintype ι]
    (m : FiniteReturnModel ι) (threshold : ℝ)
    (hdown : omegaDownside m threshold ≠ 0) :
    omegaRatio m threshold - 1 =
      (finiteExpectedReturn m - threshold) / omegaDownside m threshold := by
  calc
    omegaRatio m threshold - 1 =
        (omegaUpside m threshold - omegaDownside m threshold) /
          omegaDownside m threshold := by
            unfold omegaRatio
            field_simp [hdown]
    _ = (finiteExpectedReturn m - threshold) / omegaDownside m threshold := by
          rw [omega_upside_sub_downside]

/-- The running peak is positively homogeneous: multiplication by `c > 0` is an order
isomorphism, so it commutes with the finite suprema defining `partialSups`. This is the
group-with-zero version of Mathlib's `[Group α]` lemma `partialSups_const_mul`. -/
theorem partialSups_const_mul₀ {ι : Type*} [Preorder ι] [LocallyFiniteOrderBot ι]
    {G₀ : Type*} [GroupWithZero G₀] [SemilatticeSup G₀] [PosMulReflectLT G₀] {c : G₀}
    (hc : 0 < c) (E : ι → G₀) (t : ι) :
    partialSups (fun s ↦ c * E s) t = c * partialSups E t :=
  map_partialSups (OrderIso.mulLeft₀ c hc) E t

/-- **Maximum drawdown** of a finite price path: the largest decline `max_{s ≤ t} E s − E t` of
the path below its running peak (Mathlib's `partialSups`), which is the largest chronological
peak-to-trough loss `E s − E t`, `s ≤ t` (`sub_le_maximumDrawdown`). The empty path has drawdown
`0`. -/
noncomputable def maximumDrawdown {n : ℕ} (price : Fin n → ℝ) : ℝ :=
  ⨆ t, partialSups price t - price t

/-- The decline below the running peak at any date is at most the maximum drawdown. -/
theorem partialSups_sub_le_maximumDrawdown {n : ℕ} (price : Fin n → ℝ) (t : Fin n) :
    partialSups price t - price t ≤ maximumDrawdown price :=
  le_ciSup (f := fun t ↦ partialSups price t - price t) (Set.finite_range _).bddAbove t

/-- Every chronological peak-to-trough decline `E s − E t` (`s ≤ t`) of a finite path is at
most its `maximumDrawdown`. -/
theorem sub_le_maximumDrawdown {n : ℕ} (E : Fin n → ℝ) {s t : Fin n} (hst : s ≤ t) :
    E s - E t ≤ maximumDrawdown E :=
  (sub_le_sub_right (le_partialSups_of_le E hst) _).trans (partialSups_sub_le_maximumDrawdown E t)

/-- Maximum drawdown is nonnegative, including for an empty path. -/
theorem maximumDrawdown_nonneg {n : ℕ} (price : Fin n → ℝ) :
    0 ≤ maximumDrawdown price :=
  Real.iSup_nonneg fun t ↦ sub_nonneg.2 (le_partialSups_of_le price (le_refl t))

/-- Maximum drawdown is positively homogeneous for nonnegative scaling. -/
theorem maximumDrawdown_scale {n : ℕ} (price : Fin n → ℝ) (c : ℝ) (hc : 0 ≤ c) :
    maximumDrawdown (fun i => c * price i) = c * maximumDrawdown price := by
  rcases hc.eq_or_lt with rfl | hc
  · have h0 (t : Fin n) : partialSups (fun _ : Fin n ↦ (0 : ℝ)) t = 0 :=
      le_antisymm (partialSups_le _ _ _ fun _ _ ↦ le_rfl)
        (le_partialSups_of_le (fun _ : Fin n ↦ (0 : ℝ)) (le_refl t))
    simp [maximumDrawdown, h0]
  · rw [maximumDrawdown, maximumDrawdown, Real.mul_iSup_of_nonneg hc.le]
    refine iSup_congr fun t ↦ ?_
    rw [partialSups_const_mul₀ hc]
    ring

/-- Calmar ratio: annual return divided by maximum drawdown. -/
noncomputable def calmarRatio (annualReturn maxDrawdown : ℝ) : ℝ :=
  annualReturn / maxDrawdown

/-- Calmar ratio is invariant under strictly positive common scaling. -/
theorem calmarRatio_scale_invariant (annualReturn maxDrawdown c : ℝ) (hc : 0 < c) :
    calmarRatio (c * annualReturn) (c * maxDrawdown) =
      calmarRatio annualReturn maxDrawdown := by
  simpa [calmarRatio] using
    (diff_div_scale_invariant (c := c) hc.ne' annualReturn 0 maxDrawdown)

/-- One acceptance bundle covering Omega, maximum drawdown, and Calmar. -/
theorem downsideMetrics_bundle {ι : Type*} [Fintype ι]
    (m : FiniteReturnModel ι) (threshold : ℝ)
    (hdown : omegaDownside m threshold ≠ 0)
    {n : ℕ} (price : Fin n → ℝ) (annualReturn c : ℝ) (hc : 0 < c) :
    (0 ≤ omegaRatio m threshold ∧
      omegaRatio m threshold - 1 =
        (finiteExpectedReturn m - threshold) / omegaDownside m threshold) ∧
    (0 ≤ maximumDrawdown price ∧
      maximumDrawdown (fun i => c * price i) = c * maximumDrawdown price) ∧
    calmarRatio (c * annualReturn) (c * maximumDrawdown price) =
      calmarRatio annualReturn (maximumDrawdown price) := by
  exact
    ⟨⟨omegaRatio_nonneg m threshold,
        omegaRatio_threshold_identity m threshold hdown⟩,
      ⟨maximumDrawdown_nonneg price,
        maximumDrawdown_scale price c hc.le⟩,
      calmarRatio_scale_invariant annualReturn (maximumDrawdown price) c hc⟩

end MathFin
