/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.PercolationScale

/-!
# PercolationScaleTail

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The union bound over scales for the percolation scale

The percolation estimate of Section 5.2 produces, at every scale `k`, a bound
`P[light crossing at scale k] ≤ exp(-A 3^k)` with a rate `A` independent of `k`.
This file turns a family of such bounds into the two statements the
chains-of-good-cubes proposition needs:

* the light crossings stop occurring almost surely, so the percolation scale
  `percolationScaleTotal` is almost surely given by its defining property; and
* the tail `P[Y ≥ N] ≤ exp(-(A/6) 3^N)` for every `N ≥ 1`.

Both come from the same elementary observation: because `3^i ≥ 1 + 2i`, the
sequence `exp(-u 3^i)` is dominated by the geometric sequence
`exp(-u) exp(-2u)^i`, whose sum is at most `2 exp(-u)` as soon as
`exp(-2u) ≤ 1/2`.  Summing from the scale `N - 1` — the first scale at which the
defining property of the percolation scale can fail when `Y ≥ N` — gives
`2 exp(-A 3^{N-1})`, and the second factor of `2` is absorbed into the exponent
by lowering the rate from `A/3` to `A/6`.  The clause is stated for `N ≥ 1`: at
`N = 0` the left-hand side is `1` and no positive rate can bound it.

## Main results

* `tsum_exp_mul_three_pow_le` — the geometric domination of `exp(-u 3^i)`.
* `measure_iUnion_shift_le` — the union bound from the scale `j` upwards.
* `ae_mem_eventuallyHeavyPaths` — the light crossings stop almost surely.
* `measure_le_percolationScaleTotal_le` — the tail of the percolation scale.

## References

* ABK26, the chains of good cubes of Section 5.2.
-/

namespace Algsuperdiff.Section5.Provider

open Algsuperdiff.Section3
open Algsuperdiff.Section5.Support
open HCPolySupport MeasureTheory
open scoped ENNReal

noncomputable section

/-! ## 1. Geometric domination of a doubly exponential sequence -/

/-- The elementary inequality `1 + 2 i ≤ 3 ^ i`, which is what makes the
sequence `exp(-u 3^i)` geometrically dominated. -/
theorem one_add_two_mul_le_three_pow (i : ℕ) : (1 : ℝ) + 2 * i ≤ 3 ^ i := by
  have h := one_add_mul_le_pow (a := (2 : ℝ)) (by norm_num) i
  have h3 : ((1 : ℝ) + 2) ^ i = 3 ^ i := by norm_num
  calc (1 : ℝ) + 2 * i = 1 + (i : ℝ) * 2 := by ring
    _ ≤ (1 + 2) ^ i := h
    _ = 3 ^ i := h3

/-- The doubly exponential sequence is dominated by a geometric one of ratio
`exp(-2u)`. -/
theorem exp_mul_three_pow_le {u : ℝ} (hu : 0 < u) (i : ℕ) :
    Real.exp (-(u * 3 ^ i)) ≤ Real.exp (-u) * Real.exp (-(2 * u)) ^ i := by
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have h := one_add_two_mul_le_three_pow i
  have h' : u * (1 + 2 * i) ≤ u * 3 ^ i := mul_le_mul_of_nonneg_left h hu.le
  linarith only [h']

/-- The ratio of the dominating geometric sequence is at most `1/2` once
`log 2 ≤ 2 u`. -/
theorem exp_two_mul_le_half {u : ℝ} (hu : Real.log 2 ≤ 2 * u) :
    Real.exp (-(2 * u)) ≤ 1 / 2 := by
  have h : Real.exp (-(2 * u)) ≤ Real.exp (-Real.log 2) :=
    Real.exp_le_exp.mpr (by linarith only [hu])
  have hlog : Real.exp (-Real.log 2) = 1 / 2 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  rwa [hlog] at h

theorem summable_exp_mul_three_pow {u : ℝ} (hu : 0 < u) :
    Summable fun i : ℕ => Real.exp (-(u * 3 ^ i)) := by
  have hgeo : Summable fun i : ℕ => Real.exp (-u) * Real.exp (-(2 * u)) ^ i := by
    refine Summable.mul_left _ (summable_geometric_of_lt_one (Real.exp_pos _).le ?_)
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith only [hu])
  exact hgeo.of_nonneg_of_le (fun i => (Real.exp_pos _).le)
    fun i => exp_mul_three_pow_le hu i

/-- **The geometric domination**: the whole sum from the base scale is at most
twice its first term. -/
theorem tsum_exp_mul_three_pow_le {u : ℝ} (hu : Real.log 2 ≤ 2 * u) (hupos : 0 < u) :
    (∑' i : ℕ, Real.exp (-(u * 3 ^ i))) ≤ 2 * Real.exp (-u) := by
  have hhalf := exp_two_mul_le_half hu
  have hr0 : (0 : ℝ) ≤ Real.exp (-(2 * u)) := (Real.exp_pos _).le
  have hrLt : Real.exp (-(2 * u)) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith only [hupos])
  have hgeo : Summable fun i : ℕ => Real.exp (-u) * Real.exp (-(2 * u)) ^ i :=
    (summable_geometric_of_lt_one hr0 hrLt).mul_left _
  have hsum : (∑' i : ℕ, Real.exp (-u) * Real.exp (-(2 * u)) ^ i) =
      Real.exp (-u) * (1 - Real.exp (-(2 * u)))⁻¹ := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hrLt]
  have hden : (1 : ℝ) / 2 ≤ 1 - Real.exp (-(2 * u)) := by linarith only [hhalf]
  have hdenInv : (1 - Real.exp (-(2 * u)))⁻¹ ≤ 2 := by
    have hinv := inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 2) hden
    norm_num at hinv ⊢
    exact hinv
  calc (∑' i : ℕ, Real.exp (-(u * 3 ^ i)))
      ≤ ∑' i : ℕ, Real.exp (-u) * Real.exp (-(2 * u)) ^ i :=
        (summable_exp_mul_three_pow hupos).tsum_le_tsum
          (fun i => exp_mul_three_pow_le hupos i) hgeo
    _ = Real.exp (-u) * (1 - Real.exp (-(2 * u)))⁻¹ := hsum
    _ ≤ Real.exp (-u) * 2 := mul_le_mul_of_nonneg_left hdenInv (Real.exp_pos _).le
    _ = 2 * Real.exp (-u) := by ring

/-- Absorbing the factor `2` of the geometric sum into the exponent: the rate
drops from `A/3` at the scale `j` to `A/6` at the scale `j + 1`. -/
theorem two_mul_exp_le_exp_div {A : ℝ} (hA : 2 * Real.log 2 ≤ A) (j : ℕ) :
    2 * Real.exp (-(A * 3 ^ j)) ≤ Real.exp (-(A / 6 * 3 ^ (j + 1))) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h1 : (1 : ℝ) ≤ 3 ^ j := one_le_pow₀ (by norm_num)
  have htwo : (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
  rw [htwo, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have hpow : (3 : ℝ) ^ (j + 1) = 3 ^ j * 3 := by rw [pow_succ]
  rw [hpow]
  have hA0 : (0 : ℝ) ≤ A := by linarith only [hA, hlog2]
  have hgrow : A * 1 ≤ A * 3 ^ j := mul_le_mul_of_nonneg_left h1 hA0
  linarith only [hA, hgrow]

/-! ## 2. The union bound over scales, for an abstract family -/

section Abstract

variable {Omega : Type*} [MeasurableSpace Omega]

private theorem mul_three_pow_add {A : ℝ} (j i : ℕ) :
    A * 3 ^ (j + i) = A * 3 ^ j * 3 ^ i := by
  rw [pow_add]; ring

/-- **The union bound from a base scale.**  A family of events whose
probabilities decay like `exp(-A 3^k)` has union from the scale `j` upwards of
probability at most twice the `j`-th bound. -/
theorem measure_iUnion_shift_le (P : Measure Omega) (E : ℕ → Set Omega) {A : ℝ}
    (hApos : 0 < A) (hA : Real.log 2 ≤ 2 * A)
    (hE : ∀ k, P (E k) ≤ ENNReal.ofReal (Real.exp (-(A * 3 ^ k)))) (j : ℕ) :
    P (⋃ i : ℕ, E (j + i)) ≤ ENNReal.ofReal (2 * Real.exp (-(A * 3 ^ j))) := by
  have hupos : 0 < A * 3 ^ j := by positivity
  have hu : Real.log 2 ≤ 2 * (A * 3 ^ j) := by
    have h1 : (1 : ℝ) ≤ 3 ^ j := one_le_pow₀ (by norm_num)
    have hgrow : A * 1 ≤ A * 3 ^ j := mul_le_mul_of_nonneg_left h1 hApos.le
    linarith only [hA, hgrow]
  have hsummable := summable_exp_mul_three_pow hupos
  calc P (⋃ i : ℕ, E (j + i)) ≤ ∑' i : ℕ, P (E (j + i)) := measure_iUnion_le _
    _ ≤ ∑' i : ℕ, ENNReal.ofReal (Real.exp (-(A * 3 ^ j * 3 ^ i))) := by
        refine ENNReal.tsum_le_tsum fun i => ?_
        have hk := hE (j + i)
        rwa [mul_three_pow_add (A := A) j i] at hk
    _ = ENNReal.ofReal (∑' i : ℕ, Real.exp (-(A * 3 ^ j * 3 ^ i))) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun i => (Real.exp_pos _).le) hsummable).symm
    _ ≤ ENNReal.ofReal (2 * Real.exp (-(A * 3 ^ j))) :=
        ENNReal.ofReal_le_ofReal (tsum_exp_mul_three_pow_le hu hupos)

theorem tsum_measure_ne_top (P : Measure Omega) (E : ℕ → Set Omega) {A : ℝ}
    (hApos : 0 < A) (hE : ∀ k, P (E k) ≤ ENNReal.ofReal (Real.exp (-(A * 3 ^ k)))) :
    (∑' k : ℕ, P (E k)) ≠ ⊤ := by
  have hsummable := summable_exp_mul_three_pow hApos
  have hle : (∑' k : ℕ, P (E k)) ≤
      ENNReal.ofReal (∑' k : ℕ, Real.exp (-(A * 3 ^ k))) := by
    rw [ENNReal.ofReal_tsum_of_nonneg (fun i => (Real.exp_pos _).le) hsummable]
    exact ENNReal.tsum_le_tsum hE
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle

/-- **Almost surely the events stop occurring.**  This is the first
Borel-Cantelli lemma applied to the summable family. -/
theorem ae_exists_forall_notMem (P : Measure Omega) (E : ℕ → Set Omega) {A : ℝ}
    (hApos : 0 < A) (hE : ∀ k, P (E k) ≤ ENNReal.ofReal (Real.exp (-(A * 3 ^ k)))) :
    ∀ᵐ omega ∂P, ∃ N : ℕ, ∀ k : ℕ, N ≤ k → omega ∉ E k := by
  have h := MeasureTheory.ae_eventually_notMem (μ := P) (s := E)
    (tsum_measure_ne_top P E hApos hE)
  filter_upwards [h] with omega homega
  exact Filter.eventually_atTop.mp homega

end Abstract

/-! ## 3. The percolation scale -/

variable {d : ℕ}

/-- **The level set of the percolation scale is covered from the scale `j`.**
If `Y ≥ j + 1` then the defining property fails at `j`, so a light crossing
occurs at some scale at least `j`. -/
theorem subset_iUnion_lightQPathEvent (M : ABKModel d) (Creg Cinj : ℝ) (m : ℤ) (ep : ℝ)
    (j : ℕ) :
    {omega : Cutoff.CutoffSample d |
        j + 1 ≤ percolationScaleTotal M Creg Cinj m ep omega} ⊆
      ⋃ i : ℕ, lightQPathEvent M Creg Cinj m ep (j + i) := by
  intro omega homega
  simp only [Set.mem_ofPred_eq] at homega
  by_cases hgood : ∃ N : ℕ, ∀ k : ℕ, N ≤ k → omega ∉ lightQPathEvent M Creg Cinj m ep k
  · have hiff := (le_percolationScaleTotal_iff M Creg Cinj m ep hgood (j + 1)).1 homega
    have hj := hiff j (Nat.lt_succ_self j)
    push Not at hj
    obtain ⟨k, hjk, hk⟩ := hj
    refine Set.mem_iUnion.2 ⟨k - j, ?_⟩
    have hkj : j + (k - j) = k := by omega
    rw [hkj]
    exact hk
  · rw [percolationScaleTotal_eq_zero_of_not M Creg Cinj m ep hgood] at homega
    omega

/-- **The light crossings stop almost surely**, which is the hypothesis of
`percolationScaleTotal_ae_crossing`. -/
theorem ae_mem_eventuallyHeavyPaths (M : ABKModel d) (Creg Cinj : ℝ) (m : ℤ) (ep : ℝ)
    {P : Measure (Cutoff.CutoffSample d)} {A : ℝ} (hApos : 0 < A)
    (hE : ∀ k : ℕ, P (lightQPathEvent M Creg Cinj m ep k) ≤
      ENNReal.ofReal (Real.exp (-(A * 3 ^ k)))) :
    ∀ᵐ omega ∂P, omega ∈ eventuallyHeavyPaths M Creg Cinj m ep := by
  filter_upwards [ae_exists_forall_notMem P _ hApos hE] with omega homega
  exact homega

/-- **The tail of the percolation scale**, for every `N ≥ 1`.  The union bound
runs from the scale `N - 1`, and the factor `2` of the geometric sum is absorbed
by lowering the rate from `A/3` to `A/6`. -/
theorem measure_le_percolationScaleTotal_le (M : ABKModel d) (Creg Cinj : ℝ) (m : ℤ)
    (ep : ℝ) {P : Measure (Cutoff.CutoffSample d)} {A : ℝ} (hA : 2 * Real.log 2 ≤ A)
    (hE : ∀ k : ℕ, P (lightQPathEvent M Creg Cinj m ep k) ≤
      ENNReal.ofReal (Real.exp (-(A * 3 ^ k))))
    {N : ℕ} (hN : 1 ≤ N) :
    P {omega | N ≤ percolationScaleTotal M Creg Cinj m ep omega} ≤
      ENNReal.ofReal (Real.exp (-(A / 6 * 3 ^ N))) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hApos : 0 < A := by linarith only [hA, hlog2]
  have hAhalf : Real.log 2 ≤ 2 * A := by linarith only [hA, hlog2]
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, N = j + 1 := ⟨N - 1, by omega⟩
  calc P {omega | j + 1 ≤ percolationScaleTotal M Creg Cinj m ep omega}
      ≤ P (⋃ i : ℕ, lightQPathEvent M Creg Cinj m ep (j + i)) :=
        measure_mono (subset_iUnion_lightQPathEvent M Creg Cinj m ep j)
    _ ≤ ENNReal.ofReal (2 * Real.exp (-(A * 3 ^ j))) :=
        measure_iUnion_shift_le P _ hApos hAhalf hE j
    _ ≤ ENNReal.ofReal (Real.exp (-(A / 6 * 3 ^ (j + 1)))) :=
        ENNReal.ofReal_le_ofReal (two_mul_exp_le_exp_div hA j)

end

end Algsuperdiff.Section5.Provider
