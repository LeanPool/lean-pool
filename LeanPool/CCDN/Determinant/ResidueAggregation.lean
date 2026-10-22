/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Determinant.LocalDeterminant
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith

/-!
# Aggregating the local determinant exponents for curves

Cauchy–Schwarz preserves the leading quadratic coefficient when residue classes
have different multiplicities. These are the numerical aggregation steps in the
curve case of CCDN Proposition 2.6. The geometric local divisibility and
finite-field multiplicity estimates are not part of this module.
-/

@[expose] public section
namespace CCDN
open Finset

/-- Aggregate classwise quadratic estimates without losing the leading constant. -/
private theorem aggregate_local_exponents {ι : Type*} (S : Finset ι)
    (n μ e : ι → ℕ) (he : ∀ i ∈ S, n i ^ 2 ≤ 2 * μ i * (e i + n i)) :
    (∑ i ∈ S, n i) ^ 2 ≤ 2 * (∑ i ∈ S, μ i) * ((∑ i ∈ S, e i) + ∑ i ∈ S, n i) := by
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul S
    (r := n) (f := fun i => 2 * μ i) (g := fun i => e i + n i)
    (fun _ _ => Nat.zero_le _) (fun _ _ => Nat.zero_le _) he
  simpa only [← mul_sum, sum_add_distrib, mul_assoc] using h

/-- Apply the aggregation directly to the repeated local weights. -/
theorem aggregate_multiplicity_exponents {ι : Type*} (S : Finset ι)
    (n μ : ι → ℕ) (hμ : ∀ i ∈ S, 0 < μ i) :
    (∑ i ∈ S, n i) ^ 2 ≤ 2 * (∑ i ∈ S, μ i) *
      ((∑ i ∈ S, multiplicityExponent (n i) (μ i)) + ∑ i ∈ S, n i) :=
  aggregate_local_exponents S n μ _ (fun i hi => multiplicityExponent_lower_bound _ _ (hμ i hi))

/-- Real-valued form with a uniform upper bound for total residue multiplicity. -/
theorem aggregate_exponent_lower {ι : Type*} (S : Finset ι)
    (n μ e : ι → ℕ) (he : ∀ i ∈ S, n i ^ 2 ≤ 2 * μ i * (e i + n i))
    {N : ℝ} (hN : 0 < N) (hμ : (∑ i ∈ S, μ i : ℕ) ≤ N) :
    (∑ i ∈ S, n i : ℕ) ^ 2 / (2 * N) - (∑ i ∈ S, n i : ℕ) ≤
      (∑ i ∈ S, e i : ℕ) := by
  have h : ((∑ i ∈ S, n i : ℕ) : ℝ) ^ 2 ≤
      2 * ((∑ i ∈ S, μ i : ℕ) : ℝ) *
        (((∑ i ∈ S, e i : ℕ) : ℝ) + (∑ i ∈ S, n i : ℕ)) := by
    exact_mod_cast aggregate_local_exponents S n μ e he
  apply sub_le_iff_le_add.mpr
  apply (div_le_iff₀ (by positivity : 0 < 2 * N)).mpr
  calc _ ≤ 2 * ((∑ i ∈ S, μ i : ℕ) : ℝ) *
        (((∑ i ∈ S, e i : ℕ) : ℝ) + (∑ i ∈ S, n i : ℕ)) := h
    _ ≤ _ := by nlinarith

end CCDN
