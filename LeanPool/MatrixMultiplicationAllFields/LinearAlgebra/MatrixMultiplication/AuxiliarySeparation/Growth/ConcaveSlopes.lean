/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
public import Mathlib.Topology.Order.MonotoneConvergence
public import Mathlib.Tactic

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-!
# Slopes of positive discretely concave sequences

The row sequences in Section 6 have decreasing consecutive increments. A
nonnegative sequence cannot have a negative increment of this kind: every later
increment would be at least as negative. Consequently the increments converge
to a nonnegative limit, and the sequence divided by its index has the same limit.
-/

@[expose] public section

namespace MatrixMultiplicationAllFields



namespace MatrixMultiplication.AuxiliarySeparation

open Filter
open scoped Topology

/-- The usual second-difference inequality makes the increments decreasing. -/
theorem antitone_increments_of_discrete_concavity {u : ℕ → ℝ}
    (hu : ∀ n, u (n + 2) + u n ≤ 2 * u (n + 1)) :
    Antitone (fun n => u (n + 1) - u n) := by
  apply antitone_nat_of_succ_le
  intro n
  have h := hu n
  simp only [Nat.add_assoc] at *
  linarith

/-- A tangent-line upper bound for a sequence with decreasing increments. -/
theorem concave_sequence_le_affine {u : ℕ → ℝ}
    (hd : Antitone (fun n => u (n + 1) - u n)) (n k : ℕ) :
    u (n + k) ≤ u n + (k : ℝ) * (u (n + 1) - u n) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hstep := hd (show n ≤ n + k by omega)
      simp only at hstep
      rw [Nat.cast_add, Nat.cast_one]
      have hindex : n + (k + 1) = n + k + 1 := by omega
      rw [hindex]
      nlinarith

/-- Every increment of a nonnegative discretely concave sequence is nonnegative. -/
theorem increment_nonneg_of_antitone {u : ℕ → ℝ}
    (hu : ∀ n, 0 ≤ u n) (hd : Antitone (fun n => u (n + 1) - u n))
    (n : ℕ) : 0 ≤ u (n + 1) - u n := by
  by_contra hn
  have hneg : u (n + 1) - u n < 0 := lt_of_not_ge hn
  obtain ⟨k, hk⟩ := exists_lt_nsmul (neg_pos.mpr hneg) (u n)
  have hk' : u n < (k : ℝ) * -(u (n + 1) - u n) := by
    simpa only [nsmul_eq_mul] using hk
  have hbound := concave_sequence_le_affine hd n k
  have hnonneg := hu (n + k)
  nlinarith

/-- A nonnegative discretely concave sequence is increasing. -/
theorem monotone_of_nonneg_of_antitone_increments {u : ℕ → ℝ}
    (hu : ∀ n, 0 ≤ u n) (hd : Antitone (fun n => u (n + 1) - u n)) :
    Monotone u := by
  apply monotone_nat_of_le_succ
  intro n
  have := increment_nonneg_of_antitone hu hd n
  linarith

/-- Telescoping and Cesàro convergence identify the linear growth rate. -/
theorem tendsto_div_nat_of_tendsto_increments {u : ℕ → ℝ} {g : ℝ}
    (hd : Tendsto (fun n => u (n + 1) - u n) atTop (𝓝 g)) :
    Tendsto (fun n => u n / (n : ℝ)) atTop (𝓝 g) := by
  have hmean := hd.cesaro
  simp only [Finset.sum_range_sub] at hmean
  have hconst := tendsto_const_div_atTop_nhds_zero_nat (u 0)
  have hsum := hmean.add hconst
  simpa only [add_zero, div_eq_mul_inv, mul_sub, sub_add_cancel, mul_comm] using hsum

/-- The limiting increment of a nonnegative discretely concave sequence is
nonnegative, and it is also its linear growth rate. -/
theorem exists_nonneg_limit_of_antitone_increments {u : ℕ → ℝ}
    (hu : ∀ n, 0 ≤ u n) (hd : Antitone (fun n => u (n + 1) - u n)) :
    ∃ g : ℝ, 0 ≤ g ∧
      Tendsto (fun n => u (n + 1) - u n) atTop (𝓝 g) ∧
      Tendsto (fun n => u n / (n : ℝ)) atTop (𝓝 g) := by
  have hnonneg := increment_nonneg_of_antitone hu hd
  have hbdd : BddBelow (Set.range (fun n => u (n + 1) - u n)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact hnonneg n
  have hlim := tendsto_atTop_ciInf hd hbdd
  refine ⟨⨅ n, u (n + 1) - u n, ?_, hlim,
    tendsto_div_nat_of_tendsto_increments hlim⟩
  exact ge_of_tendsto hlim (Eventually.of_forall hnonneg)

/-- Positive-index version, suitable for the rows in Section 6. The value at
index zero is irrelevant. -/
theorem exists_concave_slope_limit {P : ℕ → ℝ}
    (hP : ∀ n, 0 < P (n + 1))
    (hd : Antitone (fun n => P (n + 2) - P (n + 1))) :
    ∃ g : ℝ, 0 ≤ g ∧
      (∀ n, g ≤ P (n + 2) - P (n + 1)) ∧
      Tendsto (fun n => P (n + 2) - P (n + 1)) atTop (𝓝 g) ∧
      Tendsto (fun n => P n / (n : ℝ)) atTop (𝓝 g) := by
  have hd' : Antitone (fun n => P ((n + 1) + 1) - P (n + 1)) := by
    simpa only [Nat.add_assoc] using hd
  obtain ⟨g, hg, hlim, hratio⟩ := exists_nonneg_limit_of_antitone_increments
    (u := fun n => P (n + 1)) (fun n => (hP n).le) hd'
  have hmul := hratio.mul (tendsto_natCast_div_add_atTop (1 : ℝ))
  have hshift : Tendsto (fun n => P (n + 1) / ((n + 1 : ℕ) : ℝ))
      atTop (𝓝 g) := by
    rw [mul_one] at hmul
    apply hmul.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    rw [Nat.cast_add, Nat.cast_one]
    field_simp
  refine ⟨g, hg, ?_, ?_, (tendsto_add_atTop_iff_nat 1).mp hshift⟩
  · intro n
    exact hd.le_of_tendsto (by simpa only [Nat.add_assoc] using hlim) n
  · simpa only [Nat.add_assoc] using hlim

end MatrixMultiplication.AuxiliarySeparation

end MatrixMultiplicationAllFields
