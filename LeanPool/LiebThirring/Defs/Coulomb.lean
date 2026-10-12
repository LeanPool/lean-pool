/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Defs.Configuration

/-!
# Coulomb interactions

Electron and nuclear interactions, nearest-nucleus distances, and the electrostatic correction
in Baxter’s inequality.
-/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal

namespace LiebThirring

/-- Nonnegative Coulomb interaction, with infinite value at a collision. -/
@[expose] noncomputable def coulombKernel (x y : Position) : ℝ≥0∞ :=
  (ENNReal.ofReal ‖x - y‖)⁻¹

/-- Sum the Coulomb interactions over each unordered pair of electrons. -/
@[expose] noncomputable def electronRepulsion {N : ℕ} (x : Configuration N) : ℝ≥0∞ :=
  ∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j : Fin N => i < j),
    coulombKernel (particlePosition x i) (particlePosition x j)

/-- Sum electron–nucleus Coulomb interactions weighted by the nuclear charges. -/
@[expose] noncomputable def attraction {N M : ℕ} (z : Fin M → ℝ≥0)
    (R : Fin M → Position) (x : Configuration N) : ℝ≥0∞ :=
  ∑ i : Fin N, ∑ k : Fin M,
    (z k : ℝ≥0∞) * coulombKernel (particlePosition x i) (R k)

/-- Sum the charge-weighted Coulomb interactions over unordered pairs of nuclei. -/
@[expose] noncomputable def nuclearRepulsion {M : ℕ} (z : Fin M → ℝ≥0)
    (R : Fin M → Position) : ℝ≥0∞ :=
  ∑ k : Fin M, ∑ l ∈ Finset.univ.filter (fun l : Fin M => k < l),
    ((z k : ℝ≥0∞) * (z l : ℝ≥0∞)) * coulombKernel (R k) (R l)

/-- The nearest nuclear distance, with infinite value when there are no nuclei. -/
@[expose] noncomputable def nearestNucleusDistance {M : ℕ}
    (R : Fin M → Position) (x : Position) : ℝ≥0∞ :=
  ⨅ k : Fin M, ENNReal.ofReal ‖x - R k‖

/-- The nearest distance to another nucleus, with infinite value for a single nucleus. -/
@[expose] noncomputable def nearestOtherNucleusDistance {M : ℕ}
    (R : Fin M → Position) (k : Fin M) : ℝ≥0∞ :=
  ⨅ l : {l : Fin M // l ≠ k}, ENNReal.ofReal ‖R k - R l‖

/-- Nearest-nucleus inverse-distance control with the electrostatic screening coefficient. -/
@[expose] noncomputable def nearestNucleusControl {N M : ℕ} (Z : ℝ≥0)
    (R : Fin M → Position) (x : Configuration N) : ℝ≥0∞ :=
  (2 * (Z : ℝ≥0∞) + 1) *
    ∑ i : Fin N, (nearestNucleusDistance R (particlePosition x i))⁻¹

/-- The positive nearest-other-nucleus correction in Baxter’s inequality. -/
@[expose] noncomputable def baxterCorrection {M : ℕ} (Z : ℝ≥0)
    (R : Fin M → Position) : ℝ≥0∞ :=
  (Z : ℝ≥0∞) ^ 2 / 4 * ∑ k : Fin M, (nearestOtherNucleusDistance R k)⁻¹

/-- An off-diagonal symmetric finite sum counts each upper-triangular term twice. -/
theorem sum_ne_eq_two_sum_lt {α : Type*} [Fintype α] [LinearOrder α]
    (f : α → α → ℝ≥0∞) (hf : ∀ i j, f i j = f j i) :
    (∑ i, ∑ j, if i ≠ j then f i j else 0) =
      2 * ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), f i j := by
  have hs (i j : α) : (if i ≠ j then f i j else 0) =
      (if i < j then f i j else 0) + (if j < i then f j i else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp only [h.ne, ne_eq, not_false_eq_true, ite_true, h, ite_false,
        not_lt.mpr h.le, add_zero]
    · subst j
      simp only [ne_eq, not_true_eq_false, ite_false, lt_self_iff_false, add_zero]
    · simp only [h.ne', ne_eq, not_false_eq_true, ite_true, h, ite_false,
        not_lt.mpr h.le, zero_add, hf i j]
  simp_rw [hs, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j => if j < i then f j i else 0)]
  simp only [Finset.sum_filter, two_mul]

/-- A symmetric finite sum is its diagonal plus twice the upper triangle. -/
theorem sum_eq_diag_add_two_sum_lt {α : Type*} [Fintype α] [LinearOrder α]
    (f : α → α → ℝ≥0∞) (hf : ∀ i j, f i j = f j i) :
    (∑ i, ∑ j, f i j) =
      (∑ i, f i i) + 2 * ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), f i j := by
  classical
  calc
    (∑ i, ∑ j, f i j) =
        (∑ i, f i i) + ∑ i, ∑ j, if i ≠ j then f i j else 0 := by
      have hsplit (i j : α) : f i j =
          (if j = i then f i i else 0) + (if i ≠ j then f i j else 0) := by
        by_cases h : j = i
        · subst j
          simp
        · have h' : i ≠ j := fun hij => h hij.symm
          simp [h, h']
      conv_lhs => arg 2; ext i; arg 2; ext j; rw [hsplit i j]
      simp only [Finset.sum_add_distrib]
      simp
    _ = (∑ i, f i i) + 2 * ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), f i j := by
      rw [sum_ne_eq_two_sum_lt f hf]

end LiebThirring

end
