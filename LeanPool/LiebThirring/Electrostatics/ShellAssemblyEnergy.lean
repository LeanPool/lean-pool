/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Electrostatics.NewtonConsequences
public import LeanPool.LiebThirring.Electrostatics.CoulombPositivity
import all LeanPool.LiebThirring.Electrostatics.Basic

/-!
# Energy bookkeeping for finite families of electron shells

Bilinearity for a finite family of positive measures, without subtraction.

A symmetric finite double sum consists of its diagonal and twice its upper triangle.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace LiebThirring

/-- Bilinearity for a finite family of positive measures, without subtraction. -/
theorem coulombEnergy_finsetSum {ι : Type*} (s : Finset ι)
    (μ : ι → Measure Position) [∀ i, SFinite (μ i)] :
    coulombEnergy (∑ i ∈ s, μ i) (∑ j ∈ s, μ j) =
      ∑ i ∈ s, ∑ j ∈ s, coulombEnergy (μ i) (μ j) := by
  unfold coulombEnergy coulombPotential
  simp_rw [lintegral_finsetSum_measure]
  apply Finset.sum_congr rfl
  intro i _
  exact lintegral_finsetSum s (fun j _ =>
    measurable_coulombKernel.lintegral_prod_right)

/-- A symmetric finite double sum consists of its diagonal and twice its upper triangle. -/
theorem symmetric_sum_eq_diagonal_add {n : ℕ} (f : Fin n → Fin n → ℝ≥0∞)
    (hf : ∀ i j, f i j = f j i) :
    (∑ i : Fin n, ∑ j : Fin n, f i j) =
      (∑ i : Fin n, f i i) +
        2 * ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j => i < j), f i j := by
  classical
  have hsplit (i j : Fin n) : f i j =
      (if j = i then f i i else 0) + (if i < j then f i j else 0) +
        (if j < i then f j i else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp only [h, h.ne.symm, not_lt_of_ge h.le, ↓reduceIte, zero_add, add_zero]
    · subst j
      simp only [↓reduceIte, lt_self_iff_false, add_zero]
    · simp only [h, h.ne, not_lt_of_ge h.le, ↓reduceIte, add_zero, zero_add, hf i j]
  have hswap : (∑ i : Fin n, ∑ j : Fin n, if j < i then f j i else 0) =
      ∑ i : Fin n, ∑ j : Fin n, if i < j then f i j else 0 :=
    Finset.sum_comm
  calc
    _ = (∑ i : Fin n, f i i) +
        (∑ i : Fin n, ∑ j : Fin n, if i < j then f i j else 0) +
        (∑ i : Fin n, ∑ j : Fin n, if j < i then f j i else 0) := by
      conv_lhs => arg 2; ext i; arg 2; ext j; rw [hsplit i j]
      simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    _ = _ := by
      rw [hswap]
      simp only [← Finset.sum_filter]
      rw [two_mul, add_assoc]

/-- A finite sum of positive-radius electron shells has finite Coulomb energy. -/
theorem coulombEnergy_sum_shell_ne_top {N : ℕ} (a : Fin N → Position)
    (r : Fin N → ℝ) (hr : ∀ i, 0 < r i) :
    coulombEnergy (∑ i, shell (a i) (r i)) (∑ i, shell (a i) (r i)) ≠ ⊤ := by
  rw [coulombEnergy_finsetSum]
  apply (ENNReal.sum_lt_top.mpr ?_).ne
  intro i _
  apply ENNReal.sum_lt_top.mpr
  intro j _
  exact lt_top_iff_ne_top.mpr (coulombEnergy_ne_top _ _
    (by rw [coulombEnergy_shell_self (a i) (hr i)]; exact
      (ENNReal.inv_lt_top.mpr (ENNReal.ofReal_pos.mpr (hr i))).ne)
    (by rw [coulombEnergy_shell_self (a j) (hr j)]; exact
      (ENNReal.inv_lt_top.mpr (ENNReal.ofReal_pos.mpr (hr j))).ne))

/-- Smearing bounds the total half-energy by repulsion and the shell self terms. -/
theorem coulombEnergy_sum_shell_div_two_le {N : ℕ} (x : Configuration N)
    (r : Fin N → ℝ) (hr : ∀ i, 0 < r i) :
    coulombEnergy (∑ i, shell (particlePosition x i) (r i))
        (∑ i, shell (particlePosition x i) (r i)) / 2 ≤
      electronRepulsion x + (∑ i, (ENNReal.ofReal (r i))⁻¹) / 2 := by
  rw [coulombEnergy_finsetSum, symmetric_sum_eq_diagonal_add]
  · simp_rw [coulombEnergy_shell_self _ (hr _)]
    have hp : (∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => i < j),
        coulombEnergy (shell (particlePosition x i) (r i))
          (shell (particlePosition x j) (r j))) ≤ electronRepulsion x := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact coulombEnergy_shell_le_kernel _ _ (hr i) (hr j)
    calc
      _ ≤ ((∑ i, (ENNReal.ofReal (r i))⁻¹) + 2 * electronRepulsion x) / 2 :=
        ENNReal.div_le_div_right (add_le_add_right (mul_le_mul_right hp 2) _) _
      _ = _ := by
        rw [ENNReal.add_div, mul_comm (2 : ℝ≥0∞), ENNReal.mul_div_cancel_right]
        · exact add_comm _ _
        all_goals norm_num
  · intro i j
    exact coulombEnergy_symm _ _

end LiebThirring

end
