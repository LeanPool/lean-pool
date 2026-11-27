/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.SubstochasticHolder
public import LeanPool.VacuumBellSeparation.Gaussian.UnitaryEigenbasisOverlap

/-!
# Actual finite unitary trace Holder for two complex diagonals

Products of entries from two independent unitaries give substochastic
weights. This proves the true complex trace estimate, including phases,
needed on finite spectral compressions in the interpolation argument.
No infinite-dimensional conclusion is inferred from this finite lemma.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix
open scoped ENNReal Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Unitary cross weight given by `‖(U : Matrix ι ι ℂ) i j‖ * ‖(V : Matrix ι ι ℂ) j i‖`. -/
def unitaryCrossWeight (U V : unitary (Matrix ι ι ℂ)) (i j : ι) : ℝ :=
  ‖(U : Matrix ι ι ℂ) i j‖ * ‖(V : Matrix ι ι ℂ) j i‖

theorem unitaryCrossWeight_nonneg (U V : unitary (Matrix ι ι ℂ)) (i j : ι) :
    0 ≤ unitaryCrossWeight U V i j := mul_nonneg (norm_nonneg _) (norm_nonneg _)

theorem sum_unitaryCrossWeight_row_le (U V : unitary (Matrix ι ι ℂ)) (i : ι) :
    ∑ j, unitaryCrossWeight U V i j ≤ 1 := by
  have hu := sum_unitaryOverlapWeight_row U i
  have hv := sum_unitaryOverlapWeight_col V i
  simp only [unitaryOverlapWeight] at hu hv
  calc
    _ ≤ ∑ j, (‖(U : Matrix ι ι ℂ) i j‖ ^ 2 + ‖(V : Matrix ι ι ℂ) j i‖ ^ 2) / 2 := by
      apply Finset.sum_le_sum
      intro j _
      dsimp only [unitaryCrossWeight]
      nlinarith [sq_nonneg (‖(U : Matrix ι ι ℂ) i j‖ - ‖(V : Matrix ι ι ℂ) j i‖)]
    _ = 1 := by rw [← Finset.sum_div, Finset.sum_add_distrib, hu, hv]; norm_num

theorem sum_unitaryCrossWeight_col_le (U V : unitary (Matrix ι ι ℂ)) (j : ι) :
    ∑ i, unitaryCrossWeight U V i j ≤ 1 := by
  have hu := sum_unitaryOverlapWeight_col U j
  have hv := sum_unitaryOverlapWeight_row V j
  simp only [unitaryOverlapWeight] at hu hv
  calc
    _ ≤ ∑ i, (‖(U : Matrix ι ι ℂ) i j‖ ^ 2 + ‖(V : Matrix ι ι ℂ) j i‖ ^ 2) / 2 := by
      apply Finset.sum_le_sum
      intro i _
      dsimp only [unitaryCrossWeight]
      nlinarith [sq_nonneg (‖(U : Matrix ι ι ℂ) i j‖ - ‖(V : Matrix ι ι ℂ) j i‖)]
    _ = 1 := by rw [← Finset.sum_div, Finset.sum_add_distrib, hu, hv]; norm_num

theorem norm_trace_two_unitary_diagonals_le (U V : unitary (Matrix ι ι ℂ))
    (a b : ι → ℂ) :
    ‖(Matrix.diagonal a * (U : Matrix ι ι ℂ) * Matrix.diagonal b *
      (V : Matrix ι ι ℂ)).trace‖ ≤
      ∑ i, ∑ j, ‖a i‖ * ‖b j‖ * unitaryCrossWeight U V i j := by
  simp only [Matrix.trace, Matrix.diag_apply]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  simp only [norm_mul, unitaryCrossWeight]
  exact le_of_eq (by ring)

theorem ennreal_trace_two_unitary_diagonals_holder
    (U V : unitary (Matrix ι ι ℂ)) (a b : ι → ℂ)
    {p q : ℝ} (hpq : p.HolderConjugate q) :
    ENNReal.ofReal ‖(Matrix.diagonal a * (U : Matrix ι ι ℂ) * Matrix.diagonal b *
      (V : Matrix ι ι ℂ)).trace‖ ≤
      (∑ i, ENNReal.ofReal ‖a i‖ ^ p) ^ (1 / p) *
        (∑ j, ENNReal.ofReal ‖b j‖ ^ q) ^ (1 / q) := by
  let w : ι → ι → ℝ≥0∞ := fun i j => ENNReal.ofReal (unitaryCrossWeight U V i j)
  have hrow (i : ι) : ∑' j, w i j ≤ 1 := by
    rw [tsum_fintype]
    change ∑ j, ENNReal.ofReal (unitaryCrossWeight U V i j) ≤ 1
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => unitaryCrossWeight_nonneg U V i j)]
    exact (ENNReal.ofReal_le_ofReal (sum_unitaryCrossWeight_row_le U V i)).trans_eq (by norm_num)
  have hcol (j : ι) : ∑' i, w i j ≤ 1 := by
    rw [tsum_fintype]
    change ∑ i, ENNReal.ofReal (unitaryCrossWeight U V i j) ≤ 1
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => unitaryCrossWeight_nonneg U V i j)]
    exact (ENNReal.ofReal_le_ofReal (sum_unitaryCrossWeight_col_le U V j)).trans_eq (by norm_num)
  have hh := ennreal_substochastic_holder w hrow hcol
    (fun i => ENNReal.ofReal ‖a i‖) (fun j => ENNReal.ofReal ‖b j‖) hpq
  simp only [tsum_fintype] at hh
  apply le_trans _ hh
  have h := ENNReal.ofReal_le_ofReal (norm_trace_two_unitary_diagonals_le U V a b)
  convert h using 1
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => Finset.sum_nonneg fun j _ =>
    mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (unitaryCrossWeight_nonneg U V i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [ENNReal.ofReal_sum_of_nonneg (fun j _ =>
    mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (unitaryCrossWeight_nonneg U V i j))]
  apply Finset.sum_congr rfl
  intro j _
  rw [ENNReal.ofReal_mul (mul_nonneg (norm_nonneg _) (norm_nonneg _)),
    ENNReal.ofReal_mul (norm_nonneg _)]

end VacuumBellSeparation.Gaussian
