/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.HighContrastHomogenization.Support.Ambient.BlockMatrix
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.MatrixOperatorNorm

/-!
# VecGauge

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Elementary gauges and matrix algebra on the ambient vector carrier

The Section 5 modules work with two sizes of a vector of `Vec d = Fin d → ℝ`:
the ambient supremum norm `‖v‖` that the carrier itself carries, and the
Euclidean size `vecNorm v` in which the shell derivative gauges are written.
This leaf collects the two facts about that carrier that several Section 5
modules need and that would otherwise be reproved in each of them:

* the homogeneity of the Euclidean size, and its comparison
  `vecNorm v ≤ √d ‖v‖` with the ambient one, which is where every dimensional
  constant of the perturbation estimates comes from;
* the compatibility of the matrix action with a finite sum of vectors.

Both are stated for the plain carrier, with no model, cube or shell data, so the
module sits below every other Section 5 support file.

## Main results

* `vecNorm_smul` — absolute homogeneity of the Euclidean size.
* `vecNorm_le_sqrt_dim_mul_norm` — the Euclidean size is at most `√d` times the
  ambient supremum norm.
* `matVecMul_finset_sum` — a fixed matrix commutes with a finite sum of vectors.
-/

namespace Algsuperdiff.Section5.Support

open HCPolySupport
open HCPolySupport.Book.Ch02

noncomputable section

variable {d : ℕ}

/-- The Euclidean vector norm is absolutely homogeneous. -/
theorem vecNorm_smul (c : ℝ) (v : Vec d) : vecNorm (c • v) = |c| * vecNorm v := by
  simp only [vecNorm]
  rw [show (WithLp.toLp 2 (c • v) : EuclideanSpace ℝ (Fin d))
      = c • (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d)) from rfl, norm_smul]
  simp only [Real.norm_eq_abs]

/-- The Euclidean vector norm is at most `√d` times the ambient supremum norm. -/
theorem vecNorm_le_sqrt_dim_mul_norm (v : Vec d) :
    vecNorm v ≤ Real.sqrt d * ‖v‖ := by
  have h1 : vecNorm v = Real.sqrt (∑ i, ‖v i‖ ^ 2) := by
    simp only [vecNorm, EuclideanSpace.norm_eq]
  have h2 : (∑ i, ‖v i‖ ^ 2) ≤ (d : ℝ) * ‖v‖ ^ 2 := by
    calc (∑ i : Fin d, ‖v i‖ ^ 2) ≤ ∑ _i : Fin d, ‖v‖ ^ 2 := by
          gcongr with i
          exact norm_le_pi_norm v i
      _ = (d : ℝ) * ‖v‖ ^ 2 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc vecNorm v = Real.sqrt (∑ i, ‖v i‖ ^ 2) := h1
    _ ≤ Real.sqrt ((d : ℝ) * ‖v‖ ^ 2) := Real.sqrt_le_sqrt h2
    _ = Real.sqrt d * ‖v‖ := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg v)]

/-- The action of a fixed matrix commutes with a finite sum of vectors. -/
theorem matVecMul_finset_sum {iota : Type*} (A : Mat d) (s : Finset iota) (v : iota → Vec d) :
    matVecMul A (∑ j ∈ s, v j) = ∑ j ∈ s, matVecMul A (v j) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · funext i
    simp only [matVecMul, Finset.sum_apply, Finset.sum_empty, mul_zero,
      Finset.sum_const_zero]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, matVecMul_add, ih]

end

end Algsuperdiff.Section5.Support
