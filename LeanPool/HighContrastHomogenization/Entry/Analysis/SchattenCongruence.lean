/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Analysis.SchattenNormFoundations
public import LeanPool.HighContrastHomogenization.Entry.Analysis.SingularValueTheory
public import LeanPool.HighContrastHomogenization.Entry.Source.BoundedWindowFiniteness
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# High-contrast homogenization: Entry.Analysis.SchattenCongruence

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The sharp Schatten congruence bound

`p.fixed.geometry.parent.child.recurrence` invokes the Schatten ideal property. Rank approximation
in the L2 operator norm proves singular-value domination for arbitrary real
congruence matrices, including singular matrices and zero. Summing powers gives
the exact deterministic coefficient; integrating genuine finite moments gives
the law-level bound with the same coefficient.

The approximation-number and singular-moment libraries are the committed K1
infrastructure consumed at
No separate Courant–Fischer construction is needed:
`exists_rank_approximation` and `singularValueAt_le_norm_sub` already provide
the required comparison. No Loewner monotonicity of the absolute value or square
is used. The independent congruence-order bridges remain available below.
-/

open HCPolySupport.HighContrast (CoeffSpace)
namespace HCPolySupport.HighContrast.Analysis

open MeasureTheory
open scoped BigOperators Matrix Matrix.Norms.L2Operator MatrixOrder

noncomputable section

variable {d : ℕ}

/-- Congruence by any real matrix preserves the Loewner order: no Hermitian, invertibility or
nonsingularity hypothesis on `S`, so `S = 0` (the printed "degenerate `B`" case) specializes to
`0 ≤ 0` with no case split. Public replacement for the `private`
`HCPoly.Entry.Multiscale.DriftAdvance.matrix_congr_le`, which this file does not and cannot reach
into. -/
theorem matrix_congr_le {ι : Type*} [Fintype ι]
    {A B : Matrix ι ι ℝ} (hAB : A ≤ B) (S : Matrix ι ι ℝ) :
    Sᵀ * A * S ≤ Sᵀ * B * S := by
  have h := (Matrix.le_iff.mp hAB).conjTranspose_mul_mul_same S
  simpa only [Matrix.le_iff, Matrix.conjTranspose_eq_transpose_of_trivial, mul_sub, sub_mul]
    using h

/-- `BlockMatLoewnerLE` plus Hermitian symmetry of both sides transports to the ambient
`Matrix` Loewner order on `toFullBlockMat`. Same construction as the `private`
`HCPoly.Entry.Multiscale.DriftAdvance.matrixOrder_of_blockMatLoewnerLE`, reproved here so this
file does
not reach into another file's private namespace. -/
theorem matrixOrder_of_blockMatLoewnerLE {A B : BlockMat d}
    (hA : (toFullBlockMat A).IsHermitian) (hB : (toFullBlockMat B).IsHermitian)
    (hAB : BlockMatLoewnerLE A B) : toFullBlockMat A ≤ toFullBlockMat B := by
  apply Matrix.le_iff.mpr
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hB.sub hA) ?_
  intro x
  have h := hAB (ofFullBlockVec x)
  simp only [← dotProduct_toFullBlockVec, toFullBlockVec_blockMatVecMul,
    toFullBlockVec_ofFullBlockVec] at h
  simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub]
  linarith only [h]

/-- The reverse bridge: an ambient `Matrix` Loewner inequality between two doubled blocks'
full representations gives `BlockMatLoewnerLE` of the (`ofFullBlockMat`-recovered) blocks. -/
theorem blockMatLoewnerLE_of_le {M N : FullBlockMat d} (hMN : M ≤ N) :
    BlockMatLoewnerLE (ofFullBlockMat M) (ofFullBlockMat N) := by
  intro X
  have hMN' := Matrix.le_iff.mp hMN
  have hx := hMN'.dotProduct_mulVec_nonneg (toFullBlockVec X)
  simp only [Matrix.sub_mulVec, dotProduct_sub, star_trivial] at hx
  have hM : dotProduct (toFullBlockVec X) (M.mulVec (toFullBlockVec X)) =
      blockVecDot X (blockMatVecMul (ofFullBlockMat M) X) := by
    rw [← dotProduct_toFullBlockVec, toFullBlockVec_blockMatVecMul, toFullBlockMat_ofFullBlockMat]
  have hN : dotProduct (toFullBlockVec X) (N.mulVec (toFullBlockVec X)) =
      blockVecDot X (blockMatVecMul (ofFullBlockMat N) X) := by
    rw [← dotProduct_toFullBlockVec, toFullBlockVec_blockMatVecMul, toFullBlockMat_ofFullBlockMat]
  rw [hM, hN] at hx
  linarith only [hx]

/-- The `BlockMat`/`BlockMatLoewnerLE` transport of `matrix_congr_le`: congruence by any
`FullBlockMat d` (via `toFullBlockMat`/`ofFullBlockMat`) preserves the doubled-block Loewner
order, given both sides are symmetric doubled blocks. -/
theorem blockMatLoewnerLE_congr_le {A B : BlockMat d}
    (hA : IsSymmetricBlockMat A) (hB : IsSymmetricBlockMat B)
    (hAB : BlockMatLoewnerLE A B) (S : FullBlockMat d) :
    BlockMatLoewnerLE (ofFullBlockMat (Sᵀ * toFullBlockMat A * S))
      (ofFullBlockMat (Sᵀ * toFullBlockMat B * S)) := by
  have hA' : (toFullBlockMat A).IsHermitian := (toFullBlockMat_isHermitian_iff A).mpr hA
  have hB' : (toFullBlockMat B).IsHermitian := (toFullBlockMat_isHermitian_iff B).mpr hB
  exact blockMatLoewnerLE_of_le
    (matrix_congr_le (matrixOrder_of_blockMatLoewnerLE hA' hB' hAB) S)

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Rank approximation gives singular-value domination under arbitrary congruence. -/
theorem singularValueAt_congr_le (X B : Matrix n n ℝ) (r : ℕ) :
    singularValueAt (Bᵀ * X * B) r ≤ ‖B‖ ^ 2 * singularValueAt X r := by
  obtain ⟨R, hRrank, hRerr⟩ := exists_rank_approximation X r
  have hrank : (Bᵀ * R * B).rank ≤ r :=
    (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_mul_le_right _ _).trans hRrank)
  calc
    singularValueAt (Bᵀ * X * B) r ≤ ‖Bᵀ * X * B - Bᵀ * R * B‖ :=
      singularValueAt_le_norm_sub _ _ hrank
    _ = ‖Bᵀ * (X - R) * B‖ := by rw [mul_sub, sub_mul]
    _ ≤ (‖Bᵀ‖ * ‖X - R‖) * ‖B‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ = ‖B‖ ^ 2 * ‖X - R‖ := by
      rw [← Matrix.conjTranspose_eq_transpose_of_trivial B,
        show B.conjTranspose = star B from rfl, norm_star]
      ring
    _ ≤ ‖B‖ ^ 2 * singularValueAt X r := mul_le_mul_of_nonneg_left hRerr (sq_nonneg _)

/-- Congruence is bounded on every positive singular p-norm. -/
theorem singularNorm_congr_le (X B : Matrix n n ℝ) {p : ℝ} (hp : 0 < p) :
    singularNorm p (Bᵀ * X * B) ≤ ‖B‖ ^ 2 * singularNorm p X := by
  have hpoint (i : Fin (Fintype.card n)) :
      singularValues₀ (Bᵀ * X * B) i ≤ ‖B‖ ^ 2 * singularValues₀ X i := by
    simpa only [singularValueAt, dite_eq_left i.isLt] using singularValueAt_congr_le X B i.val
  have hsum : (∑ i, singularValues₀ (Bᵀ * X * B) i ^ p) ≤
      (‖B‖ ^ 2) ^ p * ∑ i, singularValues₀ X i ^ p := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [← Real.mul_rpow (sq_nonneg _) (singularValues₀_nonneg X i)]
    exact Real.rpow_le_rpow (singularValues₀_nonneg _ i) (hpoint i) hp.le
  rw [sum_singularValues₀ (Bᵀ * X * B) (fun x => x ^ p),
    sum_singularValues₀ X (fun x => x ^ p)] at hsum
  calc
    singularNorm p (Bᵀ * X * B) ≤
        ((‖B‖ ^ 2) ^ p * ∑ i, singularValues X i ^ p) ^ p⁻¹ :=
      Real.rpow_le_rpow (Finset.sum_nonneg fun i _ =>
        Real.rpow_nonneg (singularValues_nonneg _ i) _) hsum (inv_nonneg.mpr hp.le)
    _ = ‖B‖ ^ 2 * singularNorm p X := by
      rw [Real.mul_rpow (Real.rpow_nonneg (sq_nonneg _) _)
        (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (singularValues_nonneg X i) _),
        Real.rpow_rpow_inv (sq_nonneg _) hp.ne']
      rfl

/-- The sharp Schatten ideal estimate, including singular congruence matrices. -/
theorem absSchattenNorm_congr_le {d : ℕ} (X : BlockMat d) (B : FullBlockMat d)
    (hX : (toFullBlockMat X).IsHermitian) {N : ℝ} (hN : 1 ≤ N) :
    absSchattenNorm N (ofFullBlockMat (Bᵀ * toFullBlockMat X * B)) ≤
      ‖B‖ ^ 2 * absSchattenNorm N X := by
  have hc : (toFullBlockMat (ofFullBlockMat (Bᵀ * toFullBlockMat X * B))).IsHermitian := by
    rw [toFullBlockMat_ofFullBlockMat, ← Matrix.conjTranspose_eq_transpose_of_trivial B]
    exact Matrix.isHermitian_conjTranspose_mul_mul B hX
  rw [← singularNorm_eq_absSchattenNorm hc hN, ← singularNorm_eq_absSchattenNorm hX hN,
    toFullBlockMat_ofFullBlockMat]
  exact singularNorm_congr_le _ _ (lt_of_lt_of_le zero_lt_one hN)

/-- Integrating the sharp pointwise estimate preserves its dimension-free coefficient. -/
theorem lqSchattenNorm_congr_le {d : ℕ} {P : Measure (CoeffSpace d)} {N : ℝ} (hN : 1 ≤ N)
    {H : CoeffSpace d → BlockMat d} (hH : SchattenMemLp P N H) (B : FullBlockMat d) :
    lqSchattenNorm P N (fun a => ofFullBlockMat (Bᵀ * toFullBlockMat (H a) * B)) ≤
      ‖B‖ ^ 2 * lqSchattenNorm P N H := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hc : SchattenMemLp P N
      (fun a => ofFullBlockMat (Bᵀ * toFullBlockMat (H a) * B)) := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Source.memLqSchatten_congruence hH hN B
  have hmono : (∫ a, absSchattenNorm N (ofFullBlockMat (Bᵀ * toFullBlockMat (H a) * B)) ^ N ∂P) ≤
      (‖B‖ ^ 2) ^ N * ∫ a, absSchattenNorm N (H a) ^ N ∂P := by
    rw [← integral_const_mul]
    apply integral_mono_ae hc.integrable (hH.integrable.const_mul _)
    filter_upwards [hH.symmetric, hc.symmetric] with a ha hca
    rw [← Real.mul_rpow (sq_nonneg _)
      (absSchattenNorm_nonneg ((toFullBlockMat_isHermitian_iff _).2 ha) hN)]
    exact Real.rpow_le_rpow
      (absSchattenNorm_nonneg ((toFullBlockMat_isHermitian_iff _).2 hca) hN)
      (absSchattenNorm_congr_le _ _ ((toFullBlockMat_isHermitian_iff _).2 ha) hN) hNpos.le
  have hInt : 0 ≤ ∫ a, absSchattenNorm N (H a) ^ N ∂P := by
    apply integral_nonneg_of_ae
    filter_upwards [hH.symmetric] with a ha
    exact Real.rpow_nonneg (absSchattenNorm_nonneg ((toFullBlockMat_isHermitian_iff _).2 ha) hN) _
  have hcInt : 0 ≤ ∫ a, absSchattenNorm N (ofFullBlockMat (Bᵀ * toFullBlockMat (H a) * B)) ^ N
    ∂P := by
    apply integral_nonneg_of_ae
    filter_upwards [hc.symmetric] with a ha
    exact Real.rpow_nonneg (absSchattenNorm_nonneg ((toFullBlockMat_isHermitian_iff _).2 ha) hN) _
  calc
    lqSchattenNorm P N (fun a => ofFullBlockMat (Bᵀ * toFullBlockMat (H a) * B)) ≤
        ((‖B‖ ^ 2) ^ N * ∫ a, absSchattenNorm N (H a) ^ N ∂P) ^ N⁻¹ :=
      Real.rpow_le_rpow hcInt hmono (inv_nonneg.mpr hNpos.le)
    _ = ‖B‖ ^ 2 * lqSchattenNorm P N H := by
      rw [Real.mul_rpow (Real.rpow_nonneg (sq_nonneg _) _) hInt,
        Real.rpow_rpow_inv (sq_nonneg _) hNpos.ne']
      rfl


end

end HCPolySupport.HighContrast.Analysis
