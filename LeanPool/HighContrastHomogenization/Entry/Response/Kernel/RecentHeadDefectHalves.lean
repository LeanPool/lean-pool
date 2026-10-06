/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Response.Core.LoadMeanIdentity
public import LeanPool.HighContrastHomogenization.Entry.Response.Core.SourceLoadBound
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.DiagonalDefectCarriers
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.RecentEnergyMapSupport

/-!
# High-contrast homogenization: Entry.Response.Kernel.RecentHeadDefectHalves

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The two halves of the recent-head defect bound

This file proves the two halves the diagonal weak-norm estimate's recent head is built from, for
the response-transfer proposition `p.response.transfer`: the `weakCellSum` half, bounding the
normalized root-mean-square of the child-optimizer mean defects by the reflected coarse-block
defect action, with the pointwise cell-defect step discharged of its metric-nondegeneracy
hypotheses; and the `weakAverageSum` half, the per-scale window sum over the good-branch
coefficient `√2 (1 + √M · 3^(ρn/2))`. Both halves record, along the way, that the branch where
the response matrix `respEhatMinus P jStar F t` is singular never occurs, since every
`diagonalWeak*`-family lemma excludes it by hypothesis.
-/

section
/-!
## HC bridge II, the recent-head cell-defect package

The pointwise cell-defect step, its form with the metric nondegeneracy hypotheses
discharged, and the full `weakCellSum` half of the recent head.
-/

open HCPolySupport.HighContrast (CoeffSpace blockSub matSqrt matSqrt_spec normalizedBlock)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ### HELPERS.  The POINTWISE CELL-DEFECT step of the recent head:
the first of the two summands of the printed right-hand side.  The per-cell input is
`metricNormSq_blockAverage_sub_adapted_le` (`DiagonalWeakNormComparison.lean`), and
`diagonalWeak_recent_cell_bound` is the cell bound.

The identity `cellAverage_optimizerField_respCoeffMinus_sub_eq`
(`DiagonalDefectCarriers.lean`) identifies the child-minus-parent optimizer
mean difference with `R D x`, where `D` is the coarse-block defect that `weakCellDefect`
normalizes and `x = (-p, q^-)` is the response load; the reflected `M_0`
metric of that vector becomes the `M_0^{-1}` quadratic form, and the matrix comparison closes
the estimate.  The lemmas below are the links between them.

The identity `cellAverage_optimizerField_respCoeffMinus_sub_eq` and its dependency chain, plus
`blockMatVecMul_blockSwap` and `blockVecDot_blockSwap_respM0`, are public in the support file
and are used directly below. -/

omit [NeZero d] in
/-- The block `diag(m^{-1}, m)` is exactly the inverse of the
flattened metric block `M_0 = diag(m, m^{-1})`.  This is what lets the matrix comparison
be applied with `M = M_0`, so that its metric constant is the printed
`K_0 = |M_0^{-1/2} Ehat M_0^{-1/2}|`. -/
theorem toFullBlockMat_respM0_inv {F : BlockMat d}
    (hm : (explicitCanonicalMetric F).PosDef) :
    toFullBlockMat (⟨(explicitCanonicalMetric F)⁻¹, 0, 0, explicitCanonicalMetric F⟩ : BlockMat d)
      = (toFullBlockMat (respM0 F))⁻¹ := by
  have hu : IsUnit (explicitCanonicalMetric F).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hm.isUnit
  have hmm : (explicitCanonicalMetric F)⁻¹ * explicitCanonicalMetric F = 1 :=
    Matrix.nonsing_inv_mul _ hu
  have hmm' : explicitCanonicalMetric F * (explicitCanonicalMetric F)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ hu
  refine (Matrix.inv_eq_left_inv ?_).symm
  ext a b
  rw [Matrix.mul_apply, Fintype.sum_sum_type]
  cases a with
  | inl i =>
    cases b with
    | inl j =>
      have : ∑ k : Fin d, (explicitCanonicalMetric F)⁻¹ i k * explicitCanonicalMetric F k j
          = ((explicitCanonicalMetric F)⁻¹ * explicitCanonicalMetric F) i j :=
            (Matrix.mul_apply).symm
      simp only [toFullBlockMat, respM0]
      rw [show (∑ k : Fin d, (explicitCanonicalMetric F)⁻¹ i k * explicitCanonicalMetric F k j) +
          (∑ k : Fin d, (0 : Mat d) i k * (0 : Mat d) k j) = _ from rfl]
      simp [this, hmm, Matrix.one_apply]
    | inr j =>
      simp [toFullBlockMat, respM0]
  | inr i =>
    cases b with
    | inl j =>
      simp [toFullBlockMat, respM0]
    | inr j =>
      have : ∑ k : Fin d, explicitCanonicalMetric F i k * (explicitCanonicalMetric F)⁻¹ k j
          = (explicitCanonicalMetric F * (explicitCanonicalMetric F)⁻¹) i j :=
            (Matrix.mul_apply).symm
      simp only [toFullBlockMat, respM0]
      rw [show (∑ k : Fin d, (0 : Mat d) i k * (0 : Mat d) k j) +
          (∑ k : Fin d, explicitCanonicalMetric F i k * (explicitCanonicalMetric F)⁻¹ k j) = _
            from rfl]
      simp [this, hmm', Matrix.one_apply]

omit [NeZero d] in
/-- POINTWISE CELL DEFECT.  The metric length of the reflected action `M_0^{1/2} R D x`
of a block defect `D` on a response load `x` is controlled by the metric factor
`K_0 = |M_0^{-1/2} E M_0^{-1/2}|`, the squared `E`-normalized size of `D` — which is exactly the
summand of `weakCellDefect` — and the `E`-quadratic load `x. E x = (L^-)^2`.  Composed with
`cellAverage_optimizerField_respCoeffMinus_sub_eq` this is the current-carrier form of
`metricNormSq_blockAverage_sub_adapted_le`. -/
theorem reflected_defect_metric_le {F E D : BlockMat d}
    (hm : (explicitCanonicalMetric F).PosDef) (hM0 : (toFullBlockMat (respM0 F)).PosDef)
    (hE : (toFullBlockMat E).PosDef) (x : BlockVec d) :
    blockVecDot
        (blockMatVecMul (blockSqrt (respM0 F))
          (blockMatVecMul (blockSwap d) (blockMatVecMul D x)))
        (blockMatVecMul (blockSqrt (respM0 F))
          (blockMatVecMul (blockSwap d) (blockMatVecMul D x)))
      ≤ ‖toFullBlockMat (normalizedBlock E (respM0 F))‖ *
          ‖toFullBlockMat (normalizedBlock D E)‖ ^ 2 *
          blockVecDot x (blockMatVecMul E x) := by
  rw [blockSqrt_qform_blockVecDot hM0.posSemidef, blockVecDot_blockSwap_respM0]
  have hquad : blockVecDot (blockMatVecMul D x)
      (blockMatVecMul (⟨(explicitCanonicalMetric F)⁻¹, 0, 0, explicitCanonicalMetric F⟩ :
        BlockMat d)
        (blockMatVecMul D x))
      = (toFullBlockMat D *ᵥ toFullBlockVec x) ⬝ᵥ
          (toFullBlockMat (respM0 F))⁻¹ *ᵥ (toFullBlockMat D *ᵥ toFullBlockVec x) := by
    rw [← dotProduct_toFullBlockVec]
    simp only [toFullBlockVec_blockMatVecMul]
    rw [toFullBlockMat_respM0_inv hm]
  rw [hquad]
  have hcmp := centered_metric_quadratic_le (M := toFullBlockMat (respM0 F))
    (E := toFullBlockMat E) (D := toFullBlockMat D) hM0 hE (toFullBlockVec x)
  have hN : ‖matSqrt (toFullBlockMat (respM0 F))⁻¹ * toFullBlockMat E *
        matSqrt (toFullBlockMat (respM0 F))⁻¹‖
      = ‖toFullBlockMat (normalizedBlock E (respM0 F))‖ := by
    simp [normalizedBlock]
  have hB : ‖matSqrt (toFullBlockMat E)⁻¹ * toFullBlockMat D *
        matSqrt (toFullBlockMat E)⁻¹‖
      = ‖toFullBlockMat (normalizedBlock D E)‖ := by
    simp [normalizedBlock]
  have hx : toFullBlockVec x ⬝ᵥ toFullBlockMat E *ᵥ toFullBlockVec x
      = blockVecDot x (blockMatVecMul E x) := by
    rw [← toFullBlockVec_blockMatVecMul, dotProduct_toFullBlockVec]
  rw [hN, hB, hx] at hcmp
  exact hcmp

/-! ## WITHOUT THE METRIC NONDEGENERACY BINDERS.
`DiagonalDefectCarriers.lean` classifies `respM0 F` for an ARBITRARY `F`.  There are
exactly three branches, and in each of them the pointwise cell-defect bound holds with the SAME
printed constants — so the pointwise estimate can be used
with `hm` and `hM0` DISCHARGED, not assumed.  The part of the classification that concerns
`explicitCanonicalMetric` / `respM0` is settled here; the `respEhatMinus` part is NOT settled
here. -/

omit [NeZero d] in
/-- The pointwise cell-defect bound holds for
EVERY `F : BlockMat d`, with no hypothesis on `explicitCanonicalMetric F` or on `respM0 F`.
* `explicitCanonicalMetric F = 0`: `blockSqrt (respM0 F)` annihilates everything, so the left
  side is `0` and the right side is a product of nonnegative factors.
* `explicitCanonicalMetric F` a unit and `respM0 F` positive semidefinite: then `respM0 F` is
positive
  DEFINITE (`Matrix.PosSemidef.posDef_iff_isUnit`) and `explicitCanonicalMetric F` is too, so this
  is
  literally the estimate with `hm` and `hM0`.
* `explicitCanonicalMetric F` a unit and `respM0 F` not positive semidefinite: `matSqrt` falls
through
  on both `respM0 F` and its inverse, so `M_0^{1/2}` acts as the identity and the
  printed metric factor is `‖Ehat‖` itself; the bound is then the matrix comparison at `M = I`. -/
theorem reflected_defect_metric_le_unconditional {F E D : BlockMat d}
    (hE : (toFullBlockMat E).PosDef) (x : BlockVec d) :
    blockVecDot
        (blockMatVecMul (blockSqrt (respM0 F))
          (blockMatVecMul (blockSwap d) (blockMatVecMul D x)))
        (blockMatVecMul (blockSqrt (respM0 F))
          (blockMatVecMul (blockSwap d) (blockMatVecMul D x)))
      ≤ ‖toFullBlockMat (normalizedBlock E (respM0 F))‖ *
          ‖toFullBlockMat (normalizedBlock D E)‖ ^ 2 *
          blockVecDot x (blockMatVecMul E x) := by
  have hL0 : 0 ≤ blockVecDot x (blockMatVecMul E x) := by
    have hh := hE.posSemidef.dotProduct_mulVec_nonneg (toFullBlockVec x)
    simp only [star_trivial, ← toFullBlockVec_blockMatVecMul,
      dotProduct_toFullBlockVec] at hh
    exact hh
  have hRHS : 0 ≤ ‖toFullBlockMat (normalizedBlock E (respM0 F))‖ *
      ‖toFullBlockMat (normalizedBlock D E)‖ ^ 2 *
      blockVecDot x (blockMatVecMul E x) :=
    mul_nonneg (mul_nonneg (norm_nonneg _) (sq_nonneg _)) hL0
  by_cases hu : IsUnit (explicitCanonicalMetric F).det
  · by_cases hpsd : (toFullBlockMat (respM0 F)).PosSemidef
    · have hM0 : (toFullBlockMat (respM0 F)).PosDef :=
        hpsd.posDef_iff_isUnit.mpr
          ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_det_toFullBlockMat_respM0 hu))
      have hm : (explicitCanonicalMetric F).PosDef :=
        (posSemidef_explicitCanonicalMetric_of_respM0 hpsd).posDef_iff_isUnit.mpr
          ((Matrix.isUnit_iff_isUnit_det _).mpr hu)
      exact reflected_defect_metric_le hm hM0 hE x
    · have hS1 : ∀ Y : BlockVec d, blockMatVecMul (blockSqrt (respM0 F)) Y = Y := by
        intro Y
        have hfull := toFullBlockVec_blockMatVecMul (blockSqrt (respM0 F)) Y
        rw [toFullBlockMat_blockSqrt_respM0_eq_one hpsd, Matrix.one_mulVec] at hfull
        calc blockMatVecMul (blockSqrt (respM0 F)) Y
            = ofFullBlockVec
                (toFullBlockVec (blockMatVecMul (blockSqrt (respM0 F)) Y)) :=
              (ofFullBlockVec_toFullBlockVec _).symm
          _ = ofFullBlockVec (toFullBlockVec Y) := by rw [hfull]
          _ = Y := ofFullBlockVec_toFullBlockVec Y
      rw [hS1, toFullBlockMat_normalizedBlock_respM0_eq_self E
        (isUnit_det_toFullBlockMat_respM0 hu) hpsd, blockMatVecMul_blockSwap]
      have hswap : blockVecDot
            ((blockMatVecMul D x).2, (blockMatVecMul D x).1)
            ((blockMatVecMul D x).2, (blockMatVecMul D x).1)
          = blockVecDot (blockMatVecMul D x) (blockMatVecMul D x) := by
        simp only [blockVecDot]
        ring
      rw [hswap]
      have hcmp := centered_metric_quadratic_le (M := (1 : FullBlockMat d))
        (E := toFullBlockMat E) (D := toFullBlockMat D) Matrix.PosDef.one hE
        (toFullBlockVec x)
      rw [inv_one, matSqrt_one, one_mul, mul_one, Matrix.one_mulVec] at hcmp
      have hB : ‖matSqrt (toFullBlockMat E)⁻¹ * toFullBlockMat D *
            matSqrt (toFullBlockMat E)⁻¹‖
          = ‖toFullBlockMat (normalizedBlock D E)‖ := by
        simp [normalizedBlock]
      have hx : toFullBlockVec x ⬝ᵥ toFullBlockMat E *ᵥ toFullBlockVec x
          = blockVecDot x (blockMatVecMul E x) := by
        rw [← toFullBlockVec_blockMatVecMul, dotProduct_toFullBlockVec]
      have hDx : (toFullBlockMat D *ᵥ toFullBlockVec x) ⬝ᵥ
            (toFullBlockMat D *ᵥ toFullBlockVec x)
          = blockVecDot (blockMatVecMul D x) (blockMatVecMul D x) := by
        rw [← toFullBlockVec_blockMatVecMul, dotProduct_toFullBlockVec]
      rw [hB, hx, hDx] at hcmp
      exact hcmp
  · rw [blockMatVecMul_blockSqrt_respM0_eq_zero
      (explicitCanonicalMetric_eq_zero_of_not_isUnit hu)]
    simpa [blockVecDot, vecDot] using hRHS

omit [NeZero d] in
/-- The normalized finite-cell root-mean-square form of
the pointwise estimate; same proof, with `hm`/`hM0` discharged instead of assumed. -/
theorem reflected_defect_avsum_le {iota : Type*} (Z : Finset iota)
    (Dfam : iota → BlockMat d) {F E : BlockMat d}
    (hE : (toFullBlockMat E).PosDef) (x : BlockVec d) :
    Real.sqrt ((Z.card : ℝ)⁻¹ *
        ∑ w ∈ Z,
          blockVecDot
            (blockMatVecMul (blockSqrt (respM0 F))
              (blockMatVecMul (blockSwap d) (blockMatVecMul (Dfam w) x)))
            (blockMatVecMul (blockSqrt (respM0 F))
              (blockMatVecMul (blockSwap d) (blockMatVecMul (Dfam w) x))))
      ≤ Real.sqrt ‖toFullBlockMat (normalizedBlock E (respM0 F))‖ *
          Real.sqrt (blockVecDot x (blockMatVecMul E x)) *
          Real.sqrt ((Z.card : ℝ)⁻¹ *
            ∑ w ∈ Z, ‖toFullBlockMat (normalizedBlock (Dfam w) E)‖ ^ 2) := by
  classical
  set K : ℝ := ‖toFullBlockMat (normalizedBlock E (respM0 F))‖ with hKdef
  set L : ℝ := blockVecDot x (blockMatVecMul E x) with hLdef
  set c : iota → ℝ := fun w => ‖toFullBlockMat (normalizedBlock (Dfam w) E)‖ with hcdef
  have hK0 : 0 ≤ K := norm_nonneg _
  have hL0 : 0 ≤ L := by
    have h := hE.posSemidef.dotProduct_mulVec_nonneg (toFullBlockVec x)
    simp only [star_trivial, ← toFullBlockVec_blockMatVecMul,
      dotProduct_toFullBlockVec] at h
    rw [hLdef]
    exact h
  have hcard : (0 : ℝ) ≤ (Z.card : ℝ)⁻¹ := by positivity
  have hS0 : 0 ≤ (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, c w ^ 2 :=
    mul_nonneg hcard (Finset.sum_nonneg fun w _ => sq_nonneg (c w))
  have hsum : ∑ w ∈ Z,
      blockVecDot
        (blockMatVecMul (blockSqrt (respM0 F))
          (blockMatVecMul (blockSwap d) (blockMatVecMul (Dfam w) x)))
        (blockMatVecMul (blockSqrt (respM0 F))
          (blockMatVecMul (blockSwap d) (blockMatVecMul (Dfam w) x)))
      ≤ ∑ w ∈ Z, K * c w ^ 2 * L :=
    Finset.sum_le_sum fun w _ => reflected_defect_metric_le_unconditional hE x
  have hpull : ∑ w ∈ Z, K * c w ^ 2 * L = (K * L) * ∑ w ∈ Z, c w ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun w _ => by ring
  have hmain : (Z.card : ℝ)⁻¹ *
      ∑ w ∈ Z,
        blockVecDot
          (blockMatVecMul (blockSqrt (respM0 F))
            (blockMatVecMul (blockSwap d) (blockMatVecMul (Dfam w) x)))
          (blockMatVecMul (blockSqrt (respM0 F))
            (blockMatVecMul (blockSwap d) (blockMatVecMul (Dfam w) x)))
      ≤ K * L * ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, c w ^ 2) := by
    calc (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, _ ≤ (Z.card : ℝ)⁻¹ * ∑ w ∈ Z, K * c w ^ 2 * L :=
          mul_le_mul_of_nonneg_left hsum hcard
      _ = K * L * ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, c w ^ 2) := by rw [hpull]; ring
  calc Real.sqrt ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, _)
      ≤ Real.sqrt (K * L * ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, c w ^ 2)) := Real.sqrt_le_sqrt hmain
    _ = Real.sqrt K * Real.sqrt L *
          Real.sqrt ((Z.card : ℝ)⁻¹ * ∑ w ∈ Z, c w ^ 2) := by
        rw [Real.sqrt_mul (mul_nonneg hK0 hL0), Real.sqrt_mul hK0]

omit [NeZero d] in
/-- `weakCellDefect` form of the normalized finite-cell root-mean-square estimate. -/
theorem weakCellDefect_avsum_le (q : Mat d) (t : ℤ) (n : ℕ) (b : CoeffField d)
    {F E : BlockMat d}
    (hE : (toFullBlockMat E).PosDef) (x : BlockVec d) :
    Real.sqrt (((triadicIndexBox d n).card : ℝ)⁻¹ *
        ∑ w ∈ triadicIndexBox d n,
          blockVecDot
            (blockMatVecMul (blockSqrt (respM0 F))
              (blockMatVecMul (blockSwap d)
                (blockMatVecMul
                  (blockSub (coarseBlockMatrix (adaptedCellAtCenter q (t - (n : ℤ)) w) b)
                    (coarseBlockMatrix (HighContrast.adaptedCell q t) b)) x)))
            (blockMatVecMul (blockSqrt (respM0 F))
              (blockMatVecMul (blockSwap d)
                (blockMatVecMul
                  (blockSub (coarseBlockMatrix (adaptedCellAtCenter q (t - (n : ℤ)) w) b)
                    (coarseBlockMatrix (HighContrast.adaptedCell q t) b)) x))))
      ≤ Real.sqrt ‖toFullBlockMat (normalizedBlock E (respM0 F))‖ *
          Real.sqrt (blockVecDot x (blockMatVecMul E x)) *
          weakCellDefect q t n E b :=
  reflected_defect_avsum_le (triadicIndexBox d n)
    (fun w => blockSub (coarseBlockMatrix (adaptedCellAtCenter q (t - (n : ℤ)) w) b)
      (coarseBlockMatrix (HighContrast.adaptedCell q t) b)) hE x

omit [NeZero d] in
/-! ## THE `weakCellSum` HALF OF THE RECENT HEAD.
With the identity `cellAverage_optimizerField_respCoeffMinus_sub_eq`
(`DiagonalDefectCarriers.lean`) available, the
child-cell mean defect is EXACTLY the reflected coarse-block defect action that
the pointwise estimates bound, at the response load `x^- = (-p, q^-)` (`ResponseBlockObjects.lean`).
The associated estimates are `diagonalWeak_recent_cell_bound`
(`DiagonalWeakNormRecentCell.lean`) and the first summand of
`diagonalWeak_recent_scale_decomposition_le` (`DiagonalWeakNormRecentDecomposition.lean`). -/

/-- The `weakCellSum` half, at one depth.  The normalized finite-cell root-mean-square
of the depth-`n` CHILD-OPTIMIZER mean defects, measured in `M_0`, is bounded by
`sqrt K_0 * L^- * weakCellDefect q t n Ehat a_-`, with constant `1` against the printed `16`. -/
theorem childMean_defect_avsum_le
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (t : ℤ) (e : Vec d)
    (hgrid : IsUnit (respGrid jStar F)) (a : CoeffSpace d) (n : ℕ)
    (u : AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hu : IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a) u)
    (V : (w : Fin d → ℤ) →
      ScalarCanonicalMaximizer (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
        (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (respCoeffMinus F a))
    (hE : (toFullBlockMat (respEhatMinus P jStar F t)).PosDef) :
    Real.sqrt (((triadicIndexBox d n).card : ℝ)⁻¹ *
        ∑ w ∈ triadicIndexBox d n,
          blockVecDot
            (blockMatVecMul (blockSqrt (respM0 F))
              (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                  (optimizerField (respCoeffMinus F a)
                    ((V w).toAHarmonicFunctionMeanZero.toAHarmonicFunction)) -
                cellAverage (respCell jStar F t) (optimizerField (respCoeffMinus F a) u)))
            (blockMatVecMul (blockSqrt (respM0 F))
              (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                  (optimizerField (respCoeffMinus F a)
                    ((V w).toAHarmonicFunctionMeanZero.toAHarmonicFunction)) -
                cellAverage (respCell jStar F t) (optimizerField (respCoeffMinus F a) u))))
      ≤ Real.sqrt ‖toFullBlockMat (normalizedBlock (respEhatMinus P jStar F t) (respM0 F))‖ *
          Real.sqrt (respLsqMinus P jStar F t e) *
          weakCellDefect (respGrid jStar F) t n (respEhatMinus P jStar F t)
            (respCoeffMinus F a) := by
  have hstep : ∀ w ∈ triadicIndexBox d n,
      blockVecDot
          (blockMatVecMul (blockSqrt (respM0 F))
            (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                (optimizerField (respCoeffMinus F a)
                  ((V w).toAHarmonicFunctionMeanZero.toAHarmonicFunction)) -
              cellAverage (respCell jStar F t) (optimizerField (respCoeffMinus F a) u)))
          (blockMatVecMul (blockSqrt (respM0 F))
            (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                (optimizerField (respCoeffMinus F a)
                  ((V w).toAHarmonicFunctionMeanZero.toAHarmonicFunction)) -
              cellAverage (respCell jStar F t) (optimizerField (respCoeffMinus F a) u)))
        = blockVecDot
            (blockMatVecMul (blockSqrt (respM0 F))
              (blockMatVecMul (blockSwap d)
                (blockMatVecMul
                  (blockSub
                    (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                      (respCoeffMinus F a))
                    (coarseBlockMatrix (HighContrast.adaptedCell (respGrid jStar F) t)
                      (respCoeffMinus F a)))
                  (respxMinus P jStar F t e))))
            (blockMatVecMul (blockSqrt (respM0 F))
              (blockMatVecMul (blockSwap d)
                (blockMatVecMul
                  (blockSub
                    (coarseBlockMatrix (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                      (respCoeffMinus F a))
                    (coarseBlockMatrix (HighContrast.adaptedCell (respGrid jStar F) t)
                      (respCoeffMinus F a)))
                  (respxMinus P jStar F t e)))) := by
    intro w _
    simp only [respCell]
    rw [cellAverage_optimizerField_respCoeffMinus_sub_eq (respGrid jStar F) hgrid t
      (t - (n : ℤ)) w F a (respP (respMean P jStar F t) e) (respqMinus P jStar F t e)
      ((V w).toAHarmonicFunctionMeanZero.toAHarmonicFunction) (V w).isMaximizer u hu]
    rfl
  rw [Finset.sum_congr rfl hstep]
  exact weakCellDefect_avsum_le (respGrid jStar F) t n (respCoeffMinus F a) hE
    (respxMinus P jStar F t e)

/-- THE `weakCellSum` HALF OF THE RECENT HEAD, all depths.  Choosing the child
maximizers simultaneously and summing the one-depth estimate against the printed `3^{-n/2}`
weights over the window `n <= H` produces EXACTLY `weakCellSum`, with constant `1` against the
printed `16`.  The first summand of `diagonalWeak_recent_scale_decomposition_le`
(`DiagonalWeakNormRecentDecomposition.lean`) is the corresponding estimate. -/
theorem weakCellSum_half_le
    (P : Measure (CoeffSpace d)) (jStar : ℕ) (F : BlockMat d) (t : ℤ) (e : Vec d)
    (hgrid : IsUnit (respGrid jStar F)) (a : CoeffSpace d) (H : ℕ)
    (u : AHarmonicFunction (respCoeffMinus F a) (respCell jStar F t))
    (hu : IsResponseMaximizer (respCell jStar F t) (respP (respMean P jStar F t) e)
      (respqMinus P jStar F t e) (respCoeffMinus F a) u)
    (hE : (toFullBlockMat (respEhatMinus P jStar F t)).PosDef) :
    ∃ V : (n : ℕ) → (w : Fin d → ℤ) →
        ScalarCanonicalMaximizer (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
          (respP (respMean P jStar F t) e) (respqMinus P jStar F t e) (respCoeffMinus F a),
      ∑ n ∈ Finset.range (H + 1),
          (3 : ℝ) ^ (-((n : ℝ) / 2)) *
            Real.sqrt (((triadicIndexBox d n).card : ℝ)⁻¹ *
              ∑ w ∈ triadicIndexBox d n,
                blockVecDot
                  (blockMatVecMul (blockSqrt (respM0 F))
                    (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                        (optimizerField (respCoeffMinus F a)
                          ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction)) -
                      cellAverage (respCell jStar F t) (optimizerField (respCoeffMinus F a) u)))
                  (blockMatVecMul (blockSqrt (respM0 F))
                    (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                        (optimizerField (respCoeffMinus F a)
                          ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction)) -
                      cellAverage (respCell jStar F t)
                        (optimizerField (respCoeffMinus F a) u))))
        ≤ Real.sqrt ‖toFullBlockMat (normalizedBlock (respEhatMinus P jStar F t) (respM0 F))‖ *
            Real.sqrt (respLsqMinus P jStar F t e) *
            weakCellSum (respGrid jStar F) t H (respEhatMinus P jStar F t)
              (respCoeffMinus F a) := by
  obtain ⟨V⟩ := nonempty_childMaximizerFamily (respGrid jStar F) hgrid t F a
    (respP (respMean P jStar F t) e) (respqMinus P jStar F t e)
  refine ⟨V, ?_⟩
  set K : ℝ :=
    Real.sqrt ‖toFullBlockMat (normalizedBlock (respEhatMinus P jStar F t) (respM0 F))‖ with hK
  set L : ℝ := Real.sqrt (respLsqMinus P jStar F t e) with hL
  have hterm : ∀ n ∈ Finset.range (H + 1),
      (3 : ℝ) ^ (-((n : ℝ) / 2)) *
          Real.sqrt (((triadicIndexBox d n).card : ℝ)⁻¹ *
            ∑ w ∈ triadicIndexBox d n,
              blockVecDot
                (blockMatVecMul (blockSqrt (respM0 F))
                  (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                      (optimizerField (respCoeffMinus F a)
                        ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction)) -
                    cellAverage (respCell jStar F t) (optimizerField (respCoeffMinus F a) u)))
                (blockMatVecMul (blockSqrt (respM0 F))
                  (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) w)
                      (optimizerField (respCoeffMinus F a)
                        ((V n w).toAHarmonicFunctionMeanZero.toAHarmonicFunction)) -
                    cellAverage (respCell jStar F t) (optimizerField (respCoeffMinus F a) u))))
        ≤ K * L *
            ((3 : ℝ) ^ (-((n : ℝ) / 2)) *
              weakCellDefect (respGrid jStar F) t n (respEhatMinus P jStar F t)
                (respCoeffMinus F a)) := by
    intro n _
    have hw : (0 : ℝ) ≤ (3 : ℝ) ^ (-((n : ℝ) / 2)) := Real.rpow_nonneg (by norm_num) _
    have hcell := childMean_defect_avsum_le P jStar F t e hgrid a n u hu (V n) hE
    calc (3 : ℝ) ^ (-((n : ℝ) / 2)) * _
        ≤ (3 : ℝ) ^ (-((n : ℝ) / 2)) *
            (K * L *
              weakCellDefect (respGrid jStar F) t n (respEhatMinus P jStar F t)
                (respCoeffMinus F a)) := by
          exact mul_le_mul_of_nonneg_left hcell hw
      _ = K * L *
            ((3 : ℝ) ^ (-((n : ℝ) / 2)) *
              weakCellDefect (respGrid jStar F) t n (respEhatMinus P jStar F t)
                (respCoeffMinus F a)) := by ring
  refine (Finset.sum_le_sum hterm).trans_eq ?_
  rw [weakCellSum, Finset.mul_sum]
end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The `weakAverageSum` half of the diagonal weak-norm bound and the nondegeneracy discharge

## The nondegeneracy discharge

In the branch where `respEhatMinus P jStar F t` is singular, the diagonal weak-norm statement
(`DiagonalWeakNormBound.lean`) is equivalent to its left-hand side being exactly `0`.
That branch is never proved: every `diagonalWeak*` lemma excludes it, by the pair
of binders `(hE : IsSymmetricBlockMat E) (hEpd : BlockPosDef E)`
(`DiagonalWeakNormPrimal.lean`), and the
only junk branch anywhere near this material — `canonFactor_exists`
(`Canonical.lean`) — carries the docstring
"the junk value on non-positive data is never used".  So the missing case is a DROPPED
HYPOTHESIS, not a missing proof.

The results below show that the dropped hypothesis is FREE at the consumers: the route's own
`RespCalibrated Cc P jStar F s t` (`CenteredEnergyIdentity.lean`) already contains
`C⁻¹ M_0 ≤ Ehat_t^±` in the Loewner order, and `RawOutput.symm`/`RawOutput.pos`
(`ResponseBlockObjects.lean`) already give `(explicitCanonicalMetric F).PosDef`, hence
`(toFullBlockMat (respM0 F)).PosDef` (`LoadMeanIdentity.lean`).  Both binders are in scope at
`respWeakEnergyOf_minus_le` (`WeakEstimateAssembly.lean`) and at
`response_weak_estimate_of_route` (`WeakEstimateAssembly.lean`) already, so no statement text
changes.  The satisfiability statement is in `∃` form.

## The `weakAverageSum` half

For the second printed summand, the estimate
`diagonalWeak_recent_average_good_le` (`DiagonalWeakNormRecentBound.lean`) feeds into
`normalized_diagonalWeak_recent_head_le` (`DiagonalWeakNormRecentHead.lean`).  Its
per-scale analytic input — the energy map `metricBlockNormSq_recent_difference_le`
(`DiagonalWeakNormRecentEnergyMap.lean`) composed with the difference-energy bound
`diagonalWeak_recent_difference_energy_le` (`DiagonalWeakNormRecentQuadratic.lean`) — has
no counterpart in this tree yet and is left as the explicit hypothesis `hscale` of
`weakAverageSum_half_le`.
Everything between that input and `weakAverageSum` is proved here:
the good-branch coefficient arithmetic `√2 (1 + √M·R) ≤ 4R` (`avCoeff_le`, cf.
`DiagonalWeakNormRecentBound.lean`), the weight identity `W · R = 3^{-(1/2-ρ/2)n}`
(`recentWeight_mul`, cf. `DiagonalWeakNormRecentHead.lean`), and the window
summation into `weakAverageSum` (`weakAverageSum_window_le`, cf.
`DiagonalWeakNormRecentHead.lean`).

CARRIER MAP (the section docstring of `DiagonalWeakNormBound.lean` is authoritative):
the source estimates use `E ↦ respEhatMinus P jStar F t`, `m ↦ respM0 F`,
`q ↦ respGrid jStar F`, `s = 1/2`, `rho = Quenched.contrastRho γ`, `delta = 1`, `k = t - n`.  The
source carriers are `ℝ≥0∞` with an
`if diagonalWeakMaximum … = ⊤ then ⊤ else …` guard; here everything is plain `ℝ`, so the guard
vanishes and the `hfinite : diagonalWeakMaximum … ≠ ⊤` binder has no counterpart at all —
`respAllScaleMax` is real-valued by construction (`ResponseBlockObjects.lean`).  The inner
size `blockSize D (blockIdentity d)` of the source carriers is this tree's
`‖toFullBlockMat D‖`
(`DiagonalDefectCarriers.lean`), which is why
`blockSize_diagonalWeakAverageDefect_nonneg`
(`DiagonalWeakNormComparison.lean`) — one of the five leaf consumers of `hEpd` — is here
just `norm_nonneg` and needs nothing.
-/

open HCPolySupport.HighContrast (CoeffSpace)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ## The dropped hypothesis and its discharge at the consumers. -/

/-! ## The `weakAverageSum` half, assembled.

The analytic input feeding this assembly is
`diagonalWeak_recent_average_bound`
(`DiagonalWeakNormRecentBound.lean`), whose own inputs are the
energy map `metricBlockNormSq_recent_difference_le`
(`…/DiagonalWeakNormRecentEnergyMap.lean`) and the difference-energy bound
`diagonalWeak_recent_difference_energy_le` (`…/DiagonalWeakNormRecentQuadratic.lean`).
Neither has a counterpart in this tree; both appear here as the hypothesis `hscale` of
`weakAverageSum_half_le`. -/

/-- `rho = Quenched.contrastRho γ = (1+γ)/2` is positive on `γ ∈ Set.Ico 0 1`; this is
the side condition `hrho : 0 < rho` (`…/DiagonalWeakNormPrimal.lean`), discharged here
rather than assumed, exactly as the section docstring of `DiagonalWeakNormBound.lean` records. -/
theorem respRho_pos {γ : ℝ} (hγ : γ ∈ Set.Ico (0 : ℝ) 1) : 0 < Quenched.contrastRho γ := by
  obtain ⟨hγ0, _⟩ := hγ
  rw [Quenched.contrastRho]
  linarith only [hγ0]

/-- The geometric weight `R = 3^{rho(t-k)/2}` at `k = t - n` is `3^{rho n / 2} ≥ 1`,
the condition `hR1` of `diagonalWeak_recent_average_good_le`
(`…/DiagonalWeakNormRecentBound.lean`). -/
theorem one_le_recentWeight {rho : ℝ} (hrho : 0 ≤ rho) (n : ℕ) :
    (1 : ℝ) ≤ (3 : ℝ) ^ (rho * (n : ℝ) / 2) := by
  have hexp : (0 : ℝ) ≤ rho * (n : ℝ) / 2 :=
    div_nonneg (mul_nonneg hrho (Nat.cast_nonneg n)) (by norm_num)
  simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hexp

/-- The good-branch coefficient: `√2 (1 + √M R) ≤ 4 R` whenever `M ≤ 1` and `1 ≤ R`.
This is the content of the good branch for the averaged term, the condition `hcoeff` of
`diagonalWeak_recent_average_good_le` (`…/DiagonalWeakNormRecentBound.lean`), at
`delta = 1` so that `hgood : M ≤ delta` and `hdelta1 : delta ≤ 1` collapse into `M ≤ 1`. -/
theorem avCoeff_le {M R : ℝ} (hM1 : M ≤ 1) (hR1 : (1 : ℝ) ≤ R) :
    Real.sqrt 2 * (1 + Real.sqrt M * R) ≤ 4 * R := by
  have hR0 : (0 : ℝ) ≤ R := le_trans zero_le_one hR1
  have hrootM : Real.sqrt M ≤ 1 := by
    simpa using Real.sqrt_le_sqrt hM1
  have hmR : Real.sqrt M * R ≤ R := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hrootM hR0
  have hB0 : (0 : ℝ) ≤ 1 + Real.sqrt M * R :=
    add_nonneg zero_le_one (mul_nonneg (Real.sqrt_nonneg _) hR0)
  have hB : 1 + Real.sqrt M * R ≤ 2 * R := by linarith only [hmR, hR1]
  have hroot2 : Real.sqrt 2 ≤ 2 := by
    rw [Real.sqrt_le_iff]
    constructor <;> norm_num
  calc
    Real.sqrt 2 * (1 + Real.sqrt M * R) ≤ 2 * (1 + Real.sqrt M * R) :=
      mul_le_mul_of_nonneg_right hroot2 hB0
    _ ≤ 2 * (2 * R) := mul_le_mul_of_nonneg_left hB (by norm_num)
    _ = 4 * R := by ring

/-- The weight identity: `W · R = 3^{-(s - rho/2) n}` at `s = 1/2`, which is the
`weakAverageSum` weight of `DiagonalDefectCarriers.lean`, the condition `hpow` of
`normalized_diagonalWeak_recent_head_le` (`…/DiagonalWeakNormRecentHead.lean`). -/
theorem recentWeight_mul (rho : ℝ) (n : ℕ) :
    (3 : ℝ) ^ (-((n : ℝ) / 2)) * (3 : ℝ) ^ (rho * (n : ℝ) / 2) =
      (3 : ℝ) ^ (-((1 / 2 : ℝ) - rho / 2) * (n : ℝ)) := by
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  congr 1
  ring

omit [NeZero d] in
/-- The window summation: a per-scale bound against the printed `weakAverageSum` weight
sums over the window `n ≤ H` to exactly `K L · weakAverageSum`, the condition `hsum` of
`normalized_diagonalWeak_recent_head_le` (`…/DiagonalWeakNormRecentHead.lean`), whose
`diagonalWeakAverageSum_eq` unfolding is here the `def` itself. -/
theorem weakAverageSum_window_le (q : Mat d) (t : ℤ) (H : ℕ) (rho : ℝ) (E : BlockMat d)
    (b : CoeffField d) {K L : ℝ} (A : ℕ → ℝ)
    (hterm : ∀ n ∈ Finset.range (H + 1), A n ≤
      K * L * ((3 : ℝ) ^ (-((1 / 2 : ℝ) - rho / 2) * (n : ℝ)) *
        Real.sqrt ‖toFullBlockMat (weakAverageDefect q t n E b)‖)) :
    ∑ n ∈ Finset.range (H + 1), A n ≤ K * L * weakAverageSum q t H rho E b := by
  refine (Finset.sum_le_sum hterm).trans_eq ?_
  rw [weakAverageSum, Finset.mul_sum]

omit [NeZero d] in
/-- The `weakAverageSum` half: `diagonalWeak_recent_average_good_le`
(`…/DiagonalWeakNormRecentBound.lean`) composed with the averaged branch of
`normalized_diagonalWeak_recent_head_le` (`…/DiagonalWeakNormRecentHead.lean`), on these
carriers at `s = 1/2`, `rho = Quenched.contrastRho γ`, `delta = 1`.

`hscale` is `diagonalWeak_recent_average_bound`
(`…/DiagonalWeakNormRecentBound.lean`) on these carriers; it is the only analytic input
and it has no counterpart here yet.  `hE` is the positive-definiteness condition on
`respEhatMinus P jStar F t`, discharged at the consumers.  Everything else — the good-branch
coefficient (`avCoeff_le`), the weight identity (`recentWeight_mul`), the window
summation (`weakAverageSum_window_le`) — is proved.

The `hfinite : diagonalWeakMaximum … ≠ ⊤` binder has no counterpart: `respAllScaleMax` is
real-valued (`ResponseBlockObjects.lean`), so the `⊤` guard vanishes with it. -/
theorem weakAverageSum_half_le (P : Measure (CoeffSpace d)) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) (jStar H : ℕ) (F : BlockMat d) (t : ℤ) (a : CoeffSpace d)
    {K L : ℝ} (hK0 : 0 ≤ K) (hL0 : 0 ≤ L) (A : ℕ → ℝ)
    (_hE : (toFullBlockMat (respEhatMinus P jStar F t)).PosDef)
    (hgood : respAllScaleMax P γ jStar F t a ≤ 1)
    (hscale : ∀ n : ℕ, A n ≤
      Real.sqrt 2 * K *
        (1 + Real.sqrt (respAllScaleMax P γ jStar F t a) *
          (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ) / 2)) * L *
        Real.sqrt ‖toFullBlockMat (weakAverageDefect (respGrid jStar F) t n
          (respEhatMinus P jStar F t) (respCoeffMinus F a))‖) :
    ∑ n ∈ Finset.range (H + 1), (3 : ℝ) ^ (-((n : ℝ) / 2)) * A n ≤
      4 * K * L *
        weakAverageSum (respGrid jStar F) t H (Quenched.contrastRho γ) (respEhatMinus P jStar F t)
          (respCoeffMinus F a) := by
  have hrho0 : 0 ≤ Quenched.contrastRho γ := (respRho_pos hγ).le
  refine weakAverageSum_window_le (K := 4 * K) (L := L) _ t H (Quenched.contrastRho γ) _ _
    (fun n => (3 : ℝ) ^ (-((n : ℝ) / 2)) * A n) ?_
  intro n _
  set M : ℝ := respAllScaleMax P γ jStar F t a with hM
  set R : ℝ := (3 : ℝ) ^ (Quenched.contrastRho γ * (n : ℝ) / 2) with hR
  set W : ℝ := (3 : ℝ) ^ (-((n : ℝ) / 2)) with hW
  set D : ℝ := Real.sqrt ‖toFullBlockMat (weakAverageDefect (respGrid jStar F) t n
    (respEhatMinus P jStar F t) (respCoeffMinus F a))‖ with hD
  have hR1 : (1 : ℝ) ≤ R := one_le_recentWeight hrho0 n
  have hW0 : (0 : ℝ) ≤ W := Real.rpow_nonneg (by norm_num) _
  have hD0 : (0 : ℝ) ≤ D := Real.sqrt_nonneg _
  have hrest0 : (0 : ℝ) ≤ K * L * D := mul_nonneg (mul_nonneg hK0 hL0) hD0
  have hcoeff : Real.sqrt 2 * (1 + Real.sqrt M * R) ≤ 4 * R := avCoeff_le hgood hR1
  have hstep : A n ≤ (4 * R) * (K * L * D) := by
    refine (hscale n).trans ?_
    calc
      Real.sqrt 2 * K * (1 + Real.sqrt M * R) * L * D
          = (Real.sqrt 2 * (1 + Real.sqrt M * R)) * (K * L * D) := by ring
      _ ≤ (4 * R) * (K * L * D) := mul_le_mul_of_nonneg_right hcoeff hrest0
  calc
    W * A n ≤ W * ((4 * R) * (K * L * D)) := mul_le_mul_of_nonneg_left hstep hW0
    _ = 4 * K * L * ((W * R) * D) := by ring
    _ = 4 * K * L * ((3 : ℝ) ^ (-((1 / 2 : ℝ) - Quenched.contrastRho γ / 2) * (n : ℝ)) * D) := by
        rw [hW, hR, recentWeight_mul]

/-! ## The all-scale-maximum bricks, stated carrier-free.

These are the three arithmetic steps that turn the all-scale maximum into the
per-cell response size `B = 1 + √M · 3^{rho n/2}` used by `hsize` of
`diagonalWeak_recent_average_bound`
(`DiagonalWeakNormRecentBound.lean`).  They are stated here on
bare reals, so they carry no `E`-nondegeneracy at all and are reusable for any carrier choice.
The step that is NOT carrier-free — `‖N‖ ≤ 1 + blockSpecBound (N - I)` for
positive semidefinite `N`, the estimate `blockSize_le_one_add_blockExcess`
(`…/DiagonalWeakNormMaximum.lean`) — is NOT here: it needs `blockSpecBound`
subadditivity, which exists in this tree only as the `private` `blockSpecBound_le_add`
(`WeakEstimateAssembly.lean`), DOWNSTREAM of this file. -/

omit [NeZero d] in
/-- Removing the maximum's weight costs the reciprocal geometric factor, the estimate
`blockExcess_le_mul_rpow_of_weighted_le` (`…/DiagonalWeakNormMaximum.lean`), at
`k = t - n` so that `t - k` is `n`. -/
theorem le_mul_rpow_of_weighted_le {rho B x : ℝ} (n : ℕ)
    (hweighted : (3 : ℝ) ^ (-(rho * (n : ℝ))) * x ≤ B) :
    x ≤ B * (3 : ℝ) ^ (rho * (n : ℝ)) := by
  have hfac0 : (0 : ℝ) ≤ (3 : ℝ) ^ (rho * (n : ℝ)) := Real.rpow_nonneg (by norm_num) _
  have hcancel : (3 : ℝ) ^ (rho * (n : ℝ)) * (3 : ℝ) ^ (-(rho * (n : ℝ))) = 1 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3), add_neg_cancel, Real.rpow_zero]
  calc
    x = (3 : ℝ) ^ (rho * (n : ℝ)) * ((3 : ℝ) ^ (-(rho * (n : ℝ))) * x) := by
      rw [← mul_assoc, hcancel, one_mul]
    _ ≤ (3 : ℝ) ^ (rho * (n : ℝ)) * B := mul_le_mul_of_nonneg_left hweighted hfac0
    _ = B * (3 : ℝ) ^ (rho * (n : ℝ)) := mul_comm _ _

omit [NeZero d] in
/-- The square root inherits half the maximum's geometric weight, producing exactly the
`√M · 3^{rho n/2}` of `B`, the estimate
`sqrt_blockExcess_le_sqrt_mul_rpow_of_weighted_le` (`…/DiagonalWeakNormMaximum.lean`).
Composed with `le_mul_rpow_of_weighted_le` this is
`sqrt_blockSize_adaptedResponse_le_of_maximum_finite`
(`…/DiagonalWeakNormMaximum.lean`) up to the one non-carrier-free step named in the
section note above. -/
theorem sqrt_le_sqrt_mul_rpow_of_weighted_le {rho B x : ℝ} (n : ℕ) (hB : 0 ≤ B)
    (hweighted : (3 : ℝ) ^ (-(rho * (n : ℝ))) * x ≤ B) :
    Real.sqrt x ≤ Real.sqrt B * (3 : ℝ) ^ (rho * (n : ℝ) / 2) := by
  have hrootB0 : (0 : ℝ) ≤ Real.sqrt B := Real.sqrt_nonneg B
  have hfac0 : (0 : ℝ) ≤ (3 : ℝ) ^ (rho * (n : ℝ) / 2) := Real.rpow_nonneg (by norm_num) _
  have hfacSq : ((3 : ℝ) ^ (rho * (n : ℝ) / 2)) ^ 2 = (3 : ℝ) ^ (rho * (n : ℝ)) := by
    rw [pow_two, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  rw [Real.sqrt_le_iff]
  refine ⟨mul_nonneg hrootB0 hfac0, ?_⟩
  calc
    x ≤ B * (3 : ℝ) ^ (rho * (n : ℝ)) := le_mul_rpow_of_weighted_le n hweighted
    _ = (Real.sqrt B * (3 : ℝ) ^ (rho * (n : ℝ) / 2)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hB, hfacSq]

end

end HCPolySupport.HighContrast.Multiscale
end
