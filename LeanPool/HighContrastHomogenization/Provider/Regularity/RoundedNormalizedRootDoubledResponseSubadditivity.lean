/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.NormalizedRootCoefficient
public import LeanPool.HighContrastHomogenization.Provider.Regularity.RoundedAffineMap
public import LeanPool.HighContrastHomogenization.Provider.Transport.WhitneyRows
public import LeanPool.HighContrastHomogenization.Provider.Window.CountableSubadditivity
public import LeanPool.HighContrastHomogenization.Provider.Transport.FillingSubadditivity
public import LeanPool.HighContrastHomogenization.Geometry.CoarseSchurBridge
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.HomogenizationError.ResponseBounds

/-!
# High-contrast homogenization:
Provider.Regularity.RoundedNormalizedRootDoubledResponseSubadditivity

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Doubled-response subadditivity over the normalized-root filling

The doubled response is the sum of the primal and reflected half-quadratic
forms, less the fixed pairing of the two loads.  On a countable almost-
everywhere partition, the weights sum to one, so the pairing cancels exactly.
This upgrades coarse-block subadditivity to the full response used by the
normalized reference certificate.
-/

namespace HCPolySupport
namespace HighContrast
namespace Transport

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The doubled response of a coefficient-space sample on a set, written in
the coarse-block splitting used by the source. -/
@[expose]
def coeffSpaceDoubledResponse (U : Set (Vec d)) (a : CoeffSpace d)
    (P Q : BlockVec d) : ℝ :=
  1 / 2 * blockVecDot P (blockMatVecMul (coarseBlock U a) P) +
    1 / 2 * blockVecDot Q (blockMatVecMul (coarseStarInv U a) Q) -
      blockVecDot P Q

/-- On a Chapter 2 domain, the coefficient-space splitting is exactly the
canonical doubled response. -/
theorem coeffSpaceDoubledResponse_eq_doubledResponseJ
    (U : Book.Ch02.Domain d) (a : CoeffSpace d) (P Q : BlockVec d) :
    coeffSpaceDoubledResponse (U : Set (Vec d)) a P Q =
      Book.Ch02.doubledResponseJ U (a.coeffOn U) P Q := by
  unfold coeffSpaceDoubledResponse
  rw [(Book.Ch02.blockCoarseMatrixTheory U (a.coeffOn U)).doubled_response_splitting,
    (Book.Ch02.blockCoarseMatrixTheory U (a.coeffOn U)).starred_inverse_formula,
    ← coarseBlock_eq_coarseBlockMatrix a U, coarseStarInv_eq_blockReflect]

/-- The coefficient-space doubled response is subadditive over a countable
almost-everywhere partition whenever the weighted cell responses are
summable.  Summability of the two nonnegative half-quadratic series is derived
from response summability and the summable partition weights. -/
theorem coeffSpaceDoubledResponse_le_tsum_weight_of_countable_aePartition
    [NeZero d] {ι : Type*} [Countable ι] {U : Set (Vec d)}
    {c : ι → Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (hU0 : volume U ≠ 0)
    (a : CoeffSpace d) (hc : ∀ i, IsOpenBoundedConvexDomain (c i))
    (hsub : ∀ i, c i ⊆ U)
    (hdisj : Pairwise fun i k : ι ↦ Disjoint (c i) (c k))
    (hnull : volume (U \ ⋃ i, c i) = 0)
    (hcell0 : ∀ i, volume (c i) ≠ 0) (P Q : BlockVec d)
    (hsum : Summable fun i ↦
      (volume (c i)).toReal / (volume U).toReal *
        coeffSpaceDoubledResponse (c i) a P Q) :
    coeffSpaceDoubledResponse U a P Q ≤
      ∑' i, (volume (c i)).toReal / (volume U).toReal *
        coeffSpaceDoubledResponse (c i) a P Q := by
  let weight : ι → ℝ := fun i ↦
    (volume (c i)).toReal / (volume U).toReal
  let primal : ι → ℝ := fun i ↦
    weight i *
      (1 / 2 * blockVecDot P (blockMatVecMul (coarseBlock (c i) a) P))
  let dual : ι → ℝ := fun i ↦
    weight i *
      (1 / 2 * blockVecDot Q (blockMatVecMul (coarseStarInv (c i) a) Q))
  have hUtop : volume U ≠ ⊤ := hU.volume_lt_top.ne
  have hweights : ∑' i, weight i = 1 := by
    exact Window.tsum_weight_eq_one_of_countable_aePartition
      (fun i ↦ (hc i).isOpen.measurableSet) hsub hdisj hnull hU0 hUtop
  have hweightSummable : Summable weight := by
    by_contra hnot
    have hzero := tsum_eq_zero_of_not_summable hnot
    rw [hweights] at hzero
    norm_num at hzero
  have hpairSummable : Summable fun i ↦ weight i * blockVecDot P Q :=
    hweightSummable.mul_right _
  have hsum' : Summable fun i ↦
      weight i * coeffSpaceDoubledResponse (c i) a P Q := by
    simpa only [weight] using hsum
  have hboth : Summable fun i ↦ primal i + dual i := by
    have h := hsum'.add hpairSummable
    exact h.congr fun i ↦ by
      dsimp only [primal, dual]
      unfold coeffSpaceDoubledResponse
      ring
  have hweight0 : ∀ i, 0 ≤ weight i := fun i ↦
    div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have hprimal0 : ∀ i, 0 ≤ primal i := by
    intro i
    exact mul_nonneg (hweight0 i)
      (zero_le_blockQuadratic_coarseBlock (hc i) (hcell0 i) a P)
  have hdual0 : ∀ i, 0 ≤ dual i := by
    intro i
    have hquad : 0 ≤ 1 / 2 * blockVecDot Q
        (blockMatVecMul (coarseStarInv (c i) a) Q) := by
      simpa only [coarseStarInv_eq_blockReflect,
        blockVecDot_blockMatVecMul_blockReflect] using
        zero_le_blockQuadratic_coarseBlock (hc i) (hcell0 i) a
          ((Q.2, Q.1) : BlockVec d)
    exact mul_nonneg (hweight0 i) hquad
  have hprimalSummable : Summable primal :=
    Summable.of_nonneg_of_le hprimal0
      (fun i ↦ le_add_of_nonneg_right (hdual0 i)) hboth
  have hdualSummable : Summable dual :=
    Summable.of_nonneg_of_le hdual0
      (fun i ↦ le_add_of_nonneg_left (hprimal0 i)) hboth
  have hprimal := Window.blockQuadratic_le_tsum_weight_of_countable_aePartition
    hU hU0 a hc hsub hdisj hnull hcell0 P (by
      simpa only [primal, weight] using hprimalSummable)
  have hdualSwapSummable : Summable fun i ↦
      weight i *
        (1 / 2 * blockVecDot ((Q.2, Q.1) : BlockVec d)
          (blockMatVecMul (coarseBlock (c i) a)
            ((Q.2, Q.1) : BlockVec d))) := by
    simpa only [dual, coarseStarInv_eq_blockReflect,
      blockVecDot_blockMatVecMul_blockReflect] using hdualSummable
  have hdualSwap := Window.blockQuadratic_le_tsum_weight_of_countable_aePartition
    hU hU0 a hc hsub hdisj hnull hcell0 ((Q.2, Q.1) : BlockVec d) (by
      simpa only [weight] using hdualSwapSummable)
  have hdual :
      1 / 2 * blockVecDot Q (blockMatVecMul (coarseStarInv U a) Q) ≤
        ∑' i, dual i := by
    simpa only [dual, weight, coarseStarInv_eq_blockReflect,
      blockVecDot_blockMatVecMul_blockReflect] using hdualSwap
  have hseries :
      (∑' i, weight i * coeffSpaceDoubledResponse (c i) a P Q) =
        (∑' i, primal i) + (∑' i, dual i) - blockVecDot P Q := by
    have hterm : (fun i ↦
        weight i * coeffSpaceDoubledResponse (c i) a P Q) =
        fun i ↦ primal i + dual i - weight i * blockVecDot P Q := by
      funext i
      dsimp only [primal, dual]
      unfold coeffSpaceDoubledResponse
      ring
    rw [hterm, Summable.tsum_sub hboth hpairSummable,
      Summable.tsum_add hprimalSummable hdualSummable, tsum_mul_right,
      hweights, one_mul]
  change coeffSpaceDoubledResponse U a P Q ≤
    ∑' i, weight i * coeffSpaceDoubledResponse (c i) a P Q
  rw [hseries]
  unfold coeffSpaceDoubledResponse
  exact sub_le_sub_right (add_le_add hprimal hdual) _

end

end Transport
end HighContrast
end HCPolySupport
