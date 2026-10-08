/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.UnitRangeGridCount
public import LeanPool.HighContrastHomogenization.Provider.Quenched.UnitRangeCoarseBlockConcentration
public import LeanPool.HighContrastHomogenization.Provider.Transport.CellDomination
public import LeanPool.HighContrastHomogenization.Provider.Quenched.AnnealedLimitBlock

/-!
# High-contrast homogenization: Provider.Quenched.UnitRangeBlockReassembly

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# From entrywise deviations to the Loewner order

The concentration estimate produced by unit range is a statement about scalar
observables; the renormalization of ellipticity consumes a statement in the
Loewner order of doubled blocks.  This file performs the passage between them,
in the two directions the argument needs.

Downwards, a coarse-ellipticity datum bounds the entries of a coarse block on the
event that the source has burnt in, which is what makes the cutoff of the
truncation argument inactive there: the truncated readout is then the readout
itself, so no truncation error is incurred on the event where the estimate is
used.

Upwards, entrywise bounds on a doubled block give a Loewner bound against any
reference block dominating the identity, at the cost of the factor `2d` — the
number of coordinates of a doubled block.  Combining that with the concentration
estimate, applied once to each of the `4d²` entries and collected by a union
bound, gives the block-level deviation estimate.
-/

namespace HCPolySupport
namespace HighContrast
namespace Quenched

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-! ## The cutoff is inactive on the source event -/

/-! ## Entrywise bounds give a Loewner bound -/

/-- The number of coordinates of a doubled block. -/
theorem card_blockCoord (d : ℕ) : (Finset.univ : Finset (BlockCoord d)).card = 2 * d := by
  simp [Finset.card_univ, Fintype.card_sum, two_mul]

/-- **Entrywise bounds give a Loewner bound.**  A doubled block whose entries are
bounded by `η` is dominated by `2dη` times any reference block that dominates the
identity form. -/
theorem blockMatLoewnerLE_blockScale_of_abs_blockMatEntry_le {H F : BlockMat d}
    {eta : ℝ} (heta : 0 ≤ eta)
    (hF : ∀ X : BlockVec d,
      ∑ α : BlockCoord d, toFullBlockVec X α * toFullBlockVec X α ≤
        blockVecDot X (blockMatVecMul F X))
    (hH : ∀ α β : BlockCoord d, |blockMatEntry H α β| ≤ eta) :
    BlockMatLoewnerLE H (blockScale (2 * (d : ℝ) * eta) F) := by
  intro X
  rw [blockVecDot_blockMatVecMul_blockScale, blockVecDot_blockMatVecMul_eq_sum]
  have habs : ∀ α β : BlockCoord d,
      toFullBlockVec X α * (blockMatEntry H α β * toFullBlockVec X β) ≤
        eta * (|toFullBlockVec X α| * |toFullBlockVec X β|) := by
    intro α β
    calc toFullBlockVec X α * (blockMatEntry H α β * toFullBlockVec X β)
        ≤ |toFullBlockVec X α * (blockMatEntry H α β * toFullBlockVec X β)| :=
          le_abs_self _
      _ = |toFullBlockVec X α| * (|blockMatEntry H α β| * |toFullBlockVec X β|) := by
          rw [abs_mul, abs_mul]
      _ ≤ |toFullBlockVec X α| * (eta * |toFullBlockVec X β|) := by
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          exact mul_le_mul_of_nonneg_right (hH α β) (abs_nonneg _)
      _ = eta * (|toFullBlockVec X α| * |toFullBlockVec X β|) := by ring
  have hdouble : ∑ α : BlockCoord d, ∑ β : BlockCoord d,
        toFullBlockVec X α * (blockMatEntry H α β * toFullBlockVec X β) ≤
      eta * (∑ α : BlockCoord d, |toFullBlockVec X α|) ^ 2 := by
    have hstep : ∑ α : BlockCoord d, ∑ β : BlockCoord d,
          toFullBlockVec X α * (blockMatEntry H α β * toFullBlockVec X β) ≤
        ∑ α : BlockCoord d, ∑ β : BlockCoord d,
          eta * (|toFullBlockVec X α| * |toFullBlockVec X β|) :=
      Finset.sum_le_sum fun α _ => Finset.sum_le_sum fun β _ => habs α β
    refine hstep.trans (le_of_eq ?_)
    rw [sq, Finset.sum_mul_sum]
    simp only [Finset.mul_sum]
  have hcs : (∑ α : BlockCoord d, |toFullBlockVec X α|) ^ 2 ≤
      2 * (d : ℝ) * ∑ α : BlockCoord d, toFullBlockVec X α * toFullBlockVec X α := by
    have hbase : (∑ α : BlockCoord d, |toFullBlockVec X α|) ^ 2 ≤
        ((Finset.univ : Finset (BlockCoord d)).card : ℝ) *
          ∑ α : BlockCoord d, |toFullBlockVec X α| ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    rw [card_blockCoord] at hbase
    refine hbase.trans (le_of_eq ?_)
    push_cast
    congr 1
    exact Finset.sum_congr rfl fun α _ => by rw [sq_abs, sq]
  have hFX := hF X
  have hsum : ∑ α : BlockCoord d, ∑ β : BlockCoord d,
      toFullBlockVec X α * (blockMatEntry H α β * toFullBlockVec X β) ≤
      2 * (d : ℝ) * eta * blockVecDot X (blockMatVecMul F X) := by
    have hchain : eta * (∑ α : BlockCoord d, |toFullBlockVec X α|) ^ 2 ≤
        eta * (2 * (d : ℝ) *
          ∑ α : BlockCoord d, toFullBlockVec X α * toFullBlockVec X α) :=
      mul_le_mul_of_nonneg_left hcs heta
    have hlast : eta * (2 * (d : ℝ) *
          ∑ α : BlockCoord d, toFullBlockVec X α * toFullBlockVec X α) ≤
        eta * (2 * (d : ℝ) * blockVecDot X (blockMatVecMul F X)) := by
      refine mul_le_mul_of_nonneg_left ?_ heta
      refine mul_le_mul_of_nonneg_left hFX ?_
      positivity
    calc ∑ α : BlockCoord d, ∑ β : BlockCoord d,
          toFullBlockVec X α * (blockMatEntry H α β * toFullBlockVec X β)
        ≤ eta * (∑ α : BlockCoord d, |toFullBlockVec X α|) ^ 2 := hdouble
      _ ≤ eta * (2 * (d : ℝ) * blockVecDot X (blockMatVecMul F X)) :=
          le_trans hchain hlast
      _ = 2 * (d : ℝ) * eta * blockVecDot X (blockMatVecMul F X) := by ring
  linarith only [hsum]

/-! ## The block-level deviation estimate -/

/-- **The reassembly.**  If every entry of a block-valued observable stays below
`η` outside an event of probability `p`, the block itself stays below `2dη` times
the reference block outside an event of probability `4d²p`. -/
theorem measureReal_not_blockMatLoewnerLE_le {P : Measure (CoeffSpace d)}
    [IsFiniteMeasure P] {H : CoeffSpace d → BlockMat d} {F : BlockMat d}
    {eta p : ℝ} (heta : 0 ≤ eta)
    (hF : ∀ X : BlockVec d,
      ∑ α : BlockCoord d, toFullBlockVec X α * toFullBlockVec X α ≤
        blockVecDot X (blockMatVecMul F X))
    (hent : ∀ α β : BlockCoord d,
      P.real {a : CoeffSpace d | eta < |blockMatEntry (H a) α β|} ≤ p) :
    P.real {a : CoeffSpace d |
        ¬ BlockMatLoewnerLE (H a) (blockScale (2 * (d : ℝ) * eta) F)} ≤
      (2 * (d : ℝ)) ^ 2 * p := by
  classical
  have hcardprod : (Finset.univ : Finset (BlockCoord d × BlockCoord d)).card
      = (2 * d) * (2 * d) := by
    simp [Finset.card_univ, Fintype.card_prod, Fintype.card_sum, two_mul]
  have hsub : {a : CoeffSpace d |
      ¬ BlockMatLoewnerLE (H a) (blockScale (2 * (d : ℝ) * eta) F)} ⊆
      ⋃ q ∈ (Finset.univ : Finset (BlockCoord d × BlockCoord d)),
        {a : CoeffSpace d | eta < |blockMatEntry (H a) q.1 q.2|} := by
    intro a ha
    by_contra hcon
    refine ha (blockMatLoewnerLE_blockScale_of_abs_blockMatEntry_le heta hF ?_)
    intro α β
    by_contra hentry
    push Not at hentry
    exact hcon (Set.mem_biUnion (Finset.mem_univ (α, β)) hentry)
  calc P.real {a : CoeffSpace d |
        ¬ BlockMatLoewnerLE (H a) (blockScale (2 * (d : ℝ) * eta) F)}
      ≤ P.real (⋃ q ∈ (Finset.univ : Finset (BlockCoord d × BlockCoord d)),
          {a : CoeffSpace d | eta < |blockMatEntry (H a) q.1 q.2|}) :=
        measureReal_mono hsub (measure_ne_top P _)
    _ ≤ ∑ q ∈ (Finset.univ : Finset (BlockCoord d × BlockCoord d)),
          P.real {a : CoeffSpace d | eta < |blockMatEntry (H a) q.1 q.2|} :=
        measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _q ∈ (Finset.univ : Finset (BlockCoord d × BlockCoord d)), p :=
        Finset.sum_le_sum fun q _ => hent q.1 q.2
    _ = (2 * (d : ℝ)) ^ 2 * p := by
        rw [Finset.sum_const, hcardprod, nsmul_eq_mul]
        push_cast
        ring

/-- **The block-level concentration estimate.**  A block-valued observable whose
entries are the averages of centred local readouts bounded by one obeys the
finite-range Gaussian tail in the Loewner order, at the fluctuation scale
`N^{-1/2}` and with the factor `2d` of the reassembly. -/
theorem measureReal_not_blockMatLoewnerLE_average_le_frGauge
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hP : HCPoly.Frozen.IsUnitRangeLaw P) {k : ℤ} (hk : 0 ≤ k)
    {X : BlockCoord d → BlockCoord d → (Fin d → ℤ) → CoeffSpace d → ℝ}
    (hXloc : ∀ α β w, @Measurable (CoeffSpace d) ℝ
      (coeffSigma d (standardCell d k w)) _ (X α β w))
    (hXbd : ∀ α β w, ∀ᵐ a ∂P, |X α β w a| ≤ 1)
    (hXmean : ∀ α β w, ∫ a, X α β w a ∂P = 0)
    {Z : Finset (Fin d → ℤ)} (hZ : Z.Nonempty)
    {H : CoeffSpace d → BlockMat d}
    (hH : ∀ (a : CoeffSpace d) (α β : BlockCoord d),
      blockMatEntry (H a) α β = ((Z.card : ℝ))⁻¹ * ∑ w ∈ Z, X α β w a)
    {F : BlockMat d}
    (hF : ∀ Y : BlockVec d,
      ∑ α : BlockCoord d, toFullBlockVec Y α * toFullBlockVec Y α ≤
        blockVecDot Y (blockMatVecMul F Y))
    {t : ℝ} (ht : 1 ≤ t) :
    P.real {a : CoeffSpace d |
        ¬ BlockMatLoewnerLE (H a) (blockScale (2 * (d : ℝ) *
          (frThreshold d * t * (Real.sqrt (Z.card : ℝ))⁻¹)) F)} ≤
      (2 * (d : ℝ)) ^ 2 * (frGauge d t)⁻¹ := by
  have hetanonneg : (0 : ℝ) ≤ frThreshold d * t * (Real.sqrt (Z.card : ℝ))⁻¹ := by
    have h1 := (frThreshold_pos d).le
    have h2 : (0 : ℝ) ≤ t := le_trans zero_le_one ht
    have h3 : (0 : ℝ) ≤ (Real.sqrt (Z.card : ℝ))⁻¹ :=
      inv_nonneg.2 (Real.sqrt_nonneg _)
    positivity
  refine measureReal_not_blockMatLoewnerLE_le hetanonneg hF ?_
  intro α β
  have hbase := measureReal_abs_average_standardCell_ge_le_frGauge hP hk
    (hXloc α β) (hXbd α β) (hXmean α β) hZ ht
  refine le_trans (measureReal_mono ?_) hbase
  intro a ha
  simp only [Set.mem_ofPred_eq, hH a α β] at ha ⊢
  exact le_of_lt ha

end

end Quenched
end HighContrast
end HCPolySupport
