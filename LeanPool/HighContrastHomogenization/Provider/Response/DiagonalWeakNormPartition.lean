/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.DiagonalWeakNormState
public import LeanPool.HighContrastHomogenization.Provider.Response.WeakNormCellAverage
public import LeanPool.HighContrastHomogenization.Provider.Recurrence.AdaptedPartitionAverage

/-!
# High-contrast homogenization: Provider.Response.DiagonalWeakNormPartition

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Equal-weight averages on an aligned subdivision

The aligned children of an adapted cell have equal volume and cover their
parent up to a null set.  Consequently the average over the parent is the
ordinary normalized finite average of the child averages.  This is the
partition identity used before the finite variance estimate in the weak-norm
estimate for the optimizer state.
-/

namespace HCPolySupport
namespace HighContrast
namespace Response

open MeasureTheory

noncomputable section

variable {d : ℕ}

private theorem aligned_cell_weight_eq_inv_card
    {q : Mat d} (hq : q.PosDef) {k t : ℤ} (hkt : k ≤ t)
    (w : Fin d → ℤ) :
    (volume (adaptedCellAt q k w)).toReal /
        (volume (adaptedCell q t)).toReal =
      (((alignedIndex q k t).card : ℝ))⁻¹ := by
  let Z := alignedIndex q k t
  have hmeas : ∀ z ∈ Z, MeasurableSet (adaptedCellAt q k z) :=
    fun z _ => (Recurrence.isOpenBoundedConvexDomain_adaptedCellAt hq k z).isOpen.measurableSet
  have hsub : ∀ z ∈ Z, adaptedCellAt q k z ⊆ adaptedCell q t :=
    fun _ hz => adaptedCellAt_subset_of_mem_alignedIndex hq hkt hz
  have hdisj : (↑Z : Set (Fin d → ℤ)).PairwiseDisjoint (adaptedCellAt q k) :=
    fun z _ z' _ hzz' => Recurrence.disjoint_adaptedCellAt hq k hzz'
  have hnull : volume (adaptedCell q t \
      ⋃ z ∈ (↑Z : Set (Fin d → ℤ)), adaptedCellAt q k z) = 0 := by
    rw [show (↑Z : Set (Fin d → ℤ)) =
      {z : Fin d → ℤ | adaptedCellCenter q k z ∈ adaptedCell q t} from
        coe_alignedIndex hq hkt]
    exact Recurrence.volume_adaptedCell_diff_iUnion_adaptedCellAt hq hkt
  have hparent : volume (adaptedCell q t) = Z.card • volume (adaptedCell q k) := by
    rw [Recurrence.measure_eq_sum_of_aePartition hmeas hsub hdisj hnull,
      Finset.sum_congr rfl fun z _ => Recurrence.volume_adaptedCellAt q k z,
      Finset.sum_const]
  have hkpos : (0 : ℝ) < (volume (adaptedCell q k)).toReal :=
    Recurrence.toReal_volume_adaptedCell_pos hq k
  rw [Recurrence.volume_adaptedCellAt, hparent, nsmul_eq_mul,
    ENNReal.toReal_mul, ENNReal.toReal_natCast]
  field_simp
  simp [Z]

/-- **The average over an adapted parent is the normalized average of the
child averages.** -/
theorem avsum_volumeAverage_adaptedCellAt_eq
    {q : Mat d} (hq : q.PosDef) {k t : ℤ} (hkt : k ≤ t)
    {g : Vec d → ℝ} (hg : IntegrableOn g (adaptedCell q t) volume) :
    avsum (alignedIndex q k t)
        (fun w => volumeAverage (adaptedCellAt q k w) g) =
      volumeAverage (adaptedCell q t) g := by
  let Z := alignedIndex q k t
  have hmeas : ∀ w ∈ Z, MeasurableSet (adaptedCellAt q k w) :=
    fun w _ => (Recurrence.isOpenBoundedConvexDomain_adaptedCellAt hq k w).isOpen.measurableSet
  have hsub : ∀ w ∈ Z, adaptedCellAt q k w ⊆ adaptedCell q t :=
    fun _ hw => adaptedCellAt_subset_of_mem_alignedIndex hq hkt hw
  have hdisj : (↑Z : Set (Fin d → ℤ)).PairwiseDisjoint (adaptedCellAt q k) :=
    fun w _ w' _ hww' => Recurrence.disjoint_adaptedCellAt hq k hww'
  have hnull : volume (adaptedCell q t \
      ⋃ w ∈ (↑Z : Set (Fin d → ℤ)), adaptedCellAt q k w) = 0 := by
    rw [show (↑Z : Set (Fin d → ℤ)) =
      {w : Fin d → ℤ | adaptedCellCenter q k w ∈ adaptedCell q t} from
        coe_alignedIndex hq hkt]
    exact Recurrence.volume_adaptedCell_diff_iUnion_adaptedCellAt hq hkt
  have hcell0 : ∀ w ∈ Z, volume (adaptedCellAt q k w) ≠ 0 :=
    fun w _ => (Recurrence.volume_adaptedCellAt_pos hq k w).ne'
  have havg := Recurrence.volumeAverage_eq_sum_weight_of_aePartition
    (U := adaptedCell q t) (Z := Z) (c := adaptedCellAt q k) (g := g)
    hmeas hsub hdisj hnull hg hcell0 (Recurrence.volume_adaptedCell_lt_top hq t).ne
  rw [havg, avsum_eq, Finset.mul_sum]
  exact Finset.sum_congr rfl fun w _ => by
    rw [aligned_cell_weight_eq_inv_card hq hkt w]

/-- **The doubled parent average is the normalized sum of the child
averages.** -/
theorem blockCellAverage_adaptedCell_eq_avsum
    {q : Mat d} (hq : q.PosDef) {k t : ℤ} (hkt : k ≤ t)
    {F : Vec d → BlockVec d}
    (hF₁ : ∀ i, IntegrableOn (fun x => (F x).1 i) (adaptedCell q t) volume)
    (hF₂ : ∀ i, IntegrableOn (fun x => (F x).2 i) (adaptedCell q t) volume) :
    blockCellAverage (adaptedCell q t) F =
      ((fun i => avsum (alignedIndex q k t) fun w =>
          (blockCellAverage (adaptedCellAt q k w) F).1 i),
        (fun i => avsum (alignedIndex q k t) fun w =>
          (blockCellAverage (adaptedCellAt q k w) F).2 i)) := by
  refine Prod.ext ?_ ?_
  · funext i
    change volumeAverage (adaptedCell q t) (fun x => (F x).1 i) =
      avsum (alignedIndex q k t)
        (fun w => volumeAverage (adaptedCellAt q k w) (fun x => (F x).1 i))
    exact (avsum_volumeAverage_adaptedCellAt_eq hq hkt (hF₁ i)).symm
  · funext i
    change volumeAverage (adaptedCell q t) (fun x => (F x).2 i) =
      avsum (alignedIndex q k t)
        (fun w => volumeAverage (adaptedCellAt q k w) (fun x => (F x).2 i))
    exact (avsum_volumeAverage_adaptedCellAt_eq hq hkt (hF₂ i)).symm

end

end Response
end HighContrast
end HCPolySupport
