/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Geometry.IntegerLatticeBallBound
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Order.CompletePartialOrder

/-! # Unit cells around the standard integer lattice

The half-open cells partition real coordinate space, have volume one, and lie
within distance one of their lattice corner in the supremum norm.
-/

@[expose] public section

namespace NairTenenbaum

open Finset MeasureTheory

variable {ι : Type*} [Fintype ι]

/-- The unit cell attached to an integer lattice point. -/
noncomputable def integerLatticeCell (m : ι → ℤ) : Set (ι → ℝ) :=
  Set.univ.pi (fun i => Set.Ico (m i : ℝ) ((m i : ℝ) + 1))

omit [Fintype ι] in
theorem mem_integerLatticeCell {m : ι → ℤ} {x : ι → ℝ} :
    x ∈ integerLatticeCell m ↔ ∀ i, (m i : ℝ) ≤ x i ∧ x i < (m i : ℝ) + 1 := by
  simp only [integerLatticeCell, Set.mem_pi, Set.mem_univ, Set.mem_Ico, forall_const]

omit [Fintype ι] in
theorem mem_integerLatticeCell_iff_floor {m : ι → ℤ} {x : ι → ℝ} :
    x ∈ integerLatticeCell m ↔ (fun i => ⌊x i⌋) = m := by
  rw [mem_integerLatticeCell]
  simp only [funext_iff, Int.floor_eq_iff]

omit [Fintype ι] in
theorem mem_integerLatticeCell_floor (x : ι → ℝ) :
    x ∈ integerLatticeCell (fun i => ⌊x i⌋) := mem_integerLatticeCell_iff_floor.mpr rfl

omit [Fintype ι] in
theorem integerLatticeCell_pairwiseDisjoint : Pairwise (fun m n : ι → ℤ => Disjoint
    (integerLatticeCell m) (integerLatticeCell n)) := by
  intro m n hmn
  apply Set.disjoint_left.mpr
  intro x hxm hxn
  exact hmn ((mem_integerLatticeCell_iff_floor.mp hxm).symm.trans
    (mem_integerLatticeCell_iff_floor.mp hxn))

omit [Fintype ι] in
theorem measurableSet_integerLatticeCell [Finite ι] (m : ι → ℤ) :
    MeasurableSet (integerLatticeCell m) :=
  MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ico)

theorem volume_integerLatticeCell (m : ι → ℤ) : volume (integerLatticeCell m) = 1 := by
  simp [integerLatticeCell, Real.volume_pi_Ico]

theorem integerLatticeCell_dist_le_one {m : ι → ℤ} {x : ι → ℝ}
    (hx : x ∈ integerLatticeCell m) : dist x (integerLatticePoint m) ≤ 1 := by
  apply (dist_pi_le_iff zero_le_one).mpr
  intro i
  obtain ⟨hlo, hhi⟩ := mem_integerLatticeCell.mp hx i
  change dist (x i) (m i : ℝ) ≤ 1
  rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hlo)]
  linarith

/-- The union of the cells attached to the selected integer lattice points. -/
noncomputable def integerLatticeCellUnion (S : Finset (ι → ℤ)) : Set (ι → ℝ) :=
  ⋃ m ∈ S, integerLatticeCell m

theorem volume_integerLatticeCellUnion (S : Finset (ι → ℤ)) :
    volume (integerLatticeCellUnion S) = S.card := by
  rw [integerLatticeCellUnion, measure_biUnion_finset]
  · simp only [volume_integerLatticeCell, sum_const, nsmul_eq_mul, mul_one]
  · exact integerLatticeCell_pairwiseDisjoint.set_pairwise _
  · intro m _
    exact measurableSet_integerLatticeCell m

theorem volume_real_integerLatticeCellUnion (S : Finset (ι → ℤ)) :
    volume.real (integerLatticeCellUnion S) = S.card := by
  rw [measureReal_def, volume_integerLatticeCellUnion]
  simp

theorem latticeCell_volume_discrepancy_le (I A O : Finset (ι → ℤ))
    (hIA : I ⊆ A) (hAO : A ⊆ O) {s : Set (ι → ℝ)}
    (hinside : integerLatticeCellUnion I ⊆ s) (houtside : s ⊆ integerLatticeCellUnion O) :
    |(A.card : ℝ) - volume.real s| ≤ ((O \ I).card : ℝ) := by
  classical
  have hfinite : volume s ≠ ⊤ := ne_top_of_le_ne_top
    (by rw [volume_integerLatticeCellUnion]; simp) (measure_mono houtside)
  have hlo := measureReal_mono (μ := volume) hinside hfinite
  have hhi := measureReal_mono (μ := volume) houtside
    (by rw [volume_integerLatticeCellUnion]; simp)
  rw [volume_real_integerLatticeCellUnion] at hlo hhi
  have hcardlo : (I.card : ℝ) ≤ A.card := Nat.cast_le.mpr (card_le_card hIA)
  have hcardhi : (A.card : ℝ) ≤ O.card := Nat.cast_le.mpr (card_le_card hAO)
  have hdiff : ((O \ I).card : ℝ) + I.card = O.card := by
    exact_mod_cast card_sdiff_add_card_eq_card (hIA.trans hAO)
  rw [abs_le]
  constructor <;> linarith

end NairTenenbaum
