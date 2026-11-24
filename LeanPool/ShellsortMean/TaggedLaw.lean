/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module
public import Mathlib.Tactic.Ring
public import LeanPool.ShellsortMean.TaggedFibers

/-! Uniform threshold states obtained by conditioning on the position of a tag. -/

@[expose] public noncomputable section
namespace Shellsort
open scoped BigOperators

abbrev TaggedSubset {n : ℕ} (i : Fin n) :=
  {B : Finset (Fin n) // i ∉ B}

/-- The smaller-key positions around the key initially occupying position i.
Its rank is random when the underlying permutation is random. -/
def tagLowerState {n : ℕ} (p : RankPlacement n) (i : Fin n) : TaggedSubset i :=
  ⟨thresholdSet p (p.symm i).val, by
    simpa using tag_not_in_threshold p (p.symm i)⟩

theorem tagLowerState_card {n : ℕ} (p : RankPlacement n) (i : Fin n) :
    (tagLowerState p i).val.card = (p.symm i).val :=
  tagged_threshold_card p (p.symm i)

theorem tagLowerState_eq_iff {n : ℕ} (p : RankPlacement n) (i : Fin n)
    (B : TaggedSubset i) :
    tagLowerState p i = B ↔
      p ⟨B.val.card, tagged_subset_card_lt B.val i B.property⟩ = i ∧
        thresholdSet p B.val.card = B.val := by
  constructor
  · intro h
    have hB : thresholdSet p (p.symm i).val = B.val := congrArg Subtype.val h
    have hr : (p.symm i).val = B.val.card := by
      rw [← tagged_threshold_card p (p.symm i), hB]
    have he : p.symm i = ⟨B.val.card, tagged_subset_card_lt B.val i B.property⟩ :=
      Fin.ext hr
    constructor
    · rw [← he, Equiv.apply_symm_apply]
    · simpa [hr] using hB
  · rintro ⟨howner, hB⟩
    apply Subtype.ext
    change thresholdSet p (p.symm i).val = B.val
    have he : p.symm i = ⟨B.val.card, tagged_subset_card_lt B.val i B.property⟩ := by
      simpa using (congrArg p.symm howner).symm
    rw [he]
    exact hB

/-- The law of the actual fixed-position tagged state is obtained by counting
permutations; no independence hypothesis is used. -/
theorem tagLowerState_fiber_card {n : ℕ} (i : Fin n) (B : TaggedSubset i) :
    Fintype.card {p : RankPlacement n // tagLowerState p i = B} =
      B.val.card.factorial * (n - 1 - B.val.card).factorial := by
  let e := Equiv.subtypeEquivRight (fun p => tagLowerState_eq_iff p i B)
  apply (Fintype.card_congr e).trans
  convert tagged_fiber_card B.val i B.property using 1

/-- Exact pushforward of the uniform permutation average to persistent tagged states. -/
theorem uniform_tagged_state_mean {n : ℕ} (i : Fin n) (f : TaggedSubset i → ℝ) :
    uniformAverage (fun p : RankPlacement n => f (tagLowerState p i)) =
      ∑ B : TaggedSubset i,
        ((B.val.card.factorial : ℝ) * ((n - 1 - B.val.card).factorial : ℝ) /
          (n.factorial : ℝ)) * f B := by
  unfold uniformAverage
  rw [← Fintype.sum_fiberwise' (fun p : RankPlacement n => tagLowerState p i) f]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, tagLowerState_fiber_card]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro B _
  push_cast
  ring

end Shellsort
end
