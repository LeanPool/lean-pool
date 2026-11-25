/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import LeanPool.ShellsortMean.TagPosition
public import LeanPool.ShellsortMean.CompletePrefix

/-! A decomposition of two-pass displacement into source and target prefix counts. -/

@[expose] public noncomputable section
namespace Shellsort
open scoped BigOperators

theorem chainPositions_card (n h s : ℕ) :
    (chainPositions n h s).card = residuePrefixCount h s n := by
  let S := (Finset.range n).filter (fun v => v % h = s)
  let e : {i : Fin n // i.val % h = s} ≃ S := {
    toFun := fun i => ⟨i.val.val, Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr i.val.isLt, i.property⟩⟩
    invFun := fun v => ⟨⟨v.val, Finset.mem_range.mp
      (Finset.mem_filter.mp v.property).1⟩, (Finset.mem_filter.mp v.property).2⟩
    left_inv := by intro i; rfl
    right_inv := by intro v; rfl }
  have hc := Fintype.card_congr e
  simpa [Fintype.card_subtype, chainPositions, S, residuePrefixCount] using hc

theorem chainLowerCount_le_length {n : ℕ} (B : Finset (Fin n)) (h s : ℕ) :
    chainLowerCount B h s ≤ residuePrefixCount h s n := by
  rw [← chainPositions_card]
  apply Finset.card_le_card
  intro i hi
  simp only [chainPositions, Finset.mem_filter, Finset.mem_univ, true_and]
  exact (Finset.mem_filter.mp hi).2

/-- Every occupied source-prefix index corresponds to a real array position;
there are no artificial positions past the finite array boundary. -/
theorem source_prefix_position_lt {n : ℕ} (B : Finset (Fin n)) (h s v : ℕ)
    (hh : 0 < h) (hs : s < h) (hv : v < chainLowerCount B h s) :
    s + h * v < n := by
  have hc := chainLowerCount_le_length B h s
  rw [residuePrefixCount_formula h s n hh hs] at hc
  have hn := Nat.mod_add_div n h
  by_cases hsrem : s < n % h
  · simp only [hsrem, ite_true] at hc
    have hv' : v ≤ n / h := by omega
    have hm := Nat.mul_le_mul_left h hv'
    omega
  · simp only [hsrem, ite_false] at hc
    have hv' : v + 1 ≤ n / h := by omega
    have hm := Nat.mul_le_mul_left h hv'
    rw [Nat.mul_add, Nat.mul_one] at hm
    omega

theorem sum_chainLowerCount {n : ℕ} (B : Finset (Fin n)) (h : ℕ) (hh : 0 < h) :
    (∑ s ∈ Finset.range h, chainLowerCount B h s) = B.card := by
  symm
  apply Finset.card_eq_sum_card_fiberwise
  intro i _
  exact Finset.mem_range.mpr (Nat.mod_lt i.val hh)

/-- Source s contributes exactly its arithmetic-prefix count to target chain j. -/
theorem lowerStep_source_target_count {n : ℕ} (B : Finset (Fin n))
    (h g j s : ℕ) (hh : 0 < h) (hs : s < h) :
    (((lowerStep B h).filter (fun i => i.val % g = j)).filter
      (fun i => i.val % h = s)).card =
      sourcePrefixCount h g j s (chainLowerCount B h s) := by
  let V := (Finset.range (chainLowerCount B h s)).filter
    (fun v => (s + h * v) % g = j)
  have hmod (v : ℕ) : (s + h * v) % h = s := by
    simp [Nat.add_mod, Nat.mod_eq_of_lt hs]
  have hdiv (v : ℕ) : (s + h * v) / h = v := by
    rw [Nat.add_mul_div_left _ _ hh, Nat.div_eq_of_lt hs, Nat.zero_add]
  let e : {i : Fin n // i ∈ lowerStep B h ∧ i.val % g = j ∧ i.val % h = s} ≃ V := {
    toFun := fun i => ⟨i.val.val / h, by
      have hi : chainOrdinal h i.val < chainLowerCount B h (i.val.val % h) := by
        simpa [lowerStep] using i.property.1
      rw [chainOrdinal_eq_div h hh, i.property.2.2] at hi
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, ?_⟩
      have hp := Nat.mod_add_div i.val.val h
      rw [i.property.2.2] at hp
      rw [hp]
      exact i.property.2.1⟩
    invFun := fun v => ⟨⟨s + h * v.val, source_prefix_position_lt B h s v.val hh hs
      (Finset.mem_range.mp (Finset.mem_filter.mp v.property).1)⟩, by
      refine ⟨?_, (Finset.mem_filter.mp v.property).2, hmod v.val⟩
      simp only [lowerStep, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [chainOrdinal_eq_div h hh, hmod, hdiv]
      exact Finset.mem_range.mp (Finset.mem_filter.mp v.property).1⟩
    left_inv := by
      intro i
      apply Subtype.ext
      apply Fin.ext
      change s + h * (i.val.val / h) = i.val.val
      simpa [i.property.2.2] using Nat.mod_add_div i.val.val h
    right_inv := by
      intro v
      apply Subtype.ext
      exact hdiv v.val }
  have hc := Fintype.card_congr e
  simpa [Fintype.card_subtype, lowerStep, Finset.filter_filter, and_assoc,
    V, sourcePrefixCount] using hc

/-- Exact finite source decomposition of a binary sorting transition. -/
theorem lowerStep_target_count {n : ℕ} (B : Finset (Fin n)) (h g j : ℕ)
    (hh : 0 < h) :
    chainLowerCount (lowerStep B h) g j =
      ∑ s ∈ Finset.range h, sourcePrefixCount h g j s (chainLowerCount B h s) := by
  unfold chainLowerCount
  rw [Finset.card_eq_sum_card_fiberwise (f := fun i : Fin n => i.val % h)
    (t := Finset.range h) (fun i _ => Finset.mem_range.mpr (Nat.mod_lt i.val hh))]
  apply Finset.sum_congr rfl
  intro s hs
  exact lowerStep_source_target_count B h g j s hh (Finset.mem_range.mp hs)

/-- Signed displacement of an actual tagged key after two sorts, in integers.
The count identity includes all finite-array boundary effects. -/
theorem two_pass_tag_displacement_int {n : ℕ} (p : RankPlacement n)
    (h g : ℕ) (hh : 0 < h) (hg : 0 < g) (x : Fin n) :
    ((gapSort (gapSort p h) g x).val : ℤ) - (x.val : ℤ) =
      (((gapSort p h x).val % g : ℕ) : ℤ) +
        ∑ s ∈ Finset.range h,
          ((g : ℤ) * (sourcePrefixCount h g ((gapSort p h x).val % g) s
            (chainLowerCount (thresholdSet p x.val) h s) : ℤ) -
            (chainLowerCount (thresholdSet p x.val) h s : ℤ)) := by
  have hp := gapSort_tag_position (gapSort p h) g hg x
  rw [gapSort_threshold_commutes, lowerStep_target_count _ h g _ hh] at hp
  have hy := sum_chainLowerCount (thresholdSet p x.val) h hh
  rw [tagged_threshold_card] at hy
  have hpZ := congrArg (fun v : ℕ => (v : ℤ)) hp
  push_cast at hpZ
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Nat.cast_sum, ← Nat.cast_sum, hy]
  rw [hpZ]
  push_cast
  ring

/-- The same exact identity in the scalar field used for finite expectations. -/
theorem two_pass_tag_displacement_real {n : ℕ} (p : RankPlacement n)
    (h g : ℕ) (hh : 0 < h) (hg : 0 < g) (x : Fin n) :
    ((gapSort (gapSort p h) g x).val : ℝ) - (x.val : ℝ) =
      (((gapSort p h x).val % g : ℕ) : ℝ) +
        ∑ s ∈ Finset.range h,
          ((g : ℝ) * (sourcePrefixCount h g ((gapSort p h x).val % g) s
            (chainLowerCount (thresholdSet p x.val) h s) : ℝ) -
            (chainLowerCount (thresholdSet p x.val) h s : ℝ)) := by
  have hcast := congrArg (fun z : ℤ => (z : ℝ))
    (two_pass_tag_displacement_int p h g hh hg x)
  push_cast at hcast
  exact hcast

end Shellsort
end
