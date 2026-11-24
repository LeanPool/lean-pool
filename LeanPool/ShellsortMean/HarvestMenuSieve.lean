/-
Copyright (c) 2026 Miaozhen Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miaozhen Yu
-/

/- Modified for Lean Pool: module conversion, import paths, and diagnostics. -/

module

public import LeanPool.ShellsortMean.Actual214PhysicalLowGrid

/-! The short-interval estimate on the actual random-gap menu. Keep one
sample per (numerator, original modulus), even for coincident fractions. -/
@[expose] public noncomputable section
namespace Shellsort.Actual214
open Finset RoughGapDenominatorAverage

def highGrid (h D : ℕ) : Finset ℕ :=
  (range h).filter (fun a => 0 < a ∧ D < h / Nat.gcd h a)

theorem nonzero_grid_split (h D : ℕ) (f : ℕ → ℝ) :
    (∑ a ∈ (range h).filter (0 < ·), f a) =
      (∑ a ∈ lowGrid h D, f a) + ∑ a ∈ highGrid h D, f a := by
  let L := lowGrid h D
  let U := highGrid h D
  have split : (range h).filter (0 < ·) = L ∪ U := by
    ext a
    simp only [L, U, lowGrid, highGrid, mem_union, mem_filter, mem_range]
    omega
  have dis : Disjoint L U := by
    apply disjoint_left.mpr
    intro a ha hb
    exact (not_lt_of_ge (mem_filter.mp ha).2.2) (mem_filter.mp hb).2.2
  rw [split, sum_union dis]

private def samplesAt (h D : ℕ) : Finset Fraction :=
  (highGrid h D).image (fun a => (a, h))

private theorem samples_disjoint (G : Finset ℕ) (D : ℕ) :
    Set.PairwiseDisjoint (↑G) (fun h => samplesAt h D) := by
  intro h _ h' _ diff
  apply disjoint_left.mpr
  intro p hp hp'
  obtain ⟨a, _, rfl⟩ := mem_image.mp hp
  obtain ⟨b, _, e⟩ := mem_image.mp hp'
  exact diff (congrArg Prod.snd e).symm

/-- The original modulus h is a tag. Two strings of integers giving the
same rational frequency still contribute once for each candidate gap. -/
theorem menu_short_energy {m B D : ℕ} (hD : 0 < D)
    (G : Finset ℕ) (bounded : ∀ h ∈ G, h ≤ B) (start : ℤ) (v : Fin m → ℂ) :
    (∑ h ∈ G, ∑ a ∈ highGrid h D, energy start v (a, h)) ≤
      B * (8 * (B : ℝ) + 2 * Real.pi * m / D) * (∑ j, ‖v j‖ ^ 2) := by
  classical
  let S := G.biUnion (fun h => samplesAt h D)
  have unpack {p : Fraction} (hp : p ∈ S) :
      p.1 < p.2 ∧ p.2 ≤ B ∧ D < (reduced p).2 := by
    obtain ⟨h, hg, htag⟩ := mem_biUnion.mp hp
    obtain ⟨a, ha, rfl⟩ := mem_image.mp htag
    obtain ⟨ar, _, ad⟩ := mem_filter.mp ha
    exact ⟨mem_range.mp ar, bounded h hg, by simpa [reduced, mult, Nat.gcd_comm] using ad⟩
  have tags : (∑ p ∈ S, energy start v p) =
      ∑ h ∈ G, ∑ a ∈ highGrid h D, energy start v (a, h) := by
    dsimp only [S]
    rw [sum_biUnion (samples_disjoint G D)]
    apply sum_congr rfl
    intro h _
    apply sum_image
    intro a _ b _ e
    exact congrArg Prod.fst e
  rw [← tags]
  by_cases hDB : D ≤ B
  · exact high_denominator_sum hD hDB S
      (fun p hp => ⟨(unpack hp).1, (unpack hp).2.1⟩)
      (fun p hp => (unpack hp).2.2.le) start v
  · have empty : S = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro p hp
      have props := unpack hp
      have rd : (reduced p).2 ≤ p.2 := Nat.div_le_self ..
      omega
    rw [empty, sum_empty]
    positivity

/-- Uniform average over the actual 2.14-recurrence menu. D may exceed every
gap in the menu, including early scales. The same input vector is sampled at
all menu frequencies. -/
theorem actual_menu_short_mean {m D : ℕ} (j : ℕ) (hc : 9400 ≤ gap j) (hD : 0 < D)
    (start : ℤ) (v : Fin m → ℂ) :
    let G := window (gap j) (Nat.gcd (gap (j + 2)) (gap (j + 1)))
    (∑ h ∈ G, ∑ a ∈ highGrid h D, energy start v (a, h)) / (G.card : ℝ) ≤
      18800 * (32 * (gap j : ℝ) + 4 * Real.pi * m / D) * (∑ i, ‖v i‖ ^ 2) := by
  intro G
  have hb : ∀ h ∈ G, h ≤ 2 * gap j := by
    intro h hh
    have hi := (mem_Icc.mp (mem_filter.mp hh).1).2
    omega
  have bound := menu_short_energy hD G hb start v
  have atom : (1 : ℝ) / G.card ≤ 18800 / (gap j : ℝ) := actual_atom_le j hc
  have pos : (gap j : ℝ) ≠ 0 := by exact_mod_cast (gap_pos j).ne'
  have rhs := mul_le_mul_of_nonneg_left bound (show 0 ≤ (1 : ℝ) / G.card by positivity)
  have weight := mul_le_mul_of_nonneg_right atom
    (show (0 : ℝ) ≤ (↑(2 * gap j) : ℝ) * (8*↑(2 * gap j) + 2 * Real.pi * m / D) * ∑ i, ‖v i‖ ^ 2 by
      positivity)
  calc
    _ = (1 / (G.card : ℝ)) * (∑ h ∈ G, ∑ a ∈ highGrid h D, energy start v (a, h)) := by ring
    _ ≤ _ := rhs.trans weight
    _ = _ := by push_cast; field_simp; ring



end Shellsort.Actual214
