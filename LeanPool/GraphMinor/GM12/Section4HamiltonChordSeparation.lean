/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section4ChordSeparation
public import LeanPool.GraphMinor.GM12.Section4HamiltonPorts
import Mathlib.Tactic.Ring

/-!
# The two Hamilton chords do not cross

The incoming port precedes the outgoing port in every vertex
block in the crossing drawing of XII (4.5), page 252. For three
successive vertex blocks, the incoming and outgoing chords at
the middle block have nonalternating ports. This remains true
when the blocks wrap around the end of the chosen full turn.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- Nested pairs of circle ports also give disjoint chords. This
is the full-turn wrap case of the separation test for XII (4.5),
page 252. -/
theorem nested_ordered_chords_disjoint {a b c d : ℝ}
    (hab : a < b) (hbc : b < c) (hcd : c < d) (hda : d < a + 1) :
    Disjoint (segment ℝ (ee a : ℂ) (ee d : ℂ))
      (segment ℝ (ee b : ℂ) (ee c : ℂ)) := by
  have h := ordered_chords_disjoint
    (a := d - 1) (c := a) (b := b) (d := c)
    (by linarith) hab hbc (by linarith)
  have hd : ee (d - 1) = ee d := ee_eq_iff.mpr ⟨-1, by push_cast; ring⟩
  rw [hd, segment_symm ℝ (ee d : ℂ) (ee a : ℂ)] at h
  exact h

/-- The Hamilton chords at the middle of three cyclically
successive vertex blocks are disjoint. This proves the local
noncrossing assertion used for XII (4.5)(vii), page 252. -/
theorem hamilton_chords_disjoint_of_cyclic_order {p : ℕ}
    (a b : Fin p → ℝ) (ha : ∀ i, a i ∈ Ioo 0 1) (hb : ∀ i, b i ∈ Ioo 0 1)
    (hab : ∀ i, a i < b i) (hblocks : ∀ i j, i < j → b i < a j)
    {u v w : Fin p}
    (hcyclic : (u < v ∧ v < w) ∨ (v < w ∧ w < u) ∨ (w < u ∧ u < v)) :
    Disjoint (segment ℝ (ee (b u) : ℂ) (ee (a v) : ℂ))
      (segment ℝ (ee (b v) : ℂ) (ee (a w) : ℂ)) := by
  rcases hcyclic with ⟨huv, hvw⟩ | ⟨hvw, hwu⟩ | ⟨hwu, huv⟩
  · exact ordered_chords_disjoint (hblocks u v huv) (hab v) (hblocks v w hvw)
      (by linarith [(hb u).1, (ha w).2])
  · have h := nested_ordered_chords_disjoint (hab v) (hblocks v w hvw)
      ((hab w).trans ((hblocks w u hwu).trans (hab u)))
      (by linarith [(ha v).1, (hb u).2])
    rw [segment_symm ℝ (ee (a v) : ℂ) (ee (b u) : ℂ)] at h
    exact h
  · have h := nested_ordered_chords_disjoint
      ((hab w).trans ((hblocks w u hwu).trans (hab u))) (hblocks u v huv) (hab v)
      (by linarith [(ha w).1, (hb v).2])
    rw [segment_symm ℝ (ee (a w) : ℂ) (ee (b v) : ℂ)] at h
    exact h.symm

/-- The two Hamilton chords incident with every vertex are
disjoint. This verifies the chord part of XII (4.5)(vii), page 252,
without an extra cyclic-order assumption. -/
theorem hamilton_chords_disjoint {p : ℕ} (hp : 3 ≤ p)
    (a b : Fin p → ℝ) (ha : ∀ i, a i ∈ Ioo 0 1) (hb : ∀ i, b i ∈ Ioo 0 1)
    (hab : ∀ i, a i < b i) (hblocks : ∀ i j, i < j → b i < a j) (v : Fin p) :
    Disjoint (segment ℝ (ee (b ((finRotate p).symm v)) : ℂ) (ee (a v) : ℂ))
      (segment ℝ (ee (b v) : ℂ) (ee (a (finRotate p v)) : ℂ)) :=
  hamilton_chords_disjoint_of_cyclic_order a b ha hb hab hblocks
    (finRotate_neighbors_cyclic_order hp v)

/-- The vertex-pair coordinates with Hamilton priorities give
disjoint incoming and outgoing Hamilton chords at every vertex.
This is condition (vii) for the inner chords in XII (4.5), page 252. -/
theorem hamilton_matrix_chords_disjoint {p : ℕ} (hp : 3 ≤ p)
    (F : Fin p → Fin p → ℝ) (hF : ∀ v w, F v w ∈ Ioo 0 1)
    (hblocks : ∀ v w i j, v < i → F v w < F i j)
    (hpriority : ∀ v w z, hamiltonPortPriority v w < hamiltonPortPriority v z → F v w < F v z)
    (v : Fin p) :
    Disjoint
      (segment ℝ (ee (F ((finRotate p).symm v) v) : ℂ) (ee (F v ((finRotate p).symm v)) : ℂ))
      (segment ℝ (ee (F v (finRotate p v)) : ℂ) (ee (F (finRotate p v) v) : ℂ)) := by
  have hlocal : ∀ i, F i ((finRotate p).symm i) < F i (finRotate p i) := by
    intro i
    apply hpriority
    rw [hamiltonPortPriority_predecessor, hamiltonPortPriority_successor hp]
    decide
  have h := hamilton_chords_disjoint hp
    (fun i => F i ((finRotate p).symm i)) (fun i => F i (finRotate p i))
    (fun i => hF _ _) (fun i => hF _ _) hlocal
    (fun i j hij => hblocks _ _ _ _ hij) v
  simpa only [Equiv.apply_symm_apply, Equiv.symm_apply_apply] using h

end GraphMinor.GM12
