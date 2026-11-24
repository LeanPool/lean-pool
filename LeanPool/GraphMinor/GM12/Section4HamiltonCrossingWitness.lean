/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section4HamiltonChordCrossing
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card

/-!
# Crossing witnesses for Hamilton chords

For XII (4.5), page 252, each vertex of a clique on at least four
vertices has a neighbor other than itself and its two Hamilton
neighbors. Its port follows the outgoing Hamilton port. The chord
to that neighbor therefore crosses the outgoing Hamilton chord.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- A clique vertex has a non-Hamilton neighbor once there are
at least four vertices. This supplies the witness for the Hamilton
edges in XII (4.5)(vi), page 252. -/
theorem exists_nonHamilton_neighbor {p : ℕ} (hp : 4 ≤ p) (v : Fin p) :
    ∃ w : Fin p, w ≠ v ∧ w ≠ (finRotate p).symm v ∧ w ≠ finRotate p v := by
  classical
  by_contra hnone
  have hcover : (Finset.univ : Finset (Fin p)) ⊆
      {v, (finRotate p).symm v, finRotate p v} := by
    intro w _
    by_cases hwv : w = v
    · simp [hwv]
    by_cases hwpre : w = (finRotate p).symm v
    · simp [hwpre]
    by_cases hwnext : w = finRotate p v
    · simp [hwnext]
    exact False.elim (hnone ⟨w, hwv, hwpre, hwnext⟩)
  have hcard := Finset.card_le_card hcover
  have hfirst := Finset.card_insert_le v ({(finRotate p).symm v, finRotate p v} : Finset (Fin p))
  have hsecond := Finset.card_insert_le ((finRotate p).symm v) ({finRotate p v} : Finset (Fin p))
  simp only [Finset.card_univ, Fintype.card_fin] at hcard
  simp only [Finset.card_singleton] at hsecond
  omega

/-- With the prescribed Hamilton port priorities, every outgoing
Hamilton chord has a crossing chord. This proves the Hamilton-edge
case of XII (4.5)(vi), page 252. -/
theorem exists_crossing_chord_for_Hamilton {p : ℕ} (hp : 4 ≤ p)
    (F : Fin p → Fin p → ℝ) (hF : ∀ v w, F v w ∈ Ioo 0 1)
    (hblocks : ∀ v w i j, v < i → F v w < F i j)
    (hpriority : ∀ v w z, hamiltonPortPriority v w < hamiltonPortPriority v z → F v w < F v z)
    (v : Fin p) :
    ∃ w : Fin p, w ≠ v ∧ w ≠ (finRotate p).symm v ∧ w ≠ finRotate p v ∧
      (segment ℝ (ee (F v (finRotate p v)) : ℂ) (ee (F (finRotate p v) v) : ℂ) ∩
        segment ℝ (ee (F v w) : ℂ) (ee (F w v) : ℂ)).Nonempty := by
  obtain ⟨w, hwv, hwpre, hwnext⟩ := exists_nonHamilton_neighbor hp v
  have hprio := (hamiltonPortPriority_order (by omega : 3 ≤ p) hwpre hwnext).2
  exact ⟨w, hwv, hwpre, hwnext,
    hamilton_chord_crosses_later_port F hF hblocks hwv hwnext
      (hpriority v (finRotate p v) w hprio)⟩

/-- Every clique chord has a different crossing chord under the
Hamilton port priorities. The witness shares one vertex and has
its other vertex outside the original pair. This proves condition
(vi) of the source crossing construction for XII (4.5), page 252. -/
theorem every_clique_chord_has_crossing {p : ℕ} (hp : 4 ≤ p)
    (F : Fin p → Fin p → ℝ) (hF : ∀ v w, F v w ∈ Ioo 0 1)
    (hblocks : ∀ v w i j, v < i → F v w < F i j)
    (hpriority : ∀ v w z, hamiltonPortPriority v w < hamiltonPortPriority v z → F v w < F v z)
    {v w : Fin p} (hvw : v ≠ w) :
    ∃ x y : Fin p, x ≠ y ∧ y ≠ v ∧ y ≠ w ∧ (x = v ∨ x = w) ∧
      (segment ℝ (ee (F v w) : ℂ) (ee (F w v) : ℂ) ∩
        segment ℝ (ee (F x y) : ℂ) (ee (F y x) : ℂ)).Nonempty := by
  by_cases hwnext : w = finRotate p v
  · subst w
    obtain ⟨z, hzv, _, hznext, hcross⟩ := exists_crossing_chord_for_Hamilton hp F hF hblocks
      hpriority v
    exact ⟨v, z, hzv.symm, hzv, hznext, Or.inl rfl, hcross⟩
  · by_cases hwpre : w = (finRotate p).symm v
    · have hnextw : finRotate p w = v := by rw [hwpre, Equiv.apply_symm_apply]
      obtain ⟨z, hzw, _, hznext, hcross⟩ := exists_crossing_chord_for_Hamilton hp F hF hblocks
        hpriority w
      have hzv : z ≠ v := by simpa only [hnextw] using hznext
      rw [hnextw, segment_symm ℝ (ee (F w v) : ℂ) (ee (F v w) : ℂ)] at hcross
      exact ⟨w, z, hzw.symm, hzv, hzw, Or.inr rfl, hcross⟩
    · have hprio := (hamiltonPortPriority_order (by omega : 3 ≤ p) hwpre hwnext).2
      have hcross := hamilton_chord_crosses_later_port F hF hblocks hvw.symm hwnext
        (hpriority v (finRotate p v) w hprio)
      obtain ⟨z, hzham, hzedge⟩ := hcross
      refine ⟨v, finRotate p v, ?_, ?_, (fun h => hwnext h.symm), Or.inl rfl, z, hzedge, hzham⟩
      · exact (finRotate_ne_self_of_two_le (by omega : 2 ≤ p) v).symm
      · exact finRotate_ne_self_of_two_le (by omega : 2 ≤ p) v

end GraphMinor.GM12
