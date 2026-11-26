/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Sigma
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Card

/-!
# Enumerating the pairs of clique vertices

XII (4.4), page 251, numbers the external paths by the unordered
pairs of distinct clique vertices. Write such a pair with the
smaller vertex first. Grouping pairs by their larger vertex gives
the sum `0 + 1 + ... + (p - 1)`, hence `p * (p - 1) / 2` labels.
-/

public section

namespace GraphMinor.GM12

/-- The number of pairs of distinct vertices, represented by a
larger vertex and a smaller index, as used in XII (4.4). -/
theorem card_ordered_clique_pairs (p : ℕ) :
    Fintype.card (Σ j : Fin p, Fin j.val) = p * (p - 1) / 2 := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  calc
    (∑ i : Fin p, i.val) = ∑ i ∈ Finset.range p, i :=
      Fin.sum_univ_eq_sum_range (fun i : ℕ => i) p
    _ = p * (p - 1) / 2 := Finset.sum_range_id p

/-- The path labels of XII (4.4), page 251, can be put in bijection
with the pairs of distinct clique vertices. -/
theorem nonempty_clique_pair_enumeration (p : ℕ) :
    Nonempty (Fin (p * (p - 1) / 2) ≃ Σ j : Fin p, Fin j.val) := by
  exact ⟨Fintype.equivOfCardEq (by rw [Fintype.card_fin, card_ordered_clique_pairs])⟩

/-- A vertex of a clique with at least three vertices has two
distinct other vertices, as used in XII (4.4), page 252. -/
theorem exists_two_other_clique_vertices {p : ℕ} (hp : 3 ≤ p) (v : Fin p) :
    ∃ w z : Fin p, w ≠ v ∧ z ≠ v ∧ w ≠ z := by
  classical
  have hcard : 1 < (Finset.univ.erase v).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨w, hw, z, hz, hwz⟩ := Finset.one_lt_card.mp hcard
  exact ⟨w, z, (Finset.mem_erase.mp hw).1, (Finset.mem_erase.mp hz).1, hwz⟩

end GraphMinor.GM12
