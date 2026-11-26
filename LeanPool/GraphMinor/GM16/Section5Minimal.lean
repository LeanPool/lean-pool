/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.ForestMarked
import Mathlib.Order.Minimal

/-!
# Choosing the forest in XVI (5.3)

Choose a subgraph with as few edges as possible while keeping the marked
vertices in the same components. A spanning forest of this subgraph keeps
the required connections and has no more edges. Minimality makes it the
whole subgraph, proving that the chosen subgraph is a forest.
-/

public section
namespace GraphMinor.GM16
open Set SimpleGraph
universe u

/-- The minimal-subgraph step in the proof of XVI (5.3), page 56.
All vertices are retained, including unused isolated vertices. They do
not affect the marked vertices or the paths used in the proof. -/
theorem exists_minimal_marked_forest {V : Type u} [Finite V]
    (G : SimpleGraph V) (Y : Set V) :
    ∃ F ≤ G, F.IsAcyclic ∧
      ∀ a ∈ Y, ∀ b ∈ Y, G.Reachable a b → F.Reachable a b := by
  classical
  let := Fintype.ofFinite V
  let P : SimpleGraph V → Prop := fun F =>
    F ≤ G ∧ ∀ a ∈ Y, ∀ b ∈ Y, G.Reachable a b → F.Reachable a b
  obtain ⟨F, hF⟩ := exists_minimalFor_of_wellFoundedLT P
    (fun F => F.edgeFinset.card) ⟨G, le_rfl, fun _ _ _ _ h => h⟩
  obtain ⟨H, hHF, hH, hreach⟩ := F.exists_isAcyclic_reachable_eq_le
  have hHP : P H := by
    refine ⟨hHF.trans hF.1.1, ?_⟩
    intro a ha b hb hab
    rw [hreach]
    exact hF.1.2 a ha b hb hab
  have hcard := hF.2 hHP (Finset.card_le_card (edgeFinset_mono hHF))
  have heq : H.edgeFinset = F.edgeFinset :=
    Finset.eq_of_subset_of_card_le (edgeFinset_mono hHF) hcard
  have hFH : F ≤ H := edgeFinset_subset_edgeFinset.mp (le_of_eq heq.symm)
  have hFH_eq : F = H := le_antisymm hFH hHF
  exact ⟨F, hF.1.1, hFH_eq ▸ hH, hF.1.2⟩

end GraphMinor.GM16
