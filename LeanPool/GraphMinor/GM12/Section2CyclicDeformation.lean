/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section2CyclicReparametrization
import LeanPool.GraphMinor.GM07.Section11c

/-!
# Gluing the region deformations around the circle

For XII (2.1), Case 1, page 244, the homotopies of successive region
paths fix their common endpoints. They therefore match at every
time and join to a closed-curve homotopy. First read the original
curve on its chosen real region intervals, then join their deformations.
The whole construction stays in the prescribed union of visited
regions and vertices.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM07

/-- Homotopies of cyclic pieces fixing their ends glue to a homotopy
of their concatenated closed curves. -/
theorem concatLoop_homotopic_of_relative_piece_homotopies
    {S : Type*} [TopologicalSpace S] {Z : Set S} {n : ℕ} (hn : 0 < n)
    (γ δ : Fin n → C(unitInterval, S))
    (hγmatch : ∀ i, γ i 1 = γ (finNext hn i) 0)
    (hδmatch : ∀ i, δ i 1 = δ (finNext hn i) 0)
    (hpiece : ∀ i, CurvesHomotopicIn Z (γ i) (δ i)) :
    ClosedCurvesHomotopicIn Z (concatLoop hn γ hγmatch) (concatLoop hn δ hδmatch) := by
  choose H hHZ hH0 hH1 hleft _ hright _ using hpiece
  apply concatLoop_homotopic hn γ δ hγmatch hδmatch H hHZ hH0 hH1
  intro i s
  exact (hright i s).trans ((hγmatch i).trans (hleft (finNext hn i) s).symm)

/-- The region-by-region deformation in XII (2.1), Case 1, assembled
from real curve intervals and relative-endpoint homotopies of them. -/
theorem closedCurve_homotopic_to_deformed_real_pieces
    {S : Type*} [TopologicalSpace S] {φ : C(Circle, S)} {Z : Set S}
    (hφZ : range φ ⊆ Z) {n : ℕ} (hn : 0 < n) (a b : Fin n → ℝ)
    (hstep : ∀ i, b i = a (finNext hn i) + if i.val + 1 = n then 1 else 0)
    (γ δ : Fin n → C(unitInterval, S))
    (hγ : ∀ i t, γ i t = periodicCurve φ (a i + t.val * (b i - a i)))
    (hγmatch : ∀ i, γ i 1 = γ (finNext hn i) 0)
    (hδmatch : ∀ i, δ i 1 = δ (finNext hn i) 0)
    (hpiece : ∀ i, CurvesHomotopicIn Z (γ i) (δ i)) :
    ClosedCurvesHomotopicIn Z φ (concatLoop hn δ hδmatch) := by
  have hfirst := closedCurve_homotopic_to_cyclic_real_pieces hφZ hn a b hstep γ hγ hγmatch
  have hsecond := concatLoop_homotopic_of_relative_piece_homotopies hn γ δ hγmatch hδmatch hpiece
  exact GM07.closedCurvesHomotopicIn_trans' hfirst hsecond

end GraphMinor.GM12
