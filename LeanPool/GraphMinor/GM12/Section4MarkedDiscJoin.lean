/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.PlaneDisc
import LeanPool.GraphMinor.GM07.JoinDiscs

/-!
# Joining source discs while preserving boundary contacts

In the source feasibility construction of XII (4.5), claim (1),
page 253, the thin discs around residual edge halves are joined
to their vertex discs. When two discs meet at one boundary point,
round their union in a neighborhood of that point. Choose the
neighborhood inside a prescribed open set and away from the
closed set of crossing discs. This keeps all contacts with that
closed set, including their boundary status.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- Joining two discs at a boundary point preserves their exact
contacts with any closed set avoiding that point. The joined
disc stays inside a prescribed open neighborhood. This is used
to thicken the vertex stars in XII (4.5), claim (1), page 253. -/
theorem exists_join_preserving_contacts {S : Type} [TopologicalSpace S]
    (hS : IsClosedSurface S) {A B U Z : Set S} {p : S}
    (hA : IsClosedDisc A) (hB : IsClosedDisc B) (hAB : A ∩ B = {p})
    (hpA : p ∈ discBd A) (hpB : p ∈ discBd B)
    (hU : IsOpen U) (hAU : A ⊆ U) (hBU : B ⊆ U)
    (hZ : IsClosed Z) (hpZ : p ∉ Z) :
    ∃ D : Set S, IsClosedDisc D ∧ A ∪ B ⊆ D ∧ D ⊆ U ∧
      D ∩ Z = (A ∪ B) ∩ Z ∧ (discBd A ∪ discBd B) ∩ Z ⊆ discBd D := by
  obtain ⟨D, hd, hsub, hbound, -, hkeep, -⟩ := GM07.exists_join hS hA hB hAB hpA hpB
    (hU.inter hZ.isOpen_compl) ⟨hAU (GM11.discBd_subset A hpA), hpZ⟩
  refine ⟨D, hd, hsub, ?_, ?_, ?_⟩
  · intro z hz
    rcases hbound hz with h | h
    · exact h.elim (fun hzA => hAU hzA) (fun hzB => hBU hzB)
    · exact h.1
  · apply Subset.antisymm
    · rintro z ⟨hzD, hzZ⟩
      rcases hbound hzD with hz | hz
      · exact ⟨hz, hzZ⟩
      · exact False.elim (hz.2 hzZ)
    · rintro z ⟨hz, hzZ⟩
      exact ⟨hsub hz, hzZ⟩
  · rintro z ⟨hz, hzZ⟩
    exact hkeep ⟨hz, fun h => h.2 hzZ⟩

end GraphMinor.GM12
