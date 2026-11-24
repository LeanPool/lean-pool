/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3OneCuffCandidate
public import LeanPool.GraphMinor.GM12.Section3TwoCuffCandidate

import LeanPool.GraphMinor.GM07.Section7
import LeanPool.GraphMinor.GM07.Bridge

/-!
# Existence of the alpha minimum's candidates

For XII (3.1), page 245, a nonempty deletion family has either one
member or two distinct members. The one-disc case is on a surface
other than the sphere and uses a normal essential circle. In the
other case, two cuff circles and a normal joining line give a
candidate. Thus the alpha estimate no longer needs an existence
hypothesis about the drawing.
-/

public section

namespace GraphMinor.GM12

open Set Surface

universe u

/-- Alpha candidates exist for every nonempty disc deletion family
in the setup of XII (3.1). The geometric construction proves existence
rather than adding it to the drawing or surface data. -/
theorem exists_alphaCandidate_in_discComplement
    {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {t : ℕ} (ht : t ≠ 0)
    (hcase : ¬ IsSphere S ∨ 3 ≤ t) (Γ : Drawing S) (Δ : Fin t → Set S)
    (hΔ : ∀ i, IsClosedDisc (Δ i))
    (hdisj : Pairwise (fun i j => Disjoint (Δ i) (Δ j)))
    (havoid : ∀ i, Γ.U ∩ Δ i = Γ.V ∩ discBd (Δ i)) :
    ∃ X, GM07.IsAlphaCandidate (drawingInSubspace Γ (discComplement Δ)
      (drawing_support_subset_discComplement hS Γ Δ hΔ hdisj havoid)) X := by
  by_cases ht1 : t = 1
  · subst t
    have hns : ¬ IsSphere S := by
      rcases hcase with hns | hthree
      · exact hns
      · exact (by omega : False).elim
    exact exists_alphaCandidate_one_disc_of_not_sphere hS hns Γ Δ hΔ hdisj havoid
  · have htwo : 2 ≤ t := by omega
    let i : Fin t := ⟨0, by omega⟩
    let j : Fin t := ⟨1, by omega⟩
    have hij : i ≠ j := fun he => Nat.zero_ne_one (congrArg Fin.val he)
    have hcase' : ¬ IsSphere S ∨ 3 ≤ Nat.card (Fin t) := by rwa [Nat.card_fin]
    exact exists_alphaCandidate_of_two_prescribed_cuffs hS Γ Δ hΔ hdisj hcase' havoid hij

end GraphMinor.GM12
