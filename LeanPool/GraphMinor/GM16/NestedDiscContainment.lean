/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.DiscArcs

/-!
# Containment from nested boundaries

Inside a fixed closed disc a circle bounds only one closed disc.
Consequently, a smaller closed disc is contained in any other closed
disc there that contains its boundary. This places the battlefield's
inner disc inside the discs of the nest in XVI (8.1), Claim (11).
-/

public section
namespace GraphMinor.GM16
open Set GraphMinor.Surface
universe u
variable {S : Type u} [TopologicalSpace S]

/-- Among closed discs inside a fixed disc, containment of one
boundary in another disc implies containment of its whole disc. -/
theorem closedDisc_subset_of_boundary_subset {D E E₀ : Set S}
    (hD : IsClosedDisc D) (hE : IsClosedDisc E) (hE₀ : IsClosedDisc E₀)
    (hED : E ⊆ D) (hE₀D : E₀ ⊆ D) (hbd : discBd E₀ ⊆ E) : E₀ ⊆ E := by
  obtain ⟨F, hF, _⟩ := disc_oArc E (discBd E₀) hE hbd hE₀.isOArc_discBd
  obtain ⟨G, _, hu⟩ := disc_oArc D (discBd E₀) hD
    ((discBd_subset E₀).trans hE₀D) hE₀.isOArc_discBd
  have h₀ : E₀ = G := hu E₀ hE₀D hE₀ rfl
  have h₁ : F = G := hu F (hF.1.trans hED) hF.2.1 hF.2.2.1
  rw [h₀, ← h₁]
  exact hF.1

end GraphMinor.GM16
