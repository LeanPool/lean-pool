/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Corners

/-!
# Retaining the neighbourhood cover in the sector construction

For the entry definition of XII page 243, one needs both the sector
properties and their cover of the neighbourhood off the drawing. This
is XI's rotation-sector construction, with the cover retained in the
conclusion when its connected pieces are assigned their regions.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11 unitInterval

universe u
variable {S : Type u} [TopologicalSpace S]

/-- XI's sector construction with its cover of the neighbourhood off
the drawing retained, for use in XII's entry-edge existence proof. -/
theorem exists_sectors_with_cover (hS : IsClosedSurface S) (Γ : Drawing S) {γ : Set S → I → S}
  (hγ : EdgePar Γ γ) {v : S}
    (hv : v ∈ Γ.V) (h2 : 2 ≤ Nat.card (halfEdges Γ γ v)) :
    ∃ next ρ P W Q τ, IsSectors Γ γ v next ρ P W Q τ ∧ W \ Γ.U ⊆ ⋃ k, Q k := by
  obtain ⟨next, ρ, P, W, Q, τ, h⟩ := GM11.exists_sectors hS Γ hγ hv h2
  refine ⟨next, ρ, P, W, Q, τ, h, ?_⟩
  exact h.cover.trans (iUnion_mono h.subQ)

end GraphMinor.GM12
