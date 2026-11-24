/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Corners

import LeanPool.GraphMinor.Surface.InvarianceOfDomain
import LeanPool.GraphMinor.Surface.DiscArcs

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
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have : T2Space S := hS.2.1
  obtain ⟨next, P, W, Q, hW, hvW, hinj, hne, hreach, hconn, hdis, hcl, hcov, hsid, hQ, hQQ, hoff,
    hbdU, τ, hτ, hτl, hτr⟩ := exists_rotation_sectors hS Γ hγ hv h2
  have hex : ∀ k, ∃ r ∈ Γ.R, P k ⊆ r := by
    intro k
    obtain ⟨x, hx⟩ : (P k).Nonempty := by
      by_contra h
      have h0 := not_nonempty_iff_eq_empty.mp h
      have := hcl k
      rw [h0] at this
      simp at this
    obtain ⟨r, hr, hxr⟩ := exists_region_of_notMem (disjoint_left.mp (hdis k) hx)
    exact ⟨r, hr, subset_region hr (hconn k) (hdis k) hx hxr⟩
  choose ρ hρ hsub using hex
  have hin : ∀ {r x}, r ∈ Γ.R → x ∈ r → ∀ k, x ∈ P k → r = ρ k := fun hr hx k hk =>
    region_eq_of_mem hr (hρ k) hx (hsub k hk)
  refine ⟨next, ρ, P, W, Q, τ, ⟨⟨hinj, hreach, hρ, fun k => closure_mono (hsub k) (hcl k), ?_, ?_,
    ?_, ?_⟩, hne, hW, hvW, hsub, hcov, fun k => (hQ k).2.2.1, fun k => (hQ k).1, fun k =>
      (hQ k).2.1, fun k => (hQ k).2.2.2, hQQ,
    hoff, hbdU, hτ, hτl, hτr⟩, ?_⟩
  · intro r hr hvr
    obtain ⟨x, hxW, hxr⟩ := mem_closure_iff.mp hvr W hW hvW
    obtain ⟨k, hk⟩ := mem_iUnion.mp (hcov ⟨hxW, region_subset hr hxr⟩)
    exact ⟨k, hin hr hxr k hk⟩
  · intro k
    obtain ⟨q, hq, O, -, -, -, h₁, -⟩ := hsid k
    exact edge_subset_closure_of_incident hS (next k).2.1 (hρ k)
      ⟨q, hq, closure_mono (hsub k) h₁⟩
  · intro k
    obtain ⟨q, hq, O, -, -, -, -, h₂⟩ := hsid k
    exact edge_subset_closure_of_incident hS (next k).2.1 (hρ _)
      ⟨q, hq, closure_mono (hsub _) h₂⟩
  · intro k r hr hsubr
    obtain ⟨q, hq, O, hO, hqO, hOs, -, -⟩ := hsid k
    obtain ⟨x, hxO, hxr⟩ := mem_closure_iff.mp (hsubr hq) O hO hqO
    rcases hOs ⟨hxO, region_subset hr hxr⟩ with h | h
    · exact Or.inl (hin hr hxr _ h)
    · exact Or.inr (hin hr hxr _ h)
  · intro x hx
    obtain ⟨k, hk⟩ := mem_iUnion.mp (hcov hx)
    exact mem_iUnion.mpr ⟨k, (hQ k).2.2.1 hk⟩

end GraphMinor.GM12
