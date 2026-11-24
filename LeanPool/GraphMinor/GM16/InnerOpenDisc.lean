/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.DiscGrow
import LeanPool.GraphMinor.GM11.Section7

/-!
# Identifying the open inside of a circle in a disc

An open connected set in a closed disc, with the same boundary as
an inner closed disc and missing the outer boundary, is the interior
of that inner disc. It is a component of the outer disc minus the
circle, and uniqueness of the inside determines that component.
This identifies the capturing open disc in XVI (8.1), Claim (11).
-/

public section
namespace GraphMinor.GM16
open Set Topology GraphMinor.Surface GraphMinor.GM11
universe u
variable {S : Type u} [TopologicalSpace S]

/-- The open inside is fixed by its circle and the containing disc. -/
theorem open_set_eq_discInt_of_boundary {D E Ω : Set S}
    (hD : IsClosedDisc D) (hE : IsClosedDisc E) (hED : E ⊆ D)
    (hΩ : IsOpen Ω) (hConn : IsConnected Ω) (hΩD : Ω ⊆ D)
    (hBd : frontier Ω = discBd E) (hDis : Disjoint Ω (discBd D)) :
    Ω = discInt E := by
  obtain ⟨E', hInside, hUnique⟩ := disc_oArc D (discBd E) hD
    ((Surface.discBd_subset E).trans hED) hE.isOArc_discBd
  have hEE' : E = E' := hUnique E hED hE rfl
  subst E'
  obtain ⟨x, hx⟩ := hConn.nonempty
  have hΩF : Ω ⊆ D \ discBd E := by
    intro z hz
    refine ⟨hΩD hz, ?_⟩
    intro hzb
    have hzf : z ∈ frontier Ω := hBd.symm ▸ hzb
    exact hzf.2 (hΩ.interior_eq.symm ▸ hz)
  have hxF := hΩF hx
  let A := connectedComponentIn (D \ discBd E) x
  have hAF : A ⊆ D \ discBd E := connectedComponentIn_subset _ _
  have hxA : x ∈ A := mem_connectedComponentIn hxF
  have hCover : A ⊆ Ω ∪ (closure Ω)ᶜ := by
    intro z hz
    by_cases hzΩ : z ∈ Ω
    · exact Or.inl hzΩ
    · right
      intro hzc
      rw [closure_eq_self_union_frontier, hBd] at hzc
      exact hzc.elim hzΩ (hAF hz).2
  have hAΩ : A ⊆ Ω :=
    isPreconnected_connectedComponentIn.subset_left_of_subset_union hΩ
      isClosed_closure.isOpen_compl
      (disjoint_left.mpr fun z hz hn => hn (subset_closure hz)) hCover ⟨x, hxA, hx⟩
  have hΩA : Ω ⊆ A := hConn.isPreconnected.subset_connectedComponentIn hx hΩF
  have hAeq : A = Ω := hAΩ.antisymm hΩA
  have hComp : Ω ∈ componentsIn (D \ discBd E) := by
    exact ⟨x, hxF, hAeq⟩
  exact hInside.2.2.2.2.2 Ω hComp hDis

end GraphMinor.GM16
