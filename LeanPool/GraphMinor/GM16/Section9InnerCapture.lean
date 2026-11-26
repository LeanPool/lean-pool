/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Defs
public import LeanPool.GraphMinor.Surface.DiscGrow
import LeanPool.GraphMinor.GM16.InnerOpenDisc
import LeanPool.GraphMinor.GM16.Section6ZoneWalks
import LeanPool.GraphMinor.GM14.Section6a

/-!
# The captured zone lies inside the battlefield circuit

Identify the battlefield's capturing open disc with the interior of
its inner closed disc. Every atom of the smaller zone closure has
radius at most its zone parameter, so the battlefield's capture
condition puts the whole smaller closure inside this inner disc.
This is the first assertion in the subproof of XVI (8.1), Claim (11).
-/

public section
namespace GraphMinor.GM16
open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM14
universe u
variable {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]

/-- The zone in XVI (8.1), Claim (11), lies inside the inner
battlefield circuit when its radius is smaller than the battlefield size. -/
theorem section9_zone_inside_inner_disc (hS : IsClosedSurface S)
    {H C : Drawing S} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} {θ β γ : ℕ} {z Λ X M D₀ : Set S}
    (hB : IsBattlefield H T d θ β z Λ C X)
    (hD₀ : IsClosedDisc D₀) (hD₀D : D₀ ⊆ closure Λ) (hBd : discBd D₀ = C.U)
    (hM : IsLambdaZoneAround H d γ z M) (hγ : γ < β) :
    closure M ⊆ discInt D₀ := by
  obtain ⟨Ω, hΩ, hΩΛ, hΩbd, hCapture⟩ := hB.openDisc_includes
  have hbd : discBd (closure Λ) = subBd Λ := by
    rw [← IsClosedDisc.subBd_eq_discBd hS hB.isZone.isClosedDisc_closure,
      subBd_closure_eq_subBd_of_isOpenDisc hS hB.isZone.isOpenDisc
        hB.isZone.isOArc_bd hB.isZone.isClosedDisc_closure]
  have hDis : Disjoint Ω (discBd (closure Λ)) := by
    rw [hbd]
    exact ((isOpen_disjoint_subBd_and_closure_eq hB.isZone.isOpenDisc.1).1).mono_left hΩΛ
  have hEq : Ω = discInt D₀ := open_set_eq_discInt_of_boundary
    hB.isZone.isClosedDisc_closure hD₀ hD₀D hΩ.1
    hΩ.isPathConnected.isConnected (hΩΛ.trans subset_closure)
    (by rw [← subBd_eq_frontier, hΩbd, hBd]) hDis
  rw [← hEq]
  exact zone_closure_subset_of_atom_neighborhood hM
    (fun a ha hda => hCapture a ha (lt_of_le_of_lt (Nat.lt_succ_iff.mp hda) hγ))

end GraphMinor.GM16
