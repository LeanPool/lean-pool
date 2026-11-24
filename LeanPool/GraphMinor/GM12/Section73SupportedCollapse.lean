/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section73RadialStar
import LeanPool.GraphMinor.GM11.Theorem75
import LeanPool.GraphMinor.Surface.Collar
import LeanPool.GraphMinor.Surface.DiscGrow

/-!
# Keeping the star collapse inside a smaller closed disc

The radial-star contraction in XII (7.3), page 261, can be
performed inside a closed disc contained in the merged region.
The finite star is compact. Enclose it in a disc in that region,
then enlarge the disc slightly so the star lies in its interior.
Apply the star collapse fixing the complement of this interior.
This gives the fixed boundary needed to compare selected insides.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- Choose the radial-star contraction with support in a closed
disc lying in the merged region. The star lies in the interior
of this disc and the contraction fixes its boundary and outside.
This refines the topological construction of XII (7.3), page 261. -/
theorem exists_radial_star_collapse_supported_in_disc
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ K : Drawing S}
    (hK : PreRad (PaintingOrDrawing.drawing Γ) K) {v : S} (hv : v ∈ Γ.V)
    (hunique : ∀ e ∈ K.E, ∀ g ∈ K.E, ∀ u : S,
      K.toGraph.IsLink e v u → K.toGraph.IsLink g v u → e = g)
    {r : Set S} (hr : r ∈ (deleteVertices Γ {v}).R) (hvr : v ∈ r)
    (hropen : IsOpenDisc r) :
    ∃ (D : Set S) (f : C(S, S)), IsClosedDisc D ∧ D ⊆ r ∧
      ({v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e) ⊆ discInt D ∧
      Function.Surjective f ∧ (∀ x ∉ discInt D, f x = x) ∧
      (∀ x ∈ {v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e, f x = v) ∧
      (∀ x y, f x = f y ↔ x = y ∨
        (x ∈ {v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e) ∧
        (y ∈ {v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e)) := by
  let : CompactSpace S := hS.1
  let : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  let E : Set (Set S) := {e ∈ K.E | v ∈ closure e}
  let A : Set S := {v} ∪ ⋃ e ∈ E, closure e
  have hE : E.Finite := K.finite_edges.subset fun _ he => he.1
  have hAc : IsCompact A := isCompact_singleton.union
    (hE.isCompact_biUnion fun _ _ => isClosed_closure.isCompact)
  have hAr : A ⊆ r := radial_star_subset_deleted_region hS hK hv hr hvr
  obtain ⟨D₀, hD₀, hD₀r, hAD₀⟩ := exists_closedDisc_of_isCompact hropen hAc hAr
  have hman : ∀ x : S, IsManifoldPoint x := fun x => (hS.2.2 x).isManifoldPoint
  obtain ⟨D, hD, hD₀D, hDsub⟩ := exists_disc_around hman hD₀
    (fun x _ => hS.2.2 x) hropen.1 ((Surface.discBd_subset D₀).trans hD₀r)
  have hDr : D ⊆ r := hDsub.trans (union_subset hD₀r subset_rfl)
  have hAD : A ⊆ discInt D := hAD₀.trans hD₀D
  obtain ⟨hlines, hmeet⟩ := radial_star_lines_and_intersections hS hK hv hunique
  have havoid : Disjoint A (discInt D)ᶜ := disjoint_left.mpr fun x hx hxn => hxn (hAD hx)
  obtain ⟨f, hsurj, hfix, hcollapse, hfibre⟩ := exists_star_collapse hS hE closure v
    hlines hmeet (hD.isOpen_discInt hman).isClosed_compl havoid
  exact ⟨D, f, hD, hDr, hAD, hsurj, hfix, hcollapse, hfibre⟩

end GraphMinor.GM12
