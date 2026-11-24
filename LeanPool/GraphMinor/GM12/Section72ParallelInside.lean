/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section72PreRadial
import LeanPool.GraphMinor.GM11.RadialBasics
import LeanPool.GraphMinor.GM11.RadialCorners
import LeanPool.GraphMinor.Surface.DiscArcs
import LeanPool.GraphMinor.Surface.DiscGrow

/-!
# An old empty bigon cannot contain another parallel spoke

For the maximality step in XII (7.2), page 260, a new spoke is
compared with an old parallel spoke. The disc between them lies in
an old region with one boundary vertex restored. It cannot contain
a third old parallel spoke: that spoke and the old boundary spoke
would bound a disc there, contrary to the old radial condition.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

variable {S : Type*} [TopologicalSpace S] [T2Space S]

/-- Two distinct old parallel spokes cannot both lie in a closed
disc in their old region with the boundary vertex restored. This is
used in the maximality verification of XII (7.2), page 260. -/
theorem not_parallel_spokes_in_region_disc (hS : IsClosedSurface S)
    {Γ K : Drawing S} (hK : (PaintingOrDrawing.drawing Γ).IsPreRadialDrawing K)
    {g h Q r : Set S} {x u : S} (hg : g ∈ K.E) (hh : h ∈ K.E) (hgh : g ≠ h)
    (hx : x ∈ Γ.V) (hr : r ∈ Γ.R) (hur : u ∈ r) (huK : u ∈ K.V)
    (hcapg : closure g ∩ K.V = {x, u}) (hcaph : closure h ∩ K.V = {x, u})
    (hQ : IsClosedDisc Q) (hQr : Q ⊆ r ∪ {x})
    (hgQ : closure g ⊆ Q) (hhQ : closure h ⊆ Q) : False := by
  have hxu : x ≠ u := fun heq => region_subset hr (heq ▸ hur) (Γ.V_subset_U hx)
  have hLg := isLine_closure hg hxu hcapg
  have hLh := isLine_closure hh hxu hcaph
  have hmeet : closure g ∩ closure h ⊆ {x, u} := fun z hz =>
    hcapg.subset ⟨hz.1, closure_inter_subset_V hg hh hgh hz⟩
  have hcircle := isOArc_union hLg hLh hmeet
  obtain ⟨P, hP, _⟩ := disc_oArc Q (closure g ∪ closure h) hQ
    (union_subset hgQ hhQ) hcircle
  have hPbd : subBd P = closure g ∪ closure h :=
    (subBd_eq_frontier P).trans
      ((IsClosedDisc.frontier_eq_discBd hS hP.2.1).trans hP.2.2.1)
  exact hK.2.2.2.2.2 g hg h hh hgh x hx r hr u ⟨hur, huK⟩ hcapg hcaph
    ⟨P, hP.2.1, hP.1.trans hQr, hPbd⟩

/-- Every third old parallel spoke misses a disc between an old
spoke and a new line. Otherwise connectedness puts the whole spoke
in the disc, giving the forbidden old empty bigon. -/
theorem parallel_spoke_disjoint_region_bigon (hS : IsClosedSurface S)
    {Γ K : Drawing S} (hK : (PaintingOrDrawing.drawing Γ).IsPreRadialDrawing K)
    {g h L Q r : Set S} {x u : S} (hg : g ∈ K.E) (hh : h ∈ K.E) (hgh : g ≠ h)
    (hx : x ∈ Γ.V) (hr : r ∈ Γ.R) (hur : u ∈ r) (huK : u ∈ K.V)
    (hcapg : closure g ∩ K.V = {x, u}) (hcaph : closure h ∩ K.V = {x, u})
    (hQ : IsClosedDisc Q) (hQr : Q ⊆ r ∪ {x}) (hbd : discBd Q = closure h ∪ L)
    (hLK : Disjoint (L \ {x, u}) K.U) : Disjoint g Q := by
  have hdis : Disjoint g (discBd Q) := by
    apply disjoint_left.mpr
    intro z hzg hzb
    rw [hbd] at hzb
    rcases hzb with hzh | hzL
    · exact (hg.2.1 hzg).2 (closure_inter_subset_V hg hh hgh ⟨subset_closure hzg, hzh⟩)
    · have hzn : z ∉ ({x, u} : Set S) := fun hz =>
        (hg.2.1 hzg).2 ((hcapg.superset hz).2)
      exact disjoint_left.mp hLK ⟨hzL, hzn⟩ (hg.2.1 hzg).1
  have hman : ∀ z : S, IsManifoldPoint z := fun z => (hS.2.2 z).isManifoldPoint
  rcases hQ.side hman hg.2.2.1.isConnected.isPreconnected hdis with hin | hout
  · have hgQ : closure g ⊆ Q := closure_minimal (hin.trans (discInt_subset Q)) hQ.isClosed
    have hhQ : closure h ⊆ Q := (hbd.symm ▸ subset_union_left).trans (Surface.discBd_subset Q)
    exact (not_parallel_spokes_in_region_disc hS hK hg hh hgh hx hr hur huK
      hcapg hcaph hQ hQr hgQ hhQ).elim
  · exact hout

end GraphMinor.GM12
