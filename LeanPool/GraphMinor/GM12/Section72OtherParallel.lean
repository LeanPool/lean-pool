/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section72RetainedBoundary
public import LeanPool.GraphMinor.GM11.RadialRegions
import LeanPool.GraphMinor.GM11.Section810

/-!
# Parallel spokes in unchanged regions

For maximality in XII (7.2), page 260, an extra spoke in an unchanged
old region misses the removed disc. It also misses the old radial
drawing in its interior, since all old radial points there survive.
Old maximality supplies a parallel spoke. Its region end is outside
the removed disc, so that spoke survives as well.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- An extra spoke in an unchanged region has a retained old
parallel spoke, as required for maximality in XII (7.2), page 260. -/
theorem exists_parallel_spoke_in_unchanged_region
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) {Γ K C : Drawing S}
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K) (hC : C.IsSubdrawing K)
    {D f s : Set S} (hD : IsClosedDisc D) (hb : frontier D = C.U) (hf : f ∈ C.E)
    (hs : s ∈ Γ.R) (hsD : Disjoint s D) {w x : S}
    (hw : w ∈ s ∩ (radialDiscDeletion K D f).V)
    (hx : x ∈ (Γ.interSet (closure (univ \ D))).V)
    {L : Set S} (hL : IsLineWithEnds L w x) (hwx : w ≠ x)
    (hLs : L \ {w, x} ⊆ s) (hLK : Disjoint (L \ {w, x}) (radialDiscDeletion K D f).U) :
    ∃ g ∈ (radialDiscDeletion K D f).E,
      closure g ∩ (radialDiscDeletion K D f).V = {x, w} ∧
      ∃ Q : Set S, IsClosedDisc Q ∧ Q ⊆ s ∪ {x} ∧ subBd Q = closure g ∪ L := by
  have hKK := radialDiscDeletion_isSubdrawing K D f
  have hfD : f ⊆ D := by
    intro y hy
    have hybd : y ∈ frontier D := hb.symm ▸ (hf.2.1 hy).1
    exact hD.isClosed.closure_subset_iff.mpr subset_rfl hybd.1
  have hdisOld : Disjoint (L \ {w, x}) K.U := by
    apply disjoint_left.mpr
    intro y hyL hyK
    have hyD : y ∉ D := disjoint_left.mp hsD (hLs hyL)
    have hyK' : y ∈ (radialDiscDeletion K D f).U := by
      rw [radialDiscDeletion_U hC hb hf]
      exact ⟨⟨hyK, subset_closure ⟨mem_univ _, hyD⟩⟩, fun hyf => hyD (hfD hyf)⟩
    exact disjoint_left.mp hLK hyL hyK'
  have hxΓ : x ∈ Γ.V := (mem_interSet_V_iff isClosed_closure).mp hx |>.1
  obtain ⟨g, hg, hcap, Q, hQ, hQs, hQbd⟩ := parallel_of_line ⟨hK.1, hK.2.1⟩ hK.2.2 hS
    hs hw.1 (hKK.1 hw.2) hxΓ hL hwx hLs hdisOld
  have hwcl : w ∈ closure g := (hcap.superset (Or.inr rfl)).1
  have hgNew := edge_retained_of_end_outside_disc hS hC hD hb hf hg hwcl
    (disjoint_left.mp hsD hw.1)
  exact ⟨g, hgNew, (hKK.closure_inter_V hgNew).trans hcap, Q, hQ, hQs, hQbd⟩

end GraphMinor.GM12
