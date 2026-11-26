/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.RadialRegions
import LeanPool.GraphMinor.GM12.Section72RadialDeletion
import LeanPool.GraphMinor.GM11.RadialCorners

/-!
# Verifying maximality by testing possible extra spokes

For the maximality check in XII (7.2), page 260, it suffices to
compare each possible extra spoke with an existing parallel spoke.
An extension has the same vertices, since every region already has
its unique hub. Any new edge would then bound a forbidden empty
bigon with its old parallel spoke.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

variable {S : Type*} [TopologicalSpace S] [T2Space S]

omit [T2Space S] in
/-- An extension satisfying the radial conditions cannot add a
vertex: every old vertex and every region hub is already present. -/
theorem preRadial_vertices_eq_of_extension {Γ K J : Drawing S}
    (hK : (PaintingOrDrawing.drawing Γ).IsPreRadialDrawing K)
    (hJ : (PaintingOrDrawing.drawing Γ).IsPreRadialDrawing J)
    (hKJ : K.IsSubdrawing J) : J.V = K.V := by
  apply Subset.antisymm
  · intro w hw
    by_cases hwΓ : w ∈ Γ.V
    · exact hK.2.1 hwΓ
    · obtain ⟨r, hr, hwr⟩ := hJ.2.2.2.1 w ⟨hw, hwΓ⟩
      obtain ⟨u, hu, _⟩ := hK.2.2.1 r hr
      have hwu : w = u := (hJ.2.2.1 r hr).unique ⟨hwr, hw⟩ ⟨hu.1, hKJ.1 hu.2⟩
      exact hwu ▸ hu.2
  · exact hKJ.1

omit [T2Space S] in
/-- A pre-radial drawing is maximal if every possible extra spoke
bounds an empty disc with an old parallel spoke. This is the
criterion used to verify maximality in XII (7.2), page 260. -/
theorem radMax_of_parallel_spokes (hS : IsClosedSurface S)
    {Γ K : Drawing S} (htwo : (PaintingOrDrawing.drawing Γ).IsTwoCell)
    (hK : (PaintingOrDrawing.drawing Γ).IsPreRadialDrawing K)
    (hparallel : ∀ (r : Set S), r ∈ Γ.R → ∀ u ∈ r ∩ K.V, ∀ x ∈ Γ.V,
      ∀ L : Set S, IsLineWithEnds L u x → u ≠ x → L \ {u, x} ⊆ r →
      Disjoint (L \ {u, x}) K.U →
      ∃ e ∈ K.E, closure e ∩ K.V = {x, u} ∧
        ∃ D : Set S, IsClosedDisc D ∧ D ⊆ r ∪ {x} ∧ subBd D = closure e ∪ L) :
    RadMax (.drawing Γ) K := by
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  intro J hJ hKJ
  have hV := preRadial_vertices_eq_of_extension hK hJ hKJ
  refine ⟨hV.subset, ?_⟩
  intro g hg
  by_contra hgK
  obtain ⟨x, hx, r, hr, u, hur, huJ, hcap, hgr⟩ := spoke_ends ⟨htwo, hJ⟩ hS hg
  have huK : u ∈ K.V := hV.subset huJ
  have hux : u ≠ x := fun hux => region_subset hr (hux ▸ hur) (Γ.V_subset_U hx)
  have hline : IsLineWithEnds (closure g) u x :=
    Surface.IsLineWithEnds.symm (isLine_closure hg hux.symm hcap)
  have hpuncture : closure g \ {u, x} = g := by
    ext y
    constructor
    · rintro ⟨hyg, hyn⟩
      apply (J.closure_diff_V hg).subset
      exact ⟨hyg, fun hyJ => hyn (by rw [pair_comm]; exact hcap.subset ⟨hyg, hyJ⟩)⟩
    · intro hyg
      exact ⟨subset_closure hyg, fun hy => (hg.2.1 hyg).2
        ((hcap.superset (by rw [pair_comm]; exact hy)).2)⟩
  have hdis : Disjoint g K.U := by
    apply disjoint_left.mpr
    intro y hyg hyK
    exact hgK (edge_mem_of_meets_subdrawing hKJ hg ⟨y, hyg, hyK⟩)
  obtain ⟨e, he, hcape, D, hD, hDr, hbd⟩ := hparallel r hr u ⟨hur, huK⟩ x hx
    (closure g) hline hux (by rw [hpuncture]; exact hgr) (by rw [hpuncture]; exact hdis)
  have heg : e ≠ g := fun heg => hgK (heg ▸ he)
  have hcapeJ : closure e ∩ J.V = {x, u} := (hKJ.closure_inter_V he).symm.trans hcape
  exact hJ.2.2.2.2.2 e (hKJ.2 he) g hg heg x hx r hr u ⟨hur, huJ⟩
    hcapeJ hcap ⟨D, hD, hDr, hbd⟩

end GraphMinor.GM12
