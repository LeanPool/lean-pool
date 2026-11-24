/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Defs
public import LeanPool.GraphMinor.Surface.CrossCut
import LeanPool.GraphMinor.GM12.Section4VertexDiscs
import LeanPool.GraphMinor.GM12.Section4ResidualArc
import LeanPool.GraphMinor.GM11.RadialCorners
import LeanPool.GraphMinor.GM11.Section7
import LeanPool.GraphMinor.Surface.DiscGrow

/-!
# The residual edges of the target drawing

In XII (4.3), claim (7), page 251, small vertex discs leave
a disjoint residual arc for each edge. Choose each arc between its
last visit to its first endpoint disc and its first later visit to
the other. Nonincident vertex discs miss the whole edge. The
residual arc misses the original vertices, since its disc contacts
are frontier points while the original vertices are interior
points. Different residual arcs are therefore disjoint.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- The source residual-edge system of XII (4.3), claim (7),
page 251, for a loopless target drawing with oriented ends. -/
theorem exists_source_residual_arc_family
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) (Γ : Drawing S) (u v : Γ.E → Γ.V)
    (hl : ∀ e, Γ.toGraph.IsLink e.val (u e).val (v e).val)
    (hne : ∀ e, u e ≠ v e) :
    ∃ (D : Γ.V → Set S) (b : Γ.E → unitInterval → S),
      (∀ w, IsClosedDisc (D w) ∧ w.val ∈ interior (D w)) ∧
      (∀ w z, w ≠ z → Disjoint (D w) (D z)) ∧
      (∀ e, IsArcMap (b e) ∧ range (b e) ⊆ closure e.val ∧
        b e 0 ∈ discBd (D (u e)) ∧ b e 1 ∈ discBd (D (v e)) ∧
        range (b e) ∩ D (u e) = {b e 0} ∧ range (b e) ∩ D (v e) = {b e 1} ∧
        Disjoint (range (b e)) Γ.V ∧
        ∀ w, w ≠ u e → w ≠ v e → Disjoint (range (b e)) (D w)) ∧
      (∀ e f, e ≠ f → Disjoint (range (b e)) (range (b f))) := by
  classical
  obtain ⟨D, hD, hDD⟩ := exists_vertex_disc_family hS Γ
  have hex : ∀ e : Γ.E, ∃ b : unitInterval → S,
      IsArcMap b ∧ range b ⊆ closure e.val ∧
        b 0 ∈ frontier (D (u e)) ∧ b 1 ∈ frontier (D (v e)) ∧
        range b ∩ D (u e) = {b 0} ∧ range b ∩ D (v e) = {b 1} := by
    intro e
    have huv : (u e).val ≠ (v e).val := fun h => hne e (Subtype.ext h)
    have hline := isLine_closure e.property huv (hl e).2.2.2
    obtain ⟨a, ha, har, ha0, ha1⟩ := hline.exists_arc
    obtain ⟨b, hb, hba, hb0, hb1, hbD, hbE⟩ := exists_residual_arc_between_closed_sets ha
      (hD (u e)).1.isClosed (hD (v e)).1.isClosed (hDD (u e) (v e) (hne e))
      (ha0 ▸ interior_subset (hD (u e)).2.1) (ha1 ▸ interior_subset (hD (v e)).2.1)
    exact ⟨b, hb, hba.trans har.subset, hb0, hb1, hbD, hbE⟩
  choose b hb hsub hb0 hb1 hbD hbE using hex
  have hmissV : ∀ e, Disjoint (range (b e)) Γ.V := by
    intro e
    apply Set.disjoint_left.mpr
    intro z hzb hzV
    have hzends : z ∈ ({(u e).val, (v e).val} : Set S) := (hl e).2.2.2 ▸ ⟨hsub e hzb, hzV⟩
    rcases hzends with hzu | hzv
    · have hzDu : z ∈ D (u e) := hzu ▸ interior_subset (hD (u e)).2.1
      have hz0 : z = b e 0 := Set.mem_singleton_iff.mp ((hbD e).subset ⟨hzb, hzDu⟩)
      have hzint : z ∈ interior (D (u e)) := hzu ▸ (hD (u e)).2.1
      exact (hb0 e).2 (hz0 ▸ hzint)
    · have hzv' := Set.mem_singleton_iff.mp hzv
      have hzDv : z ∈ D (v e) := hzv' ▸ interior_subset (hD (v e)).2.1
      have hz1 : z = b e 1 := Set.mem_singleton_iff.mp ((hbE e).subset ⟨hzb, hzDv⟩)
      have hzint : z ∈ interior (D (v e)) := hzv' ▸ (hD (v e)).2.1
      exact (hb1 e).2 (hz1 ▸ hzint)
  have hoff : ∀ e w, w ≠ u e → w ≠ v e → Disjoint (range (b e)) (D w) := by
    intro e w hwu hwv
    have hnot : ¬ Γ.toGraph.Inc e.val w.val := by
      intro hinc
      rcases hinc.eq_or_eq_of_isLink (hl e) with hw | hw
      · exact hwu (Subtype.ext hw)
      · exact hwv (Subtype.ext hw)
    exact ((hD w).2.2.2 e.val e.property hnot).symm.mono_left (hsub e)
  refine ⟨D, b, fun w => ⟨(hD w).1, (hD w).2.1⟩, hDD, ?_, ?_⟩
  · intro e
    have hbd0 : b e 0 ∈ discBd (D (u e)) := by
      have h := hb0 e
      rwa [GM11.IsClosedDisc.frontier_eq_discBd hS (hD (u e)).1] at h
    have hbd1 : b e 1 ∈ discBd (D (v e)) := by
      have h := hb1 e
      rwa [GM11.IsClosedDisc.frontier_eq_discBd hS (hD (v e)).1] at h
    exact ⟨hb e, hsub e, hbd0, hbd1, hbD e, hbE e, hmissV e, hoff e⟩
  · intro e f hef
    have hef' : e.val ≠ f.val := fun h => hef (Subtype.ext h)
    apply Set.disjoint_left.mpr
    intro z hze hzf
    have hzV := closure_inter_subset_V e.property f.property hef' ⟨hsub e hze, hsub f hzf⟩
    exact Set.disjoint_left.mp (hmissV e) hze hzV

end GraphMinor.GM12
