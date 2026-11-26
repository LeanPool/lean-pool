/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section4EndPartition
import LeanPool.GraphMinor.GM12.Section4SourceResiduals
import LeanPool.GraphMinor.GM12.Section4DisjointArcDiscs
import LeanPool.GraphMinor.Surface.DiscGrow

/-!
# A source disc system for the target drawing

For XII (4.3), claim (7), page 251, thicken the disjoint
residual edges while forbidding all vertex discs. The edge discs
are mutually disjoint and touch the vertex discs only at their
marked ends. A marked end belongs to exactly its assigned vertex
disc, since the vertex discs are disjoint. Thus their intersections
are precisely the oriented end classes used in (3.2).
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- The source vertex and marked edge discs in XII (4.3), claim
(7), page 251, with their exact oriented contact classes. -/
theorem exists_source_disc_system
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (Γ : Drawing S) (u v : Γ.E → Γ.V)
    (hl : ∀ e, Γ.toGraph.IsLink e.val (u e).val (v e).val)
    (hne : ∀ e, u e ≠ v e) :
    ∃ (D : Γ.V → Set S) (Δ : Γ.E → Set S) (a b : Γ.E → S),
      (∀ w, IsClosedDisc (D w)) ∧
      (∀ w z, w ≠ z → Disjoint (D w) (D z)) ∧
      (∀ e, IsClosedDisc (Δ e) ∧ a e ≠ b e ∧ ({a e, b e} : Set S) ⊆ discBd (Δ e)) ∧
      (∀ e f, e ≠ f → Disjoint (Δ e) (Δ f)) ∧
      ∀ w, D w ∩ ⋃ e, Δ e =
        edgeEndClass (fun q : Γ.E × Bool => if q.2 then a q.1 else b q.1)
          (fun q : Γ.E × Bool => if q.2 then u q.1 else v q.1) w := by
  classical
  let : Finite Γ.V := Γ.finite_V.to_subtype
  let : Finite Γ.E := Γ.finite_edges.to_subtype
  obtain ⟨D, c, hD, hDD, hc, hcc⟩ := exists_source_residual_arc_family hS Γ u v hl hne
  let B : Set S := ⋃ w, D w
  have hB : IsClosed B := isClosed_iUnion_of_finite fun w => (hD w).1.isClosed
  have hcontact : ∀ e : Γ.E, range (c e) ∩ B = {c e 0, c e 1} := by
    intro e
    apply Set.Subset.antisymm
    · rintro z ⟨hzc, hzB⟩
      obtain ⟨w, hzw⟩ := mem_iUnion.mp hzB
      by_cases hwu : w = u e
      · subst w
        exact Or.inl (Set.mem_singleton_iff.mp ((hc e).2.2.2.2.1.subset ⟨hzc, hzw⟩))
      · by_cases hwv : w = v e
        · subst w
          exact Or.inr (Set.mem_singleton_iff.mpr
            (Set.mem_singleton_iff.mp ((hc e).2.2.2.2.2.1.subset ⟨hzc, hzw⟩)))
        · exact False.elim (Set.disjoint_left.mp ((hc e).2.2.2.2.2.2.2 w hwu hwv) hzc hzw)
    · intro z hz
      rcases hz with hz | hz
      · exact hz ▸ ⟨mem_range_self 0, mem_iUnion.mpr ⟨u e, discBd_subset _ (hc e).2.2.1⟩⟩
      · have hz' := Set.mem_singleton_iff.mp hz
        exact hz' ▸ ⟨mem_range_self 1, mem_iUnion.mpr ⟨v e, discBd_subset _ (hc e).2.2.2.1⟩⟩
  obtain ⟨Δ, hΔ, hΔΔ⟩ := exists_disjoint_arc_discs hS (toFinite (univ : Set Γ.E)) c
    (fun e _ => (hc e).1) (fun e _ f _ hef => hcc e f hef) B hB (fun e _ => hcontact e)
  have hΔ' := fun e => hΔ e (mem_univ e)
  have hΔΔ' := fun e f hef => hΔΔ e (mem_univ e) f (mem_univ f) hef
  have hend0 : ∀ e, c e 0 ∈ D (u e) := fun e => discBd_subset _ (hc e).2.2.1
  have hend1 : ∀ e, c e 1 ∈ D (v e) := fun e => discBd_subset _ (hc e).2.2.2.1
  have howner0 : ∀ e w, c e 0 ∈ D w → u e = w := by
    intro e w hw
    by_contra hne'
    exact Set.disjoint_left.mp (hDD (u e) w hne') (hend0 e) hw
  have howner1 : ∀ e w, c e 1 ∈ D w → v e = w := by
    intro e w hw
    by_contra hne'
    exact Set.disjoint_left.mp (hDD (v e) w hne') (hend1 e) hw
  refine ⟨D, Δ, (fun e => c e 0), (fun e => c e 1), fun w => (hD w).1, hDD, ?_, hΔΔ', ?_⟩
  · intro e
    refine ⟨(hΔ' e).1, ?_, (hΔ' e).2.2.1⟩
    intro heq
    exact (show (0 : unitInterval) ≠ 1 by norm_num) ((hc e).1.2 heq)
  · intro w
    apply Set.Subset.antisymm
    · rintro z ⟨hzw, hzΔ⟩
      obtain ⟨e, hze⟩ := mem_iUnion.mp hzΔ
      have hzends := (hΔ' e).2.1.subset ⟨hze, mem_iUnion.mpr ⟨w, hzw⟩⟩
      rcases hzends with hz0 | hz1
      · exact ⟨(e, true), howner0 e w (hz0 ▸ hzw), hz0.symm⟩
      · have hz1' := Set.mem_singleton_iff.mp hz1
        exact ⟨(e, false), howner1 e w (hz1' ▸ hzw), hz1'.symm⟩
    · rintro z ⟨⟨e, b⟩, hew, hez⟩
      cases b
      · change v e = w at hew
        change c e 1 = z at hez
        exact hez ▸ ⟨hew ▸ hend1 e,
          mem_iUnion.mpr ⟨e, (hΔ' e).2.2.2 (mem_range_self 1)⟩⟩
      · change u e = w at hew
        change c e 0 = z at hez
        exact hez ▸ ⟨hew ▸ hend0 e,
          mem_iUnion.mpr ⟨e, (hΔ' e).2.2.2 (mem_range_self 0)⟩⟩

end GraphMinor.GM12
