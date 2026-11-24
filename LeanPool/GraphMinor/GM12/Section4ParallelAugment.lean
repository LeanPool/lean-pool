/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Defs
import LeanPool.GraphMinor.GM12.Section4ParallelFamily
import LeanPool.GraphMinor.GM12.Section4FiniteLineDrawing
import LeanPool.GraphMinor.GM11.PaintingCells
import LeanPool.GraphMinor.GM11.RadialChord
import LeanPool.GraphMinor.GM11.Walks
import LeanPool.GraphMinor.Surface.SurfaceGraph

/-!
# Doubling the nonloop edges of a drawing

In the target replacement of XII (4.3), page 249, vertices
incident with one edge can be given a second incident edge by
adding a parallel copy. Assemble all the copies as a drawing and
glue them to the original. Each copy has the original two distinct
ends. Thus the augmented drawing stays loopless, and every
original edge has a distinct parallel edge in the augmentation.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

/-- The parallel-edge part of the loopless minimum-degree-two
target replacement in XII (4.3), page 249. -/
theorem exists_parallel_edge_augmentation
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (Γ : Drawing S) (u v : Set S → S)
    (hl : ∀ e ∈ Γ.E, Γ.toGraph.IsLink e (u e) (v e))
    (hne : ∀ e ∈ Γ.E, u e ≠ v e) :
    ∃ H : Drawing S, Γ.IsSubdrawing H ∧ H.V = Γ.V ∧
      (∀ e x, ¬ H.toGraph.IsLink e x x) ∧
      ∀ e ∈ Γ.E, ∃ g ∈ H.E, g ≠ e ∧
        H.toGraph.IsLink e (u e) (v e) ∧ H.toGraph.IsLink g (u e) (v e) := by
  obtain ⟨P, hP, hPP⟩ := exists_parallel_edge_family hS Γ Γ.finite_edges u v hl hne
  have hPV : ∀ e ∈ Γ.E, P e ∩ Γ.V = {u e, v e} := by
    intro e he
    apply Set.Subset.antisymm
    · exact fun x hx => (hP e he).2.1.subset ⟨hx.1, Γ.V_subset_U hx.2⟩
    · intro x hx
      rcases hx with rfl | hx
      · exact ⟨Surface.IsLineWithEnds.left_mem (hP e he).1, (hl e he).left_mem⟩
      · exact (Set.mem_singleton_iff.mp hx) ▸ ⟨Surface.IsLineWithEnds.right_mem (hP e he).1,
          (hl e he).right_mem⟩
  obtain ⟨K, hKU, hKV, hKE⟩ := exists_drawing_of_finite_lines Γ.finite_V Γ.finite_edges P u v
    (fun e he => (hP e he).1) hne hPV hPP
  have hglue : Γ.U ∩ K.U ⊆ Γ.V ∩ K.V := by
    rintro x ⟨hxΓ, hxK⟩
    rw [hKU] at hxK
    have hxV : x ∈ Γ.V := by
      rcases hxK with hxV | hxK
      · exact hxV
      · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hxK
        have hends := (hP e he).2.1.subset ⟨hxe, hxΓ⟩
        rcases hends with rfl | hends
        · exact (hl e he).left_mem
        · exact (Set.mem_singleton_iff.mp hends) ▸ (hl e he).right_mem
    exact ⟨hxV, hKV.symm ▸ hxV⟩
  let H := Γ.glue K hglue
  have hHV : H.V = Γ.V := by
    change Γ.V ∪ K.V = Γ.V
    rw [hKV, union_self]
  have hHE : H.E = Γ.E ∪ K.E := Drawing.glue_E hglue
  have hΓH : Γ.IsSubdrawing H := by
    refine ⟨?_, ?_⟩
    · rw [hHV]
    · rw [hHE]
      exact subset_union_left
  have hlink : ∀ e ∈ Γ.E, H.toGraph.IsLink (P e \ {u e, v e}) (u e) (v e) := by
    intro e he
    refine ⟨?_, hHV.symm ▸ (hl e he).left_mem, hHV.symm ▸ (hl e he).right_mem, ?_⟩
    · rw [hHE, hKE]
      exact Or.inr ⟨e, he, rfl⟩
    · rw [closure_sdiff_pair (hP e he).1, hHV]
      exact hPV e he
  have hnonloop : ∀ g ∈ H.E, ∃ x y, x ≠ y ∧ H.toGraph.IsLink g x y := by
    intro g hg
    rw [hHE, hKE] at hg
    rcases hg with hg | ⟨e, he, rfl⟩
    · exact ⟨u g, v g, hne g hg, (hΓH.isLink_iff hg).mp (hl g hg)⟩
    · exact ⟨u e, v e, hne e he, hlink e he⟩
  refine ⟨H, hΓH, hHV, ?_, ?_⟩
  · intro g x hloop
    obtain ⟨y, z, hyz, hlink'⟩ := hnonloop g hloop.edge_mem
    have hy : y = x := (H.toGraph.eq_or_eq_of_isLink_of_isLink hlink' hloop).elim id id
    have hz : z = x := (H.toGraph.eq_or_eq_of_isLink_of_isLink hlink'.symm hloop).elim id id
    exact hyz (hy.trans hz.symm)
  · intro e he
    refine ⟨P e \ {u e, v e}, (hlink e he).edge_mem, ?_, (hΓH.isLink_iff he).mp (hl e he),
      hlink e he⟩
    intro heq
    obtain ⟨x, hxe⟩ := he.1
    have hxnew : x ∈ P e \ {u e, v e} := heq.symm ▸ hxe
    exact hxnew.2 ((hP e he).2.1.subset ⟨hxnew.1, (he.2.1 hxe).1⟩)

/-- Doubling edges makes every nonisolated vertex incident with at
least two distinct edges, while preserving the vertex set and looplessness. -/
theorem exists_minimum_degree_two_augmentation
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (Γ : Drawing S)
    (hloopless : ∀ e x, ¬ Γ.toGraph.IsLink e x x)
    (hincident : ∀ x ∈ Γ.V, ∃ e, Γ.toGraph.Inc e x) :
    ∃ H : Drawing S, Γ.IsSubdrawing H ∧ H.V = Γ.V ∧
      (∀ e x, ¬ H.toGraph.IsLink e x x) ∧
      ∀ x ∈ H.V, ∃ e f, e ≠ f ∧ H.toGraph.Inc e x ∧ H.toGraph.Inc f x := by
  classical
  let dflt : S := Classical.arbitrary S
  have hex : ∀ e : Γ.E, ∃ u v, Γ.toGraph.IsLink e.val u v :=
    fun e => Γ.toGraph.exists_isLink_of_mem_edgeSet e.property
  choose u₀ v₀ hlink using hex
  let u : Set S → S := fun e => if he : e ∈ Γ.E then u₀ ⟨e, he⟩ else dflt
  let v : Set S → S := fun e => if he : e ∈ Γ.E then v₀ ⟨e, he⟩ else dflt
  have hl : ∀ e ∈ Γ.E, Γ.toGraph.IsLink e (u e) (v e) := by
    intro e he
    simpa only [u, v, dite_eq_left he] using hlink ⟨e, he⟩
  have hne : ∀ e ∈ Γ.E, u e ≠ v e := by
    intro e he heq
    have h := hl e he
    rw [heq] at h
    exact hloopless e (v e) h
  obtain ⟨H, hΓH, hHV, hHloop, hparallel⟩ := exists_parallel_edge_augmentation hS Γ u v hl hne
  refine ⟨H, hΓH, hHV, hHloop, ?_⟩
  intro x hx
  have hxΓ : x ∈ Γ.V := hHV ▸ hx
  obtain ⟨e, hex⟩ := hincident x hxΓ
  have he : e ∈ Γ.E := hex.edge_mem
  obtain ⟨f, _, hfe, heH, hfH⟩ := hparallel e he
  refine ⟨e, f, Ne.symm hfe, ?_, ?_⟩
  · rcases hex.eq_or_eq_of_isLink (hl e he) with hx | hx
    · exact hx ▸ heH.inc_left
    · exact hx ▸ heH.inc_right
  · rcases hex.eq_or_eq_of_isLink (hl e he) with hx | hx
    · exact hx ▸ hfH.inc_left
    · exact hx ▸ hfH.inc_right

end GraphMinor.GM12
