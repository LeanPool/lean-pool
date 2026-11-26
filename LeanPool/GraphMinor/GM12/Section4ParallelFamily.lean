/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Defs
import LeanPool.GraphMinor.GM12.Section4ParallelLine
import LeanPool.GraphMinor.GM11.EdgeSides
import LeanPool.GraphMinor.GM11.RadialCorners
import LeanPool.GraphMinor.Surface.SurfaceGraph

/-!
# Adding all parallel edge copies without crossings

For the minimum-degree-two replacement in XII (4.3), page 249,
add a parallel line for each nonloop edge. At each step forbid
the original drawing with that edge removed and all copies already
added. This is a closed set meeting the edge closure only at its
ends. Thus the new copy introduces no crossing with any old copy.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

/-- The simultaneous parallel-copy construction used in the target
replacement at the start of XII (4.3), page 249. -/
theorem exists_parallel_edge_family
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (Γ : Drawing S) {E : Set (Set S)} (hE : E.Finite)
    (u v : Set S → S) (hl : ∀ e ∈ E, Γ.toGraph.IsLink e (u e) (v e))
    (hne : ∀ e ∈ E, u e ≠ v e) :
    ∃ P : Set S → Set S,
      (∀ e ∈ E, IsLineWithEnds (P e) (u e) (v e) ∧
        P e ∩ Γ.U = {u e, v e} ∧ P e ∩ closure e = {u e, v e}) ∧
      (∀ e ∈ E, ∀ f ∈ E, e ≠ f → P e ∩ P f ⊆ Γ.V) := by
  classical
  revert hl hne
  induction E, hE using Set.Finite.induction_on with
  | empty =>
    intro _ _
    exact ⟨fun _ => ∅, by simp, by simp⟩
  | @insert e E he hE ih =>
    intro hl hne
    obtain ⟨P, hP, hPP⟩ := ih (fun f hf => hl f (Or.inr hf)) (fun f hf => hne f (Or.inr hf))
    have hel := hl e (Or.inl rfl)
    have huv := hne e (Or.inl rfl)
    have hL : IsLineWithEnds (closure e) (u e) (v e) :=
      isLine_closure hel.edge_mem huv hel.2.2.2
    let Z : Set S := (Γ.U \ e) ∪ ⋃ f ∈ E, P f
    have hZ : IsClosed Z := (isClosed_U_sdiff_edge Γ hel.edge_mem).union
      (hE.isClosed_biUnion (fun f hf => (Surface.IsLineWithEnds.isCompact (hP f hf).1).isClosed))
    have hcap : closure e ∩ Z ⊆ {u e, v e} := by
      rintro x ⟨hxcl, hxZ⟩
      have hxV : x ∈ Γ.V := by
        rcases hxZ with hx | hx
        · by_contra hxV
          have hxe : x ∈ e := by rw [← Γ.closure_diff_V hel.edge_mem]; exact ⟨hxcl, hxV⟩
          exact hx.2 hxe
        · obtain ⟨f, hf, hxP⟩ := mem_iUnion₂.mp hx
          have hxU : x ∈ Γ.U := Γ.closure_subset_U hel.edge_mem hxcl
          have hends := (hP f hf).2.1.subset ⟨hxP, hxU⟩
          rcases hends with rfl | hends
          · exact (hl f (Or.inr hf)).left_mem
          · exact (Set.mem_singleton_iff.mp hends) ▸ (hl f (Or.inr hf)).right_mem
      exact hel.2.2.2 ▸ ⟨hxcl, hxV⟩
    obtain ⟨Q, hQ, hQZ, hQL⟩ := exists_parallel_line hS hL huv hZ hcap
    have hQU : Q ∩ Γ.U = {u e, v e} := by
      apply Set.Subset.antisymm
      · rintro x ⟨hxQ, hxU⟩
        by_cases hxe : x ∈ e
        · exact hQL.subset ⟨hxQ, subset_closure hxe⟩
        · exact hQZ ⟨hxQ, Or.inl ⟨hxU, hxe⟩⟩
      · intro x hx
        rcases hx with rfl | hx
        · exact ⟨hQ.left_mem, Γ.V_subset_U hel.left_mem⟩
        · exact (Set.mem_singleton_iff.mp hx) ▸ ⟨hQ.right_mem, Γ.V_subset_U hel.right_mem⟩
    have hQP : ∀ f ∈ E, Q ∩ P f ⊆ Γ.V := by
      intro f hf x hx
      have hends := hQZ ⟨hx.1, Or.inr (mem_iUnion₂.mpr ⟨f, hf, hx.2⟩)⟩
      rcases hends with rfl | hends
      · exact hel.left_mem
      · exact (Set.mem_singleton_iff.mp hends) ▸ hel.right_mem
    let P' : Set S → Set S := fun f => if f = e then Q else P f
    refine ⟨P', ?_, ?_⟩
    · intro f hf
      rcases hf with hfe | hf
      · subst f
        simpa only [P', ↓reduceIte] using (show IsLineWithEnds Q (u e) (v e) ∧
          Q ∩ Γ.U = {u e, v e} ∧ Q ∩ closure e = {u e, v e} from ⟨hQ, hQU, hQL⟩)
      · have hfe : f ≠ e := fun h => he (h ▸ hf)
        simpa only [P', hfe, ↓reduceIte] using hP f hf
    · intro f hf g hg hfg
      by_cases hfe : f = e
      · subst f
        have hge : g ≠ e := Ne.symm hfg
        have hgE : g ∈ E := hg.resolve_left hge
        simpa only [P', ↓reduceIte, hge, ↓reduceIte] using hQP g hgE
      · have hfE : f ∈ E := hf.resolve_left hfe
        by_cases hge : g = e
        · subst g
          have hc : P f ∩ Q ⊆ Γ.V := fun x hx => hQP f hfE ⟨hx.2, hx.1⟩
          simpa only [P', ↓reduceIte, hfe, ↓reduceIte] using hc
        · have hgE : g ∈ E := hg.resolve_left hge
          simpa only [P', hfe, ↓reduceIte, hge, ↓reduceIte] using hPP f hfE g hgE hfg

end GraphMinor.GM12
