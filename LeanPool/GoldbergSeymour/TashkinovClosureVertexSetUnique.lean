/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashkinovClosure

/-!
# Tashkinov Closure Vertex Set Unique

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem TashkinovClosureVertexSetUnique {V E : Type*}
    [Fintype V] [Fintype E] {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    (phi : PartialEdgeColoring E k) (T T₁ T₂ : TreeSequence G e0)
    (h₁ : TashkinovClosure phi T T₁) (h₂ : TashkinovClosure phi T T₂) :
    TreeSequenceVertexSet T₁ = TreeSequenceVertexSet T₂ := by
  classical
  rcases h₁ with ⟨hseq₁, hclosed₁⟩
  rcases h₂ with ⟨hseq₂, hclosed₂⟩
  have initial_subset : ∀ {A B : TreeSequence G e0},
      TreeSequenceInitialSegment A B →
        TreeSequenceVertexSet A ⊆ TreeSequenceVertexSet B := by
    intro A B hinit v hv
    obtain ⟨i, hi, hvi⟩ := Finset.mem_image.mp hv
    obtain ⟨hlen, hvertices, hedges⟩ := hinit
    apply Finset.mem_image.mpr
    refine ⟨Fin.castLE (Nat.succ_le_succ hlen) i, Finset.mem_univ _, ?_⟩
    show B.vertex (Fin.castLE (Nat.succ_le_succ hlen) i) = v
    rw [hvertices i]
    exact hvi
  have base_subset : ∀ {C : TreeSequence G e0},
      Relation.ReflTransGen (TashkinovAugmentation phi) T C →
        TreeSequenceVertexSet T ⊆ TreeSequenceVertexSet C := by
    intro C hreach
    induction hreach with
    | refl => exact Finset.Subset.rfl
    | tail hreach hab ih =>
        rename_i mid last
        exact ih.trans (initial_subset hab.2.1)
  have contain :
    ∀ {C S : TreeSequence G e0}, Relation.ReflTransGen (TashkinovAugmentation phi) T C →
        ColoredVertexSetClosed G phi (TreeSequenceVertexSet C) → Relation.ReflTransGen
        (TashkinovAugmentation phi) T S → TreeSequenceVertexSet S ⊆ TreeSequenceVertexSet C := by
    intro C S hC hclosed hS
    have start : TreeSequenceVertexSet T ⊆ TreeSequenceVertexSet C :=
      base_subset hC
    induction hS with
    | refl => exact start
    | tail hreach hab ih =>
        rename_i mid last
        have old_subset : TreeSequenceVertexSet mid ⊆ TreeSequenceVertexSet C := ih
        obtain ⟨hlen, hinit, c, hcolor, hmissing⟩ := hab
        rcases hinit with ⟨hbound, hvertices, hedges⟩
        have new_subset : TreeSequenceVertexSet last ⊆ TreeSequenceVertexSet C := by
          intro v hv
          obtain ⟨j, hj, hjv⟩ := Finset.mem_image.mp hv
          by_cases hlast : j.val = last.length
          · have hjlast : j = Fin.last _ := Fin.ext hlast
            subst j
            by_contra hout
            obtain ⟨z, hzold, hzmiss⟩ := Finset.mem_biUnion.mp hmissing
            have hzC : z ∈ TreeSequenceVertexSet C := old_subset hzold
            obtain ⟨q, hq⟩ := last.attaches
              (Fin.cast hlen.symm (Fin.last mid.length))
            let qnew : Fin (last.length + 1) := Fin.castLT q (by omega)
            let qold : Fin (mid.length + 1) := Fin.castLT q (by omega)
            have hqold : last.vertex qnew ∈
                TreeSequenceVertexSet C := by
              apply old_subset
              apply Finset.mem_image.mpr
              refine ⟨qold, Finset.mem_univ _, ?_⟩
              rw [← hvertices qold]
              apply congrArg last.vertex
              apply Fin.ext
              dsimp [qnew, qold]
            have hnew : (Fin.cast hlen.symm (Fin.last mid.length)).succ =
                (Fin.last last.length : Fin (last.length + 1)) := by
              apply Fin.ext
              simp [Fin.last]
              omega
            have hedge : G.ends (last.edge (Fin.cast hlen.symm (Fin.last mid.length))) =
                Sym2.mk (last.vertex (Fin.cast hlen.symm (Fin.last mid.length)).succ)
                  (last.vertex qnew) := by
              rw [hnew]
              rw [hnew] at hq
              simpa [qnew] using hq
            have hboundary : last.edge (Fin.cast hlen.symm (Fin.last mid.length)) ∈
                BoundaryEdges G (TreeSequenceVertexSet C) := by
              unfold BoundaryEdges
              refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
              have hout' : last.vertex (Fin.last last.length) ∉
                  TreeSequenceVertexSet C := by
                rw [hjv]
                exact hout
              refine ⟨last.vertex qnew, hqold,
                last.vertex (Fin.last last.length), hout', ?_⟩
              have hedge' := hedge
              rw [hnew] at hedge'
              exact hedge'.trans Sym2.eq_swap
            exact (hclosed hboundary hzC hcolor) hzmiss
          · apply old_subset
            apply Finset.mem_image.mpr
            let jold : Fin (mid.length + 1) := ⟨j.val, by omega⟩
            refine ⟨jold, Finset.mem_univ _, ?_⟩
            rw [← hvertices jold]
            have hindices : Fin.castLE (Nat.succ_le_succ hbound) jold = j := by
              apply Fin.ext
              dsimp [jold]
            rw [hindices]
            exact hjv
        exact new_subset
  have first : TreeSequenceVertexSet T₁ ⊆ TreeSequenceVertexSet T₂ :=
    contain hseq₂ hclosed₂ hseq₁
  have second : TreeSequenceVertexSet T₂ ⊆ TreeSequenceVertexSet T₁ :=
    contain hseq₁ hclosed₁ hseq₂
  exact Finset.Subset.antisymm first second

end GoldbergSeymour

end
