/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ScheideGlobalMaximumOrder
public import LeanPool.GoldbergSeymour.ScheideReducedConfiguration
public import LeanPool.GoldbergSeymour.ScheideStructuralReorderingData

/-!
# Scheide Structural Reduced Assembly

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

private noncomputable def assembledConfiguration {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideStructuralConfiguration G k e0 phi T)
    (D : ScheideStructuralSelectionData G k e0 phi T C)
    (T' : TreeSequence G e0)
    (Q : ScheideStructuralReorderingData G k e0 phi T C D T')
    (oldExitBase : ∀ v ∈ ScheideExitVertices T phi, ∃ q : Fin C.p, C.y q = v) :
    ScheideReducedConfiguration G k e0 phi T' := by
  classical
  let newP := C.p + 2 * D.absorbedCount
  let newS := D.retainedCount
  let newVertex : Fin newP → V := fun q =>
    T'.vertex ⟨q.val, by
      have hq := q.isLt
      have hc := C.length_eq
      have hd := D.count_eq
      rw [Q.length_eq]
      omega⟩
  let newGamma : Fin newS → Fin k := fun t => C.gamma (D.retained t)
  let newBlockVertex : Fin newS → Fin 2 → V := fun t j =>
    T'.vertex ⟨C.p + 2 * D.absorbedCount + 2 * t.val + j.val, by
      have ht := t.isLt
      have hj := j.isLt
      have hc := C.length_eq
      have hd := D.count_eq
      rw [Q.length_eq]
      omega⟩
  let newBaseEdge : Fin (newP - 1) → E := fun q =>
    T'.edge ⟨q.val, by
      have hq := q.isLt
      have hp := C.p_ge_two
      have hc := C.length_eq
      have hd := D.count_eq
      rw [Q.length_eq]
      omega⟩
  let newBlockEdge : Fin newS → Fin 2 → E := fun t j =>
    T'.edge ⟨C.p - 1 + 2 * D.absorbedCount + 2 * t.val + j.val, by
      have ht := t.isLt
      have hj := j.isLt
      have hp := C.p_ge_two
      have hc := C.length_eq
      have hd := D.count_eq
      rw [Q.length_eq]
      omega⟩
  let assembled : ScheideReducedConfiguration G k e0 phi T' := {
    p := newP,
    s := newS,
    p_ge_two := by have hp := C.p_ge_two; dsimp [newP]; omega,
    gamma := newGamma,
    gamma_injective := by
      intro a b hab
      apply D.retained_injective
      apply C.gamma_injective
      exact hab,
    y := newVertex,
    baseEdge := newBaseEdge,
    blockVertex := newBlockVertex,
    blockEdge := newBlockEdge,
    length_eq := by
      dsimp [newP, newS]
      have hc := C.length_eq
      have hd := D.count_eq
      rw [Q.length_eq]
      omega,
    base_vertex_position := by
      intro q
      rfl,
    block_vertex_position := by
      intro t j
      rfl,
    base_edge_position := by
      intro q
      rfl,
    block_edge_position := by
      intro t j
      dsimp [newBlockEdge, newP]
      apply congrArg T'.edge
      apply Fin.ext
      change C.p + 2 * D.absorbedCount - 1 + 2 * t.val + j.val =
        C.p - 1 + 2 * D.absorbedCount + 2 * t.val + j.val
      have hp := C.p_ge_two
      omega,
    block_attaches_to_base := by
      intro t j
      have h := C.block_attaches_to_base (D.retained t) j
      obtain ⟨q, hq⟩ := h
      let qnew : Fin newP := ⟨q.val, by
        dsimp [newP]
        omega⟩
      refine ⟨qnew, ?_⟩
      rw [show newBlockEdge t j = C.blockEdge (D.retained t) j by
        dsimp [newBlockEdge]
        exact Q.retained_edge_position t j]
      rw [show newVertex qnew = C.y q by
        dsimp [newVertex]
        exact Q.base_vertex_position q]
      rw [show newBlockVertex t j = C.blockVertex (D.retained t) j by
        dsimp [newBlockVertex]
        exact Q.retained_vertex_position t j]
      exact hq,
    block_color := by
      intro t j
      rw [show newBlockEdge t j = C.blockEdge (D.retained t) j by
        dsimp [newBlockEdge]
        exact Q.retained_edge_position t j]
      exact C.block_color (D.retained t) j,
    block_color_missing_on_base := by
      intro t
      let v := (D.exitEquiv t).1
      have hv : v ∈ ScheideExitVertices T phi := (D.exitEquiv t).2
      obtain ⟨q, hq⟩ := oldExitBase v hv
      let qnew : Fin newP := ⟨q.val, by dsimp [newP]; omega⟩
      refine ⟨qnew, ?_⟩
      rw [show newGamma t = C.gamma (D.retained t) by rfl]
      rw [show newVertex qnew = C.y q by
        dsimp [newVertex]
        exact Q.base_vertex_position q]
      rw [hq]
      exact D.retained_missing t,
    initial_nonfirst_avoids_blocks := by
      intro q hq c hc r
      let split : Fin ((C.p - 1) + 2 * D.absorbedCount) := ⟨q.val, by
        dsimp [newP] at q ⊢
        omega⟩
      have core := @ScheideStructuralReorderingData.initialNonfirstAvoidsRetainedColor V E
          inferInstance inferInstance inferInstance inferInstance G k
          e0 phi T C D T' Q
      apply core split (by exact hq) c
      · simpa [split, newBaseEdge] using hc
    exit_covered := by
      intro v hv
      rw [Q.exit_set_eq] at hv
      obtain ⟨t, ht⟩ := (D.exitEquiv.surjective ⟨v, hv⟩)
      have htv : (D.exitEquiv t).1 = v := congrArg Subtype.val ht
      refine ⟨t, ?_⟩
      rw [← htv]
      exact D.retained_missing t,
    no_isolated := C.no_isolated,
    globally_maximum := by
      refine ⟨C.globally_maximum.1, Q.tashkinov, ?_⟩
      rw [Q.vertex_set_eq]
      exact C.globally_maximum.2.2,
    exit_card_eq := by
      rw [Q.exit_set_eq]
      exact D.exit_count_eq.symm,
    exit_exactly_one := by
      intro v hv
      rw [Q.exit_set_eq] at hv
      obtain ⟨t, ht⟩ := D.exitEquiv.surjective ⟨v, hv⟩
      have htv : (D.exitEquiv t).1 = v := congrArg Subtype.val ht
      refine ⟨t, ?_, ?_⟩
      · rw [← htv]
        exact D.retained_missing t
      · intro t' hm
        apply D.selected_unique t t'
        rw [← htv] at hm
        exact hm,
    every_block_color_at_exit := by
      intro t
      refine ⟨(D.exitEquiv t).1, ?_, ?_⟩
      · rw [Q.exit_set_eq]
        exact (D.exitEquiv t).2
      · exact D.retained_missing t
    }
  exact assembled

private theorem helper_oldExitBase_593.{u_1, u_2} :
    ∀ {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E]
      [DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
      (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
      (C : ScheideStructuralConfiguration G k e0 phi T),
    ∀ v ∈ ScheideExitVertices T phi,
    ∃ (q : Fin C.p),
    C.y q = v := by
  classical
  intro V E _ _ _ G k e0 phi T C v hv
  have hstructure := ScheideGlobalMaximumOrder G k e0 phi T C.globally_maximum
  have helementary : ColoredVertexSetElementary G phi (TreeSequenceVertexSet T) :=
    hstructure.2.2.2.1
  have hvertex : v ∈ TreeSequenceVertexSet T := by
    let : DecidablePred (fun w : V => ScheideExitVertex T phi w) := Classical.decPred _
    rcases (Finset.mem_filter.mp hv).2 with ⟨u, color, defect, hu, hmiss, hdefect,
      z, path, hpath, index, hindex, hvertex, hafter⟩
    exact hvertex
  have baseInTree : ∀ q : Fin C.p, C.y q ∈ TreeSequenceVertexSet T := by
    intro q
    have hlength := C.length_eq
    have witness :=
      (@Finset.mem_image (Fin (T.length + 1)) V (Classical.decEq V)).mpr
        (⟨⟨q.val, by omega⟩, Finset.mem_univ _, C.base_vertex_position q⟩ :
          ∃ a ∈ (Finset.univ : Finset (Fin (T.length + 1))), T.vertex a = C.y q)
    simpa only [TreeSequenceVertexSet] using witness
  obtain ⟨colorIndex, hcolor⟩ := C.exit_covered v hv
  obtain ⟨base, hbase⟩ := C.block_color_missing_on_base colorIndex
  have hne : v = C.y base := by
    by_contra hne
    have hdisjoint := helementary hvertex (baseInTree base) hne
    exact (Finset.disjoint_left.mp hdisjoint) hcolor hbase
  exact ⟨base, hne.symm⟩

private abbrev helperBranch504Conditions.{u_1, u_2} : Prop :=
 ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
  [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
  (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
  (C : ScheideStructuralConfiguration G k e0 phi T)
  (D : ScheideStructuralSelectionData G k e0 phi T C) (T' : TreeSequence G e0)
  (Q : ScheideStructuralReorderingData G k e0 phi T C D T'),
  ∀ (oldExitBase : ∀ v ∈ ScheideExitVertices T phi, ∃ q : Fin C.p, C.y q = v),
  let assembled := assembledConfiguration G k e0 phi T C D T' Q oldExitBase;
   ∀ (i : Fin C.s),
    (∃! h : Fin D.absorbedCount,
      (↑((D.absorbedEquiv : Fin D.absorbedCount → { i : Fin C.s // i ∉ Set.range D.retained }) h) :
        Fin C.s) =
       i) →
     (∃ (r : Fin assembled.s),
       C.gamma i = assembled.gamma r ∧
        ∀ (j : Fin (2 : ℕ)),
         C.blockVertex i j = assembled.blockVertex r j ∧
          C.blockEdge i j = assembled.blockEdge r j) ∨
      ∀ (j : Fin (2 : ℕ)), C.blockVertex i j ∈ Finset.image assembled.y Finset.univ

private abbrev helperBranch516Conditions.{u_1, u_2} : Prop :=
 ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
  [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
  (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
  (C : ScheideStructuralConfiguration G k e0 phi T)
  (D : ScheideStructuralSelectionData G k e0 phi T C) (T' : TreeSequence G e0)
  (Q : ScheideStructuralReorderingData G k e0 phi T C D T'),
  ∀ (oldExitBase : ∀ v ∈ ScheideExitVertices T phi, ∃ q : Fin C.p, C.y q = v),
  let assembled := assembledConfiguration G k e0 phi T C D T' Q oldExitBase;
   ∀ (i : Fin C.s),
    (∃! t : Fin D.retainedCount, D.retained t = i) →
     (∃ (r : Fin assembled.s),
       C.gamma i = assembled.gamma r ∧
        ∀ (j : Fin (2 : ℕ)),
         C.blockVertex i j = assembled.blockVertex r j ∧
          C.blockEdge i j = assembled.blockEdge r j) ∨
      ∀ (j : Fin (2 : ℕ)), C.blockVertex i j ∈ Finset.image assembled.y Finset.univ

private abbrev helperBranch513Conditions.{u_1, u_2} : Prop :=
 ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
  [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
  (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
  (C : ScheideStructuralConfiguration G k e0 phi T)
  (D : ScheideStructuralSelectionData G k e0 phi T C) (T' : TreeSequence G e0)
  (Q : ScheideStructuralReorderingData G k e0 phi T C D T'),
  ∀ (oldExitBase : ∀ v ∈ ScheideExitVertices T phi, ∃ q : Fin C.p, C.y q = v),
  let assembled := assembledConfiguration G k e0 phi T C D T' Q oldExitBase;
   ∀ (i : Fin C.s),
    (∃ (r : Fin assembled.s),
      C.gamma i = assembled.gamma r ∧
       ∀ (j : Fin (2 : ℕ)),
        C.blockVertex i j = assembled.blockVertex r j ∧ C.blockEdge i j = assembled.blockEdge r j) ∨
     ∀ (j : Fin (2 : ℕ)), C.blockVertex i j ∈ Finset.image assembled.y Finset.univ

private abbrev helperContinuation263Conditions.{u_1, u_2} : Prop :=
 ∀ {V : Type u_1} {E : Type u_2} [ Fintype V] [ Fintype E] [ DecidableEq V]
  [ DecidableEq E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
  (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
  (C : ScheideStructuralConfiguration G k e0 phi T)
  (D : ScheideStructuralSelectionData G k e0 phi T C) (T' : TreeSequence G e0)
  (_ : ScheideStructuralReorderingData G k e0 phi T C D T'),
  ∀ (_ : ∀ v ∈ ScheideExitVertices T phi, ∃ q : Fin C.p, C.y q = v),
   ∃ (R : ScheideReducedConfiguration G k e0 phi T'),
    TreeSequenceVertexSet T' = TreeSequenceVertexSet T ∧
     (∀ (q : Fin C.p), C.y q ∈ Finset.image R.y Finset.univ) ∧
      ∀ (i : Fin C.s),
       (∃ (r : Fin R.s),
         C.gamma i = R.gamma r ∧
          ∀ (j : Fin (2 : ℕ)),
           C.blockVertex i j = R.blockVertex r j ∧ C.blockEdge i j = R.blockEdge r j) ∨
        ∀ (j : Fin (2 : ℕ)), C.blockVertex i j ∈ Finset.image R.y Finset.univ

private theorem helper_branch_504.{u_1, u_2} :
    helperBranch504Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D T' Q oldExitBase assembled i ha
  obtain ⟨h, hi, _⟩ := ha
  right
  intro j
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  refine ⟨⟨C.p + 2 * h.val + j.val, ?_⟩, ?_⟩
  · change C.p + 2 * h.val + j.val < C.p + 2 * D.absorbedCount
    have hh := h.isLt
    have hj := j.isLt
    omega
  · dsimp [assembled, assembledConfiguration]
    rw [Q.absorbed_vertex_position h j]
    rw [hi]

private theorem helper_branch_516.{u_1, u_2} :
    helperBranch516Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D T' Q oldExitBase assembled i hr
  obtain ⟨t, ht, _⟩ := hr
  left
  refine ⟨t, ?_, ?_⟩
  · dsimp [assembled, assembledConfiguration]
    rw [ht]
  · intro j
    constructor
    · dsimp [assembled, assembledConfiguration]
      rw [← ht]
      exact (Q.retained_vertex_position t j).symm
    · dsimp [assembled, assembledConfiguration]
      rw [← ht]
      exact (Q.retained_edge_position t j).symm

private theorem helper_branch_513.{u_1, u_2} :
    helperBranch513Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D T' Q oldExitBase _ i
  rcases D.partition i with ha | hr
  · exact @helper_branch_504 V E inferInstance inferInstance inferInstance inferInstance G k e0
      phi T C D T' Q oldExitBase i ha
  · exact @helper_branch_516 V E inferInstance inferInstance inferInstance inferInstance G k e0
      phi T C D T' Q oldExitBase i hr
private theorem helper_continuation_263.{u_1, u_2} :
    helperContinuation263Conditions.{u_1, u_2} := by
  classical
  intro V E _ _ _ _ G k e0 phi T C D T' Q oldExitBase
  let assembled := assembledConfiguration G k e0 phi T C D T' Q oldExitBase
  refine ⟨assembled, Q.vertex_set_eq, ?_, ?_⟩
  · intro q
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    refine ⟨⟨q.val, ?_⟩, ?_⟩
    · have hq := q.isLt
      change q.val < C.p + 2 * D.absorbedCount
      omega
    · dsimp [assembled, assembledConfiguration]
      exact Q.base_vertex_position q
  · exact @helper_branch_513 V E inferInstance inferInstance inferInstance inferInstance G k e0
      phi T C D T' Q oldExitBase
theorem ScheideStructuralReducedAssembly {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideStructuralConfiguration G k e0 phi T)
    (D : ScheideStructuralSelectionData G k e0 phi T C)
    (T' : TreeSequence G e0)
    (Q : ScheideStructuralReorderingData G k e0 phi T C D T') :
    ∃ R : ScheideReducedConfiguration G k e0 phi T',
    TreeSequenceVertexSet T' = TreeSequenceVertexSet T ∧
      (∀ q : Fin C.p, C.y q ∈ Finset.univ.image R.y) ∧
        (∀ i : Fin C.s,
          (∃ r : Fin R.s,
              C.gamma i = R.gamma r ∧
                ∀ j : Fin 2,
                  C.blockVertex i j = R.blockVertex r j ∧
                    C.blockEdge i j = R.blockEdge r j) ∨
            ∀ j : Fin 2, C.blockVertex i j ∈ Finset.univ.image R.y) := by
  classical
  have oldExitBase := @helper_oldExitBase_593 V E inferInstance inferInstance inferInstance G k e0
      phi T C
  exact @helper_continuation_263 V E inferInstance inferInstance inferInstance inferInstance G k
      e0 phi T C D T' Q oldExitBase

end GoldbergSeymour

end
