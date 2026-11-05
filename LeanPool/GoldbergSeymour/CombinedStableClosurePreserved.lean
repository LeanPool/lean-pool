/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.CombinedStableColoring
public import LeanPool.GoldbergSeymour.HierarchyBase
public import LeanPool.GoldbergSeymour.HkuTreeColorsControlled

/-!
# Combined Stable Closure Preserved

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem CombinedStableClosurePreserved {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (input : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (generating phi sigma : PartialEdgeColoring E k)
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (hpositive : 0 < ett.rounds)
    (base : HierarchyBase ett phi)
    (hphi : phi = ett.series.data.coloring (Fin.last ett.rounds))
    (hPE : ett.series.data.kind (Fin.last ett.rounds) =
      some TashkinovExtensionKind.PE)
    (hproperPhi : IsProperEdgeColoring G phi)
    (honePhi : IsOneEdgeUncolored phi e0)
    (hproperSigma : IsProperEdgeColoring G sigma)
    (honeSigma : IsOneEdgeUncolored sigma e0)
    (hstable : CombinedStableColoring
      (ett.series.data.tree (Fin.last ett.rounds).castSucc)
      base.closure
      (TashkinovStoredColors ett.series.data (Fin.last ett.rounds))
      phi sigma) :
    let Tn := ett.series.data.tree (Fin.last ett.rounds).castSucc
    let seed := TreeSequencePrefix Tn base.supportPosition.val
      base.supportPositive (Nat.le_of_lt_succ base.supportPosition.isLt)
    (∀ j : Fin Tn.length, sigma (Tn.edge j) = phi (Tn.edge j)) ∧
    (∀ j : Fin base.closure.length,
      sigma (base.closure.edge j) = phi (base.closure.edge j)) ∧
    TashkinovClosure sigma seed base.closure := by
  classical
  dsimp
  let n := ett.rounds
  let Tn := ett.series.data.tree (Fin.last ett.rounds).castSucc
  let seed := TreeSequencePrefix Tn base.supportPosition.val
    base.supportPositive (Nat.le_of_lt_succ base.supportPosition.isLt)
  have hfirst : StableColoring Tn
      (TashkinovStoredColors ett.series.data (Fin.last ett.rounds)) phi sigma := by
    exact hstable.1
  have hqpos : 0 < ett.rounds := hpositive
  let q : Fin ett.rounds := ⟨ett.rounds - 1, Nat.sub_lt (Nat.zero_lt_of_lt hpositive) (by omega)⟩
  have hq : q.succ = Fin.last ett.rounds := by
    apply Fin.ext
    simp [q]
    omega
  have hcontrol := HkuTreeColorsControlled G k ett.rounds e0 input ett.series q
  have hterminal : ∀ j : Fin Tn.length, sigma (Tn.edge j) = phi (Tn.edge j) := by
    rw [hq] at hcontrol
    have hh := hcontrol.2.2 sigma hproperSigma honeSigma
      (by simpa [Tn, hphi] using hfirst)
    simpa [Tn, hphi] using hh
  have vertexTransfer {A B : TreeSequence G e0}
      (hab : TreeSequenceInitialSegment A B) {v : V}
      (hv : v ∈ TreeSequenceVertexSet A) :
      v ∈ TreeSequenceVertexSet B := by
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] at hv ⊢
    rcases hv with ⟨i, hi⟩
    rcases hab with ⟨hlen, hvertices, hedges⟩
    refine ⟨Fin.castLE (Nat.succ_le_succ hlen) i, ?_⟩
    exact (hvertices i).trans hi
  have edgeIncident {A : TreeSequence G e0} (j : Fin A.length) :
      TreeIncidentEdge A (A.edge j) := by
    rcases A.attaches j with ⟨i, hi⟩
    refine ⟨A.vertex j.succ, ?_, ?_⟩
    · simp [TreeSequenceVertexSet]
    · change A.vertex j.succ ∈ G.ends (A.edge j)
      rw [hi]
      exact Sym2.mem_mk_left _ _
  have vertexInclusion {A B : TreeSequence G e0}
      (hseq : TashkinovAugmentationSequence phi A B) :
      ∀ v, v ∈ TreeSequenceVertexSet A → v ∈ TreeSequenceVertexSet B := by
    unfold TashkinovAugmentationSequence at hseq
    induction hseq using Relation.ReflTransGen.head_induction_on with
    | refl => intro v hv; exact hv
    | head hstep htail ih =>
      intro v hv
      exact ih v (vertexTransfer hstep.2.1 hv)
  have hclosurePhi : TashkinovClosure phi seed base.closure :=
    (base.parallel hPE).2.1
  have hseqPhi : TashkinovAugmentationSequence phi seed base.closure :=
    hclosurePhi.1
  have hseed : ∀ j : Fin seed.length,
      sigma (seed.edge j) = phi (seed.edge j) := by
    intro j
    exact hterminal (Fin.castLE (Nat.le_of_lt_succ base.supportPosition.isLt) j)
  have hrev : StableColoring base.closure ∅ sigma phi := by
    let a : {psi : PartialEdgeColoring E k //
        IsProperEdgeColoring G psi ∧ IsOneEdgeUncolored psi e0} :=
      ⟨phi, ⟨hproperPhi, honePhi⟩⟩
    let b : {psi : PartialEdgeColoring E k //
        IsProperEdgeColoring G psi ∧ IsOneEdgeUncolored psi e0} :=
      ⟨sigma, ⟨hproperSigma, honeSigma⟩⟩
    have hab : StableColoring base.closure ∅ a.1 b.1 := hstable.2
    have hba := (sc2 G e0 base.closure ∅).symm hab
    exact hba
  have hseqSigma : TashkinovAugmentationSequence sigma seed base.closure := by
    have transport : ∀ {A : TreeSequence G e0},
        Relation.ReflTransGen (TashkinovAugmentation phi) A base.closure →
        Relation.ReflTransGen (TashkinovAugmentation sigma) A base.closure := by
      intro A hs
      induction hs using Relation.ReflTransGen.head_induction_on with
      | refl => exact Relation.ReflTransGen.refl
      | @head A B hstep htail ih =>
      have htailVertex := vertexInclusion htail
      have hnew : TashkinovAugmentation sigma A B := by
        rcases hstep with ⟨hlen, hseg, c, hcolor, hmiss⟩
        refine ⟨hlen, hseg, c, ?_, ?_⟩
        · let hlast : Fin B.length := Fin.cast hlen.symm (Fin.last A.length)
          have hcolor' : phi (B.edge hlast) = some c := by
            dsimp [hlast]
            exact hcolor
          have hinc : TreeIncidentEdge base.closure (B.edge hlast) := by
            rcases edgeIncident hlast with ⟨v, hv, he⟩
            exact ⟨v, htailVertex v hv, he⟩
          have hcR : c ∈ TreeMissingColors phi base.closure := by
            unfold TreeMissingColors at hmiss ⊢
            rcases Finset.mem_biUnion.mp hmiss with ⟨v, hv, hvc⟩
            exact Finset.mem_biUnion.mpr ⟨v, htailVertex v (vertexTransfer hseg hv), hvc⟩
          have heq := hstable.2.1 _ hinc
            ⟨c, Finset.mem_union_left _ hcR, by
              exact hcolor'⟩
          exact heq.trans (by
            exact hcolor')
        · unfold TreeMissingColors at hmiss ⊢
          rcases Finset.mem_biUnion.mp hmiss with ⟨v, hv, hvc⟩
          refine Finset.mem_biUnion.mpr ⟨v, hv, ?_⟩
          rw [hstable.2.2 v (htailVertex v (vertexTransfer hseg hv))]
          exact hvc
      exact Relation.ReflTransGen.head hnew ih
    exact transport (A := seed) hseqPhi
  exact ⟨hterminal, by
    have equalityReach : ∀ {A : TreeSequence G e0},
        Relation.ReflTransGen (TashkinovAugmentation phi) A base.closure →
        (∀ j : Fin A.length, sigma (A.edge j) = phi (A.edge j)) →
        ∀ j : Fin base.closure.length,
          sigma (base.closure.edge j) = phi (base.closure.edge j) := by
      intro A hreach
      induction hreach using Relation.ReflTransGen.head_induction_on with
      | refl => intro hA; exact hA
      | @head A B hstep htail ih =>
        intro hA
        rcases hstep with ⟨hlen, hseg, c, hcolor, hmiss⟩
        have htailVertex := vertexInclusion htail
        have hB : ∀ j : Fin B.length,
            sigma (B.edge j) = phi (B.edge j) := by
          intro j
          let hlast : Fin B.length := Fin.cast hlen.symm (Fin.last A.length)
          have hlastVal : hlast.val = A.length := by simp [hlast]
          by_cases hj : j.val < A.length
          · let ja : Fin A.length := ⟨j.val, by omega⟩
            have he : B.edge (Fin.castLE hseg.1 ja) = A.edge ja := hseg.2.2 ja
            have hjcast : Fin.castLE hseg.1 ja = j := by apply Fin.ext; rfl
            rw [← hjcast]
            exact (congrArg sigma he).trans ((hA ja).trans (congrArg phi he.symm))
          · have je : j = hlast := by apply Fin.ext; omega
            subst je
            have hi := edgeIncident hlast
            rcases hi with ⟨v, hvv, hvi⟩
            have hinc : TreeIncidentEdge base.closure (B.edge hlast) :=
              ⟨v, htailVertex v hvv, hvi⟩
            have hcR : c ∈ TreeMissingColors phi base.closure := by
              unfold TreeMissingColors at hmiss ⊢
              rcases Finset.mem_biUnion.mp hmiss with ⟨v, hvv, hvc⟩
              exact Finset.mem_biUnion.mpr ⟨v, htailVertex v (vertexTransfer hseg hvv), hvc⟩
            have hcolor' : phi (B.edge hlast) = some c := by
              dsimp [hlast]
              exact hcolor
            exact hstable.2.1 _ hinc
              ⟨c, Finset.mem_union_left _ hcR, hcolor'⟩
        exact ih hB
    have hEq : ∀ j : Fin base.closure.length,
        sigma (base.closure.edge j) = phi (base.closure.edge j) :=
      equalityReach hseqPhi hseed
    exact ⟨hEq, ⟨hseqSigma, by
        unfold ColoredVertexSetClosed
        intro f c v hf hv hfc
        have hinc : TreeIncidentEdge base.closure f := by
          simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and] at hf
          rcases hf with ⟨u, hu, w, hw, he⟩
          refine ⟨u, hu, ?_⟩
          change u ∈ G.ends f
          rw [he]
          exact Sym2.mem_mk_left _ _
        have hm := hstable.2.2 v hv
        intro hc
        have hcR : c ∈ TreeMissingColors sigma base.closure := by
          unfold TreeMissingColors
          exact Finset.mem_biUnion.mpr ⟨v, hv, hc⟩
        have heq := hrev.1 f hinc
          ⟨c, Finset.mem_union_left _ hcR, hfc⟩
        have hcphi : c ∈ MissingColors G phi v := by
          exact hm ▸ hc
        apply (hclosurePhi.2 hf hv (by rw [heq]; exact hfc))
        exact hcphi⟩⟩⟩

end GoldbergSeymour

end
