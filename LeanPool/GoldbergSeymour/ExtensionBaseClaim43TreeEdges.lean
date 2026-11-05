/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ExtensionBaseClaimTreeEdgeColors
public import LeanPool.GoldbergSeymour.ExtensionBaseRestorationInvariant

/-!
# Extension Base Claim43Tree Edges

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem ExtensionBaseClaim43TreeEdges {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    {input : PartialEdgeColoring E k} {T : TreeSequence G e0}
    {generating : PartialEdgeColoring E k}
    (ett : ExtendedTashkinovTree G k e0 input T generating)
    (terminalSupport : V)
    (hterminalSupport : terminalSupport ∈ TreeSequenceVertexSet T)
    (jSlot q : Fin ett.rounds) (hjle : jSlot.val ≤ q.val)
    (hqTerminal : q.val + 1 = ett.rounds)
    (sigmaN : PartialEdgeColoring E k)
    (hsigmaProper : IsProperEdgeColoring G sigmaN)
    (hsigmaOne : IsOneEdgeUncolored sigmaN e0)
    (hsigmaStable : StableColoring
      (ett.series.data.tree q.succ.castSucc)
      (TashkinovStoredColors ett.series.data q.succ)
      (ett.series.data.coloring q.succ) sigmaN)
    (trace : ExtensionBaseRestorationTrace ett terminalSupport
      hterminalSupport sigmaN)
    (hinvariant : ExtensionBaseRestorationInvariant ett terminalSupport
      hterminalSupport jSlot q sigmaN trace) :
    ∀ a : Fin (ett.series.data.tree jSlot.succ.castSucc).length, trace.coloring (Fin.last
        trace.steps) ((ett.series.data.tree jSlot.succ.castSucc).edge a) = sigmaN
        ((ett.series.data.tree jSlot.succ.castSucc).edge a) ∧ sigmaN ((ett.series.data.tree
        jSlot.succ.castSucc).edge a) = ett.series.data.coloring jSlot.castSucc
        ((ett.series.data.tree jSlot.succ.castSucc).edge a) := by
  classical
  let : DecidableEq V := Classical.decEq V
  intro a
  let Tj := ett.series.data.tree jSlot.succ.castSucc
  let f := Tj.edge a
  have edgeOutside : ∀ b : Fin trace.steps,
      Sum.inr f ∉ TwoColorComponent G (trace.coloring b.castSucc)
        (trace.gamma b) (trace.delta b) (Sum.inl (trace.support b)) := by
    intro b edgeMem
    have stepInvariant := hinvariant.2.1 b
    rcases stepInvariant.2.2 with
      ⟨segment, supportInTree, deltaMissing, pathComponent,
        exactIntersection, remaining⟩
    rcases segment with ⟨hlen, vertexEntries, edgeEntries⟩
    let currentTree := ett.series.data.tree (trace.slot b).succ.castSucc
    let laterA : Fin currentTree.length := Fin.castLE hlen a
    have edgeEntry : currentTree.edge laterA = f := by
      exact (edgeEntries a).trans rfl
    rcases Tj.attaches a with ⟨i, attachment⟩
    let earlier : Fin (Tj.length + 1) :=
      Fin.castLT i (Nat.lt_trans i.isLt (Nat.succ_lt_succ a.isLt))
    let laterVertex : Fin (currentTree.length + 1) :=
      Fin.castLE (Nat.succ_le_succ hlen) a.succ
    let earlierVertex : Fin (currentTree.length + 1) :=
      Fin.castLE (Nat.succ_le_succ hlen) earlier
    have laterVertexEntry : currentTree.vertex laterVertex = Tj.vertex a.succ :=
      vertexEntries a.succ
    have earlierVertexEntry : currentTree.vertex earlierVertex = Tj.vertex earlier :=
      vertexEntries earlier
    have laterInTree : Tj.vertex a.succ ∈ TreeSequenceVertexSet currentTree := by
      unfold TreeSequenceVertexSet
      apply Finset.mem_image.mpr
      exact ⟨laterVertex, Finset.mem_univ _, laterVertexEntry⟩
    have earlierInTree : Tj.vertex earlier ∈ TreeSequenceVertexSet currentTree := by
      unfold TreeSequenceVertexSet
      apply Finset.mem_image.mpr
      exact ⟨earlierVertex, Finset.mem_univ _, earlierVertexEntry⟩
    have laterIncident : Incident G (Tj.vertex a.succ) f := by
      change Tj.vertex a.succ ∈ G.ends f
      rw [attachment]
      exact Sym2.mem_mk_left _ _
    have earlierIncident : Incident G (Tj.vertex earlier) f := by
      change Tj.vertex earlier ∈ G.ends f
      rw [attachment]
      exact Sym2.mem_mk_right _ _
    let H := TwoColorIncidenceGraph G (trace.coloring b.castSucc)
      (trace.gamma b) (trace.delta b)
    have activeColor : trace.coloring b.castSucc f = some (trace.gamma b) ∨
        trace.coloring b.castSucc f = some (trace.delta b) := by
      have edgeSupport : Sum.inr f ∈ H.support := by
        apply SimpleGraph.mem_support_of_reachable
          (G := H) (u := Sum.inr f) (v := Sum.inl (trace.support b))
        · simp
        · exact SimpleGraph.ConnectedComponent.eq.mp edgeMem
      obtain ⟨neighbor, adjacency⟩ := H.mem_support.mp edgeSupport
      cases neighbor with
      | inl v => exact adjacency.2
      | inr e => simp [H, TwoColorIncidenceGraph] at adjacency
    have endpointInComponent : ∀ v : V, Incident G v f →
        Sum.inl v ∈ TwoColorComponent G (trace.coloring b.castSucc)
          (trace.gamma b) (trace.delta b) (Sum.inl (trace.support b)) := by
      intro v incident
      have adjacent : H.Adj (Sum.inl v) (Sum.inr f) := by
        simp [H, TwoColorIncidenceGraph, incident, activeColor]
      change H.connectedComponentMk (Sum.inl v) =
        H.connectedComponentMk (Sum.inl (trace.support b))
      exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
        adjacent).trans edgeMem
    have laterEq : Tj.vertex a.succ = trace.support b :=
      (exactIntersection (Tj.vertex a.succ) laterInTree).mp
        (endpointInComponent (Tj.vertex a.succ) laterIncident)
    have earlierEq : Tj.vertex earlier = trace.support b :=
      (exactIntersection (Tj.vertex earlier) earlierInTree).mp
        (endpointInComponent (Tj.vertex earlier) earlierIncident)
    have earlierEq' :
        Tj.vertex (Fin.castLT i
          (Nat.lt_trans i.isLt (Nat.succ_lt_succ a.isLt))) = trace.support b := by
      simpa [earlier] using earlierEq
    apply G.loopless f (trace.support b)
    simpa [f, laterEq, earlierEq'] using attachment
  have preserved : ∀ n : ℕ, (hn : n ≤ trace.steps) →
      trace.coloring ⟨n, Nat.lt_succ_of_le hn⟩ f = sigmaN f := by
    intro n hn
    induction n with
    | zero =>
        simpa using congrFun trace.initialColoring f
    | succ n ih =>
        let b : Fin trace.steps := ⟨n, Nat.lt_of_succ_le hn⟩
        have transition := congrFun (trace.transition b) f
        have unchanged :
            TwoColorComponentSwap G (trace.coloring b.castSucc)
                (trace.gamma b) (trace.delta b) (Sum.inl (trace.support b)) f =
              trace.coloring b.castSucc f := by
          simp [TwoColorComponentSwap, edgeOutside b]
        have atPrevious : trace.coloring b.castSucc f = sigmaN f := by
          have indexEq : b.castSucc =
              ⟨n, Nat.lt_succ_of_le (Nat.le_of_succ_le hn)⟩ := by
            apply Fin.ext
            simp [b]
          rw [indexEq]
          exact ih (Nat.le_of_succ_le hn)
        have atSuccessor : trace.coloring b.succ f = sigmaN f := by
          rw [transition, unchanged, atPrevious]
        have indexEq : (⟨n + 1, Nat.lt_succ_of_le hn⟩ : Fin (trace.steps + 1)) =
            b.succ := by
          apply Fin.ext
          simp [b]
        rw [indexEq]
        exact atSuccessor
  have firstEquality : trace.coloring (Fin.last trace.steps) f = sigmaN f := by
    simpa [Fin.last] using preserved trace.steps le_rfl
  have secondEquality : sigmaN f = ett.series.data.coloring jSlot.castSucc f := by
    exact (ExtensionBaseClaimTreeEdgeColors G k e0 input ett.rounds ett.series
      jSlot q hjle hqTerminal sigmaN hsigmaProper hsigmaOne hsigmaStable).2 a
  exact ⟨firstEquality, secondEquality⟩

end GoldbergSeymour

end
