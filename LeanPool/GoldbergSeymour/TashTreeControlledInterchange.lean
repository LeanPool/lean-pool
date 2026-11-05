/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashTreeMinimumBadPair
public import LeanPool.GoldbergSeymour.TashTreeProperInitialSegmentRankLess
public import LeanPool.GoldbergSeymour.TashkinovTreeComponentSwapWitnessTransport
public import LeanPool.GoldbergSeymour.TreeColorUnusedThrough
public import LeanPool.GoldbergSeymour.TreeSequencePrefix
public import LeanPool.GoldbergSeymour.TwoColorComponentSwap
public import LeanPool.GoldbergSeymour.TwoColorComponentSwapNonElementary
public import LeanPool.GoldbergSeymour.TwoColorComponentSwapProper
public import LeanPool.GoldbergSeymour.TwoColorPathComponent

/-!
# Tash Tree Controlled Interchange

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem TashTreeControlledInterchange {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hmin : TashTreeMinimumBadPair G k e0 phi T)
    (i j : Fin (T.length + 1)) (hij : i.val < j.val)
    (hj : j.val < T.length) (alpha beta : Fin k) (hne : alpha ≠ beta)
    (ha : alpha ∈ MissingColors G phi (T.vertex i))
    (hb : beta ∈ MissingColors G phi (T.vertex j))
    (hau : TreeColorUnusedThrough phi T alpha j)
    (hbu : TreeColorUnusedThrough phi T beta j) :
    let phi' := TwoColorComponentSwap G phi alpha beta (Sum.inl (T.vertex j))
    TwoColorPathComponent G phi alpha beta (Sum.inl (T.vertex j)) ∧
      Sum.inl (T.vertex i) ∈
        TwoColorComponent G phi alpha beta (Sum.inl (T.vertex j)) ∧
      Set.Subsingleton
        ((TwoColorIncidenceGraph G phi alpha beta).neighborSet
          (Sum.inl (T.vertex i))) ∧
      Set.Subsingleton
        ((TwoColorIncidenceGraph G phi alpha beta).neighborSet
          (Sum.inl (T.vertex j))) ∧
      beta ∈ MissingColors G phi' (T.vertex i) ∧
      alpha ∈ MissingColors G phi' (T.vertex j) ∧
      (∀ r : Fin T.length, 1 ≤ r.val → r.val < j.val →
        phi' (T.edge r) = phi (T.edge r)) ∧
      (∀ r : Fin T.length, j.val ≤ r.val →
        ∀ w : Fin (r.val + 1), ∀ c : Fin k,
          phi (T.edge r) = some c →
          c ∈ MissingColors G phi
            (T.vertex (Fin.castLT w
              (Nat.lt_trans w.isLt (Nat.succ_lt_succ r.isLt)))) →
          ∃ w' : Fin (r.val + 1), ∃ c' : Fin k,
            phi' (T.edge r) = some c' ∧
            c' ∈ MissingColors G phi'
              (T.vertex (Fin.castLT w'
                (Nat.lt_trans w'.isLt (Nat.succ_lt_succ r.isLt))))) ∧
      TashTreeMinimumBadPair G k e0 phi' T := by
  classical
  dsimp only
  let C := TwoColorComponent G phi alpha beta (Sum.inl (T.vertex j))
  let phi' := TwoColorComponentSwap G phi alpha beta (Sum.inl (T.vertex j))
  rcases hmin with ⟨hbad, hminimal⟩
  rcases hbad with ⟨htriple, hTash, hnotElementary⟩
  rcases htriple with ⟨hcritical, hchromatic, hdegree, hproper, hone⟩
  have hvjC : Sum.inl (T.vertex j) ∈ C := by
    change Sum.inl (T.vertex j) ∈
      ((TwoColorIncidenceGraph G phi alpha beta).connectedComponentMk
        (Sum.inl (T.vertex j))).supp
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
  have hvertex_ne : T.vertex i ≠ T.vertex j := by
    intro h
    exact (Fin.ne_of_lt hij) (T.vertex_injective h)
  have incidence_subsingleton_alpha :
      ∀ v : V, alpha ∈ MissingColors G phi v →
        Set.Subsingleton
          ((TwoColorIncidenceGraph G phi alpha beta).neighborSet (Sum.inl v)) := by
    intro v hv
    let : Fintype
        ((TwoColorIncidenceGraph G phi alpha beta).neighborSet (Sum.inl v)) :=
      Fintype.ofFinite _
    have hdeg := MissingColorIncidenceEndpoint G phi alpha beta hne hproper v hv
    have hcard :
        ((TwoColorIncidenceGraph G phi alpha beta).neighborFinset
          (Sum.inl v)).card ≤ 1 := by
      rw [SimpleGraph.card_neighborFinset_eq_degree]
      exact hdeg
    intro x hx y hy
    exact (Finset.card_le_one.mp hcard) x
      (by simpa [SimpleGraph.mem_neighborFinset] using hx) y
      (by simpa [SimpleGraph.mem_neighborFinset] using hy)
  have hiSub : Set.Subsingleton
      ((TwoColorIncidenceGraph G phi alpha beta).neighborSet
        (Sum.inl (T.vertex i))) := incidence_subsingleton_alpha _ ha
  have hjSub : Set.Subsingleton
      ((TwoColorIncidenceGraph G phi alpha beta).neighborSet
        (Sum.inl (T.vertex j))) := by
    let : Fintype
        ((TwoColorIncidenceGraph G phi beta alpha).neighborSet
          (Sum.inl (T.vertex j))) := Fintype.ofFinite _
    have hdeg := MissingColorIncidenceEndpoint G phi beta alpha hne.symm
      hproper (T.vertex j) hb
    have hcard :
        ((TwoColorIncidenceGraph G phi beta alpha).neighborFinset
          (Sum.inl (T.vertex j))).card ≤ 1 := by
      rw [SimpleGraph.card_neighborFinset_eq_degree]
      exact hdeg
    intro x hx y hy
    have hx' : x ∈ (TwoColorIncidenceGraph G phi beta alpha).neighborFinset
        (Sum.inl (T.vertex j)) := by
      apply (SimpleGraph.mem_neighborFinset
        (TwoColorIncidenceGraph G phi beta alpha) (Sum.inl (T.vertex j)) x).2
      cases x with
      | inl x => simp [TwoColorIncidenceGraph] at hx
      | inr x => simpa [TwoColorIncidenceGraph, or_comm] using hx
    have hy' : y ∈ (TwoColorIncidenceGraph G phi beta alpha).neighborFinset
        (Sum.inl (T.vertex j)) := by
      apply (SimpleGraph.mem_neighborFinset
        (TwoColorIncidenceGraph G phi beta alpha) (Sum.inl (T.vertex j)) y).2
      cases y with
      | inl y => simp [TwoColorIncidenceGraph] at hy
      | inr y => simpa [TwoColorIncidenceGraph, or_comm] using hy
    exact (Finset.card_le_one.mp hcard) x hx' y hy'
  have hpath : TwoColorPathComponent G phi alpha beta
      (Sum.inl (T.vertex j)) := by
    exact ⟨hne, Sum.inl (T.vertex j), hvjC, hjSub⟩
  have hmissing := TwoColorComponentSwapMissingBehavior G phi alpha beta hne
    hproper (Sum.inl (T.vertex j))
  dsimp only at hmissing
  have hproper' : IsProperEdgeColoring G phi' := by
    exact TwoColorComponentSwapProper G phi alpha beta hne hproper
      (Sum.inl (T.vertex j))
  have hone' : IsOneEdgeUncolored phi' e0 := by
    constructor
    · simp [phi', TwoColorComponentSwap, hone.1]
    · intro e he
      obtain ⟨c, hc⟩ := hone.2 e he
      by_cases hm : Sum.inr e ∈ C
      · by_cases hca : c = alpha
        · refine ⟨beta, ?_⟩
          simp [phi', C, TwoColorComponentSwap, hm, hc, hca]
        · by_cases hcb : c = beta
          · refine ⟨alpha, ?_⟩
            simp [phi', C, TwoColorComponentSwap, hm, hc, hcb]
          · refine ⟨c, ?_⟩
            simp [phi', C, TwoColorComponentSwap, hm, hc, hca, hcb]
      · exact ⟨c, by simpa [phi', C, TwoColorComponentSwap, hm] using hc⟩
  have htriple' : KTriple G k e0 phi' :=
    ⟨hcritical, hchromatic, hdegree, hproper', hone'⟩
  have htransport := TashkinovTreeComponentSwapWitnessTransport
    G k e0 phi T hproper hTash i j hij alpha beta hne ha hb hau hbu
  dsimp only at htransport
  have hiC : Sum.inl (T.vertex i) ∈ C := by
    by_contra hiC
    have hji : 1 ≤ j.val := by omega
    have hjle : j.val ≤ T.length := Nat.le_of_lt hj
    let P := TreeSequencePrefix T j.val hji hjle
    have hPprefix : TreeSequenceInitialSegment P T := by
      refine ⟨hjle, ?_, ?_⟩
      · intro r
        rfl
      · intro r
        rfl
    have hPlength : P.length = j.val := rfl
    have hPTash : TashkinovTree G e0 phi' P :=
      htransport.2.1 P hPprefix hPlength
    have hiMissing : alpha ∈ MissingColors G phi' (T.vertex i) := by
      rw [hmissing.1 (T.vertex i) hiC]
      exact ha
    have hjMissing : alpha ∈ MissingColors G phi' (T.vertex j) :=
      hmissing.2.2.1 (T.vertex j) hvjC hb
    have hiP : T.vertex i ∈ TreeSequenceVertexSet P := by
      rw [TreeSequenceVertexSet]
      apply Finset.mem_image.mpr
      let ip : Fin (P.length + 1) := ⟨i.val, by
        change i.val < j.val + 1
        omega⟩
      refine ⟨ip, Finset.mem_univ _, ?_⟩
      apply congrArg T.vertex
      apply Fin.ext
      rfl
    have hjP : T.vertex j ∈ TreeSequenceVertexSet P := by
      rw [TreeSequenceVertexSet]
      apply Finset.mem_image.mpr
      let jp : Fin (P.length + 1) := ⟨j.val, by
        change j.val < j.val + 1
        omega⟩
      refine ⟨jp, Finset.mem_univ _, ?_⟩
      apply congrArg T.vertex
      apply Fin.ext
      rfl
    have hnotP : ¬ ColoredVertexSetElementary G phi'
        (TreeSequenceVertexSet P) := by
      intro hPelem
      have hd := hPelem hiP hjP hvertex_ne
      exact (Finset.disjoint_left.mp hd) hiMissing hjMissing
    have hbadP : TashTreeBadPair G k e0 phi' P :=
      ⟨htriple', hPTash, hnotP⟩
    have hproperP : P.length < T.length := by
      change j.val < T.length
      exact hj
    have hrank : TashTreeRankLess G P T :=
      TashTreeProperInitialSegmentRankLess G P T hPprefix hproperP
    exact (hminimal hbadP) hrank
  have hiMissing' : beta ∈ MissingColors G phi' (T.vertex i) :=
    hmissing.2.1 (T.vertex i) hiC ha
  have hjMissing' : alpha ∈ MissingColors G phi' (T.vertex j) :=
    hmissing.2.2.1 (T.vertex j) hvjC hb
  have hearly := htransport.1
  have hlater := (htransport.2.2 hiC).1
  have hTash' := (htransport.2.2 hiC).2
  have hiT : T.vertex i ∈ TreeSequenceVertexSet T := by
    rw [TreeSequenceVertexSet]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hjT : T.vertex j ∈ TreeSequenceVertexSet T := by
    rw [TreeSequenceVertexSet]
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  have hnotElementary' : ¬ ColoredVertexSetElementary G phi'
      (TreeSequenceVertexSet T) := by
    exact TwoColorComponentSwapNonElementary G phi alpha beta hne hproper
      (Sum.inl (T.vertex j)) (TreeSequenceVertexSet T)
      (T.vertex i) (T.vertex j) hiT hjT hvertex_ne hiC hvjC ha hb
      hnotElementary
  have hminimum' : TashTreeMinimumBadPair G k e0 phi' T := by
    exact ⟨⟨htriple', hTash', hnotElementary'⟩, hminimal⟩
  exact ⟨hpath, hiC, hiSub, hjSub, hiMissing', hjMissing', hearly,
    hlater, hminimum'⟩

end GoldbergSeymour

end
