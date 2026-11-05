/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ScheideDefectiveSetupExists
public import LeanPool.GoldbergSeymour.ScheideEnlargedStronglyClosed
public import LeanPool.GoldbergSeymour.ScheideReplacementFamilyExists
public import LeanPool.GoldbergSeymour.ScheideStructuralReduction
public import LeanPool.GoldbergSeymour.CriticalGraphElementaryWitness

/-!
# Scheide Structural Lemma

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem ScheideStructuralLemma {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideStructuralConfiguration G k e0 phi T) :
    Elementary G := by
  classical
  obtain ⟨T', R, hset, hy, hblocks⟩ :=
    ScheideStructuralReduction G k e0 phi T C
  have htriple : KTriple G k e0 phi := R.globally_maximum.1
  have hproper : IsProperEdgeColoring G phi := htriple.2.2.2.1
  have hone : IsOneEdgeUncolored phi e0 := htriple.2.2.2.2
  have hindex : ChromaticIndex G = k + 1 := htriple.2.1
  have hdegree : MaximumDegree G + 1 ≤ k := htriple.2.2.1
  have hends : ∀ v, v ∈ G.ends e0 → v ∈ TreeSequenceVertexSet T' := by
    intro v hv
    have hatt := T'.attaches (⟨0, T'.positive⟩ : Fin T'.length)
    obtain ⟨i, hi⟩ := hatt
    have hi0 : i = ⟨0, Nat.zero_lt_succ _⟩ := by
      apply Fin.ext
      exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ i.isLt)
    subst i
    have hmem' : T'.vertex ⟨0, Nat.zero_lt_succ _⟩ ∈
        G.ends (T'.edge ⟨0, T'.positive⟩) := by
      have hzero : (⟨0, Nat.zero_lt_succ _⟩ : Fin (T'.length + 1)) =
          Fin.castLT (⟨0, Nat.zero_lt_succ _⟩ : Fin (0 + 1)) (by omega) := by
        apply Fin.ext
        rfl
      rw [hi]
      simp [hzero]
    have hmem : T'.vertex ⟨0, Nat.zero_lt_succ _⟩ ∈ G.ends e0 := by
      simpa [T'.first_edge] using hmem'
    have hvertices : ∀ w, w ∈ G.ends e0 → w ∈ TreeSequenceVertexSet T' := by
      intro w hw
      have hw' := hw
      rw [← T'.first_edge, hi] at hw'
      rcases (by simpa using hw') with hw' | hw'
      · simp [TreeSequenceVertexSet, hw']
      · simp [TreeSequenceVertexSet, hw']
    exact hvertices v hv
  have hzero_mem : T'.vertex ⟨0, Nat.zero_lt_succ _⟩ ∈
        TreeSequenceVertexSet T' := by
      simp [TreeSequenceVertexSet]
  have hcritical : Critical G := htriple.1
  have hnoisolated : ∀ v : V, ∃ e : E, Incident G v e := C.no_isolated
  have graph := egraph2 G k hcritical hindex hdegree hnoisolated
  have finish : ∀ (X : Finset V),
      ColoredVertexSetElementary G phi X →
      ColoredVertexSetStronglyClosed G phi X →
      (∀ v, v ∈ G.ends e0 → v ∈ X) → Elementary G := by
    intro X he hs hend
    apply graph.1.mpr
    apply graph.2.1.mpr
    apply graph.2.2.mpr
    exact ⟨e0, phi, X, hproper, hone, hend, he, hs⟩
  by_cases hdef : DefectiveColors G phi (TreeSequenceVertexSet T') = ∅
  · have hclosed := (ScheideGlobalMaximumBoundaryFacts G k e0 phi T'
      R.globally_maximum).1 hdef
    have horder := ScheideGlobalMaximumOrder G k e0 phi T' R.globally_maximum
    apply finish (TreeSequenceVertexSet T') horder.2.2.2.1 hclosed hends
  · obtain ⟨D⟩ := ScheideDefectiveSetupExists G k e0 phi T' R hdef
    obtain ⟨family⟩ := ScheideReplacementFamilyExists G k e0 phi T' R D
    have henlarged : ColoredVertexSetElementary G phi
        (ScheideEnlargedVertexSet family) :=
      ScheideEnlargedElementary (G := G) (k := k) (e0 := e0) (phi := phi)
        (T := T') (C := R) (D := D) family
    have hstrong : ColoredVertexSetStronglyClosed G phi
        (ScheideEnlargedVertexSet family) :=
      ScheideEnlargedStronglyClosed (G := G) (k := k) (e0 := e0) (phi := phi)
        (T := T') (C := R) (D := D) family
    have hcontain : TreeSequenceVertexSet T' ⊆ ScheideEnlargedVertexSet family := by
      intro v hv
      exact Finset.mem_union_left _ hv
    have hend : ∀ v, v ∈ G.ends e0 → v ∈ ScheideEnlargedVertexSet family := by
      intro v hv
      exact hcontain (hends v hv)
    exact finish (ScheideEnlargedVertexSet family) henlarged hstrong hend

end GoldbergSeymour

end
