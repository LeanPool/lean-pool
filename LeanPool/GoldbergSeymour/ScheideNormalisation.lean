/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.NormalGlobalMaximumTriple
public import LeanPool.GoldbergSeymour.ScheideGlobalMaximumFixedPairMaximal
public import LeanPool.GoldbergSeymour.ScheideGlobalMaximumMissingCounts
public import LeanPool.GoldbergSeymour.ScheideMaximalKempePath
public import LeanPool.GoldbergSeymour.ScheideMaximumExtensionNormalWitness
public import LeanPool.GoldbergSeymour.ScheideReversedKempePathTree
public import LeanPool.GoldbergSeymour.TwoColorComponent

/-!
# Scheide Normalisation

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem ScheideNormalisation {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hglobal : GlobalMaximumTriple G k e0 phi T) :
    ∃ (alpha beta : Fin k) (p :
      (TwoColorIncidenceGraph G phi alpha beta).Walk
        (Sum.inl (T.vertex ⟨0, Nat.zero_lt_succ T.length⟩))
        (Sum.inl (T.vertex ⟨1, Nat.succ_lt_succ T.positive⟩)))
      (T' : TreeSequence G e0) (N : NormalGlobalMaximumTriple G k e0 phi T'),
    alpha ∈ MissingColors G phi (T.vertex ⟨0, Nat.zero_lt_succ T.length⟩) ∧
      beta ∈ MissingColors G phi (T.vertex ⟨1, Nat.succ_lt_succ T.positive⟩) ∧
        p.IsPath ∧
          {x | x ∈ p.support} =
              TwoColorComponent G phi alpha beta
                (Sum.inl (T.vertex ⟨0, Nat.zero_lt_succ T.length⟩)) ∧
            TreeSequenceVertexSet T' = TreeSequenceVertexSet T ∧
              N.alpha = alpha ∧ N.beta = beta ∧ N.height = p.length / 2 + 1 := by
  classical
  let i0 : Fin (T.length + 1) := ⟨0, Nat.zero_lt_succ T.length⟩
  let i1 : Fin (T.length + 1) := ⟨1, Nat.succ_lt_succ T.positive⟩
  have hfirstEnds : G.ends e0 = s(T.vertex i1, T.vertex i0) := by
    obtain ⟨i, hi⟩ := T.attaches ⟨0, T.positive⟩
    have hi0 : i = 0 := Fin.eq_zero i
    subst i
    rw [T.first_edge] at hi
    have hsucc : (⟨0, T.positive⟩ : Fin T.length).succ = i1 := by
      apply Fin.ext
      rfl
    have hcast : Fin.castLT (0 : Fin 1)
        (Nat.lt_trans (0 : Fin 1).isLt
          (Nat.succ_lt_succ (⟨0, T.positive⟩ : Fin T.length).isLt)) = i0 := by
      apply Fin.ext
      rfl
    rw [hsucc, hcast] at hi
    exact hi
  have hinc0 : Incident G (T.vertex i0) e0 := by
    unfold Incident
    rw [hfirstEnds]
    simp
  have hinc1 : Incident G (T.vertex i1) e0 := by
    unfold Incident
    rw [hfirstEnds]
    simp
  have hi0mem : T.vertex i0 ∈ TreeSequenceVertexSet T := by
    simp [TreeSequenceVertexSet]
  have hi1mem : T.vertex i1 ∈ TreeSequenceVertexSet T := by
    simp [TreeSequenceVertexSet]
  have hcount0 :=
    (ScheideGlobalMaximumMissingCounts G k e0 phi T hglobal
      (T.vertex i0) hi0mem).1 hinc0
  have hcount1 :=
    (ScheideGlobalMaximumMissingCounts G k e0 phi T hglobal
      (T.vertex i1) hi1mem).1 hinc1
  obtain ⟨alpha, halpha⟩ := Finset.card_pos.mp (by omega :
    0 < (MissingColors G phi (T.vertex i0)).card)
  obtain ⟨beta, hbeta⟩ := Finset.card_pos.mp (by omega :
    0 < (MissingColors G phi (T.vertex i1)).card)
  have hmax : FixedPairMaximalTashkinovTree G e0 phi T :=
    ScheideGlobalMaximumFixedPairMaximal G k e0 phi T hglobal
  obtain ⟨_, p, hp, hsupport, hdiv, _, _⟩ :=
    ScheideMaximalKempePath G k e0 phi T T hglobal.1 hmax hglobal.2.1
      i0 i1 (by simp [i0, i1]) alpha beta halpha hbeta
  obtain ⟨C⟩ := ScheideReversedKempePathTree G k e0 phi T hglobal.1
    alpha beta halpha hbeta p hp hdiv
  obtain ⟨T', N, hvertexSet, hNalpha, hNbeta, hheight⟩ :=
    ScheideMaximumExtensionNormalWitness G k e0 phi T hglobal hmax
      alpha beta halpha hbeta p hp C
  exact ⟨alpha, beta, p, T', N, halpha, hbeta, hp, hsupport,
    hvertexSet, hNalpha, hNbeta, hheight⟩

end GoldbergSeymour

end
