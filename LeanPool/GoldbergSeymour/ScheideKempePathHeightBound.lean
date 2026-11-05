/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.FixedPairMaximalTashkinovTree
public import LeanPool.GoldbergSeymour.GlobalMaximumTriple
public import LeanPool.GoldbergSeymour.Incident
public import LeanPool.GoldbergSeymour.IsOneEdgeUncolored
public import LeanPool.GoldbergSeymour.KTriple
public import LeanPool.GoldbergSeymour.LooplessMultigraph
public import LeanPool.GoldbergSeymour.MissingColors
public import LeanPool.GoldbergSeymour.NormalGlobalMaximumTriple
public import LeanPool.GoldbergSeymour.ScheideGraphHeight
public import LeanPool.GoldbergSeymour.ScheideGlobalMaximumFixedPairMaximal
public import LeanPool.GoldbergSeymour.ScheideMaximumExtensionNormalWitness
public import LeanPool.GoldbergSeymour.ScheideMaximalExtendsEveryTree
public import LeanPool.GoldbergSeymour.ScheideMaximalKempePath
public import LeanPool.GoldbergSeymour.ScheideReversedKempePathTree
public import LeanPool.GoldbergSeymour.TashkinovOrder
public import LeanPool.GoldbergSeymour.TashkinovTree
public import LeanPool.GoldbergSeymour.TreeSequence
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegment
public import LeanPool.GoldbergSeymour.TreeSequenceVertexSet
public import LeanPool.GoldbergSeymour.TwoColorComponent
public import LeanPool.GoldbergSeymour.TwoColorIncidenceGraph

/-!
# Scheide Kempe Path Height Bound

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem ScheideKempePathHeightBound {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hglobal : GlobalMaximumTriple G k e0 phi T)
    (alpha beta : Fin k)
    (halpha : alpha ∈ MissingColors G phi
      (T.vertex ⟨0, Nat.zero_lt_succ T.length⟩))
    (hbeta : beta ∈ MissingColors G phi
      (T.vertex ⟨1, Nat.succ_lt_succ T.positive⟩)) :
    ∃ p :
      (TwoColorIncidenceGraph G phi alpha beta).Walk
        (Sum.inl (T.vertex ⟨0, Nat.zero_lt_succ T.length⟩))
        (Sum.inl (T.vertex ⟨1, Nat.succ_lt_succ T.positive⟩)),
    p.IsPath ∧
      {x | x ∈ p.support} =
          TwoColorComponent G phi alpha beta
            (Sum.inl (T.vertex ⟨0, Nat.zero_lt_succ T.length⟩)) ∧
        4 ∣ p.length ∧
          (∀ v : V, Sum.inl v ∈ p.support → v ∈ TreeSequenceVertexSet T) ∧
            p.length / 2 + 1 ≤ ScheideGraphHeight G := by
  classical
  have hmax : FixedPairMaximalTashkinovTree G e0 phi T :=
    ScheideGlobalMaximumFixedPairMaximal G k e0 phi T hglobal
  obtain ⟨_, p, hp, hsupport, hdiv, hvertices, _⟩ :=
    ScheideMaximalKempePath G k e0 phi T T hglobal.1 hmax hglobal.2.1
      ⟨0, Nat.zero_lt_succ T.length⟩
      ⟨1, Nat.succ_lt_succ T.positive⟩ (by norm_num)
      alpha beta halpha hbeta
  obtain ⟨C⟩ := ScheideReversedKempePathTree G k e0 phi T hglobal.1
    alpha beta halpha hbeta p hp hdiv
  obtain ⟨T', N, _, _, _, hN⟩ :=
    ScheideMaximumExtensionNormalWitness G k e0 phi T hglobal hmax
      alpha beta halpha hbeta p hp C
  have hheight : p.length / 2 + 1 ≤ ScheideGraphHeight G := by
    rw [← hN]
    have hcard : T'.length + 1 ≤ Fintype.card V := by
      simpa using Fintype.card_le_of_injective T'.vertex T'.vertex_injective
    have hNcard : N.height < Fintype.card V + 1 :=
      lt_of_le_of_lt N.height_upper (by omega)
    let heights := (Finset.range (Fintype.card V + 1)).filter fun q =>
      ∃ (m : ℕ) (f : E) (c : PartialEdgeColoring E m)
        (S : TreeSequence G f),
        ∃ M : NormalGlobalMaximumTriple G m f c S, M.height = q
    have hmem : N.height ∈ heights := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_range.mpr hNcard, k, e0, phi, T', N, rfl⟩
    unfold ScheideGraphHeight
    dsimp only
    apply Finset.le_max'
    exact Finset.mem_insert_of_mem hmem
  exact ⟨p, hp, hsupport, hdiv, hvertices, hheight⟩

end GoldbergSeymour

end
