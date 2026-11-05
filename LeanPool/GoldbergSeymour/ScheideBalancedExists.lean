/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ScheideBalancedFromMaxNormal

/-!
# Scheide Balanced Exists

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem ScheideBalancedExists {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hglobal : GlobalMaximumTriple G k e0 phi T) :
    ∃ (e1 : E) (psi : PartialEdgeColoring E k)
      (T' : TreeSequence G e1)
      (N' : NormalGlobalMaximumTriple G k e1 psi T'),
      BalancedGlobalMaximumTriple N' := by
  classical
  obtain ⟨alpha, beta, p, U, N0, ha, hb, hp, hc, hU, hα, hβ, hN⟩ :=
    ScheideNormalisation G k e0 phi T hglobal
  have hmem : ScheideGraphHeight G ∈
      insert 0 ((Finset.range (Fintype.card V + 1)).filter fun q =>
        ∃ (m : ℕ) (f : E) (c : PartialEdgeColoring E m)
          (S : TreeSequence G f),
          ∃ M : NormalGlobalMaximumTriple G m f c S, M.height = q) := by
    unfold ScheideGraphHeight
    exact Finset.max'_mem _ _
  have hpos : ScheideGraphHeight G ≠ 0 := by
    intro hz
    have hcard : U.length + 1 ≤ Fintype.card V := by
      simpa using Fintype.card_le_of_injective U.vertex U.vertex_injective
    have hbound : N0.height ≤ U.length + 1 := N0.height_upper
    have hle : N0.height ≤ ScheideGraphHeight G := by
      unfold ScheideGraphHeight
      apply Finset.le_max'
      apply Finset.mem_insert_of_mem
      apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_range.mpr (by omega)
      · exact ⟨k, e0, phi, U, N0, rfl⟩
    omega
  rcases Finset.mem_insert.mp hmem with hzero | hnormal
  · exact (hpos hzero).elim
  obtain ⟨m, f, c, S, M, hM⟩ := (Finset.mem_filter.mp hnormal).2
  have hm : m = k := by
    have hmχ := M.global.1.2.1
    have hkχ := hglobal.1.2.1
    omega
  subst m
  obtain ⟨S', M', hbal, hset, hcolors⟩ :=
    ScheideBalancedFromMaxNormal G k f c S M hM
  exact ⟨f, c, S', M', hbal⟩

end GoldbergSeymour

end
