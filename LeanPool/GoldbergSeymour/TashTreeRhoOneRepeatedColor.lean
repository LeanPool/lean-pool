/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashTreeProperPrefixElementary

public import LeanPool.GoldbergSeymour.TreeSequencePrefix

/-!
# Tash Tree Rho One Repeated Color

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem TashTreeRhoOneRepeatedColor {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (hmin : TashTreeMinimumBadPair G k e0 phi T)
    (hlen : 2 ≤ T.length) (_ : TashTreePathIndex G T = 1) :
    ∃ beta : Fin k, ∃ i : Fin T.length,
      beta ∈ MissingColors G phi (T.vertex i.castSucc) ∧
      beta ∈ MissingColors G phi (T.vertex (Fin.last T.length)) := by
  classical
  let q := T.length - 1
  have hqpos : 1 ≤ q := by omega
  have hqle : q ≤ T.length := Nat.sub_le _ _
  let S := TreeSequencePrefix T q hqpos hqle
  have hprefix : TreeSequenceInitialSegment S T := by
    unfold TreeSequenceInitialSegment
    refine ⟨?_, ?_, ?_⟩
    · change q ≤ T.length
      exact hqle
    · intro i
      dsimp [S, TreeSequencePrefix]
    · intro j
      dsimp [S, TreeSequencePrefix]
  have helemS : ColoredVertexSetElementary G phi (TreeSequenceVertexSet S) :=
    TashTreeProperPrefixElementary G k e0 phi T S hmin hprefix (by
      change q < T.length
      omega)
  have hnot : ¬ ColoredVertexSetElementary G phi (TreeSequenceVertexSet T) := hmin.1.2.2
  unfold ColoredVertexSetElementary at hnot
  have hbad : ∃ u, u ∈ TreeSequenceVertexSet T ∧ ∃ v, v ∈ TreeSequenceVertexSet T ∧
      u ≠ v ∧ ¬ Disjoint (MissingColors G phi u) (MissingColors G phi v) := by
    by_contra hnone
    apply hnot
    intro u hu v hv huv
    by_contra hdis
    apply hnone
    exact ⟨u, hu, v, hv, huv, hdis⟩
  rcases hbad with ⟨u, hu, v, hv, huv, hdis⟩
  have hbadDis := hdis
  rw [Finset.disjoint_left] at hdis
  push Not at hdis
  rcases hdis with ⟨beta, hbu, hbv⟩
  have huindex : ∃ a : Fin (T.length + 1), T.vertex a = u := by
    simpa [TreeSequenceVertexSet] using (Finset.mem_image.mp hu)
  have hvindex : ∃ a : Fin (T.length + 1), T.vertex a = v := by
    simpa [TreeSequenceVertexSet] using (Finset.mem_image.mp hv)
  have outsideLast : ∀ {w : V} (a : Fin (T.length + 1)),
      T.vertex a = w → w ∉ TreeSequenceVertexSet S →
        a = Fin.last T.length := by
    intro w a haw hwa
    by_contra hneq
    have hval : a.val ≠ T.length := by
      intro hh
      apply hneq
      apply Fin.ext
      exact hh
    have halt : a.val < T.length := by
      omega
    apply hwa
    rw [TreeSequenceVertexSet]
    apply Finset.mem_image.mpr
    have hsmall : a.val < q + 1 := by omega
    refine ⟨⟨a.val, hsmall⟩, Finset.mem_univ _, ?_⟩
    have hidx : Fin.castLE (Nat.succ_le_succ hqle)
        ⟨a.val, hsmall⟩ = a := by
      apply Fin.ext
      rfl
    dsimp [S, TreeSequencePrefix]
    simpa [hidx] using haw
  have prefixIndex : ∀ {w : V}, w ∈ TreeSequenceVertexSet S →
      ∃ i : Fin T.length, T.vertex i.castSucc = w := by
    intro w hw
    rw [TreeSequenceVertexSet] at hw
    rcases Finset.mem_image.mp hw with ⟨c, -, hc⟩
    have hcq : c.val < q + 1 := by
      simpa [S, TreeSequencePrefix] using c.isLt
    have hct : c.val < T.length := by
      omega
    let i : Fin T.length := ⟨c.val, hct⟩
    refine ⟨i, ?_⟩
    calc
      T.vertex i.castSucc = S.vertex c := by
        dsimp [S, TreeSequencePrefix]
        congr 1
      _ = w := hc
  by_cases hus : u ∈ TreeSequenceVertexSet S
  · have hvs : v ∉ TreeSequenceVertexSet S := by
      intro hmem
      exact hbadDis (helemS hus hmem huv)
    obtain ⟨i, hi⟩ := prefixIndex hus
    obtain ⟨b, hb⟩ := hvindex
    have hbLast : b = Fin.last T.length := outsideLast b hb hvs
    refine ⟨beta, i, ?_, ?_⟩
    · rw [hi]
      exact hbu
    · rw [← hb, hbLast] at hbv
      exact hbv
  · have hvs : v ∈ TreeSequenceVertexSet S := by
      by_contra hmem
      obtain ⟨a, ha⟩ := huindex
      obtain ⟨b, hb⟩ := hvindex
      have haLast : a = Fin.last T.length := outsideLast a ha hus
      have hbLast : b = Fin.last T.length := outsideLast b hb hmem
      apply huv
      calc
        u = T.vertex a := ha.symm
        _ = T.vertex b := by rw [haLast, hbLast]
        _ = v := hb
    obtain ⟨i, hi⟩ := prefixIndex hvs
    obtain ⟨a, ha⟩ := huindex
    have haLast : a = Fin.last T.length := outsideLast a ha hus
    refine ⟨beta, i, ?_, ?_⟩
    · rw [hi]
      exact hbv
    · rw [← ha, haLast] at hbu
      exact hbu

end GoldbergSeymour

end
