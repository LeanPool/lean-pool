/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequence
public import LeanPool.GoldbergSeymour.TashkinovTree
public import LeanPool.GoldbergSeymour.TreeSequencePrefix
public import Mathlib.Data.Fintype.EquivFin

/-!
# Tashkinov Tree From Length One Prefix

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

lemma TashkinovTreeFromLengthOnePrefix
    {V E : Type*} [Finite V] [Fintype E] {G : LooplessMultigraph V E} {k : Nat} {e0 : E}
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (htree : TashkinovTree G e0 phi T) :
    TashkinovAugmentationSequence phi (TreeSequencePrefix T 1 (by omega) T.positive) T := by
  classical
  let _ := Fintype.ofFinite V
  let pref (q : Nat) (hq : 1 <= q) (hqT : q <= T.length) :=
    TreeSequencePrefix T q hq hqT
  have step : forall (q : Nat) (hq : 1 <= q) (hqT : q < T.length),
      TashkinovAugmentation phi
        (pref q hq (Nat.le_of_lt hqT))
        (pref (q + 1) (by omega) (by omega)) := by
    intro q hq hqT
    let A := pref q hq (Nat.le_of_lt hqT)
    let B := pref (q + 1) (by omega) (by omega)
    let j : Fin T.length := ⟨q, hqT⟩
    obtain ⟨i, c, hcolor, hmissing⟩ := htree j hq
    have hlen : B.length = A.length + 1 := by
      change q + 1 = q + 1
      rfl
    refine ⟨hlen, ?_, c, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · change q <= q + 1
        omega
      · intro x
        change T.vertex _ = T.vertex _
        congr 1
      · intro x
        change T.edge _ = T.edge _
        congr 1
    · have hedge :
          B.edge (Fin.cast hlen.symm (Fin.last A.length)) = T.edge j := by
          change T.edge _ = T.edge _
          congr 1
      change phi (B.edge (Fin.cast hlen.symm (Fin.last A.length))) = some c
      rw [hedge]
      exact hcolor
    · change c ∈ TreeMissingColors phi A
      unfold TreeMissingColors
      apply Finset.mem_biUnion.mpr
      refine ⟨T.vertex (Fin.castLT i (Nat.lt_trans i.isLt
        (Nat.succ_lt_succ hqT))), ?_, hmissing⟩
      rw [TreeSequenceVertexSet]
      apply (@Finset.mem_image _ _ (Classical.decEq V)).mpr
      refine ⟨i, Finset.mem_univ _, ?_⟩
      change T.vertex _ = T.vertex _
      congr 1
  have build : forall (q : Nat) (hq : 1 <= q) (hqT : q <= T.length),
      TashkinovAugmentationSequence phi
        (pref 1 (by omega) T.positive) (pref q hq hqT) := by
    intro q
    induction q with
    | zero => intro hq; omega
    | succ q ih =>
        intro hq hqT
        by_cases hq0 : q = 0
        · subst q
          exact Relation.ReflTransGen.refl
        · have hqpos : 1 <= q := by omega
          have hqle : q <= T.length := by omega
          have hqlt : q < T.length := by omega
          exact Relation.ReflTransGen.tail (ih hqpos hqle)
            (step q hqpos hqlt)
  have hfull := build T.length T.positive (le_refl T.length)
  have prefixFull : pref T.length T.positive (le_refl T.length) = T := by
    cases T
    rfl
  simpa [pref, prefixFull] using hfull

end GoldbergSeymour

end
