/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ColoredVertexSetElementary
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequenceInitialSegment
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegmentVertexSetSubset
public import LeanPool.GoldbergSeymour.TwoColorComponentSwapMissingBehavior

/-!
# P2668_T2_Copy Augmentation Prefix

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem P2668_T2_CopyAugmentationPrefix
    {V E : Type*} [Finite V] [Fintype E] {G : LooplessMultigraph V E} {k : Nat} {e0 : E}
    (phi : PartialEdgeColoring E k) (alpha beta : Fin k)
    (hab : alpha ≠ beta) (hproper : IsProperEdgeColoring G phi)
    (z : Sum V E) (S R : TreeSequence G e0) (X : Finset V)
    (hElem : ColoredVertexSetElementary G phi X)
    (hRX : TreeSequenceVertexSet R ⊆ X)
    (u v : V) (huX : u ∈ X) (huR : u ∉ TreeSequenceVertexSet R)
    (hvR : v ∈ TreeSequenceVertexSet R) (hvS : v ∉ TreeSequenceVertexSet S)
    (hua : alpha ∈ MissingColors G phi u)
    (hvb : beta ∈ MissingColors G phi v)
    (hroute : TashkinovAugmentationSequence phi S R) :
    ∃ B : TreeSequence G e0, TreeSequenceInitialSegment B R ∧
      B.vertex (Fin.last B.length) = v ∧
      TashkinovAugmentationSequence
        (TwoColorComponentSwap G phi alpha beta z) S B := by
  classical
  let _ := Fintype.ofFinite V
  let psi := TwoColorComponentSwap G phi alpha beta z
  have unaffected := (TwoColorComponentSwapMissingBehavior
    G phi alpha beta hab hproper z).2.2.2
  have copy :
    ∀ (A : TreeSequence G e0), TashkinovAugmentationSequence phi A R → v ∉ TreeSequenceVertexSet A
        →
    ∃ B : TreeSequence G e0, TreeSequenceInitialSegment B R ∧ B.vertex (Fin.last B.length) = v ∧
        TashkinovAugmentationSequence psi A B := by
    intro A hr
    induction hr using Relation.ReflTransGen.head_induction_on with
    | refl => intro hv; exact (hv hvR).elim
    | @head A D hstep htail ih =>
      intro hvA
      have hDR := TashkinovAugmentationSequenceInitialSegment phi D R htail
      obtain ⟨hlen, hAD, c, hec, hc⟩ := hstep
      obtain ⟨w, hwA, hcw⟩ := Finset.mem_biUnion.mp hc
      have hwR : w ∈ TreeSequenceVertexSet R :=
        TreeSequenceInitialSegmentVertexSetSubset hDR
          (TreeSequenceInitialSegmentVertexSetSubset hAD hwA)
      have hwu : w ≠ u := by intro h; exact huR (h ▸ hwR)
      have hwv : w ≠ v := by intro h; exact hvA (h ▸ hwA)
      have hca : c ≠ alpha := by
        intro h
        exact (Finset.disjoint_left.mp
          (hElem (hRX hwR) huX hwu)) (h ▸ hcw) hua
      have hcb : c ≠ beta := by
        intro h
        exact (Finset.disjoint_left.mp
          (hElem (hRX hwR) (hRX hvR) hwv)) (h ▸ hcw) hvb
      have newStep : TashkinovAugmentation psi A D := by
        refine ⟨hlen, hAD, c, ?_, ?_⟩
        · simp [psi, TwoColorComponentSwap, hec, hca, hcb]
        · exact Finset.mem_biUnion.mpr
            ⟨w, hwA, (unaffected w c hca hcb).mpr hcw⟩
      by_cases hvD : v ∈ TreeSequenceVertexSet D
      · have hlast : D.vertex (Fin.last D.length) = v := by
          obtain ⟨i, hi⟩ := by simpa [TreeSequenceVertexSet] using hvD
          by_cases hilast : i = Fin.last D.length
          · simpa [hilast] using hi
          · have hiA : i.val < A.length + 1 := by
              have hival : i.val ≠ D.length := by
                intro h
                apply hilast
                exact Fin.ext h
              have hibound := i.isLt
              omega
            let j : Fin (A.length + 1) := ⟨i.val, hiA⟩
            have hj : Fin.castLE (Nat.succ_le_succ hAD.1) j = i := by
              apply Fin.ext
              rfl
            have hjv : A.vertex j = v := by
              rw [← hAD.2.1 j, hj]
              exact hi
            exact (hvA (by simp [TreeSequenceVertexSet, ← hjv])).elim
        exact ⟨D, hDR, hlast, Relation.ReflTransGen.single newStep⟩
      · obtain ⟨B, hBR, hlast, hAB⟩ := ih hvD
        exact ⟨B, hBR, hlast, Relation.ReflTransGen.head newStep hAB⟩
  exact copy S hroute hvS

end GoldbergSeymour

end
