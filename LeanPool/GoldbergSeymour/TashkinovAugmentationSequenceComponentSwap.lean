/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.MissingColors
public import LeanPool.GoldbergSeymour.TashkinovAugmentation
public import LeanPool.GoldbergSeymour.TashkinovAugmentationSequence
public import LeanPool.GoldbergSeymour.TreeMissingColors
public import LeanPool.GoldbergSeymour.TreeSequenceInitialSegment
public import LeanPool.GoldbergSeymour.TreeSequenceVertexSet
public import LeanPool.GoldbergSeymour.TwoColorComponentSwap

/-!
# Tashkinov Augmentation Sequence Component Swap

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem TashkinovAugmentationSequenceComponentSwap {V E : Type*}
    [Finite V] [Fintype E] (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (alpha beta : Fin k)
    (_ : alpha ≠ beta) (z : Sum V E)
    (X Y : TreeSequence G e0)
    (hsequence : TashkinovAugmentationSequence phi X Y)
    (halpha : alpha ∈ TreeMissingColors
      (TwoColorComponentSwap G phi alpha beta z) X)
    (hbeta : beta ∈ TreeMissingColors
      (TwoColorComponentSwap G phi alpha beta z) X) :
    TashkinovAugmentationSequence (TwoColorComponentSwap G phi alpha beta z) X Y := by
  classical
  let _ := Fintype.ofFinite V
  let sigma := TwoColorComponentSwap G phi alpha beta z
  have vertexTransfer {A B : TreeSequence G e0}
      (hab : TreeSequenceInitialSegment A B) {v : V}
      (hv : v ∈ TreeSequenceVertexSet A) :
      v ∈ TreeSequenceVertexSet B := by
    simp only [TreeSequenceVertexSet, Finset.mem_image, Finset.mem_univ, true_and] at hv ⊢
    rcases hv with ⟨i, hi⟩
    rcases hab with ⟨hlen, hvertices, hedges⟩
    refine ⟨Fin.castLE (Nat.succ_le_succ hlen) i, ?_⟩
    exact (hvertices i).trans hi
  have missingTransfer {c : Fin k} {A B : TreeSequence G e0}
      (hab : TreeSequenceInitialSegment A B)
      (hc : c ∈ TreeMissingColors sigma A) :
      c ∈ TreeMissingColors sigma B := by
    simp only [TreeMissingColors, Finset.mem_biUnion] at hc ⊢
    rcases hc with ⟨v, hv, hvc⟩
    exact ⟨v, vertexTransfer hab hv, hvc⟩
  have missingStable {c : Fin k} (hcα : c ≠ alpha) (hcβ : c ≠ beta)
      {v : V} (hv : c ∈ MissingColors G phi v) :
      c ∈ MissingColors G sigma v := by
    unfold MissingColors at hv ⊢
    rw [Finset.mem_sdiff] at hv ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hp
    apply hv.2
    rw [PresentColors]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [PresentColors] at hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    rcases hp with ⟨e, he, hpe⟩
    refine ⟨e, he, ?_⟩
    change TwoColorComponentSwap G phi alpha beta z e = some c at hpe
    unfold TwoColorComponentSwap at hpe
    by_cases hcomp : Sum.inr e ∈ TwoColorComponent G phi alpha beta z
    · simp only [ite_eq_left hcomp] at hpe
      by_cases ha : phi e = some alpha
      · simp only [ite_eq_left ha] at hpe
        exact (hcβ (Option.some.inj hpe).symm).elim
      · by_cases hb : phi e = some beta
        · simp only [ite_eq_right ha, ite_eq_left hb] at hpe
          exact (hcα (Option.some.inj hpe).symm).elim
        · simp only [ite_eq_right ha, ite_eq_right hb] at hpe
          exact hpe
    · simpa [hcomp] using hpe
  have stepTransfer {A B : TreeSequence G e0}
      (hstep : TashkinovAugmentation phi A B)
      (ha : alpha ∈ TreeMissingColors sigma A)
      (hb : beta ∈ TreeMissingColors sigma A) :
      TashkinovAugmentation sigma A B := by
    rcases hstep with ⟨hlen, hinit, c, hedge, hc⟩
    refine ⟨hlen, hinit, ?_⟩
    have hcolor : phi (B.edge (Fin.cast hlen.symm (Fin.last A.length))) = some c := hedge
    have hcases : c = alpha ∨ c = beta ∨ (c ≠ alpha ∧ c ≠ beta) := by
      by_cases ha : c = alpha
      · exact Or.inl ha
      · by_cases hb : c = beta
        · exact Or.inr (Or.inl hb)
        · exact Or.inr (Or.inr ⟨ha, hb⟩)
    rcases hcases with hca | hcb | ⟨hcα, hcβ⟩
    · subst c
      by_cases hcomp : Sum.inr (B.edge (Fin.cast hlen.symm (Fin.last A.length))) ∈
          TwoColorComponent G phi alpha beta z
      · refine ⟨beta, ?_, hb⟩
        simp [sigma, TwoColorComponentSwap, hcomp, hcolor]
      · refine ⟨alpha, ?_, ha⟩
        simp [sigma, TwoColorComponentSwap, hcomp, hcolor]
    · subst c
      by_cases hcomp : Sum.inr (B.edge (Fin.cast hlen.symm (Fin.last A.length))) ∈
          TwoColorComponent G phi alpha beta z
      · refine ⟨alpha, ?_, ha⟩
        simp [sigma, TwoColorComponentSwap, hcomp, hcolor]
      · refine ⟨beta, ?_, hb⟩
        simp [sigma, TwoColorComponentSwap, hcomp, hcolor]
    · refine ⟨c, ?_, ?_⟩
      · change sigma (B.edge (Fin.cast hlen.symm (Fin.last A.length))) = some c
        by_cases hcomp : Sum.inr (B.edge (Fin.cast hlen.symm (Fin.last A.length))) ∈
            TwoColorComponent G phi alpha beta z
        · simp [sigma, TwoColorComponentSwap, hcomp, hcolor, hcα, hcβ]
        · simp [sigma, TwoColorComponentSwap, hcomp, hcolor]
      · rw [TreeMissingColors] at hc
        rcases Finset.mem_biUnion.mp hc with ⟨v, hv, hvc⟩
        simp only [TreeMissingColors, Finset.mem_biUnion]
        exact ⟨v, hv, missingStable hcα hcβ hvc⟩
  have transport :
    ∀ (A B : TreeSequence G e0), TashkinovAugmentationSequence phi A B → alpha ∈ TreeMissingColors
        sigma A → beta ∈ TreeMissingColors sigma A → TashkinovAugmentationSequence sigma A B := by
    intro A B hreach
    unfold TashkinovAugmentationSequence at hreach ⊢
    induction hreach using Relation.ReflTransGen.head_induction_on with
    | refl =>
        intro ha hb
        exact Relation.ReflTransGen.refl
    | head hstep htail ih =>
        intro ha hb
        rcases hstep with ⟨hlen, hinit, c, hedge, hc⟩
        have hac := missingTransfer hinit ha
        have hbc := missingTransfer hinit hb
        exact Relation.ReflTransGen.head
          (stepTransfer ⟨hlen, hinit, c, hedge, hc⟩ ha hb) (ih hac hbc)
  exact transport X Y hsequence halpha hbeta

end GoldbergSeymour

end
