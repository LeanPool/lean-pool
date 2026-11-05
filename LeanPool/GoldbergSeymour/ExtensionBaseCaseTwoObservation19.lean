/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TashkinovClosure

/-!
# Extension Base Case Two Observation19

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem ExtensionBaseCaseTwoObservation19 {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    (rho1 : PartialEdgeColoring E k) (seed TjPrime : TreeSequence G e0)
    (terminalSupport : V) (supportColors : Finset (Fin k))
    (deltaN : Fin k)
    (hclosure : TashkinovClosure rho1 seed TjPrime)
    (hterminal : terminalSupport ∈ TreeSequenceVertexSet TjPrime)
    (hcaseTwo : ∀ v : V,
      v ∈ (TreeSequenceVertexSet TjPrime).erase terminalSupport →
      MissingColors G rho1 v ∩ supportColors = ∅)
    (hterminalColors :
      MissingColors G rho1 terminalSupport ∩ supportColors = {deltaN}) :
    TreeMissingColors rho1 TjPrime ∩ supportColors = {deltaN} ∧
      ∀ a : Fin TjPrime.length, seed.length ≤ a.val →
        ∀ c : Fin k, c ∈ supportColors \ {deltaN} →
          rho1 (TjPrime.edge a) ≠ some c := by
  classical
  rcases hclosure with ⟨hseq, hclosed⟩
  have initial_subset : ∀ {A B : TreeSequence G e0},
      TreeSequenceInitialSegment A B →
        TreeSequenceVertexSet A ⊆ TreeSequenceVertexSet B := by
    intro A B hinit v hv
    simp only [TreeSequenceVertexSet, Finset.mem_image] at hv ⊢
    obtain ⟨i, hi, hvi⟩ := hv
    obtain ⟨hlen, hvertices, hedges⟩ := hinit
    refine ⟨Fin.castLE (Nat.succ_le_succ hlen) i, Finset.mem_univ _, ?_⟩
    exact (hvertices i).trans hvi
  have missing_subset : ∀ {A B : TreeSequence G e0},
      TreeSequenceVertexSet A ⊆ TreeSequenceVertexSet B →
      TreeMissingColors rho1 A ⊆ TreeMissingColors rho1 B := by
    intro A B hab c hc
    unfold TreeMissingColors at hc ⊢
    obtain ⟨v, hv, hvc⟩ := Finset.mem_biUnion.mp hc
    apply Finset.mem_biUnion.mpr
    exact ⟨v, hab hv, hvc⟩
  have tree_subset : ∀ {A : TreeSequence G e0},
      TashkinovAugmentationSequence rho1 seed A →
      TreeSequenceVertexSet seed ⊆ TreeSequenceVertexSet A := by
    intro A hA
    unfold TashkinovAugmentationSequence at hA
    induction hA with
    | refl => exact Finset.Subset.rfl
    | tail hreach hstep ih =>
        exact ih.trans (initial_subset hstep.2.1)
  have set_result : TreeMissingColors rho1 TjPrime ∩ supportColors =
      {deltaN} := by
    apply Finset.ext
    intro c
    constructor
    · intro hc
      have hcm : c ∈ TreeMissingColors rho1 TjPrime := (Finset.mem_inter.mp hc).1
      have hcs : c ∈ supportColors := (Finset.mem_inter.mp hc).2
      unfold TreeMissingColors at hcm
      obtain ⟨v, hv, hvm⟩ := Finset.mem_biUnion.mp hcm
      by_cases hvt : v = terminalSupport
      · subst v
        have hboth : c ∈ MissingColors G rho1 terminalSupport ∩ supportColors :=
          Finset.mem_inter.mpr ⟨hvm, hcs⟩
        have hd : c ∈ ({deltaN} : Finset (Fin k)) :=
          hterminalColors ▸ hboth
        simpa using hd
      · have hver : v ∈ (TreeSequenceVertexSet TjPrime).erase terminalSupport := by
          exact Finset.mem_erase.mpr ⟨hvt, hv⟩
        have hempty := hcaseTwo v hver
        have hboth : c ∈ MissingColors G rho1 v ∩ supportColors :=
          Finset.mem_inter.mpr ⟨hvm, hcs⟩
        rw [hempty] at hboth
        exact False.elim (by simp at hboth)
    · intro hc
      have hcd : c = deltaN := by simpa using hc
      subst c
      have hmiss : deltaN ∈ MissingColors G rho1 terminalSupport := by
        have ht : deltaN ∈ MissingColors G rho1 terminalSupport ∩ supportColors := by
          rw [hterminalColors]
          simp
        exact (Finset.mem_inter.mp ht).1
      have htm : deltaN ∈ TreeMissingColors rho1 TjPrime := by
        unfold TreeMissingColors
        exact Finset.mem_biUnion.mpr ⟨terminalSupport, hterminal, hmiss⟩
      apply Finset.mem_inter.mpr
      have ht : deltaN ∈ MissingColors G rho1 terminalSupport ∩ supportColors := by
        rw [hterminalColors]
        simp
      exact ⟨htm, (Finset.mem_inter.mp ht).2⟩
  refine ⟨set_result, ?_⟩
  have edge_colors :
    ∀ {A : TreeSequence G e0}, TashkinovAugmentationSequence rho1 seed A →
    ∀ a : Fin A.length, seed.length ≤ a.val →
    ∀ c : Fin k, rho1 (A.edge a) = some c → c ∈ TreeMissingColors rho1 A := by
    intro A hA
    unfold TashkinovAugmentationSequence at hA
    induction hA with
    | refl =>
        intro a ha c hcolor
        omega
    | tail hreach hstep ih =>
        rename_i mid last
        obtain ⟨hlen, hinit, d, hcolor, hmissing⟩ := hstep
        intro a ha c hedge
        by_cases hnew : a.val = mid.length
        · have hlast : a = Fin.cast hlen.symm (Fin.last mid.length) := by
            apply Fin.ext
            simp [Fin.last]
            omega
          rw [hlast] at hedge
          have hdc : c = d := by
            simpa [hcolor] using hedge.symm
          subst c
          apply missing_subset (initial_subset hinit)
          exact hmissing
        · have hold : a.val < mid.length := by
            have hbound : a.val < mid.length + 1 := by
              rw [← hlen]
              exact a.isLt
            omega
          let j : Fin mid.length := ⟨a.val, hold⟩
          have hja : Fin.castLE hinit.1 j = a := by
            apply Fin.ext
            rfl
          have hmid : seed.length ≤ j.val := by
            exact ha
          have hmidcolor : rho1 (mid.edge j) = some c := by
            rw [← hinit.2.2 j]
            rw [hja]
            exact hedge
          exact missing_subset (initial_subset hinit) (ih j hmid c hmidcolor)
  intro a ha c hc heq
  have hcm : c ∈ TreeMissingColors rho1 TjPrime := by
    apply edge_colors hseq a ha c
    exact heq
  have hnot : c ∉ ({deltaN} : Finset (Fin k)) := by
    simpa using (Finset.mem_sdiff.mp hc).2
  have hcs : c ∈ supportColors := (Finset.mem_sdiff.mp hc).1
  have hcsingle : c ∈ TreeMissingColors rho1 TjPrime ∩ supportColors :=
    Finset.mem_inter.mpr ⟨hcm, hcs⟩
  have hcd : c ∈ ({deltaN} : Finset (Fin k)) :=
    set_result ▸ hcsingle
  exact hnot hcd

end GoldbergSeymour

end
