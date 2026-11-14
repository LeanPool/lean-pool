/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.TreeInterchangeableFacts

public import LeanPool.GoldbergSeymour.ElementaryClosedExitPairExtendsTriple
public import LeanPool.GoldbergSeymour.ElementaryClosedNoninterchangeableExitPair

public import LeanPool.GoldbergSeymour.TchangeKempeClosurePreparation
public import LeanPool.GoldbergSeymour.TchangeOutsideSwapPreparation
public import LeanPool.GoldbergSeymour.TchangeStrictShortening

/-!
# Tchange

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem Tchange {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (htriple : KTriple G k e0 phi)
    (hT : TashkinovTree G e0 phi T)
    (hclosed : ColoredVertexSetClosed G phi (TreeSequenceVertexSet T))
    (alpha beta : Fin k)
    (hmissing : alpha ∈ TreeMissingColors phi T ∨
      beta ∈ TreeMissingColors phi T) :
    TreeInterchangeable G T phi alpha beta := by
  classical
  by_cases heq : alpha = beta
  · subst beta
    simp [TreeInterchangeable, TwoColorPathComponent]
  by_contra hnot
  have helementary :
      ColoredVertexSetElementary G phi (TreeSequenceVertexSet T) :=
    TashTree G k e0 phi T htriple hT
  have interchangeSwap : TreeInterchangeable G T phi alpha beta ↔
      TreeInterchangeable G T phi beta alpha :=
    ⟨TreeInterchangeable.symm, TreeInterchangeable.symm⟩
  have boundaryEmpty (c : Fin k) (hc : c ∈ TreeMissingColors phi T) :
      BoundaryColorEdges G phi (TreeSequenceVertexSet T) c = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro f hf
    obtain ⟨v, hv, hvm⟩ := Finset.mem_biUnion.mp hc
    have hdata := Finset.mem_filter.mp hf
    exact (hclosed hdata.1 hv hdata.2) hvm
  have buildCounterexample (a b : Fin k) (hab : a ≠ b)
      (ha : a ∈ TreeMissingColors phi T)
      (hn : ¬ TreeInterchangeable G T phi a b) :
      Nonempty (TchangeCounterexample G k e0) := by
    have haclosed : TreeColorSetClosed G phi T {a} := by
      intro c hc
      have hca : c = a := by simpa using hc
      subst c
      exact boundaryEmpty a ha
    obtain ⟨a1, b1, a2, b2, P1, P2, f1, f2, hP1, hP2,
        h12, ha12, hb12, hf1, hf2, hi1, hi2, hs1, hs2⟩ :=
      ElementaryClosedNoninterchangeableExitPair G T phi htriple.2.2.2.1
        helementary a b hab ha haclosed hn
    have hb : b ∉ TreeMissingColors phi T := by
      intro hb
      have hempty := boundaryEmpty b hb
      rw [hempty] at hf1
      simp at hf1
    obtain ⟨a3, b3, P3, f3, hP3, h13, h23, ha31, ha32, hb31, hb32,
        hf3, hi3, hs3⟩ :=
      ElementaryClosedExitPairExtendsTriple G T phi htriple.2.2.2.1
        helementary a b hab ha haclosed hb a1 b1 a2 b2 P1 P2 hP1 hP2
        h12 ha12 hb12
    exact ⟨{
      phi := phi
      T := T
      a := a
      b := b
      colorsDistinct := hab
      triple := htriple
      tree := hT
      closed := hclosed
      aMissing := ha
      bNotMissing := hb
      a1 := a1
      b1 := b1
      a2 := a2
      b2 := b2
      a3 := a3
      b3 := b3
      P1 := P1
      P2 := P2
      P3 := P3
      exit1 := hP1
      exit2 := hP2
      exit3 := hP3
      disjoint12 := h12
      disjoint13 := h13
      disjoint23 := h23
      remote12 := ha12
      remote13 := ha31.symm
      remote23 := ha32.symm
      tree12 := hb12
      tree13 := hb31.symm
      tree23 := hb32.symm
      f1 := f1
      f2 := f2
      f3 := f3
      boundary1 := hf1
      boundary2 := hf2
      boundary3 := hf3
      incident1 := hi1
      incident2 := hi2
      incident3 := hi3
      support1 := hs1
      support2 := hs2
      support3 := hs3 }⟩
  have initial : Nonempty (TchangeCounterexample G k e0) := by
    by_cases ha : alpha ∈ TreeMissingColors phi T
    · exact buildCounterexample alpha beta heq ha hnot
    · have hb : beta ∈ TreeMissingColors phi T := hmissing.resolve_left ha
      have hnot' : ¬ TreeInterchangeable G T phi beta alpha := by
        intro h
        exact hnot (interchangeSwap.mpr h)
      exact buildCounterexample beta alpha (fun h => heq h.symm) hb hnot'
  have descend : ∀ C : TchangeCounterexample G k e0,
      ∃ D : TchangeCounterexample G k e0,
        TchangeCounterexampleMeasure D < TchangeCounterexampleMeasure C := by
    intro C
    obtain ⟨C1, _, _, _, hgamma, h13, h23, hmeasure⟩ :=
      TchangeOutsideSwapPreparation C
    obtain ⟨K⟩ := TchangeKempeClosurePreparation C1 hgamma h13 h23
    obtain ⟨D, hshort⟩ := TchangeStrictShortening C1 K
    exact ⟨D, by omega⟩
  obtain ⟨C0⟩ := initial
  let P : Nat → Prop := fun n => ∃ C : TchangeCounterexample G k e0,
    TchangeCounterexampleMeasure C = n
  have hex : ∃ n, P n :=
    ⟨TchangeCounterexampleMeasure C0, C0, rfl⟩
  obtain ⟨Cmin, hmin⟩ := Nat.find_spec hex
  obtain ⟨D, hshort⟩ := descend Cmin
  have hleast : Nat.find hex ≤ TchangeCounterexampleMeasure D :=
    Nat.find_min' hex ⟨D, rfl⟩
  dsimp [P] at hmin
  omega

end GoldbergSeymour

end
