/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ScheideGlobalMaximumOrder

public import LeanPool.GoldbergSeymour.ScheideStructuralSelectionData

/-!
# Scheide Structural Selection

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem ScheideStructuralSelection {V E : Type*}
    [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : LooplessMultigraph V E) (k : ℕ) (e0 : E)
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0)
    (C : ScheideStructuralConfiguration G k e0 phi T) :
    Nonempty (ScheideStructuralSelectionData G k e0 phi T C) := by
  classical
  let X : Finset V := TreeSequenceVertexSet T
  have hElementary : ColoredVertexSetElementary G phi X := by
    dsimp [X]
    exact (ScheideGlobalMaximumOrder G k e0 phi T C.globally_maximum).2.2.2.1
  have hBaseMem (q : Fin C.p) : C.y q ∈ X := by
    rw [← C.base_vertex_position q]
    simp only [X, TreeSequenceVertexSet, Finset.mem_image]
    have hlength := C.length_eq
    have hp : C.p ≤ T.length + 1 := by omega
    exact ⟨⟨q.val, q.isLt.trans_le hp⟩, Finset.mem_univ _, rfl⟩
  have hOldColorUnique (i : Fin C.s) :
      ∃! v : {v : V // v ∈ X},
        C.gamma i ∈ MissingColors G phi v.1 := by
    rcases C.block_color_missing_on_base i with ⟨q, hmissing⟩
    refine ⟨⟨C.y q, hBaseMem q⟩, hmissing, ?_⟩
    intro v hv
    apply Subtype.ext
    by_contra hne
    exact (Finset.disjoint_left.mp
      (hElementary v.property (hBaseMem q) hne)) hv hmissing
  have hSameOldColor (i : Fin C.s) {u v : V}
      (hu : u ∈ X) (hv : v ∈ X)
      (hmu : C.gamma i ∈ MissingColors G phi u)
      (hmv : C.gamma i ∈ MissingColors G phi v) : u = v := by
    rcases hOldColorUnique i with ⟨w, hw, hunique⟩
    have eu : (⟨u, hu⟩ : {x : V // x ∈ X}) = w := hunique _ hmu
    have ev : (⟨v, hv⟩ : {x : V // x ∈ X}) = w := hunique _ hmv
    exact congrArg Subtype.val (eu.trans ev.symm)
  have hExitMem (v : {v : V // v ∈ ScheideExitVertices T phi}) :
      v.1 ∈ X := by
    have hexit : ScheideExitVertex T phi v.1 := by
      simpa [ScheideExitVertices] using v.property
    rcases hexit with
      ⟨u, gamma, delta, hu, hgamma, hdelta, z, P, hP, i, hi, hv, hlast⟩
    exact hv
  let chosen : {v : V // v ∈ ScheideExitVertices T phi} → Fin C.s :=
    fun v => Classical.choose (C.exit_covered v.1 v.2)
  have hChosenMissing (v : {v : V // v ∈ ScheideExitVertices T phi}) :
      C.gamma (chosen v) ∈ MissingColors G phi v.1 := by
    exact Classical.choose_spec (C.exit_covered v.1 v.2)
  have hChosenInjective : Function.Injective chosen := by
    intro v w heq
    apply Subtype.ext
    apply hSameOldColor (chosen v) (hExitMem v) (hExitMem w)
    · exact hChosenMissing v
    · rw [heq]
      exact hChosenMissing w
  let retainedCount := (ScheideExitVertices T phi).card
  let exitEquiv : Fin retainedCount ≃
      {v : V // v ∈ ScheideExitVertices T phi} :=
    (Finset.equivFin (ScheideExitVertices T phi)).symm
  let retained : Fin retainedCount → Fin C.s := fun t => chosen (exitEquiv t)
  have hRetainedInjective : Function.Injective retained :=
    hChosenInjective.comp exitEquiv.injective
  have hRetainedMissing (t : Fin retainedCount) :
      C.gamma (retained t) ∈ MissingColors G phi (exitEquiv t).1 := by
    exact hChosenMissing (exitEquiv t)
  have hSelectedUnique (t t' : Fin retainedCount)
      (hmissing : C.gamma (retained t') ∈
        MissingColors G phi (exitEquiv t).1) : t' = t := by
    apply exitEquiv.injective
    apply Subtype.ext
    exact (hSameOldColor (retained t') (hExitMem (exitEquiv t))
      (hExitMem (exitEquiv t')) hmissing (hRetainedMissing t')).symm
  let absorbedCount := Fintype.card
    {i : Fin C.s // i ∉ Set.range retained}
  let absorbedEquiv : Fin absorbedCount ≃
      {i : Fin C.s // i ∉ Set.range retained} :=
    (Fintype.equivFin {i : Fin C.s // i ∉ Set.range retained}).symm
  have hRangeCard : Fintype.card {i : Fin C.s // i ∈ Set.range retained} =
      retainedCount := by
    simpa only [Fintype.card_fin] using
      Fintype.card_congr (Equiv.ofInjective retained hRetainedInjective).symm
  have hTotal :
      Fintype.card {i : Fin C.s // i ∈ Set.range retained} +
        Fintype.card {i : Fin C.s // i ∉ Set.range retained} = C.s := by
    have hnotCard : Fintype.card {i : Fin C.s // i ∉ Set.range retained} =
        Fintype.card ↥((Set.range retained)ᶜ) := by
      apply Fintype.card_congr
      exact ⟨(fun i => ⟨i.1, i.2⟩), (fun i => ⟨i.1, i.2⟩),
        (fun _ => rfl), (fun _ => rfl)⟩
    have hrangeCard : Fintype.card {i : Fin C.s // i ∈ Set.range retained} =
        Fintype.card (Set.range retained) := by
      apply Fintype.card_congr
      exact ⟨(fun i => ⟨i.1, i.2⟩), (fun i => ⟨i.1, i.2⟩),
        (fun _ => rfl), (fun _ => rfl)⟩
    rw [hrangeCard, hnotCard]
    simpa only [Fintype.card_sum, Fintype.card_fin] using
      Fintype.card_congr (Equiv.Set.sumCompl (Set.range retained))
  have hCount : C.s = absorbedCount + retainedCount := by
    dsimp [absorbedCount]
    omega
  have hPartition (i : Fin C.s) :
      (∃! h : Fin absorbedCount, (absorbedEquiv h).1 = i) ∨
        (∃! t : Fin retainedCount, retained t = i) := by
    by_cases hi : i ∈ Set.range retained
    · right
      rcases hi with ⟨t, ht⟩
      refine ⟨t, ht, ?_⟩
      intro t' ht'
      apply hRetainedInjective
      exact ht'.trans ht.symm
    · left
      obtain ⟨h, hh⟩ := absorbedEquiv.surjective ⟨i, hi⟩
      refine ⟨h, congrArg Subtype.val hh, ?_⟩
      intro h' hh'
      apply absorbedEquiv.injective
      apply Subtype.ext
      exact hh'.trans (congrArg Subtype.val hh).symm
  exact ⟨{
    absorbedCount := absorbedCount
    retainedCount := retainedCount
    exitEquiv := exitEquiv
    retained := retained
    retained_injective := hRetainedInjective
    retained_missing := hRetainedMissing
    selected_unique := hSelectedUnique
    absorbedEquiv := absorbedEquiv
    count_eq := hCount
    exit_count_eq := rfl
    partition := hPartition
  }⟩

end GoldbergSeymour

end
