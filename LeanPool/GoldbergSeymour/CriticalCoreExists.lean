/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.GoldbergSeymour.ChromaticIndexRestrict
public import LeanPool.GoldbergSeymour.Critical
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic.Bound.Init

/-!
# Critical Core Exists

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem CriticalCoreExists {V E : Type*} [Finite V] [Fintype E] [DecidableEq E]
    (G : LooplessMultigraph V E) :
    ∃ F : Finset E,
      ChromaticIndex (RestrictEdges G F) = ChromaticIndex G ∧
      Critical (RestrictEdges G F) := by
  classical
  let _ := Fintype.ofFinite V
  let candidates : Finset (Finset E) :=
    (Finset.univ : Finset E).powerset.filter
      (fun F => ChromaticIndex (RestrictEdges G F) = ChromaticIndex G)
  have candidates_nonempty : candidates.Nonempty := by
    refine ⟨Finset.univ, ?_⟩
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_powerset.mpr (Finset.subset_univ _)
    · have coloring := (ChromaticIndexSpec G).1
      obtain ⟨φ, hproper, hfull⟩ := coloring
      apply le_antisymm
      · exact ChromaticIndexRestrict G Finset.univ
      · obtain ⟨ψ, hψ, hψfull⟩ :=
          (ChromaticIndexSpec (RestrictEdges G Finset.univ)).1
        apply (ChromaticIndexSpec G).2
        refine ⟨(fun e => ψ ⟨e, by simp⟩), ?_, ?_⟩
        · intro e f c hne hadj he hf
          apply hψ (e := (⟨e, by simp⟩ : {x // x ∈ (Finset.univ : Finset E)}))
            (f := (⟨f, by simp⟩ : {x // x ∈ (Finset.univ : Finset E)})) ?_ ?_ he hf
          · intro h
            apply hne
            exact congrArg Subtype.val h
          · simpa [AdjacentEdges, Incident, RestrictEdges] using hadj
        · intro e
          exact hψfull ⟨e, by simp⟩
  obtain ⟨F, hF, hmin⟩ :=
    Finset.exists_min_image candidates (fun X => X.card) candidates_nonempty
  have hFeq : ChromaticIndex (RestrictEdges G F) = ChromaticIndex G := by
    simpa [candidates] using hF
  refine ⟨F, hFeq, ?_⟩
  intro e
  have hle := ChromaticIndexRestrict G (F.erase e.1)
  have hstrict : ChromaticIndex (RestrictEdges G (F.erase e.1)) <
      ChromaticIndex (RestrictEdges G F) := by
    apply lt_of_le_of_ne
    · simpa [hFeq] using hle
    · intro heq
      have smaller : (F.erase e.1).card < F.card := Finset.card_erase_lt_of_mem e.property
      have member : F.erase e.1 ∈ candidates := by
        apply Finset.mem_filter.mpr
        constructor
        · apply Finset.mem_powerset.mpr
          exact (Finset.erase_subset _ _).trans (Finset.subset_univ _)
        · exact heq.trans hFeq
      exact (Nat.not_lt_of_ge (hmin _ member)) smaller
  have indexMatch :
      ChromaticIndex (RestrictEdges (RestrictEdges G F) (F.attach.erase e)) =
        ChromaticIndex (RestrictEdges G (F.erase e.1)) := by
    let mapDirect : {x // x ∈ F.erase e.1} →
        {x // x ∈ F.attach.erase e} := fun x =>
      ⟨⟨x.1, Finset.mem_of_mem_erase x.2⟩, by
        apply Finset.mem_erase.mpr
        constructor
        · intro h
          apply (Finset.mem_erase.mp x.2).1
          exact congrArg Subtype.val h
        · exact Finset.mem_attach _ _⟩
    let mapNested : {x // x ∈ F.attach.erase e} →
        {x // x ∈ F.erase e.1} := fun x =>
      ⟨x.1.1, by
        apply Finset.mem_erase.mpr
        constructor
        · intro h
          apply (Finset.mem_erase.mp x.2).1
          exact Subtype.ext h
        · exact x.1.2⟩
    apply le_antisymm
    · obtain ⟨φ, hφ, hfull⟩ :=
        (ChromaticIndexSpec (RestrictEdges G (F.erase e.1))).1
      apply (ChromaticIndexSpec (RestrictEdges (RestrictEdges G F) (F.attach.erase e))).2
        (ChromaticIndex (RestrictEdges G (F.erase e.1)))
      refine ⟨(fun x => φ (mapNested x)), ?_, ?_⟩
      · intro x y c hne hadj hx hy
        apply hφ (e := mapNested x) (f := mapNested y) ?_ ?_ hx hy
        · intro h
          apply hne
          apply Subtype.ext
          apply Subtype.ext
          exact congrArg (fun z => z.1) h
        · simpa [mapNested, AdjacentEdges, Incident, RestrictEdges] using hadj
      · intro x
        exact hfull (mapNested x)
    · obtain ⟨φ, hφ, hfull⟩ :=
        (ChromaticIndexSpec (RestrictEdges (RestrictEdges G F) (F.attach.erase e))).1
      apply (ChromaticIndexSpec (RestrictEdges G (F.erase e.1))).2
        (ChromaticIndex (RestrictEdges (RestrictEdges G F) (F.attach.erase e)))
      refine ⟨(fun x => φ (mapDirect x)), ?_, ?_⟩
      · intro x y c hne hadj hx hy
        apply hφ (e := mapDirect x) (f := mapDirect y) ?_ ?_ hx hy
        · intro h
          apply hne
          exact Subtype.ext (congrArg (fun z => z.1.1) h)
        · simpa [mapDirect, AdjacentEdges, Incident, RestrictEdges] using hadj
      · intro x
        exact hfull (mapDirect x)
  rw [DeleteEdge]
  exact indexMatch ▸ hstrict

end GoldbergSeymour

end
