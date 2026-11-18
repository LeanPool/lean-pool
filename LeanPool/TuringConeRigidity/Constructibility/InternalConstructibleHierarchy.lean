/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/InternalConstructibleHierarchy.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.CollectionHierarchyInternal
public import LeanPool.TuringConeRigidity.Constructibility.ConstructibleGroundReals

/-!
# Internal Constructible Hierarchy
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding
open BoundedDefinability SetModelFunctions
universe u

theorem seed_mem (M R : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M) (hR : R ∈ M) :
    seed R ∈ M := by
  let C : Context M :=
    ⟨hM,hT.pairing,hT.union,hT.powerSet,hT.separation.finitePrefix.bounded,hT.infinity⟩
  exact seed_mem_collection M R C hT.replacement.finitePrefix hR

theorem internal_hierarchy_cover (M R o : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (hR : R ∈ M) (ho : o ∈ M) :
    ∃ d ∈ M, ∃ f ∈ M, o ∈ d ∧
      HierarchyGraph M (seed R) d (iterUnion 2 f) f := by
  let C : Context M :=
    ⟨hM,hT.pairing,hT.union,hT.powerSet,hT.separation.finitePrefix.bounded,hT.infinity⟩
  have hColl := sigma_collection M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix hT.replacement.finitePrefix hT.infinity hT.choice
  exact internal_hierarchy_cover_collection M R o C hT.replacement.finitePrefix hColl hR ho

theorem stage_mem (M R o : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (hR : R ∈ M) (ho : o ∈ M) : stage R o ∈ M := by
  let C : Context M :=
    ⟨hM,hT.pairing,hT.union,hT.powerSet,hT.separation.finitePrefix.bounded,hT.infinity⟩
  have hColl := sigma_collection M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix hT.replacement.finitePrefix hT.infinity hT.choice
  exact stage_mem_collection M R o C hT.replacement.finitePrefix hColl hR ho

theorem level_mem (M R : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (hR : R ∈ M) (o : Ordinal.{u}) (ho : o.toZFSet ∈ M) : level R o ∈ M :=
  stage_mem M R o.toZFSet hM hT hR ho

theorem level_subset_model (M R : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (hR : R ∈ M) (o : Ordinal.{u}) (ho : o.toZFSet ∈ M) : level R o ⊆ M :=
  fun x hx => hM _ (level_mem M R hM hT hR o ho) x hx

theorem internally_indexed_ground_reals (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (x : ZFSet.{u}) (hx : x ⊆ ZFSet.omega) :
    (∃ o : Ordinal.{u}, o.toZFSet ∈ M ∧ x ∈ level (groundReals M) o) ↔ x ∈ M := by
  constructor
  · rintro ⟨o,ho,hxl⟩
    exact level_subset_model M (groundReals M) hM hT (groundReals_mem M hM hT) o ho hxl
  · intro hxM
    have hω := sourceT_omega_mem M hM hT
    refine ⟨0,?_,?_⟩
    · simpa only [Ordinal.toZFSet_zero] using hM _ hω _ ZFSet.omega_zero
    · rw [level_zero]
      exact parameter_subset_seed (groundReals M) ((mem_groundReals M x).mpr ⟨hxM,hx⟩)

end TuringRigidity.RelativeConstructible

end OAI
