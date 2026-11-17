/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/CollectionHierarchyInternal.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.CollectionHierarchyRecursion
public import LeanPool.TuringConeRigidity.Constructibility.InternalConstructibleHierarchy

/-!
# Collection Hierarchy Internal
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding
open BoundedDefinability SetModelFunctions
universe u
theorem seed_mem_collection (M R : ZFSet.{u}) (C : Context M) (hRep : SigmaReplacement M) (hR : R
  ∈ M) :
    seed R ∈ M := by
  obtain ⟨b,hb,hdef⟩ := collect_unionIterates M C.transitive C.pairing C.union
    hRep (C.omega_mem)
    (singleton_mem M C.transitive C.pairing hR)
  have he : ZFSet.sUnion b = seed R := by
    apply ZFSet.ext; intro z
    rw [ZFSet.mem_sUnion,mem_seed]
    constructor
    · rintro ⟨a,ha,hz⟩
      obtain ⟨n,rfl⟩ := (hdef a).mp ha
      exact ⟨n,hz⟩
    · rintro ⟨n,hz⟩
      exact ⟨_,(hdef _).mpr ⟨n,rfl⟩,hz⟩
  exact he ▸ union_mem M C.transitive C.union hb

theorem internal_hierarchy_cover_collection (M R o : ZFSet.{u}) (C : Context M) (hRep :
  SigmaReplacement M) (hColl : SigmaCollection M)
    (hR : R ∈ M) (ho : o ∈ M) :
    ∃ d ∈ M, ∃ f ∈ M, o ∈ d ∧
      HierarchyGraph M (seed R) d (iterUnion 2 f) f := by
  obtain ⟨c,hc,hct,hoc⟩ := internal_transitive_container M C.transitive C.pairing C.union
    C.separation hRep C.infinity ho
  obtain ⟨q,hq,hqdef⟩ := internal_power M C.transitive C.power hc
  obtain ⟨f,hf,hfg⟩ := internal_hierarchyGraph_collection M R c q C hRep hColl
    (seed_mem_collection M R C hRep hR)
    hc hq hct hqdef o hoc
  exact ⟨hull c q o,hull_mem M c q C.transitive C.separation hc hq ho,
    f,hf,self_mem_hull c q hoc,hfg⟩

theorem stage_mem_collection (M R o : ZFSet.{u}) (C : Context M) (hRep : SigmaReplacement M)
  (hColl : SigmaCollection M)
    (hR : R ∈ M) (ho : o ∈ M) : stage R o ∈ M := by
  obtain ⟨d,_,f,hf,hod,hfg⟩ := internal_hierarchy_cover_collection M R o C hRep hColl hR ho
  obtain ⟨v,hv,hfv,_⟩ := hfg.2.1.2 o hod
  have hvM : v ∈ M := C.transitive _ (iterUnion_mem M C.transitive C.union hf 2) v hv
  rw [hfg.correct o hod v hv hfv] at hvM
  exact C.transitive _ hvM _ (self_mem_definablePower (stage R o))

theorem level_mem_collection (M R : ZFSet.{u}) (C : Context M) (hRep : SigmaReplacement M) (hColl
  : SigmaCollection M)
    (hR : R ∈ M) (o : Ordinal.{u}) (ho : o.toZFSet ∈ M) : level R o ∈ M :=
  stage_mem_collection M R o.toZFSet C hRep hColl hR ho

theorem level_subset_model_collection (M R : ZFSet.{u}) (C : Context M) (hRep : SigmaReplacement
  M) (hColl : SigmaCollection M)
    (hR : R ∈ M) (o : Ordinal.{u}) (ho : o.toZFSet ∈ M) : level R o ⊆ M :=
  fun x hx => C.transitive _ (level_mem_collection M R C hRep hColl hR o ho) x hx

end TuringRigidity.RelativeConstructible

end OAI
