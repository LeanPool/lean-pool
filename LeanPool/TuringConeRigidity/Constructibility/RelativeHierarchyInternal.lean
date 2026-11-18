/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/RelativeHierarchyInternal.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.CheckedHierarchySyntax
public import LeanPool.TuringConeRigidity.Constructibility.RelativeDefCertificates
public import LeanPool.TuringConeRigidity.Constructibility.RelativeModelOrdinals

/-!
# Relative Hierarchy Internal
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding
open BoundedDefinability SetModelFunctions
universe u

theorem relative_internal_hierarchy_cover (M x : ZFSet.{u})
    (hM : Transitive M) (hT : SourceT M)
    (hx : x ∈ relativeModel M (groundReals M)) :
    ∃ d ∈ relativeModel M (groundReals M), ∃ f ∈ relativeModel M (groundReals M),
      x ∈ d ∧ HierarchyGraph (relativeModel M (groundReals M)) (seed (groundReals M))
        d (iterUnion 2 f) f := by
  have hR := groundReals_mem M hM hT
  exact internal_hierarchy_cover_collection _ _ x (ground_relative_context M hM hT)
    (relativeModel_sigma_replacement M _ hM hT hR)
    (relativeModel_sigma_collection M _ hM hT hR)
    ((mem_relativeModel M _ _ hM hT hR).mpr (parameter_in_relativeModel M _ hM hT)) hx

theorem relative_internal_ordinal_hierarchy (M : ZFSet.{u})
    (hM : Transitive M) (hT : SourceT M) (o : Ordinal.{u}) (ho : o.toZFSet ∈ M) :
    ∃ d ∈ relativeModel M (groundReals M), ∃ f ∈ relativeModel M (groundReals M),
      o.toZFSet ∈ d ∧ CheckedHierarchyGraph (relativeModel M (groundReals M))
        ZFSet.omega (ZFSet.prod ZFSet.omega ZFSet.omega) (seed (groundReals M))
        d (iterUnion 2 f) f := by
  obtain ⟨d,hd,f,hf,ho,hg⟩ := relative_internal_hierarchy_cover M o.toZFSet hM hT
    ((ground_relativeModel_ordinal_iff M hM hT o).mpr ho)
  exact ⟨d,hd,f,hf,ho,(checkedHierarchyGraph_of_context _ _ _ _ _
    (ground_relative_context M hM hT)).mpr hg⟩

end TuringRigidity.RelativeConstructible

end OAI
