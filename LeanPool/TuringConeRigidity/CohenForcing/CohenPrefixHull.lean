/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/CohenPrefixHull.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.CohenPrefixReconstruction
public import LeanPool.TuringConeRigidity.Representation.RealGeneratedModel
public import LeanPool.TuringConeRigidity.SetModels.RegularTreeExtension
public import LeanPool.TuringConeRigidity.CohenForcing.InternalCohenValue

/-!
# Cohen Prefix Hull
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.InternalCohen
open TransitiveNameModel BoundedSetTheory CohenBorelForcing CountableForcing
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem prefix_extension_eq_hull (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (A : Oracle) (hA : AtomicForcing.GroundGeneric M (pushFilter (realFilter A))) :
    genericExtensionSet M conditions (pushFilter (realFilter A)).carrier =
      RealGeneratedModel.hull M (realCode A) := by
  obtain ⟨hN,hTN,hMN,_⟩ := RegularTreeExtension.extension_properties M conditions hM hT
    (conditions_mem M hM hT) (pushFilter (realFilter A)) hA
  have hAN : realCode A ∈ genericExtensionSet M conditions (pushFilter (realFilter A)).carrier :=
    (mem_extensionSet _ _ _ _).mpr ⟨realName,realName_internal M hM hT,val_realName A⟩
  symm
  apply RealGeneratedModel.hull_eq_of_least M _ _ ⟨hN,hTN,hMN,hAN⟩
  intro N hN
  exact InternalNameEvaluation.extension_subset M N hN.1 hN.2.1 hN.2.2.1 _
    (prefixFilterSet_mem N hN.1 hN.2.1 A hN.2.2.2)

theorem prefix_extension_eq_of_hull (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (A B : Oracle)
    (hA : AtomicForcing.GroundGeneric M (pushFilter (realFilter A)))
    (hB : AtomicForcing.GroundGeneric M (pushFilter (realFilter B)))
    (he : RealGeneratedModel.hull M (realCode A) = RealGeneratedModel.hull M (realCode B)) :
    genericExtensionSet M conditions (pushFilter (realFilter A)).carrier =
      genericExtensionSet M conditions (pushFilter (realFilter B)).carrier := by
  rw [prefix_extension_eq_hull M hM hT A hA,prefix_extension_eq_hull M hM hT B hB,he]

end TuringRigidity.InternalCohen

end OAI
