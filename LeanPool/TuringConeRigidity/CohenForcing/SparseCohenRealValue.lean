/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/SparseCohenRealValue.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.SparseCohenRealName
public import LeanPool.TuringConeRigidity.CohenForcing.SparseCohenFilter
public import LeanPool.TuringConeRigidity.CohenForcing.CohenGenericUnion

/-!
# Sparse Cohen Real Value
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.SparseCohenRealName
open TransitiveNameModel BoundedSetTheory InternalCollapse CountableForcing RecursiveNames
open InternalCohen (bitSet)
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
  CohenNiceNameConstruction.cohenTop

theorem val_realName (G : GenericFilter (Conditions poset)) (A : Oracle)
    (hA : ∀ n b, ZFSet.pair (natSet n) (bitSet b) ∈ unionGraph G ↔ A n = b) :
    realName.val G.carrier = realCode A := by
  obtain ⟨p,hp⟩ := G.nonempty
  have ht : (⊤ : Conditions poset) ∈ G.carrier := G.upper le_top hp
  apply ZFSet.ext; intro z
  rw [realName,CohenRealNameCode.realName,CohenRealNameCode.realNameFromPredicate,
    Name.mem_val]
  simp only [Name.val_check _ ht]
  constructor
  · rintro ⟨⟨⟨q,n⟩,hbit⟩,hq,rfl⟩
    exact (natSet_mem_realCode A n).mpr ((hA n true).mp
      ((mem_unionGraph G _).mpr ⟨q,hq,hbit⟩))
  · intro hz
    obtain ⟨n,rfl⟩ := (mem_omega _).mp (realCode_subset A hz)
    obtain ⟨q,hq,hbit⟩ := (mem_unionGraph G _).mp
      ((hA n true).mpr ((natSet_mem_realCode A n).mp hz))
    exact ⟨⟨(q,n),hbit⟩,hq,rfl⟩

theorem generic_real_value (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (G : GenericFilter (Conditions poset)) (hG : AtomicForcing.GroundGeneric M G) :
    ∃ A : Oracle, realName.val G.carrier = realCode A ∧
      (∀ p : Conditions poset, p ∈ G.carrier ↔ ∀ n b,
        ZFSet.pair (natSet n) (bitSet b) ∈ label poset p → A n = b) ∧
      (∀ n b, ZFSet.pair (natSet n) (bitSet b) ∈ unionGraph G ↔ A n = b) ∧
      realCode A ∈ genericExtensionSet M poset G.carrier := by
  obtain ⟨A,hA⟩ := SparseCohenFilter.union_real G
    (CohenGenericUnion.union_function M ZFSet.omega hM hT
      (sourceT_omega_mem M hM hT) G hG)
  have hv := val_realName G A hA
  exact ⟨A,hv,SparseCohenFilter.mem_filter_iff_agrees G A hA,hA,
    (mem_extensionSet M poset _ _).mpr ⟨realName,realName_internal M hM hT,hv⟩⟩

end TuringRigidity.SparseCohenRealName

end OAI
