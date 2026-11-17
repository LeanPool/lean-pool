/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/UniformOwnRealsName.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.UniformPowerName
public import LeanPool.TuringConeRigidity.Representation.GroundInclusion
public import LeanPool.TuringConeRigidity.Constructibility.RelativeConstruction

/-!
# Uniform Own Reals Name
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RelativeConstructible
open RecursiveNames TransitiveNameModel BoundedSetTheory AtomicForcing CountableForcing
universe u

theorem uniform_ownReals_name (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {c o : ZFSet.{u}} [Preorder (Conditions c)] [Top (Conditions c)]
    (hc : c ∈ M) (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s) :
    ∃ R : Name (Conditions c), R.encode (label c) ∈ M ∧
      ∀ G : GenericFilter (Conditions c), GroundGeneric M G → ⊤ ∈ G.carrier →
        R.val G.carrier = groundReals (genericExtensionSet M c G.carrier) := by
  have hω := encoded_check_mem M c hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc
      (sourceT_omega_mem M hM hT)
  obtain ⟨R,hR,hval⟩ := uniform_power_name M hM hT hc hoM ho (Name.check ZFSet.omega) hω
  refine ⟨R,hR,?_⟩
  intro G hG ht
  apply ZFSet.ext; intro x
  rw [hval G hG ht x,mem_groundReals,Name.val_check G.carrier ht]

theorem uniform_zero_stage_name (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {c o : ZFSet.{u}} [Preorder (Conditions c)] [Top (Conditions c)]
    (hc : c ∈ M) (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s) :
    ∃ A : Name (Conditions c), A.encode (label c) ∈ M ∧
      ∀ G : GenericFilter (Conditions c), GroundGeneric M G → ⊤ ∈ G.carrier →
        A.val G.carrier = stage (groundReals (genericExtensionSet M c G.carrier)) ∅ := by
  obtain ⟨R,hR,hval⟩ := uniform_ownReals_name M hM hT hc hoM ho
  let P := Name.pair (Name.pair R R) R
  have hRR := names_pair_closed M c hM hT.pairing hc hR hR
  have hP : P.encode (label c) ∈ M := names_pair_closed M c hM hT.pairing hc hRR hR
  have hA : (Name.union P).encode (label c) ∈ M := by
    rw [encode_union c o ho]
    exact unionCode_mem M hM hT.pairing hT.union hT.powerSet
      hT.separation.finitePrefix.bounded hP hc hoM
  refine ⟨Name.union P,hA,?_⟩
  intro G hG ht
  rw [Name.val_union,stage_zero,ground_seed_shape _ (genericExtensionSet_transitive M c hM
    G.carrier)]
  dsimp only [P]
  rw [Name.val_pair G.carrier ht,Name.val_pair G.carrier ht,hval G hG ht]
  apply ZFSet.ext; intro x
  simp only [ZFSet.mem_sUnion,ZFSet.mem_insert_iff,ZFSet.mem_singleton]
  constructor
  · rintro ⟨y,hy,hx⟩
    rcases hy with rfl|rfl
    · exact Or.inl (by simpa only [ZFSet.mem_insert_iff,ZFSet.mem_singleton,or_self] using hx)
    · exact Or.inr hx
  · rintro (rfl|hx)
    · exact ⟨_,Or.inl rfl,ZFSet.mem_insert _ _⟩
    · exact ⟨_,Or.inr rfl,hx⟩

end TuringRigidity.RelativeConstructible

end OAI
