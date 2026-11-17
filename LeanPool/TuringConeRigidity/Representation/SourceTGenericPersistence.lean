/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/SourceTGenericPersistence.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Representation.SourceTAbsolutenessEndpoint

/-!
# Source TGeneric Persistence
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.ArithmeticTree
open UniformArithmetic ArithmeticPersistence BoundedSetTheory TransitiveNameModel
open SetModelReals SetModelFunctions SetModelSyntax SetDegreeDecoding SetModelCountability
open SetModelSatisfaction PersistentRestrictions CountableForcing
universe u
noncomputable section

/-- The model contains the correct degree universe and order and satisfies the native
persistence formula. -/
def NativePersistent (M : ZFSet.{u}) (I : CountableIdeal) (ρ : I ≃o I) : Prop :=
  ∃ D ∈ M, ∃ L ∈ M,
    (∀ x, x ∈ D ↔ ∃ A ∈ reals M, x = degreeSet (degree A)) ∧
    (∀ A ∈ reals M, ∀ B ∈ reals M,
      ZFSet.pair (degreeSet (degree A)) (degreeSet (degree B)) ∈ L ↔ Reduces A B) ∧
    persistenceFormula.Realize M (cons D (cons L (cons (idealSet I)
      (cons (automorphismSet ρ) (fun _ => ZFSet.omega)))))

theorem nativePersistent_iff (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (I : CountableIdeal) (hI : idealSet I ∈ M) (hct : InternallyCountable M (idealSet I))
    (ρ : I ≃o I) (hρ : automorphismSet ρ ∈ M)
    (hz : degree (OracleJump.jump FixedArithmetic.zero) ∈ I.carrier) :
    NativePersistent M I ρ ↔ Persistent I ρ := by
  constructor
  · rintro ⟨D,hDM,L,hLM,hD,hL,hp⟩
    exact (native_persistence_absolute M hM hT hDM hLM hD hL I hI hct ρ hρ hz).mp hp
  · intro hp
    obtain ⟨D,hDM,L,hLM,hD,hL,hpD,_⟩ := source_4_2_2_transitive_countable M hM hT I hI hct hz
    exact ⟨D,hDM,L,hLM,hD,hL,(hpD ρ hρ).mpr hp⟩

theorem generic_nativePersistent_iff (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {c o : ZFSet.{u}} [Preorder (Conditions c)] [Top (Conditions c)]
    (hc : c ∈ M) (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G) (ht : ⊤ ∈ G.carrier)
    (I : CountableIdeal) (hI : idealSet I ∈ M) (ρ : I ≃o I) (hρ : automorphismSet ρ ∈ M)
    (hz : degree (OracleJump.jump FixedArithmetic.zero) ∈ I.carrier)
    (hct : InternallyCountable (genericExtensionSet M c G.carrier) (idealSet I)) :
    NativePersistent (genericExtensionSet M c G.carrier) I ρ ↔ Persistent I ρ := by
  have hsub := ground_inclusion_set M c hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hT.replacement.finitePrefix hT.infinity hc G.carrier ht
  exact nativePersistent_iff _ (genericExtensionSet_transitive M c hM G.carrier)
    (extension_sourceT M hM hT hc hoM ho G hG ht) I (hsub hI) hct ρ (hsub hρ) hz

theorem generic_persistence_transfer (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {c o d v : ZFSet.{u}} [Preorder (Conditions c)] [Top (Conditions c)]
    [Preorder (Conditions d)] [Top (Conditions d)]
    (hc : c ∈ M) (hoM : o ∈ M)
    (ho : ∀ r s : Conditions c, ZFSet.pair (label c r) (label c s) ∈ o ↔ r ≤ s)
    (hd : d ∈ M) (hvM : v ∈ M)
    (hv : ∀ r s : Conditions d, ZFSet.pair (label d r) (label d s) ∈ v ↔ r ≤ s)
    (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G) (htG : ⊤ ∈ G.carrier)
    (H : GenericFilter (Conditions d)) (hH : AtomicForcing.GroundGeneric M H) (htH : ⊤ ∈ H.carrier)
    (I : CountableIdeal) (hI : idealSet I ∈ M) (ρ : I ≃o I) (hρ : automorphismSet ρ ∈ M)
    (hz : degree (OracleJump.jump FixedArithmetic.zero) ∈ I.carrier)
    (hctG : InternallyCountable (genericExtensionSet M c G.carrier) (idealSet I))
    (hctH : InternallyCountable (genericExtensionSet M d H.carrier) (idealSet I)) :
    NativePersistent (genericExtensionSet M c G.carrier) I ρ ↔
      NativePersistent (genericExtensionSet M d H.carrier) I ρ :=
  (generic_nativePersistent_iff M hM hT hc hoM ho G hG htG I hI ρ hρ hz hctG).trans
    (generic_nativePersistent_iff M hM hT hd hvM hv H hH htH I hI ρ hρ hz hctH).symm

end
end TuringRigidity.ArithmeticTree

end OAI
