/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/CommonExtensionProgram.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.DefinedPrefixRemoval
public import LeanPool.TuringConeRigidity.Representation.OwnSourceEquation

/-!
# Common Extension Program
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.RelativeConstructible
open TransitiveNameModel BoundedSetTheory CountableForcing AtomicForcing RecursiveNames
open CohenColumnRealName ElementaryModel PersistentRestrictions SetDegreeDecoding BoundedForcing
open GenericIdentity
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

/-- A ground-generic filter realizes the extension `E` and gives column `a` the real value
`A`. -/
def ColumnRealizesExtension (M K a E : ZFSet.{0}) (A : Oracle) : Prop :=
  ∃ H : GenericFilter (Conditions (poset K)), GroundGeneric M H ∧
    genericExtensionSet M (poset K) H.carrier = E ∧
    (realName K a).val H.carrier = realCode A

theorem own_program_in_common_extension (M K a : ZFSet.{0}) (δ : Ordinal.{0})
    (Z : ZFSet.{0}) (φ : SentenceForm) (f : Name (Conditions (poset K)))
    (hfv : ∀ H : GenericFilter (Conditions (poset K)), GroundGeneric M H →
      f.val H.carrier = definedSubset
        (level (groundReals (genericExtensionSet M (poset K) H.carrier)) δ)
          φ (fun _ : Fin φ.bound => Z))
    (p : OracleCode) (R : Oracle)
    (hprog : ∀ H : GenericFilter (Conditions (poset K)), GroundGeneric M H →
      ∀ A : Oracle, (realName K a).val H.carrier = realCode A →
        OwnProgramAt (genericExtensionSet M (poset K) H.carrier) (f.val H.carrier) p R A)
    (G : GenericFilter (Conditions (poset K))) (hG : GroundGeneric M G)
    (A : Oracle) (hA : ColumnRealizesExtension M K a
      (genericExtensionSet M (poset K) G.carrier) A) :
    OwnProgramAt (genericExtensionSet M (poset K) G.carrier) (f.val G.carrier) p R A := by
  obtain ⟨H,hH,he,hv⟩ := hA
  have hf := defined_value_extension_eq M (poset K) δ Z φ f hfv H G hH hG he
  have h := hprog H hH A hv
  rwa [he,hf] at h

theorem sourceEquation_of_common_extension (M K a : ZFSet.{0})
    (δ : Ordinal.{0}) (Z : ZFSet.{0}) (φ : SentenceForm) (f : Name (Conditions (poset K)))
    (hfv : ∀ H : GenericFilter (Conditions (poset K)), GroundGeneric M H →
      f.val H.carrier = definedSubset
        (level (groundReals (genericExtensionSet M (poset K) H.carrier)) δ)
          φ (fun _ : Fin φ.bound => Z))
    (p : OracleCode) (P : Oracle)
    (hprog : ∀ H : GenericFilter (Conditions (poset K)), GroundGeneric M H →
      ∀ A : Oracle, (realName K a).val H.carrier = realCode A →
        OwnProgramAt (genericExtensionSet M (poset K) H.carrier) (f.val H.carrier) p P A)
    (G : GenericFilter (Conditions (poset K))) (hG : GroundGeneric M G)
    (hE : Transitive (genericExtensionSet M (poset K) G.carrier))
    (hTE : SourceT (genericExtensionSet M (poset K) G.carrier))
    [Countable (Conditions (genericExtensionSet M (poset K) G.carrier))]
    (I : CountableIdeal) (ρ : I ≃o I)
    (hOwn : OwnDegreeExtension (genericExtensionSet M (poset K) G.carrier)
      (idealSet I) (automorphismSet ρ) (f.val G.carrier))
    (Y L R : Oracle) (hL : GenericCoding.InfiniteOdd L) (hR : GenericCoding.InfiniteOdd R)
    (hideal : PrincipalIntersection Y (join Y L) (join Y R))
    (hlifts : ∀ A ∈ ({Y,L,R,GenericCoding.code Y L,GenericCoding.code Y R} : Set Oracle),
      ColumnRealizesExtension M K a (genericExtensionSet M (poset K) G.carrier) A) :
    SourceEquation p P (Y,L,R) := by
  have hrep (A : Oracle) (hA : A ∈ ({Y,L,R,GenericCoding.code Y L,GenericCoding.code Y R} : Set
    Oracle)) :=
    own_program_in_common_extension M K a δ Z φ f hfv p P hprog G hG A (hlifts A hA)
  exact sourceEquation_of_own_extension _ hE hTE I ρ _ hOwn p P Y L R hL hR hideal
    (hrep Y (by simp)) (hrep L (by simp)) (hrep R (by simp))
    (hrep (GenericCoding.code Y L) (by simp)) (hrep (GenericCoding.code Y R) (by simp))

end TuringRigidity.RelativeConstructible

end OAI
