/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/SetModelArithmeticInterface.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.SetModelJoin
public import LeanPool.TuringConeRigidity.SetModels.SetModelPersistence
public import LeanPool.TuringConeRigidity.SetModels.SetModelOmegaJump

/-!
# Set Model Arithmetic Interface
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.SetModelArithmetic
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelSequences
open SetDegreeDecoding SetModelPersistence PersistentRestrictions PersistentPresentation
universe u
noncomputable section

theorem realClosure_of_lower_and_jump (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hI : Infinity M)
    (hL : ∀ {A B}, B ∈ reals M → Reduces A B → A ∈ reals M)
    (hJ : ∀ A ∈ reals M, OracleJump.jump A ∈ reals M)
    {g : ZFSet.{u}} (hgM : g ∈ M)
    (hg : ∀ A ∈ reals M, ∀ B ∈ reals M,
      ZFSet.pair (realSet A) (realSet B) ∈ g ↔ B = OracleJump.jump A) :
    PersistenceRealClosure.Closed (reals M) :=
  realClosure_of_arithmetic_graphs M hM hP hU hPow hS hI hL
    (fun hA hB => join_mem M hM hP hU hPow hS hI hA hB) hJ
    (pairingSet_mem M hM hP hU hPow hS hI) pairingSet_code hgM hg

theorem persistent_model_sets (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hI : Infinity M)
    (hL : ∀ {A B}, B ∈ reals M → Reduces A B → A ∈ reals M)
    (hJ : ∀ A ∈ reals M, OracleJump.jump A ∈ reals M)
    {g E : ZFSet.{u}} (hgM : g ∈ M)
    (hg : ∀ A ∈ reals M, ∀ B ∈ reals M,
      ZFSet.pair (realSet A) (realSet B) ∈ g ↔ B = OracleJump.jump A)
    (hEM : E ∈ M) (hE : ∀ A ∈ reals M, ∀ B ∈ reals M,
      ZFSet.pair (realSet A) (realSet B) ∈ E ↔ degree A = degree B)
    {I : CountableIdeal} {A : Oracle} (hA : Presented I A) (hAM : A ∈ reals M)
    (ρ : I ≃o I) (hρ : Persistent I ρ)
    (hz : degree (OracleJump.jump FixedArithmetic.zero) ∈ I.carrier) :
    idealSet I ∈ M ∧ automorphismSet ρ ∈ M :=
  persistent_decoding M hM hP hU hPow hS hI
    (realClosure_of_lower_and_jump M hM hP hU hPow hS hI hL hJ hgM hg)
    (pairingSet_mem M hM hP hU hPow hS hI) pairingSet_code hEM hE hA hAM ρ hρ hz

theorem persistent_model_extension_sets (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hI : Infinity M)
    (hL : ∀ {A B}, B ∈ reals M → Reduces A B → A ∈ reals M)
    (hJ : ∀ A ∈ reals M, OracleJump.jump A ∈ reals M)
    {g E : ZFSet.{u}} (hgM : g ∈ M)
    (hg : ∀ A ∈ reals M, ∀ B ∈ reals M,
      ZFSet.pair (realSet A) (realSet B) ∈ g ↔ B = OracleJump.jump A)
    (hEM : E ∈ M) (hE : ∀ A ∈ reals M, ∀ B ∈ reals M,
      ZFSet.pair (realSet A) (realSet B) ∈ E ↔ degree A = degree B)
    {I : CountableIdeal} {A : Oracle} (hA : Presented I A) (hAM : A ∈ reals M)
    (ρ : I ≃o I) (hρ : Persistent I ρ)
    (hz : degree (OracleJump.jump FixedArithmetic.zero) ∈ I.carrier)
    {X : Oracle} (hX : X ∈ reals M) :
    ∃ (J : CountableIdeal) (σ : J ≃o J) (hIJ : I.carrier ⊆ J.carrier),
      degree X ∈ J.carrier ∧ Extends hIJ ρ σ ∧ Persistent J σ ∧
      idealSet J ∈ M ∧ automorphismSet σ ∈ M :=
  persistent_extension_sets M hM hP hU hPow hS hI
    (realClosure_of_lower_and_jump M hM hP hU hPow hS hI hL hJ hgM hg)
    (pairingSet_mem M hM hP hU hPow hS hI) pairingSet_code hEM hE hA hAM ρ hρ hz hX

end
end TuringRigidity.SetModelArithmetic

end OAI
