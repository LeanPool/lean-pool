/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalOrdinalCodes.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.InternalOmegaPower
public import LeanPool.TuringConeRigidity.OrdinalCodes.OrdinalSumClosure
public import LeanPool.TuringConeRigidity.OrdinalCodes.OrdinalCodeDomains

/-!
# Internal Ordinal Codes
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OrdinalCoding
open TransitiveNameModel BoundedSetTheory OrdinalArithmetic RelativeConstructible
universe u

theorem pairCode_internal (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (x y : Ordinal.{u}) (hx : x.toZFSet ∈ M) (hy : y.toZFSet ∈ M) :
    (pairCode x y).toZFSet ∈ M := by
  unfold pairCode
  split
  · exact (ordinal_add_internal M hM hT _ _
      (ordinal_omega_opow_internal M hM hT _ (internal_ordinal_succ M hM hT x hx))
      (ordinal_omega_opow_internal M hM hT y hy)).1
  · exact (ordinal_add_internal M hM hT _ _
      (ordinal_mul_two_internal M hM hT _
        (ordinal_omega_opow_internal M hM hT _ (internal_ordinal_succ M hM hT y hy)))
      (ordinal_omega_opow_internal M hM hT x hx)).1

theorem vectorCode_internal (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {n : ℕ} (v : Fin n → Ordinal.{u}) (hv : ∀ i, (v i).toZFSet ∈ M) :
    (vectorCode v).toZFSet ∈ M := by
  induction n with
  | zero =>
    simpa only [vectorCode,zero_add] using internal_ordinal_succ M hM hT 0 (internal_ordinal_zero
      M hM hT)
  | succ n ih =>
    exact pairCode_internal M hM hT _ _ (hv 0) (ih _ (fun i => hv i.succ))

theorem paddedCode_internal (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {n : ℕ} (v : Fin n → Ordinal.{u}) (β : Ordinal.{u})
    (hv : ∀ i, (v i).toZFSet ∈ M) (hβ : β.toZFSet ∈ M) :
    (paddedCode v β).toZFSet ∈ M :=
  pairCode_internal M hM hT _ _ hβ (vectorCode_internal M hM hT v hv)

theorem padded_height_index_from_inputs (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {n : ℕ} (v : Fin n → Ordinal.{u}) (β : Ordinal.{u})
    (hv : ∀ i, (v i).toZFSet ∈ M) (hβ : β.toZFSet ∈ M) :
    (heightDomainIndex (paddedCode v β)).toZFSet ∈ M :=
  padded_height_index_internal M hM hT v β (paddedCode_internal M hM hT v β hv hβ)

theorem internal_padded_codes_cofinal (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {n : ℕ} (v : Fin n → Ordinal.{u}) (hv : ∀ i, (v i).toZFSet ∈ M)
    (β : Ordinal.{u}) (hβ : β.toZFSet ∈ M) :
    ∃ a : Ordinal.{u}, a.toZFSet ∈ M ∧ β < a ∧ paddedDecode n a = v ∧
      (∀ i, v i < a) ∧ (heightDomainIndex a).toZFSet ∈ M :=
  ⟨paddedCode v β,paddedCode_internal M hM hT v β hv hβ,
    padding_lt_paddedCode v β,paddedDecode_paddedCode v β,entry_lt_paddedCode v β,
    padded_height_index_from_inputs M hM hT v β hv hβ⟩

end TuringRigidity.OrdinalCoding

end OAI
