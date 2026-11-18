/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/FiniteOrdinalCode.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.OrdinalPairCode

/-!
# Finite Ordinal Code
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OrdinalCoding
universe u

/-- Encode a finite ordinal vector by iterated ordinal pairing, using one for the empty
vector. -/
noncomputable def vectorCode : {n : ℕ} → (Fin n → Ordinal.{u}) → Ordinal.{u}
  | 0, _ => 1
  | _+1, v => pairCode (v 0) (vectorCode (fun i => v i.succ))

/-- Decode the specified number of entries from an ordinal-vector code. -/
noncomputable def vectorDecode : (n : ℕ) → Ordinal.{u} → Fin n → Ordinal.{u}
  | 0, _, i => Fin.elim0 i
  | n+1, a, i => Fin.cases (unpairCode a).1
      (vectorDecode n (unpairCode a).2) i

theorem vectorDecode_vectorCode {n : ℕ} (v : Fin n → Ordinal.{u}) :
    vectorDecode n (vectorCode v) = v := by
  induction n with
  | zero => funext i; exact Fin.elim0 i
  | succ n ih =>
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [vectorCode,vectorDecode,unpairCode_pairCode,Fin.cases_zero]
    · simpa only [vectorCode,vectorDecode,unpairCode_pairCode,Fin.cases_succ] using
        congrFun (ih (fun k => v k.succ)) j

theorem vectorCode_injective (n : ℕ) :
    Function.Injective (vectorCode (n := n) : (Fin n → Ordinal.{u}) → Ordinal.{u}) := by
  intro v w h
  have h' := congrArg (vectorDecode n) h
  simpa only [vectorDecode_vectorCode] using h'

theorem entry_lt_vectorCode {n : ℕ} (v : Fin n → Ordinal.{u}) (i : Fin n) :
    v i < vectorCode v := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact left_lt_pairCode _ _
    · exact (ih (fun k => v k.succ) j).trans (right_lt_pairCode _ _)

theorem vectorCode_pos {n : ℕ} (v : Fin n → Ordinal.{u}) : 0 < vectorCode v := by
  cases n with
  | zero => exact zero_lt_one
  | succ n => exact (show 0 ≤ v 0 from zero_le).trans_lt (left_lt_pairCode _ _)

/-- Pair an ordinal padding parameter with the vector's ordinal code. -/
noncomputable def paddedCode {n : ℕ} (v : Fin n → Ordinal.{u}) (β : Ordinal.{u}) : Ordinal.{u} :=
  pairCode β (vectorCode v)

/-- Decode the vector portion of a padded ordinal code. -/
noncomputable def paddedDecode (n : ℕ) (a : Ordinal.{u}) : Fin n → Ordinal.{u} :=
  vectorDecode n (unpairCode a).2

theorem paddedDecode_paddedCode {n : ℕ} (v : Fin n → Ordinal.{u}) (β : Ordinal.{u}) :
    paddedDecode n (paddedCode v β) = v := by
  simp only [paddedDecode,paddedCode,unpairCode_pairCode,vectorDecode_vectorCode]

theorem padding_recovered {n : ℕ} (v : Fin n → Ordinal.{u}) (β : Ordinal.{u}) :
    (unpairCode (paddedCode v β)).1 = β := by
  simp only [paddedCode,unpairCode_pairCode]

theorem padding_lt_paddedCode {n : ℕ} (v : Fin n → Ordinal.{u}) (β : Ordinal.{u}) :
    β < paddedCode v β := left_lt_pairCode _ _

theorem entry_lt_paddedCode {n : ℕ} (v : Fin n → Ordinal.{u}) (β : Ordinal.{u}) (i : Fin n) :
    v i < paddedCode v β := (entry_lt_vectorCode v i).trans (right_lt_pairCode _ _)

theorem paddedCode_inj {n : ℕ} (v w : Fin n → Ordinal.{u}) (β γ : Ordinal.{u}) :
    paddedCode v β = paddedCode w γ ↔ β = γ ∧ v = w := by
  rw [paddedCode,paddedCode,pairCode_inj]
  exact and_congr Iff.rfl (vectorCode_injective n).eq_iff

theorem paddedCode_cofinal {n : ℕ} (v : Fin n → Ordinal.{u}) (β : Ordinal.{u}) :
    ∃ a : Ordinal.{u}, β < a ∧ paddedDecode n a = v ∧ (∀ i, v i < a) :=
  ⟨paddedCode v β,padding_lt_paddedCode v β,paddedDecode_paddedCode v β,
    entry_lt_paddedCode v β⟩

theorem pairCode_isSuccLimit (x y : Ordinal.{u}) (hx : 0 < x) (hy : 0 < y) :
    Order.IsSuccLimit (pairCode x y) := by
  unfold pairCode
  split
  · exact Ordinal.isSuccLimit_add _ (Ordinal.isSuccLimit_opow_left
      Ordinal.isSuccLimit_omega0 (ne_of_gt hy))
  · exact Ordinal.isSuccLimit_add _ (Ordinal.isSuccLimit_opow_left
      Ordinal.isSuccLimit_omega0 (ne_of_gt hx))

theorem paddedCode_isSuccLimit {n : ℕ} (v : Fin n → Ordinal.{u}) (β : Ordinal.{u})
    (hβ : 0 < β) : Order.IsSuccLimit (paddedCode v β) :=
  pairCode_isSuccLimit β (vectorCode v) hβ (vectorCode_pos v)

theorem finite_margin_lt_paddedCode {n : ℕ} (v : Fin n → Ordinal.{u}) (β c : Ordinal.{u})
    (hβ : 0 < β) (hc : c < paddedCode v β) (k : ℕ) :
    c + (k : Ordinal.{u}) < paddedCode v β := by
  induction k with
  | zero => simpa only [Nat.cast_zero,add_zero] using hc
  | succ k ih =>
    have h := (paddedCode_isSuccLimit v β hβ).succ_lt ih
    simpa only [Order.succ_eq_add_one,Nat.cast_add,Nat.cast_one,add_assoc] using h

end TuringRigidity.OrdinalCoding

end OAI
