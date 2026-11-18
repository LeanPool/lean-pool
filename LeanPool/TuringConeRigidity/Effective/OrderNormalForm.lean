/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/OrderNormalForm.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.CertificateMatrix

/-!
# Order Normal Form
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OrderNormalForm
open Encodable TableIndices IndexMatrix IndexedOrder CertificateMatrix

/-- A challenge-response matrix expressing compatible certified outputs for a proposed Turing
reduction. -/
def orderMatrix (Y : Oracle) (e₀ e₁ d q r : ℕ) : Prop :=
  let n := (Nat.unpair q).1
  let challenge := (Nat.unpair q).2
  let m := (Nat.unpair challenge).1
  let a := (Nat.unpair (Nat.unpair challenge).2).1
  let b := (Nat.unpair (Nat.unpair (Nat.unpair challenge).2).2).1
  let z := (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair challenge).2).2).2).1
  let w := (Nat.unpair (Nat.unpair (Nat.unpair (Nat.unpair challenge).2).2).2).2
  let answer := (Nat.unpair r).1
  let cert := (Nat.unpair (Nat.unpair r).2).1
  let trial := (Nat.unpair (Nat.unpair r).2).2
  (Certificate Y (machine e₁) (machine d) n answer cert ∧
    TableIndices.run Y (machine e₀) n trial = some answer) ∧
    (Certificate Y (machine e₁) (machine d) m a z →
      Certificate Y (machine e₁) (machine d) m b w → a = b)

instance (Y : Oracle) (e₀ e₁ d q r : ℕ) : Decidable (orderMatrix Y e₀ e₁ d q r) := by
  unfold orderMatrix
  infer_instance

theorem witness_normal_form (Y : Oracle) (e₀ e₁ d : ℕ) :
    OrderWitness Y (machine e₀) (machine e₁) (machine d) ↔
      ∀ q, ∃ r, orderMatrix Y e₀ e₁ d q r := by
  constructor
  · rintro ⟨hc, ht⟩ q
    obtain ⟨a, z, w, hz, hw⟩ := ht (Nat.unpair q).1
    exact ⟨Nat.pair a (Nat.pair z w), ⟨by simpa using hz, by simpa using hw⟩,
      hc _ _ _ _ _⟩
  · intro h
    refine ⟨?_, ?_⟩
    · intro n a b z w hz hw
      obtain ⟨r, _, hc⟩ := h (Nat.pair 0 (Nat.pair n (Nat.pair a (Nat.pair b (Nat.pair z w)))))
      simp only [Nat.unpair_pair] at hc
      exact hc hz hw
    · intro n
      obtain ⟨r, ⟨hc, ht⟩, _⟩ := h (Nat.pair n 0)
      exact ⟨(Nat.unpair r).1, (Nat.unpair (Nat.unpair r).2).1,
        (Nat.unpair (Nat.unpair r).2).2, by simpa using hc, by simpa using ht⟩

theorem order_normal_form {Y A₀ A₁ : Oracle} {e₀ e₁ : ℕ}
    (h₀ : Represents Y (machine e₀) A₀) (h₁ : Represents Y (machine e₁) A₁) :
    Reduces A₀ A₁ ↔ ∃ d : ℕ, ∀ q : ℕ, ∃ r : ℕ, orderMatrix Y e₀ e₁ d q r := by
  rw [order_iff_witness h₀ h₁]
  constructor
  · rintro ⟨d, hd⟩
    refine ⟨encode d, (witness_normal_form Y e₀ e₁ (encode d)).mp ?_⟩
    simpa using hd
  · rintro ⟨d, hd⟩
    exact ⟨machine d, (witness_normal_form Y e₀ e₁ d).mpr hd⟩

end TuringRigidity.OrderNormalForm

end OAI
