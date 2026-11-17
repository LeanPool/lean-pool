/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/EncodableTree.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

/-
Copyright (c) 2024 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller

Adapted for the Palomar module-system port: the finite-tree encoding from
Mathlib.Tactic.DeriveEncodable is exposed here, so clients do not rely on
that deriving handler's private helper type across module boundaries.
-/
module

public import Mathlib

/-!
# An explicit finite-tree encoding for the module-system port

This is the natural-labelled binary-tree encoding used by Mathlib's Encodable
deriving handler. Exposing the type and its codec avoids generated references
to the handler's private `S`. OracleCode and SentenceForm use the same constructor
tags and list layout as before; their mathematical types and operations do not
change. Every decoding and inverse law below is an ordinary kernel-checked
Lean definition or proof, not a new deriving handler or an axiom.
-/


@[expose] public section

namespace OAI.TuringRigidity

inductive EncodableTree : Type where
  | nat (n : ℕ)
  | cons (a b : EncodableTree)

namespace EncodableTree

def encode : EncodableTree → ℕ
  | nat n => Nat.pair 0 n
  | cons a b => Nat.pair (encode a + 1) (encode b)

theorem unpair_right_lt {n : ℕ} (h : (Nat.unpair n).1 ≠ 0) :
    (Nat.unpair n).2 < n := by
  obtain ⟨⟨a, b⟩, rfl⟩ := Nat.pairEquiv.surjective n
  simp only [Nat.pairEquiv_apply, Function.uncurry_apply_pair, Nat.unpair_pair] at *
  unfold Nat.pair
  have := Nat.le_mul_self a
  have := Nat.le_mul_self b
  split <;> lia

def decode (n : ℕ) : EncodableTree :=
  let p := Nat.unpair n
  if h : p.1 = 0 then
    .nat p.2
  else
    have : p.1 ≤ n := Nat.unpair_left_le n
    have := Nat.unpair_lt (by lia : 1 ≤ n)
    have := unpair_right_lt h
    .cons (decode (p.1 - 1)) (decode p.2)

theorem decode_encode (s : EncodableTree) : decode (encode s) = s := by
  induction s with
  | nat n =>
    unfold encode decode
    simp
  | cons a b iha ihb =>
    unfold encode decode
    simp [iha, ihb]

instance : Encodable EncodableTree where
  encode := encode
  decode n := some (decode n)
  encodek s := by simp [decode_encode]

end EncodableTree
end OAI.TuringRigidity
