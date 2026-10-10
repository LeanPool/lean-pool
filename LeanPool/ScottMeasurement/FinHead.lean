/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson
-/

module

public import Mathlib.Data.Fin.Basic

/-!
# Stable `Fin (n + 1)` head index

Compared Scott permutation/cancellation conditions mention the distinguished
index `0 : Fin (n + 1)`.  Elaborating that literal attaches a generated
`._proof_N` to whichever declaration first needs `OfNat`.  Palomar compares
those generated constants, so Challenge and Solution must share a named
proof of `0 < n + 1` instead.
-/

@[expose] public section

namespace Scott1964.MeasurementStructures

theorem fin_succ_pos (n : ℕ) : 0 < n + 1 :=
  Nat.succ_pos n

/-- The distinguished index in a nonempty Scott sequence of length `n + 1`. -/
def finHead (n : ℕ) : Fin (n + 1) :=
  ⟨0, fin_succ_pos n⟩

theorem finHead_eq_zero (n : ℕ) : finHead n = 0 :=
  Fin.ext rfl

end Scott1964.MeasurementStructures
