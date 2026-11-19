/-
Copyright (c) 2026 Daniel Souza. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Souza
-/
module

-- Adapted for Lean Pool.

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Erase
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Finset.Insert
public import Mathlib.LinearAlgebra.Matrix.Defs

/-! # Occupation-basis fermion operators -/

@[expose] public section

namespace HubbardMoments

open Finset

variable {O : Type*} [DecidableEq O]

/-- The number of occupied orbitals of `S` that come before `o` in the order `ord`. -/
def countBelow (ord : O ↪ ℕ) (S : Finset O) (o : O) : ℕ := (S.filter fun x => ord x < ord o).card

/-- **Fermion annihilation operator** `c_o` on the Fock space of the orbitals `O`. The basis
state of an occupied set `S` is `|S⟩ = c†_{o₁} ⋯ c†_{o_k} |0⟩`, with `o₁, …, o_k` the orbitals
of `S` in the order `ord`. Then `c_o |S⟩ = (-1)^m |S \ {o}⟩` if `o ∈ S`, `m` the number of
orbitals of `S` before `o`, and `c_o |S⟩ = 0` otherwise. -/
def annihilate (ord : O ↪ ℕ) (o : O) : Matrix (Finset O) (Finset O) ℂ := fun S' S =>
  if o ∈ S ∧ S' = S.erase o then (-1) ^ countBelow ord S o else 0

/-- **Fermion creation operator** `c†_o`: `c†_o |S⟩ = (-1)^m |S ∪ {o}⟩` if `o ∉ S`, `m` the
number of orbitals of `S` before `o`, and `0` otherwise. It is the adjoint of `annihilate`. -/
def create (ord : O ↪ ℕ) (o : O) : Matrix (Finset O) (Finset O) ℂ := fun S' S =>
  if o ∉ S ∧ S' = insert o S then (-1) ^ countBelow ord S o else 0

end HubbardMoments
