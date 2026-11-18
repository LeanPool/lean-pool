/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-auto/OAI/Computability/DegreeRigidity/Model.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import Mathlib.Computability.TuringDegree


/-!
# Model
-/


@[expose] public section

namespace OAI

namespace TuringRigidity

/-- A Boolean oracle on the natural numbers. -/
abbrev Oracle := ℕ → Bool

/-- The total partial-function representation of an oracle, with Boolean values encoded as
zero and one. -/
def oracleFunction (A : Oracle) : ℕ →. ℕ := fun n => Part.some (if A n then 1 else 0)

/-- Ordinary Turing reducibility between the total Boolean characteristic functions. -/
def Reduces (A B : Oracle) : Prop := TuringReducible (oracleFunction A) (oracleFunction B)

instance : IsPreorder Oracle Reduces where
  refl A := TuringReducible.refl (oracleFunction A)
  trans _ _ _ h k := TuringReducible.trans h k

/-- The partial-order quotient of Boolean oracles by mutual Turing reducibility. -/
def Degree := Antisymmetrization Oracle Reduces

instance : PartialOrder Degree :=
  @instPartialOrderAntisymmetrization Oracle
    { le := Reduces
      lt A B := Reduces A B ∧ ¬ Reduces B A
      lt_iff_le_not_ge _ _ := Iff.rfl
      le_refl A := TuringReducible.refl (oracleFunction A)
      le_trans _ _ _ h k := TuringReducible.trans h k }

private instance oraclePreorder : Preorder Oracle where
  le := Reduces
  lt A B := Reduces A B ∧ ¬ Reduces B A
  lt_iff_le_not_ge _ _ := Iff.rfl
  le_refl A := TuringReducible.refl (oracleFunction A)
  le_trans _ _ _ h k := TuringReducible.trans h k

/-- Every order automorphism of the ordinary Turing degrees fixes every degree. -/
def MainTheorem : Prop := ∀ π : Degree ≃o Degree, ∀ a : Degree, π a = a

end TuringRigidity

end OAI
