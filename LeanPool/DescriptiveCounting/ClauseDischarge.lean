/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
module

public import LeanPool.DescriptiveCounting.SecondOrder
public import LeanPool.DescriptiveCounting.Padding

/-!
# Shared scaffolding of the clausal discharges

The clausal fragments of existential second-order logic – SO-Horn
(`DescriptiveComplexity.SecondOrderHorn`) and SO-Krom
(`DescriptiveComplexity.SecondOrderKrom`) – have discharges of the same shape: a
program is translated, inside an ordered input structure, into a CNF instance
whose propositional variables are the second-order atoms and whose clauses are
the instances of the program's clauses whose guard holds
(`DescriptiveComplexity.Problems.HornSat.Hardness`,
`DescriptiveComplexity.Problems.TwoSat.Hardness`). Only the *literals* differ: a head
and a body list on the Horn side, two signed slots on the Krom side.

Everything that does not depend on that difference is here:

* `DescriptiveComplexity.clauseDim`: the dimension of the interpretation, wide enough
  for the `k` universally quantified variables of the program and for every
  argument tuple of a relation variable of the block;
* `DescriptiveComplexity.ClauseTag`: the tags – one per clause of the program, one per
  relation variable of the block, plus a junk tag keeping the tag type nonempty;
* `DescriptiveComplexity.guardF`, `DescriptiveComplexity.atomOccF`: the defining formula of a
  clause's guard, and the formula saying that a coordinate tuple holds the
  canonically padded (`DescriptiveComplexity.Padding`) argument tuple of a
  second-order atom – the two building blocks of every defining formula of such
  a discharge, with their realization lemmas.
-/

@[expose] public section

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

section Scaffolding

variable {L : Language.{0, 0}} {B : SOBlock} {k : ℕ}

/-! ### Dimension and tags -/

/-- The dimension of a clausal discharge: large enough for the `k` universally
quantified first-order variables of the program and for every argument tuple of
a relation variable of the block. -/
noncomputable def clauseDim (B : SOBlock) (k : ℕ) : ℕ :=
  max k (blockArityBound B)

theorem le_clauseDim : k ≤ clauseDim B k :=
  le_max_left _ _

theorem arity_le_clauseDim (i : B.ι) : B.arity i ≤ clauseDim B k :=
  (arity_le_blockArityBound B i).trans (le_max_right _ _)

/-- The tags of a clausal discharge of a program with `m` clauses: one per
clause, one per relation variable of the block, plus a junk tag keeping the tag
type nonempty when the program has no clause and the block no variable (its
elements are neither clauses nor literals). -/
abbrev ClauseTag (m : ℕ) (B : SOBlock) : Type :=
  (Fin m ⊕ B.ι) ⊕ Unit

/-- The tag of the clauses coming from the `c`-th clause of the program. -/
abbrev clTag {m : ℕ} {B : SOBlock} (c : Fin m) : ClauseTag m B :=
  Sum.inl (Sum.inl c)

/-- The tag of the propositional variables standing for the atoms of the
relation variable `i`. -/
abbrev varTag {m : ℕ} {B : SOBlock} (i : B.ι) : ClauseTag m B :=
  Sum.inl (Sum.inr i)

/-- The arguments of a second-order atom, as coordinates of the clause
tuple. -/
noncomputable def atomIdx (a : SOAtom B k) : Fin (B.arity a.idx) → Fin (clauseDim B k) :=
  fun j => Fin.castLE le_clauseDim (a.args j)

/-! ### The two defining formulas -/

section Formulas

variable {γ : Type}

/-- The guard of a clause, reading its variables off the coordinates selected
by `u`. -/
noncomputable def guardF (φ : (L.sum Language.order).Formula (Fin k))
    (u : Fin (clauseDim B k) → γ) : (L.sum Language.order).Formula γ :=
  φ.relabel fun j => u (Fin.castLE (le_clauseDim (B := B)) j)

/-- The occurrence formula of a second-order atom: the coordinates selected by
`x` hold the canonically padded tuple of the atom's arguments, read off the
coordinates selected by `u`. -/
noncomputable def atomOccF (a : SOAtom B k) (u x : Fin (clauseDim B k) → γ) :
    (L.sum Language.order).Formula γ :=
  padTupF (atomIdx a) u x

variable {A : Type} [L.Structure A] [LinearOrder A] {v : γ → A}

private theorem realize_guardF {φ : (L.sum Language.order).Formula (Fin k)}
    {u : Fin (clauseDim B k) → γ} :
    (guardF (L := L) (B := B) φ u).Realize v ↔
      φ.Realize fun j => v (u (Fin.castLE le_clauseDim j)) := by
  rw [guardF, Formula.realize_relabel]
  rfl

private theorem realize_atomOccF {a : SOAtom B k} {u x : Fin (clauseDim B k) → γ} :
    (atomOccF (L := L) a u x).Realize v ↔
      PadTup (atomIdx a) (fun j => v (u j)) fun j => v (x j) := by
  rw [atomOccF, realize_padTupF]

end Formulas

end Scaffolding

end DescriptiveComplexity
