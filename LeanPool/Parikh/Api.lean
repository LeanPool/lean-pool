/-
Copyright (c) 2026 Umang Mathur. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Umang Mathur
-/

module

public import LeanPool.Parikh.ExecutableCompiler
public import Mathlib.Computability.DFA
import LeanPool.Parikh.RegularRealization
import LeanPool.Parikh.Statements

/-! Ported from focs-lab/parikh-theorem at
`9c1cde93f29bbaa91542e401e074ec3cd7646880`; module headers and import paths
adapted for Lean Pool. -/

public section

/-!
# Public interface

Count letters with `parikhVector` and take a language's `parikhImage`.
The main theorems give semilinearity, finite representations, and regular
languages with the same image. `compileGrammar` computes a representation
from a finite encoded grammar.
-/
namespace Parikh

/-- A natural-number count for each letter in the alphabet. -/
abbrev CountVector (T : Type*) := Vector T

/-- One base vector and a finite list of period vectors. -/
abbrev LinearComponent (T : Type*) := Component T

/-- A finite list of linear components. -/
abbrev SemilinearRepresentation (T : Type*) := Witness T

/-- The vector recording how often each letter occurs in a word. -/
abbrev parikhVector {T : Type*} [DecidableEq T] (w : List T) : CountVector T := counts w

/-- The set of count vectors of the words in a language. -/
abbrev parikhImage {T : Type*} [DecidableEq T] (L : Language T) : Set (CountVector T) := image L

/-- The base plus arbitrary natural multiples of the indexed periods. -/
abbrev LinearComponent.denotation {T : Type*} (c : LinearComponent T) : Set (CountVector T) :=
  Component.denotation c

/-- The union of the represented linear sets. -/
abbrev SemilinearRepresentation.denotation {T : Type*}
    (W : SemilinearRepresentation T) : Set (CountVector T) := Witness.denotation W

/-- Concatenating words adds their count vectors. -/
theorem parikhVector_append {T : Type*} [DecidableEq T] (u v : List T) :
    parikhVector (u ++ v) = parikhVector u + parikhVector v := counts_append u v

/-- Each component denotes a linear set in Mathlib's sense. -/
theorem LinearComponent.isLinearSet {T : Type*} (c : LinearComponent T) :
    IsLinearSet c.denotation := component_isLinearSet c

/-- Every finite representation denotes a semilinear set. -/
theorem SemilinearRepresentation.isSemilinearSet {T : Type*}
    (W : SemilinearRepresentation T) : IsSemilinearSet W.denotation := witness_isSemilinearSet W

/-- The Parikh image of a context-free grammar is semilinear. -/
theorem parikhImage_isSemilinear_of_grammar {T : Type*} [Finite T] [DecidableEq T]
    (g : ContextFreeGrammar T) : IsSemilinearSet (parikhImage g.language) := grammar_image g

/-- Parikh's theorem for a context-free language over a finite alphabet. -/
theorem parikhImage_isSemilinear_of_isContextFree {T : Type*} [Finite T] [DecidableEq T]
    (L : Language T) (hL : L.IsContextFree) : IsSemilinearSet (parikhImage L) :=
  contextFree_image L hL

/-- The Parikh image of a regular language is semilinear. -/
theorem parikhImage_isSemilinear_of_isRegular {T : Type*} [Finite T] [DecidableEq T]
    (L : Language T) (hL : L.IsRegular) : IsSemilinearSet (parikhImage L) := regular_image L hL

/-- Every grammar has a finite representation of exactly its Parikh image. -/
theorem exists_semilinearRepresentation_of_grammar {T : Type*} [Finite T] [DecidableEq T]
    (g : ContextFreeGrammar T) :
    ∃ W : SemilinearRepresentation T, W.denotation = parikhImage g.language := grammar_witness g

/-- An exact representation also exists within the grammar's size bounds. -/
theorem exists_boundedSemilinearRepresentation_of_grammar {T : Type*}
    [Fintype T] [DecidableEq T] (g : ContextFreeGrammar T) :
    ∃ W : SemilinearRepresentation T,
      W.denotation = parikhImage g.language ∧ WithinBounds (grammarSize g) W := bounded_witness g

/-- Every semilinear set is the Parikh image of a regular language. -/
theorem exists_regularLanguage_with_parikhImage {T : Type*} [Finite T] [DecidableEq T]
    (X : Set (CountVector T)) (hX : IsSemilinearSet X) :
    ∃ R : Language T, R.IsRegular ∧ parikhImage R = X := converse X hX

/-- Every context-free grammar has a regular language with the same Parikh image. -/
theorem exists_regularLanguage_with_grammar_parikhImage {T : Type*}
    [Finite T] [DecidableEq T] (g : ContextFreeGrammar T) :
    ∃ R : Language T, R.IsRegular ∧ parikhImage R = parikhImage g.language := regular_realization g

/-- Compute an exact finite representation from a grammar with numeric labels. -/
abbrev compileGrammar (g : EncodedGrammar) : SemilinearRepresentation (Fin g.terminalCount) :=
  compiler.compile g

/-- The computed representation denotes exactly the grammar's Parikh image. -/
theorem compileGrammar_correct (g : EncodedGrammar) :
    (compileGrammar g).denotation = parikhImage g.decode.language := compiler.correct g

/-- The computed representation satisfies the component, period, and norm bounds. -/
theorem compileGrammar_size_bounds (g : EncodedGrammar) :
    WithinBounds g.size (compileGrammar g) := compiler.bounded g

/-- The computed coordinates fit the fixed-width numerical bit budget. -/
theorem compileGrammar_bit_bound (g : EncodedGrammar) :
    entryBits g.size (compileGrammar g) ≤ g.size.vectorBits ∧
      (∀ c ∈ compileGrammar g, ∀ a, c.base a < 2 ^ g.size.coordinateBits) ∧
      (∀ c ∈ compileGrammar g, ∀ p ∈ c.periods, ∀ a, p a < 2 ^ g.size.coordinateBits) :=
  g.compile_bit_bound

end Parikh
