/-
Copyright (c) 2026 Umang Mathur. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Umang Mathur
-/

module

public import LeanPool.Parikh.Activation
public import Mathlib.Computability.DFA
import LeanPool.Parikh.GrammarImage
import LeanPool.Parikh.RegularRealization

/-! Ported from focs-lab/parikh-theorem at
`9c1cde93f29bbaa91542e401e074ec3cd7646880`; module headers and import paths
adapted for Lean Pool. -/

public section

/-!
# Using Parikh's theorem

This module proves semilinearity, exact finite representation, and the existence
of a regular language with the same Parikh image. `Parikh/Api.lean` exposes
descriptive public names for these results.

The proof assembles earlier modules through `treeRepresentation_eq`: the union
of activatable tree components is exactly the grammar image. Its proof and
semilinearity are shared in `GrammarImage.lean`, so regular-language specialization
can reuse them without an import cycle.
The public results do not require a finite ambient nonterminal type.

`Parikh/ExecutableCompiler.lean` computes a representation for finite encoded input.

Source: `thm:main`, `thm:parikh-statement`.
-/
namespace Parikh
variable {T : Type*}

/-- The exact tree/context union equals the Mathlib grammar image (`thm:main`). -/
theorem treeRepresentation_eq [Finite T] [DecidableEq T] (g : ContextFreeGrammar T) :
    treeRepresentation g = image g.language := by
  exact (treeRepresentation_correct g).1

/-- Forward Parikh theorem for Mathlib grammars (`thm:parikh-statement`).
No finiteness or decidable-equality assumption is imposed on `g.NT`.
-/
theorem grammar_image [Finite T] [DecidableEq T] (g : ContextFreeGrammar T) :
    IsSemilinearSet (image g.language) := by
  exact (treeRepresentation_correct g).2

/-- A finite indexed witness with exact denotation, not merely containment (`thm:main`). -/
theorem grammar_witness [Finite T] [DecidableEq T] (g : ContextFreeGrammar T) :
    ∃ W : Witness T, W.denotation = image g.language := by
  exact exists_witness (image g.language) (grammar_image g)

/-- Language-level specialization using Mathlib's context-free predicate. -/
theorem contextFree_image [Finite T] [DecidableEq T] (L : Language T) (hL : L.IsContextFree) :
    IsSemilinearSet (image L) := by
  obtain ⟨g, rfl⟩ := hL
  exact grammar_image g

/-- Every CFL has a DFA-regular language with the same image (`thm:parikh-statement`). -/
theorem regular_realization [Finite T] [DecidableEq T] (g : ContextFreeGrammar T) :
    ∃ R : Language T, R.IsRegular ∧ image R = image g.language := by
  exact converse (image g.language) (grammar_image g)

end Parikh
