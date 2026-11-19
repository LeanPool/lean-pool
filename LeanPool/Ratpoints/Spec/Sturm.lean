/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.Polynomial.Sturm.Sequence
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.List.SignVariations

/-!
# Sturm's theorem

Sturm's theorem in the form that the theorems on the Sturm step of `ratpoints` assume: for a
squarefree real polynomial `p` and reals `a ≤ b`, the number of roots of `p` in `(a, b]` is the
number of sign variations of the Sturm sequence of `p` and `p'` at `a` less that at `b`. Mathlib has
the Sturm sequence (`Polynomial.sturmSeq`) and the sign variations of a list
(`List.signVariations`), but not the theorem; here it is a `Prop`-valued definition, a hypothesis
of the theorems that need it. The specification uses Mathlib and nothing of the model; the
comparator challenge restates the definition verbatim.

## Main definitions

* `Ratpoints.SturmTheorem`: Sturm's theorem, as a proposition.

## Implementation notes

The file imports `Mathlib.Algebra.Polynomial.Sturm.Sequence`, which brings the derivative and the
cardinality of sets (`Set.ncard`) with it, `Mathlib.Data.List.SignVariations`,
`Mathlib.Algebra.Squarefree.Basic` and `Mathlib.Basic.Real.Basic`; the comparator challenge imports
the Mathlib modules among the public imports of the files of the specification.
-/

@[expose] public section

namespace Ratpoints

open Polynomial in
/-- Sturm's theorem: for every squarefree real polynomial `p` and all reals `a ≤ b`, the number of
roots of `p` in `(a, b]` plus the number of sign variations of the Sturm sequence of `p` and its
derivative evaluated at `b` is that number at `a`. A hypothesis of the theorems on the Sturm step,
not an axiom. -/
def SturmTheorem : Prop :=
  ∀ p : ℝ[X], Squarefree p → ∀ a b : ℝ, a ≤ b →
    {x | a < x ∧ x ≤ b ∧ p.IsRoot x}.ncard +
        ((sturmSeq p (derivative p)).map (eval b)).signVariations =
      ((sturmSeq p (derivative p)).map (eval a)).signVariations

end Ratpoints

end
