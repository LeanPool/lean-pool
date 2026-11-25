/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Order.Basic

/-!
# Restriction after adjoining trivial legs

The embedding preserves products. A direct sum over the larger site
set gives each extra leg a block label. This costs an inequality in
one direction and permits independent closures in the other.
-/

@[expose] public section

namespace MatrixMultiplicationAllFields.MatrixExponent.Prices

/-- The data for the padding construction, including `zero`, `one`, `le_iff`, `mul`, `add_le`. -/
structure Padding {S T : Type*} [CommSemiring S] [CommSemiring T]
    [PartialOrder S] [PartialOrder T] (pad : S → T) : Prop where
  zero : pad 0 = 0
  one : pad 1 = 1
  le_iff (s t) : pad s ≤ pad t ↔ s ≤ t
  mul (s t) : pad (s * t) = pad s * pad t
  add_le (s t) : pad (s + t) ≤ pad s + pad t
  split {s x y} : pad s ≤ x + y → ∃ a b, pad a ≤ x ∧ pad b ≤ y ∧ s ≤ a + b
  factor {s a x} : pad s ≤ pad a * x → ∃ b, pad b ≤ x ∧ s ≤ a * b

end MatrixMultiplicationAllFields.MatrixExponent.Prices
