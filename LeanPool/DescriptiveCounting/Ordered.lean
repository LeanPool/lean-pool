/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
module

public import LeanPool.DescriptiveCounting.Interpretation
public import Mathlib.ModelTheory.Order

/-!
# Ordered first-order reductions

Textbook FO reductions ([Immerman 1999][immerman1999descriptive],
*Descriptive Complexity*, ch. 3) operate on *ordered* finite structures: the
input structure comes with a linear order on
its universe, which the defining formulas may mention. The order is essential
for many reductions: e.g., reducing SAT to 3-colorability threads an OR-gadget
chain along the order of each clause's literals, which no order-free
first-order interpretation can express.

This file provides the ordered variant of `DescriptiveComplexity.FOReduction`:

* an `(L.sum Language.order).Structure` instance on any linearly ordered
  `L`-structure, realizing the extra binary symbol `leSymb` as `≤`;
* `DescriptiveComplexity.OrderedFOReduction P Q`: a first-order interpretation of `L'` in
  the ordered expansion `L.sum Language.order`, mapping yes-instances of `P`
  exactly to yes-instances of `Q` – for every *finite* linearly ordered input
  structure. Finiteness matters: gadget constructions traverse the order and
  need minima, maxima and successors.

Since the problem `P` does not mention the order and correctness is required
for *every* linear order on the input structure, an `OrderedFOReduction` is
what descriptive complexity calls an order-invariant FO reduction.
-/

@[expose] public section

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

variable (L : Language.{0, 0})

section OrderedStructures

variable (A : Type) [L.Structure A] [LE A]

/-- A linearly ordered `L`-structure is a structure over the ordered expansion
`L.sum Language.order`, interpreting the order symbol as `≤`. -/
instance sumOrderStructure : (L.sum Language.order).Structure A :=
  letI := orderStructure (M := A)
  inferInstance

instance : (L.sum Language.order).OrderedStructure A :=
  ⟨fun _ => Iff.rfl⟩

variable {L A}

@[simp]
theorem relMap_sumInl {n : ℕ} (r : L.Relations n) (x : Fin n → A) :
    RelMap (L := L.sum Language.order) (Sum.inl r) x ↔ RelMap r x :=
  Iff.rfl

end OrderedStructures

variable {L} {L' : Language.{0, 0}}

/-- An *ordered* first-order reduction from the problem `P` (on
`L`-structures) to the problem `Q` (on `L'`-structures): a first-order
interpretation over the ordered expansion of `L` that maps yes-instances of
`P` exactly to yes-instances of `Q`, for every finite linearly ordered input
structure.

As `P` does not depend on the order, correctness for every linear order makes
this an order-invariant FO reduction; it is computable in AC⁰ ⊆ PTIME on
(encodings of) finite ordered structures, hence in particular a Karp
reduction. -/
structure OrderedFOReduction [L.IsRelational] [L'.IsRelational]
    (P : DecisionProblem L) (Q : DecisionProblem L') where
  /-- The tags (copies of `A^dim`) used by the underlying interpretation. -/
  Tag : Type
  /-- Tags are finite, so that finite structures map to finite structures. -/
  [tagFinite : Finite Tag]
  /-- Tags are nonempty, so that nonempty structures map to nonempty
  structures. -/
  [tagNonempty : Nonempty Tag]
  /-- The dimension of the underlying interpretation. -/
  dim : ℕ
  /-- The underlying first-order interpretation, over the ordered expansion. -/
  toInterpretation : FOInterpretation (L.sum Language.order) L' Tag dim
  /-- Yes-instances map exactly to yes-instances, whatever the linear order. -/
  correct : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
    P A ↔ Q (toInterpretation.Map A)

@[inherit_doc]
scoped notation:50 P:51 " ≤ᶠᵒ[≤] " Q:51 => OrderedFOReduction P Q

end DescriptiveComplexity
