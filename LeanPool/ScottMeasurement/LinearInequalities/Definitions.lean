/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.Convex.Hull

/-!
# Scott's finite systems of linear inequalities

Definitions corresponding to §1 of Scott (1964), pp. 233–237.
-/

@[expose] public section

open Set

namespace Scott1964.MeasurementStructures.LinearInequalities

variable {L : Type*} [AddCommGroup L] [Module ℝ L]

/-- A set is symmetric when it is closed under negation. -/
def Symmetric (X : Set L) : Prop := ∀ ⦃x⦄, x ∈ X → -x ∈ X

/-- `N` is realized on `X` by a real linear functional. -/
def Realizable (X N : Set L) : Prop :=
  ∃ φ : Module.Dual ℝ L, ∀ x ∈ X, x ∈ N ↔ 0 ≤ φ x

/-- Scott's notation `x ≻ 0`: positive, but its negative is not positive. -/
def strictPositive (X N : Set L) : Set L :=
  {x | x ∈ X ∧ x ∈ N ∧ -x ∉ N}

/-- Vectors declared both nonnegative and nonpositive. -/
def indifferent (X N : Set L) : Set L :=
  {x | x ∈ X ∧ x ∈ N ∧ -x ∈ N}

/-- Condition (1): every vector has one of the two weak signs. -/
def SignComplete (X N : Set L) : Prop :=
  ∀ ⦃x⦄, x ∈ X → x ∈ N ∨ -x ∈ N

/-- Geometric form of Scott's condition (2).

No convex combination of strictly positive vectors belongs to the linear
span of vectors carrying both weak signs. For finite symmetric systems this
is equivalent to Scott's positive-coefficient cancellation condition.
-/
def WeightedCancellation (X N : Set L) : Prop :=
  Disjoint (convexHull ℝ (strictPositive X N))
    (Submodule.span ℝ (indifferent X N) : Set L)

/-- Scott's literal positive-weight finite-sequence condition (2).
Sequences are indexed by `Fin (n + 1)`, making nonemptiness explicit. -/
def WeightedSequenceCancellation (X N : Set L) : Prop :=
  ∀ (n : ℕ) (x : Fin (n + 1) → L) (c : Fin (n + 1) → ℝ),
    (∀ i, x i ∈ X) → (∀ i, x i ∈ N) → (∀ i, 0 < c i) →
    ∑ i, c i • x i = 0 → ∀ i, -x i ∈ N

/-- Scott's literal unweighted finite-sequence condition (4). -/
def UnweightedSequenceCancellation (X N : Set L) : Prop :=
  ∀ (n : ℕ) (x : Fin (n + 1) → L),
    (∀ i, x i ∈ X) → (∀ i, x i ∈ N) →
    ∑ i, x i = 0 → ∀ i, -x i ∈ N

/-- Positive natural-multiplicity version, intermediate between rational
weights and literal repetition. -/
def NatWeightedSequenceCancellation (X N : Set L) : Prop :=
  ∀ (n : ℕ) (x : Fin (n + 1) → L) (k : Fin (n + 1) → ℕ),
    (∀ i, x i ∈ X) → (∀ i, x i ∈ N) → (∀ i, 0 < k i) →
    ∑ i, k i • x i = 0 → ∀ i, -x i ∈ N

/-- A vector in `S → ℝ` has rational coordinates. -/
def IsRationalVector {S : Type*} (x : S → ℝ) : Prop :=
  ∀ s, ∃ q : ℚ, x s = q

/-- A set consists of rational vectors. -/
def IsRationalSet {S : Type*} (X : Set (S → ℝ)) : Prop :=
  ∀ ⦃x⦄, x ∈ X → IsRationalVector x

/-- Realizability of a relation by comparison of functional values. -/
def RelationRealizable (Y : Set L) (R : L → L → Prop) : Prop :=
  ∃ φ : Module.Dual ℝ L, ∀ x ∈ Y, ∀ y ∈ Y, R x y ↔ φ y ≤ φ x

/-- Condition (5): completeness on `Y`. -/
def RelationComplete (Y : Set L) (R : L → L → Prop) : Prop :=
  ∀ ⦃x⦄, x ∈ Y → ∀ ⦃y⦄, y ∈ Y → R x y ∨ R y x

/-- Strictly positive differences associated to a relation. -/
def strictDifferences (Y : Set L) (R : L → L → Prop) : Set L :=
  {z | ∃ x ∈ Y, ∃ y ∈ Y, R x y ∧ ¬R y x ∧ z = x - y}

/-- Indifferent differences associated to a relation. -/
def indifferentDifferences (Y : Set L) (R : L → L → Prop) : Set L :=
  {z | ∃ x ∈ Y, ∃ y ∈ Y, R x y ∧ R y x ∧ z = x - y}

/-- Geometric form of Scott's equal-sums cancellation condition (6). -/
def RelationCancellation (Y : Set L) (R : L → L → Prop) : Prop :=
  Disjoint (convexHull ℝ (strictDifferences Y R))
    (Submodule.span ℝ (indifferentDifferences Y R) : Set L)

/-- Scott's literal paired equal-sums condition (6). -/
def RelationSequenceCancellation (Y : Set L) (R : L → L → Prop) : Prop :=
  ∀ (n : ℕ) (x y : Fin (n + 1) → L),
    (∀ i, x i ∈ Y) → (∀ i, y i ∈ Y) → (∀ i, R (x i) (y i)) →
    ∑ i, x i = ∑ i, y i → ∀ i, R (y i) (x i)

/-- The additive closure `Y⁺` (including the empty sum). -/
def additiveClosure (Y : Set L) : Set L :=
  AddSubmonoid.closure Y

/-- Scott's three axioms (i)–(iii) for a strictly monotonic relation. -/
structure StrictlyMonotonic (Z : Set L) (R : L → L → Prop) : Prop where
  complete : ∀ ⦃x⦄, x ∈ Z → ∀ ⦃y⦄, y ∈ Z → R x y ∨ R y x
  add : ∀ ⦃x₀ y₀ x₁ y₁⦄, x₀ ∈ Z → y₀ ∈ Z → x₁ ∈ Z → y₁ ∈ Z →
    R x₀ y₀ → R x₁ y₁ → R (x₀ + x₁) (y₀ + y₁)
  cancel : ∀ ⦃x₀ y₀ x₁ y₁⦄, x₀ ∈ Z → y₀ ∈ Z → x₁ ∈ Z → y₁ ∈ Z →
    x₀ + x₁ = y₀ + y₁ → R x₁ y₁ → R y₀ x₀

/-- `Rplus` extends `R` from `Y` to `Z`. -/
def ExtendsOn (Y Z : Set L) (R Rplus : L → L → Prop) : Prop :=
  Y ⊆ Z ∧ ∀ ⦃x⦄, x ∈ Y → ∀ ⦃y⦄, y ∈ Y → (Rplus x y ↔ R x y)

end Scott1964.MeasurementStructures.LinearInequalities
