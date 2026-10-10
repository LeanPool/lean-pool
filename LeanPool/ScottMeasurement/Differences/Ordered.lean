/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson
-/

module

public import LeanPool.ScottMeasurement.Differences.Pair

/-!
# Ordered differences

Scott's reduction of the one-utility problem to Theorem 3.1 is entirely
algebraic.  The key point is that reversal lets the two utilities be combined.
-/

@[expose] public section

namespace Scott1964.MeasurementStructures

/-- Representation of comparisons of utility differences. -/
def RealizableDifference {A : Type u} (D : A → A → A → A → Prop) : Prop :=
  ∃ f : A → ℝ, ∀ x y z w, D x y z w ↔ f x - f y ≥ f z - f w

/-- Scott 1964, condition `(1_D)`. -/
def DiffTotal {A : Type u} (D : A → A → A → A → Prop) : Prop :=
  ∀ x y z w, D x y z w ∨ D z w x y

/-- Scott 1964, condition `(2_D)`. -/
def DiffPermutation {A : Type u} (D : A → A → A → A → Prop) : Prop :=
  ∀ (n : ℕ) (x y : Fin (n + 1) → A) (π σ : Equiv.Perm (Fin (n + 1))),
    (∀ i, i ≠ finHead n → D (x i) (y i) (x (π i)) (y (σ i))) →
      D (x (π (finHead n))) (y (σ (finHead n))) (x (finHead n)) (y (finHead n))

/-- Scott 1964, condition `(3_D)`. -/
def DiffReversal {A : Type u} (D : A → A → A → A → Prop) : Prop :=
  ∀ x y z w, D x y z w → D w z y x

theorem RealizableDifference.utilityPair {A : Type u}
    {D : A → A → A → A → Prop} (hD : RealizableDifference D) :
    RealizableUtilityPair D := by
  rcases hD with ⟨f, hf⟩
  refine ⟨f, fun y ↦ -f y, ?_⟩
  intro x y z w
  rw [hf]
  constructor <;> intro h <;> dsimp at h ⊢ <;> linarith

theorem RealizableDifference.reversal {A : Type u}
    {D : A → A → A → A → Prop} (hD : RealizableDifference D) :
    DiffReversal D := by
  rcases hD with ⟨f, hf⟩
  intro x y z w h
  rw [hf] at h ⊢
  linarith

theorem RealizableDifference.necessary {A : Type u}
    {D : A → A → A → A → Prop} (hD : RealizableDifference D) :
    DiffTotal D ∧ DiffPermutation D ∧ DiffReversal D := by
  have hp := hD.utilityPair.necessary
  exact ⟨hp.1, hp.2, hD.reversal⟩

/-- The combining-utilities argument in the proof of Theorem 3.2. -/
theorem difference_of_pair_and_reversal {A : Type u}
    {D : A → A → A → A → Prop} (hp : RealizableUtilityPair D)
    (hr : DiffReversal D) : RealizableDifference D := by
  rcases hp with ⟨g, q, hrep⟩
  refine ⟨fun x ↦ g x - q x, ?_⟩
  intro x y z w
  constructor
  · intro h
    have h₁ := (hrep x y z w).1 h
    have h₂ := (hrep w z y x).1 (hr x y z w h)
    dsimp
    linarith
  · intro hdiff
    by_contra hn
    have hstrict : g x + q y < g z + q w :=
      lt_of_not_ge (fun h ↦ hn ((hrep x y z w).2 h))
    have hreverse : D z w x y := (hrep z w x y).2 (le_of_lt hstrict)
    have h₂ := (hrep y x w z).1 (hr z w x y hreverse)
    dsimp at hdiff
    linarith

/-- The exact logical reduction used for Theorem 3.2. -/
theorem realizableDifference_iff_pair_reversal {A : Type u}
    (D : A → A → A → A → Prop) :
    RealizableDifference D ↔ RealizableUtilityPair D ∧ DiffReversal D := by
  exact ⟨fun h ↦ ⟨h.utilityPair, h.reversal⟩,
    fun h ↦ difference_of_pair_and_reversal h.1 h.2⟩

/-- Once Theorem 3.1 is available, its sufficiency immediately yields Scott's
Theorem 3.2 through the preceding combining lemma. -/
theorem difference_sufficient_of_pair_sufficient {A : Type u}
    (pairSufficient :
      ∀ V : A → A → A → A → Prop,
        PairTotal V ∧ PairPermutation V → RealizableUtilityPair V)
    {D : A → A → A → A → Prop}
    (hD : DiffTotal D ∧ DiffPermutation D ∧ DiffReversal D) :
    RealizableDifference D :=
  difference_of_pair_and_reversal (pairSufficient D ⟨hD.1, hD.2.1⟩) hD.2.2

/-- **Scott 1964, Theorem 3.2 (ordered differences).**
The result also holds when the alternative type is empty. -/
theorem theorem_3_2 {A : Type u} [Finite A]
    (D : A → A → A → A → Prop) :
    RealizableDifference D ↔ DiffTotal D ∧ DiffPermutation D ∧ DiffReversal D := by
  let := Fintype.ofFinite A
  constructor
  · exact RealizableDifference.necessary
  · rintro ⟨htotal, hperm, hreversal⟩
    exact difference_of_pair_and_reversal
      ((theorem_3_1 D).2 ⟨htotal, hperm⟩) hreversal

end Scott1964.MeasurementStructures
