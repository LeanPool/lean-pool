/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson
-/

module

public import Mathlib.Order.Atoms
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import LeanPool.ScottMeasurement.Probability.Basic

/-!
# Atom vectors for finite Boolean algebras

Scott identifies an event with its `0`/`1` characteristic vector on the atoms.
The cancellation identity in Theorem 4.1 is equality of sums of these vectors.
-/

@[expose] public section

namespace Scott1964.MeasurementStructures

open scoped BigOperators

noncomputable section

open Classical in
/-- The real characteristic vector of an event on Boolean atoms. -/
def atomVector {B : Type u} [BooleanAlgebra B] (x : B) :
    {a : B // IsAtom a} → ℝ :=
  fun a ↦ if (a : B) ≤ x then 1 else 0

open Classical in
@[simp]
theorem atomVector_apply {B : Type u} [BooleanAlgebra B] (x : B)
    (a : {a : B // IsAtom a}) :
    atomVector x a = if (a : B) ≤ x then 1 else 0 :=
  rfl

theorem atomVector_bot {B : Type u} [BooleanAlgebra B] :
    atomVector (⊥ : B) = 0 := by
  classical
  funext a
  simp [atomVector, a.property.1]

theorem atomVector_top {B : Type u} [BooleanAlgebra B] :
    atomVector (⊤ : B) = 1 := by
  classical
  funext a
  simp [atomVector]

theorem atomVector_sup_of_disjoint {B : Type u} [BooleanAlgebra B]
    {x y : B} (hxy : Disjoint x y) :
    atomVector (x ⊔ y) = atomVector x + atomVector y := by
  classical
  funext a
  have hatom := a.property
  by_cases hx : (a : B) ≤ x
  · have hny : ¬(a : B) ≤ y := by
      classical
      intro hy
      have : (a : B) ≤ x ⊓ y := le_inf hx hy
      rw [hxy.eq_bot] at this
      exact hatom.1 (bot_unique this)
    have hsup : (a : B) ≤ x ⊔ y := hx.trans le_sup_left
    simp [atomVector, hx, hny, hsup]
  · by_cases hy : (a : B) ≤ y
    · have hsup : (a : B) ≤ x ⊔ y := hy.trans le_sup_right
      simp [atomVector, hx, hy, hsup]
    · have hsup : ¬(a : B) ≤ x ⊔ y := by
        classical
        intro ha
        have hix : (a : B) ⊓ x = ⊥ := by
          classical
          rcases hatom.le_iff.mp inf_le_left with hbot | heq
          · exact hbot
          · exact False.elim (hx (by rw [← heq]; exact inf_le_right))
        have hiy : (a : B) ⊓ y = ⊥ := by
          classical
          rcases hatom.le_iff.mp inf_le_left with hbot | heq
          · exact hbot
          · exact False.elim (hy (by rw [← heq]; exact inf_le_right))
        have haeq : (a : B) ⊓ (x ⊔ y) = a := inf_eq_left.mpr ha
        rw [inf_sup_left, hix, hiy, bot_sup_eq] at haeq
        exact hatom.1 haeq.symm
      simp [atomVector, hx, hy, hsup]

theorem atomVector_injective {B : Type u} [BooleanAlgebra B] [Finite B] :
    Function.Injective (atomVector : B → ({a : B // IsAtom a} → ℝ)) := by
  classical
  let := Fintype.ofFinite B
  let _ : IsAtomic B := inferInstance
  intro x y hxy
  apply BooleanAlgebra.eq_iff_atom_le_iff.mpr
  intro a ha
  have h := congrFun hxy ⟨a, ha⟩
  simp only [atomVector_apply] at h
  constructor <;> intro hle
  · by_contra hn
    simp [hle, hn] at h
  · by_contra hn
    simp [hle, hn] at h

/-- Distinct Boolean atoms are disjoint. -/
theorem disjoint_atoms_of_ne {B : Type u} [BooleanAlgebra B]
    (a b : {a : B // IsAtom a}) (hab : a ≠ b) :
    Disjoint (a : B) b := by
  classical
  rw [disjoint_iff_inf_le]
  rcases a.property.le_iff.mp inf_le_left with hbot | heq
  · exact le_of_eq hbot
  · have hab_le : (a : B) ≤ b := by
      classical
      rw [← heq]
      exact inf_le_right
    rcases b.property.le_iff.mp hab_le with ha0 | heqab
    · exact False.elim (a.property.1 ha0)
    · exact False.elim (hab (Subtype.ext heqab))

theorem disjoint_atom_finset_sup {B : Type u} [BooleanAlgebra B]
    (a : {a : B // IsAtom a}) (s : Finset {a : B // IsAtom a})
    (ha : a ∉ s) :
    Disjoint (a : B) (s.sup fun b ↦ (b : B)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert b s hb ih =>
      rw [Finset.sup_insert]
      exact (disjoint_sup_right).2
        ⟨disjoint_atoms_of_ne a b (by
            intro hab
            subst b
            exact ha (Finset.mem_insert_self _ _)),
          ih (fun has ↦ ha (Finset.mem_insert_of_mem has))⟩

/-- A signed charge evaluates a supremum of distinct atoms as the sum of
their charges. -/
theorem IsSignedCharge.finset_sup_atoms
    {B : Type u} [BooleanAlgebra B] {μ : B → ℝ}
    (hμ : IsSignedCharge μ) (s : Finset {a : B // IsAtom a}) :
    μ (s.sup fun a ↦ (a : B)) = ∑ a ∈ s, μ a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hμ.bot]
  | @insert a s ha ih =>
      rw [Finset.sup_insert, hμ.additive _ _ (disjoint_atom_finset_sup a s ha),
        Finset.sum_insert ha, ih]

/-- Finite additivity evaluates a supremum of distinct atoms as the sum of
their masses. -/
theorem IsProbability.finset_sup_atoms
    {B : Type u} [BooleanAlgebra B] {μ : B → ℝ}
    (hμ : IsProbability μ) (s : Finset {a : B // IsAtom a}) :
    μ (s.sup fun a ↦ (a : B)) = ∑ a ∈ s, μ a :=
  hμ.isSignedCharge.finset_sup_atoms s

open Classical in
/-- The atoms below an event. -/
def atomsBelow {B : Type u} [BooleanAlgebra B] [Fintype B] (x : B) :
    Finset {a : B // IsAtom a} :=
  Finset.univ.filter fun a ↦ (a : B) ≤ x

theorem sup_atomsBelow {B : Type u} [BooleanAlgebra B] [Fintype B] (x : B) :
    (atomsBelow x).sup (fun a ↦ (a : B)) = x := by
  classical
  let _ : IsAtomic B := inferInstance
  apply BooleanAlgebra.eq_iff_atom_le_iff.mpr
  intro a ha
  constructor
  · intro h
    exact h.trans (Finset.sup_le fun b hb ↦
      (Finset.mem_filter.mp hb).2)
  · intro h
    exact Finset.le_sup (f := fun b : {a : B // IsAtom a} ↦ (b : B))
      (show ⟨a, ha⟩ ∈ atomsBelow x by simp [atomsBelow, h])

/-- Every finitely additive signed charge is the sum of its atom charges. -/
theorem IsSignedCharge.eq_sum_atoms
    {B : Type u} [BooleanAlgebra B] [Fintype B] {μ : B → ℝ}
    (hμ : IsSignedCharge μ) (x : B) :
    μ x = ∑ a ∈ atomsBelow x, μ a := by
  classical
  calc
    μ x = μ ((atomsBelow x).sup fun a ↦ (a : B)) := by
      classical
      rw [sup_atomsBelow]
    _ = ∑ a ∈ atomsBelow x, μ a := hμ.finset_sup_atoms (atomsBelow x)

/-- Every finitely additive probability is the sum of its atom masses. -/
theorem IsProbability.eq_sum_atoms
    {B : Type u} [BooleanAlgebra B] [Fintype B] {μ : B → ℝ}
    (hμ : IsProbability μ) (x : B) :
    μ x = ∑ a ∈ atomsBelow x, μ a :=
  hμ.isSignedCharge.eq_sum_atoms x

open Classical in
/-- Pointwise equality of sums of event vectors is exactly Scott's
atom-count identity. -/
theorem sum_atomVector_eq_iff {B : Type u} [BooleanAlgebra B]
    (n : ℕ) (x y : Fin n → B) :
    (∑ i, atomVector (x i)) = ∑ i, atomVector (y i) ↔
      ∀ a : B, IsAtom a →
        (∑ i, if a ≤ x i then 1 else 0) =
          (∑ i, if a ≤ y i then 1 else 0 : ℕ) := by
  classical
  have hcast (a : B) (z : Fin n → B) :
      ((∑ i, if a ≤ z i then 1 else 0 : ℕ) : ℝ) =
        ∑ i, (if a ≤ z i then 1 else 0 : ℝ) := by
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs <;> norm_num
  constructor
  · intro h a ha
    have haeq := congrFun h ⟨a, ha⟩
    simp only [Finset.sum_apply, atomVector_apply] at haeq
    have hcounts :
        ((∑ i, if a ≤ x i then 1 else 0 : ℕ) : ℝ) =
          ((∑ i, if a ≤ y i then 1 else 0 : ℕ) : ℝ) := by
      rw [hcast, hcast]
      exact haeq
    exact_mod_cast hcounts
  · intro h
    funext a
    simp only [Finset.sum_apply, atomVector_apply]
    have hcounts := congrArg ((↑) : ℕ → ℝ) (h a a.property)
    simpa only [hcast] using hcounts

/-- Scott 1964, literal condition `(4_B)`: cancellation is stated using
equality of sums of the characteristic vectors themselves. -/
def ProbVectorCancellation {B : Type u} [BooleanAlgebra B]
    (R : B → B → Prop) : Prop :=
  ∀ (n : ℕ) (x y : Fin (n + 1) → B),
    (∑ i, atomVector (x i)) = ∑ i, atomVector (y i) →
      (∀ i, i ≠ 0 → R (x i) (y i)) → R (y 0) (x 0)

/-- The literal vector-sum and atom-count formulations of `(4_B)` agree. -/
theorem probVectorCancellation_iff_probCancellation
    {B : Type u} [BooleanAlgebra B]
    {R : B → B → Prop} :
    ProbVectorCancellation R ↔ ProbCancellation R := by
  classical
  constructor
  · intro h n x y hcount hweak
    exact h n x y ((sum_atomVector_eq_iff (n + 1) x y).2 hcount) hweak
  · intro h n x y hsum hweak
    exact h n x y ((sum_atomVector_eq_iff (n + 1) x y).1 hsum) hweak

end

end Scott1964.MeasurementStructures
