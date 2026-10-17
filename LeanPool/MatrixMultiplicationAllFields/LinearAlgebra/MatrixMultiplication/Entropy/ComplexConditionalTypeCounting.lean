/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Separation.ComplexTypeCounting

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-! Finite entropy, rate estimates and ordered asymptotic limits. -/

@[expose] public section

namespace MatrixMultiplicationAllFields



namespace MatrixMultiplication.Foundation

open scoped BigOperators

variable {A B I : Type*} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype I] [DecidableEq I]

/-- Words on an arbitrary finite position set with prescribed letter populations. -/
abbrev PopulationWords (I : Type*) [Fintype I] (counts : A → ℕ) :=
  {w : I → A // ∀ a, wordPopulation w a = counts a}

/-- Identify population-constrained words with words on the standard finite position set. -/
noncomputable def populationWordsEquiv (counts : A → ℕ)
    (h : Fintype.card I = ∑ a, counts a) : PopulationWords I counts ≃ ExactWords counts := by
  let e : I ≃ Fin (∑ a, counts a) := Fintype.equivFinOfCardEq h
  exact
    { toFun := fun w =>
        ⟨w.val ∘ e.symm, fun a => (wordPopulation_reindex w.val e.symm a).trans (w.property a)⟩
      invFun := fun w =>
        ⟨w.val ∘ e, fun a => (wordPopulation_reindex w.val e a).trans (w.property a)⟩
      left_inv := by
        intro w
        apply Subtype.ext
        funext i
        simp
      right_inv := by
        intro w
        apply Subtype.ext
        funext i
        simp }

theorem populationWords_card (counts : A → ℕ)
    (h : Fintype.card I = ∑ a, counts a) :
    Fintype.card (PopulationWords I counts) = Nat.multinomial Finset.univ counts := by
  rw [Fintype.card_congr (populationWordsEquiv counts h), exactWords_card]

/-- Refinements with prescribed joint populations relative to an existing coarse word. -/
abbrev ConditionalWords (w : I → A) (counts : A → B → ℕ) :=
  {r : I → B // ∀ a b, Fintype.card {i // w i = a ∧ r i = b} = counts a b}

/-- Restrict a word to the fibers of a coarse labelling, reversibly. -/
def fiberWordEquiv (w : I → A) : (I → B) ≃ (∀ a, {i // w i = a} → B) where
  toFun r _ i := r i.val
  invFun r i := r (w i) ⟨i, rfl⟩
  left_inv _ := rfl
  right_inv := by
    intro r
    funext a i
    rcases i with ⟨i, hi⟩
    cases hi
    rfl

omit [Fintype A] [Fintype B] [DecidableEq I] in
theorem wordPopulation_fiber (w : I → A) (r : I → B) (a : A) (b : B) :
    wordPopulation (fun i : {i // w i = a} => r i.val) b =
      Fintype.card {i // w i = a ∧ r i = b} :=
  Fintype.card_congr
    (Equiv.subtypeSubtypeEquivSubtypeInter (fun i => w i = a) (fun i => r i = b))

/-- Identify conditional refinements with independent population-constrained words in each
fiber. -/
def conditionalWordsEquiv (w : I → A) (counts : A → B → ℕ) :
    ConditionalWords w counts ≃ ∀ a, PopulationWords {i // w i = a} (counts a) := by
  let e : ConditionalWords w counts ≃
      {r : ∀ a, {i // w i = a} → B // ∀ a b, wordPopulation (r a) b = counts a b} :=
    Equiv.subtypeEquiv (fiberWordEquiv w) fun r => by
      change (∀ a b, Fintype.card {i // w i = a ∧ r i = b} = counts a b) ↔
        ∀ a b, wordPopulation (fun i : {i // w i = a} => r i.val) b = counts a b
      simp only [wordPopulation_fiber]
  exact e.trans (Equiv.subtypePiEquivPi
    (β := fun a : A => {i // w i = a} → B)
    (p := fun a r => ∀ b, wordPopulation r b = counts a b))

theorem conditionalWords_card (w : I → A) (counts : A → B → ℕ)
    (h : ∀ a, wordPopulation w a = ∑ b, counts a b) :
    Fintype.card (ConditionalWords w counts) =
      ∏ a, Nat.multinomial Finset.univ (counts a) := by
  rw [Fintype.card_congr (conditionalWordsEquiv w counts), Fintype.card_pi]
  exact Finset.prod_congr rfl fun a _ => populationWords_card (counts a) (h a)

theorem conditionalWords_card_pos (w : I → A) (counts : A → B → ℕ)
    (h : ∀ a, wordPopulation w a = ∑ b, counts a b) :
    0 < Fintype.card (ConditionalWords w counts) := by
  rw [conditionalWords_card w counts h]
  exact Finset.prod_pos fun a _ => Nat.multinomial_pos Finset.univ (counts a)

omit [Fintype A] [DecidableEq I] in
theorem conditionalWords_nonempty [Finite A] (w : I → A) (counts : A → B → ℕ)
    (h : ∀ a, wordPopulation w a = ∑ b, counts a b) :
    Nonempty (ConditionalWords w counts) := by
  classical
  let : Fintype A := Fintype.ofFinite A
  exact Fintype.card_pos_iff.mp (conditionalWords_card_pos w counts h)

omit [Fintype A] [DecidableEq I] in
theorem conditionalWords_nonempty_iff [Finite A] (w : I → A) (counts : A → B → ℕ) :
    Nonempty (ConditionalWords w counts) ↔
      ∀ a, wordPopulation w a = ∑ b, counts a b := by
  classical
  let : Fintype A := Fintype.ofFinite A
  constructor
  · rintro ⟨r⟩ a
    calc
      wordPopulation w a =
          ∑ b, wordPopulation (fun i : {i // w i = a} => r.val i.val) b :=
        (wordPopulation_sum _).symm
      _ = ∑ b, counts a b := by
        apply Finset.sum_congr rfl
        intro b _
        rw [wordPopulation_fiber, r.property]
  · exact conditionalWords_nonempty w counts

omit [DecidableEq A] [DecidableEq B] in
theorem multinomial_prod_counts (counts : A × B → ℕ) :
    Nat.multinomial Finset.univ counts =
      Nat.multinomial Finset.univ (fun a => ∑ b, counts (a, b)) *
        ∏ a, Nat.multinomial Finset.univ (fun b => counts (a, b)) := by
  apply Nat.mul_left_cancel (Nat.prod_factorial_pos Finset.univ counts)
  rw [Nat.multinomial_spec]
  symm
  calc
    (∏ ab, (counts ab).factorial) *
        (Nat.multinomial Finset.univ (fun a => ∑ b, counts (a, b)) *
          ∏ a, Nat.multinomial Finset.univ (fun b => counts (a, b))) =
        ((∏ a, ∏ b, (counts (a, b)).factorial) *
          ∏ a, Nat.multinomial Finset.univ (fun b => counts (a, b))) *
          Nat.multinomial Finset.univ (fun a => ∑ b, counts (a, b)) := by
      rw [Fintype.prod_prod_type]
      ac_rfl
    _ = (∏ a, ((∏ b, (counts (a, b)).factorial) *
          Nat.multinomial Finset.univ (fun b => counts (a, b)))) *
          Nat.multinomial Finset.univ (fun a => ∑ b, counts (a, b)) := by
      rw [Finset.prod_mul_distrib]
    _ = (∏ a, (∑ b, counts (a, b)).factorial) *
          Nat.multinomial Finset.univ (fun a => ∑ b, counts (a, b)) := by
      congr 1
      apply Finset.prod_congr rfl
      intro a _
      exact Nat.multinomial_spec Finset.univ (fun b => counts (a, b))
    _ = (∑ a, ∑ b, counts (a, b)).factorial :=
      Nat.multinomial_spec Finset.univ (fun a => ∑ b, counts (a, b))
    _ = (∑ ab, counts ab).factorial := by rw [Fintype.sum_prod_type]

theorem exactWords_card_prod_counts (counts : A × B → ℕ) :
    Fintype.card (ExactWords counts) =
      Fintype.card (ExactWords (fun a => ∑ b, counts (a, b))) *
        ∏ a, Fintype.card (ExactWords (fun b => counts (a, b))) := by
  simpa only [exactWords_card] using multinomial_prod_counts counts

theorem exactWords_card_eq_coarse_mul_conditional (counts : A × B → ℕ)
    (w : ExactWords (fun a => ∑ b, counts (a, b))) :
    Fintype.card (ExactWords counts) =
      Fintype.card (ExactWords (fun a => ∑ b, counts (a, b))) *
        Fintype.card (ConditionalWords w.val (fun a b => counts (a, b))) := by
  rw [conditionalWords_card w.val (fun a b => counts (a, b)) w.property]
  simpa only [exactWords_card] using multinomial_prod_counts counts

end MatrixMultiplication.Foundation

end MatrixMultiplicationAllFields
