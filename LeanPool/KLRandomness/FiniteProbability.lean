/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.NormNum

/-!
# Uniform probabilities on finite sample spaces

The candidate-list construction uses only finite uniform experiments.  These
definitions expose their actual normalized counting probabilities and averages;
independence of repeated samples follows from finite product sums.
-/

@[expose] public section

namespace Klr.FiniteProbability

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω]

/-- The uniform average of a real-valued function on a finite type. -/
noncomputable def average (f : Ω → ℝ) : ℝ := (∑ x, f x) / Fintype.card Ω

/-- The actual uniform counting probability of a finite event. -/
noncomputable def probability (A : Set Ω) : ℝ := by
  classical
  exact average (fun x => if x ∈ A then 1 else 0)

theorem probability_eq_card (A : Set Ω) :
    probability A = (Nat.card A : ℝ) / Fintype.card Ω := by
  classical
  simp [probability, average, Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem average_congr {f g : Ω → ℝ} (h : ∀ x, f x = g x) : average f = average g := by
  simp only [average, funext h]

theorem average_nonneg {f : Ω → ℝ} (hf : ∀ x, 0 ≤ f x) : 0 ≤ average f := by
  exact div_nonneg (Finset.sum_nonneg fun x _ => hf x) (Nat.cast_nonneg _)

theorem average_mono {f g : Ω → ℝ} (h : ∀ x, f x ≤ g x) : average f ≤ average g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun x _ => h x) (Nat.cast_nonneg _)

theorem average_add (f g : Ω → ℝ) :
    average (fun x => f x + g x) = average f + average g := by
  simp [average, Finset.sum_add_distrib, add_div]

theorem average_sub (f g : Ω → ℝ) :
    average (fun x => f x - g x) = average f - average g := by
  simp [average, Finset.sum_sub_distrib, sub_div]

theorem average_const_mul (c : ℝ) (f : Ω → ℝ) :
    average (fun x => c * f x) = c * average f := by
  simp [average, ← Finset.mul_sum, mul_div_assoc]

theorem average_mul_const (f : Ω → ℝ) (c : ℝ) :
    average (fun x => f x * c) = average f * c := by
  simp [average, ← Finset.sum_mul, div_mul_eq_mul_div]

theorem average_sum {ι : Type*} [Fintype ι] (f : ι → Ω → ℝ) :
    average (fun x => ∑ i, f i x) = ∑ i, average (f i) := by
  unfold average
  rw [Finset.sum_comm, Finset.sum_div]

theorem probability_nonneg (A : Set Ω) : 0 ≤ probability A := by
  classical
  exact average_nonneg fun x => by split_ifs <;> norm_num

theorem probability_mono {A B : Set Ω} (h : A ⊆ B) : probability A ≤ probability B := by
  classical
  apply average_mono
  intro x
  by_cases hx : x ∈ A
  · have hy := h hx
    simp [hx, hy]
  · simp only [ite_eq_right hx]
    split_ifs <;> norm_num

@[simp] theorem probability_empty : probability (∅ : Set Ω) = 0 := by
  simp [probability, average]

theorem probability_iUnion_le {ι : Type*} [Fintype ι] (A : ι → Set Ω) :
    probability (⋃ i, A i) ≤ ∑ i, probability (A i) := by
  classical
  change average (fun x => if x ∈ ⋃ i, A i then (1 : ℝ) else 0) ≤
    ∑ i, average (fun x => if x ∈ A i then (1 : ℝ) else 0)
  rw [← average_sum]
  apply average_mono
  intro x
  by_cases hx : x ∈ ⋃ i, A i
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    have hs : (1 : ℝ) ≤ ∑ j, if x ∈ A j then (1 : ℝ) else 0 := by
      simpa only [ite_eq_left hi] using
        (Finset.single_le_sum (f := fun j => if x ∈ A j then (1 : ℝ) else 0)
          (fun j _ => by split_ifs <;> norm_num) (Finset.mem_univ i))
    simpa only [ite_eq_left hx] using hs
  · simp only [ite_eq_right hx]
    exact Finset.sum_nonneg fun i _ => by split_ifs <;> norm_num

section Nonempty

variable [Nonempty Ω]

theorem card_pos : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos

@[simp] theorem average_const (c : ℝ) : average (fun _ : Ω => c) = c := by
  have hc : (Fintype.card Ω : ℝ) ≠ 0 := ne_of_gt (card_pos (Ω := Ω))
  simp [average, hc]

@[simp] theorem probability_univ : probability (Set.univ : Set Ω) = 1 := by
  simp [probability]

theorem probability_le_one (A : Set Ω) : probability A ≤ 1 := by
  simpa using probability_mono (Set.subset_univ A)

theorem probability_compl (A : Set Ω) : probability Aᶜ = 1 - probability A := by
  classical
  calc
    probability Aᶜ = average (fun x => 1 - (if x ∈ A then (1 : ℝ) else 0)) := by
      apply average_congr
      intro x
      by_cases hx : x ∈ A <;> simp [hx]
    _ = 1 - probability A := by rw [average_sub, average_const]; rfl

omit [Nonempty Ω] in
/-- The finite Markov bound for a nonnegative random variable. -/
theorem probability_le_average_div (f : Ω → ℝ) (hf : ∀ x, 0 ≤ f x)
    (a : ℝ) (ha : 0 < a) : probability {x | a ≤ f x} ≤ average f / a := by
  classical
  apply (le_div_iff₀ ha).mpr
  change average (fun x => if a ≤ f x then (1 : ℝ) else 0) * a ≤ average f
  rw [← average_mul_const]
  apply average_mono
  intro x
  by_cases hx : a ≤ f x
  · simpa only [Set.mem_ofPred_eq, ite_eq_left hx, one_mul] using hx
  · simpa only [Set.mem_ofPred_eq, ite_eq_right hx, zero_mul] using hf x

/-- A finite experiment with failure probability less than one has a successful outcome. -/
theorem exists_not_mem_of_probability_lt_one (A : Set Ω) (h : probability A < 1) :
    ∃ x, x ∉ A := by
  by_contra hn
  have he : A = Set.univ := Set.eq_univ_of_forall (by simpa using hn)
  simp [he] at h

end Nonempty

/-- Product averages factor, expressing independence of the actual finite uniform samples. -/
theorem average_prod_samples (f : Ω → ℝ) (J : ℕ) :
    average (fun z : Fin J → Ω => ∏ i, f (z i)) = (average f) ^ J := by
  unfold average
  rw [← Fintype.sum_pow]
  simp [div_pow]

/-- Taking the uniform average on a product is iterated uniform averaging. -/
theorem average_prod {Γ : Type*} [Fintype Γ] (f : Ω × Γ → ℝ) :
    average f = average (fun x : Ω => average (fun y : Γ => f (x, y))) := by
  unfold average
  rw [Fintype.sum_prod_type]
  simp only [Fintype.card_prod, Nat.cast_mul, ← Finset.sum_div, div_div, mul_comm]

/-- The probability of an event on a product is the average of its fiber probabilities. -/
theorem probability_prod_fiber {Γ : Type*} [Fintype Γ] (A : Set (Ω × Γ)) :
    probability A = average (fun x : Ω => probability {y : Γ | (x, y) ∈ A}) := by
  classical
  exact average_prod _

end Klr.FiniteProbability
