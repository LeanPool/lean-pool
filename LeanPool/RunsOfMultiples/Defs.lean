/-
Copyright (c) 2026 Jason Hoelscher-Obermaier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hoelscher-Obermaier, Claude Opus 5.5
-/
module

-- Adapted for Lean Pool: module visibility, imports, and proof organization.

public import Mathlib.Order.Lattice.Nat
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Runs of multiples: definitions

For a finite set `S` of positive integers and `a ∈ S`, `kVal S a` is the least positive
integer `k` with `k * a ∉ S`. We write `L S a = kVal S a - 1` for the length of the run
`a, 2a, …, L a` inside `S`, and `A S t` for the set of `a ∈ S` whose run has length `≥ t`.
-/

open Finset

@[expose] public section

namespace RunsOfMultiples

/-- `kVal S a` is the least positive integer `k` with `k * a ∉ S`. -/
noncomputable def kVal (S : Finset ℕ) (a : ℕ) : ℕ := sInf {k : ℕ | 0 < k ∧ k * a ∉ S}

/-- The elements of `S` whose first `t` multiples all lie in `S`. -/
def A (S : Finset ℕ) (t : ℕ) : Finset ℕ := S.filter (fun a => ∀ i ∈ Icc 1 t, i * a ∈ S)

/-- Run length `L S a = kVal S a - 1`. -/
noncomputable def L (S : Finset ℕ) (a : ℕ) : ℕ := kVal S a - 1

lemma kVal_set_nonempty (S : Finset ℕ) {a : ℕ} (ha : 0 < a) :
    {k : ℕ | 0 < k ∧ k * a ∉ S}.Nonempty := by
  refine ⟨S.sup id + 1, Nat.succ_pos _, fun h => ?_⟩
  have h1 : (S.sup id + 1) * a ≤ S.sup id := Finset.le_sup (f := id) h
  have h2 : S.sup id + 1 ≤ (S.sup id + 1) * a := Nat.le_mul_of_pos_right _ ha
  omega

lemma kVal_pos (S : Finset ℕ) {a : ℕ} (ha : 0 < a) : 0 < kVal S a :=
  (Nat.sInf_mem (kVal_set_nonempty S ha)).1

lemma kVal_not_mem (S : Finset ℕ) {a : ℕ} (ha : 0 < a) : kVal S a * a ∉ S :=
  (Nat.sInf_mem (kVal_set_nonempty S ha)).2

lemma mul_mem_of_lt_kVal (S : Finset ℕ) {a i : ℕ} (hi : 0 < i) (hik : i < kVal S a) :
    i * a ∈ S := by
  by_contra h
  exact Nat.notMem_of_lt_sInf hik ⟨hi, h⟩

/-- The run characterisation: the first `t` multiples of `a` lie in `S` iff `t < kVal S a`. -/
lemma forall_mul_mem_iff (S : Finset ℕ) {a : ℕ} (ha : 0 < a) (t : ℕ) :
    (∀ i ∈ Icc 1 t, i * a ∈ S) ↔ t < kVal S a := by
  constructor
  · intro h
    by_contra hle
    push Not at hle
    exact kVal_not_mem S ha (h _ (mem_Icc.2 ⟨kVal_pos S ha, hle⟩))
  · intro h i hi
    rw [mem_Icc] at hi
    exact mul_mem_of_lt_kVal S (by omega) (by omega)

lemma mem_A_iff (S : Finset ℕ) (hS : ∀ a ∈ S, 0 < a) {a t : ℕ} :
    a ∈ A S t ↔ a ∈ S ∧ t ≤ L S a := by
  unfold A L
  rw [mem_filter]
  constructor
  · rintro ⟨haS, h⟩
    have := (forall_mul_mem_iff S (hS a haS) t).1 h
    exact ⟨haS, by omega⟩
  · rintro ⟨haS, h⟩
    refine ⟨haS, (forall_mul_mem_iff S (hS a haS) t).2 ?_⟩
    have := kVal_pos S (hS a haS)
    omega

lemma A_subset (S : Finset ℕ) (t : ℕ) : A S t ⊆ S := filter_subset _ _

lemma A_anti (S : Finset ℕ) {s t : ℕ} (hst : s ≤ t) : A S t ⊆ A S s := by
  intro a ha
  simp only [A, mem_filter, mem_Icc] at ha ⊢
  exact ⟨ha.1, fun i hi => ha.2 i ⟨hi.1, hi.2.trans hst⟩⟩

/-- If `a ∈ A S t` and `1 ≤ i ≤ t` then `i * a ∈ S`. -/
lemma mul_mem_of_mem_A {S : Finset ℕ} {t a i : ℕ} (ha : a ∈ A S t) (hi1 : 1 ≤ i) (hit : i ≤ t) :
    i * a ∈ S := by
  simp only [A, mem_filter, mem_Icc] at ha
  exact ha.2 i ⟨hi1, hit⟩

/-- The run length is at most `|S|`. -/
lemma L_le_card (S : Finset ℕ) (hS : ∀ a ∈ S, 0 < a) {a : ℕ} (haS : a ∈ S) :
    L S a ≤ S.card := by
  have ha := hS a haS
  have hsub : (Icc 1 (L S a)).image (fun i => i * a) ⊆ S := by
    intro x hx
    rw [mem_image] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    rw [mem_Icc] at hi
    have := kVal_pos S ha
    exact mul_mem_of_lt_kVal S (by omega) (by unfold L at hi; omega)
  have hinj : Set.InjOn (fun i => i * a) (Icc 1 (L S a) : Set ℕ) := by
    intro i _ j _ h
    exact Nat.eq_of_mul_eq_mul_right ha h
  have := card_le_card hsub
  rw [card_image_of_injOn hinj, Nat.card_Icc] at this
  omega

lemma sum_kVal_eq (S : Finset ℕ) (hS : ∀ a ∈ S, 0 < a) :
    ∑ a ∈ S, kVal S a = S.card + ∑ a ∈ S, L S a := by
  rw [card_eq_sum_ones, ← sum_add_distrib]
  refine sum_congr rfl fun a ha => ?_
  have := kVal_pos S (hS a ha)
  unfold L
  omega

end RunsOfMultiples
