/-
Copyright (c) 2026 David Turturean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
module

-- Adapted for Lean Pool’s module system and pinned Mathlib.

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Tauto
public import LeanPool.AaronsonAmbainis.Row.Chi

/-!
# Degree calculus for `HasDegreeLE`

Rules for the predicate `HasDegreeLE` of `Defs.lean`: characters, constants, sums, constant
multiples, monotonicity in the bound, products (the degrees add), powers, finite products, a real
polynomial of a function of degree at most `1`, and the indicator of a coordinate. They serve
step (b) of the proof of the block inequality (Lemma 6.4 of the paper): the function `G`
constructed there has degree at most `d m` (`Row.hasDegreeLE_gadget` in `Row/Gadget.lean`).
-/

@[expose] public section

namespace AaronsonAmbainis
namespace Row

open Finset

variable {β : Type*} [Fintype β]

lemma hasDegreeLE_congr {f g : Cube β → ℝ} {k : ℕ} (h : HasDegreeLE f k)
    (hfg : ∀ w, g w = f w) : HasDegreeLE g k := by
  obtain ⟨c, hc, hf⟩ := h
  exact ⟨c, hc, fun w => (hfg w).trans (hf w)⟩

lemma hasDegreeLE_chi (S : Finset β) {k : ℕ} (h : S.card ≤ k) : HasDegreeLE (chi S) k := by
  classical
  refine ⟨fun T => if T = S then 1 else 0, fun T hT => ?_, fun w => ?_⟩
  · have hne : T ≠ S := by
      rintro rfl
      omega
    simp [hne]
  · simp

lemma hasDegreeLE_zero (k : ℕ) : HasDegreeLE (fun _ : Cube β => (0 : ℝ)) k :=
  ⟨fun _ => 0, fun _ _ => rfl, fun w => by simp⟩

lemma hasDegreeLE_add {f g : Cube β → ℝ} {k : ℕ} (hf : HasDegreeLE f k) (hg : HasDegreeLE g k) :
    HasDegreeLE (fun w => f w + g w) k := by
  obtain ⟨c, hc, hf⟩ := hf
  obtain ⟨c', hc', hg⟩ := hg
  refine ⟨fun T => c T + c' T, fun T hT => by simp [hc T hT, hc' T hT], fun w => ?_⟩
  change f w + g w = ∑ T, (c T + c' T) * chi T w
  rw [hf w, hg w, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun T _ => by ring)

lemma hasDegreeLE_const_mul (a : ℝ) {f : Cube β → ℝ} {k : ℕ} (hf : HasDegreeLE f k) :
    HasDegreeLE (fun w => a * f w) k := by
  obtain ⟨c, hc, hf⟩ := hf
  refine ⟨fun T => a * c T, fun T hT => by simp [hc T hT], fun w => ?_⟩
  change a * f w = ∑ T, a * c T * chi T w
  rw [hf w, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun T _ => by ring)

lemma hasDegreeLE_const (a : ℝ) (k : ℕ) : HasDegreeLE (fun _ : Cube β => a) k := by
  have h := hasDegreeLE_const_mul a (hasDegreeLE_chi (∅ : Finset β) (Nat.zero_le k))
  exact hasDegreeLE_congr h (fun w => by simp [chi])

lemma hasDegreeLE_sum {α : Type*} (s : Finset α) (F : α → Cube β → ℝ) {k : ℕ}
    (h : ∀ j ∈ s, HasDegreeLE (F j) k) : HasDegreeLE (fun w => ∑ j ∈ s, F j w) k := by
  classical
  induction s using Finset.induction_on with
  | empty => exact hasDegreeLE_congr (hasDegreeLE_zero k) (fun w => by simp)
  | insert j s hj ih =>
    have h1 := hasDegreeLE_add (h j (Finset.mem_insert_self j s))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))
    exact hasDegreeLE_congr h1 (fun w => by rw [Finset.sum_insert hj])

lemma hasDegreeLE_mono {f : Cube β → ℝ} {k l : ℕ} (hkl : k ≤ l) (hf : HasDegreeLE f k) :
    HasDegreeLE f l := by
  obtain ⟨c, hc, hf⟩ := hf
  exact ⟨c, fun T hT => hc T (lt_of_le_of_lt hkl hT), hf⟩

/-- Products add degrees. -/
lemma hasDegreeLE_mul {f g : Cube β → ℝ} {k l : ℕ} (hf : HasDegreeLE f k)
    (hg : HasDegreeLE g l) : HasDegreeLE (fun w => f w * g w) (k + l) := by
  classical
  obtain ⟨c, hc, hf⟩ := hf
  obtain ⟨c', hc', hg⟩ := hg
  have key : HasDegreeLE (fun w => ∑ S ∈ (univ : Finset (Finset β)),
      ∑ T ∈ (univ : Finset (Finset β)), c S * c' T * chi (symmDiff S T) w) (k + l) := by
    apply hasDegreeLE_sum
    intro S _
    apply hasDegreeLE_sum
    intro T _
    by_cases hST : S.card ≤ k ∧ T.card ≤ l
    · refine hasDegreeLE_const_mul _ (hasDegreeLE_chi _ ?_)
      have hsub : symmDiff S T ⊆ S ∪ T := by
        intro i hi
        rw [Finset.mem_symmDiff] at hi
        rw [Finset.mem_union]
        tauto
      calc (symmDiff S T).card ≤ (S ∪ T).card := Finset.card_le_card hsub
        _ ≤ S.card + T.card := Finset.card_union_le S T
        _ ≤ k + l := Nat.add_le_add hST.1 hST.2
    · have h0 : c S * c' T = 0 := by
        rcases not_and_or.mp hST with h | h
        · rw [hc S (not_le.mp h), zero_mul]
        · rw [hc' T (not_le.mp h), mul_zero]
      exact hasDegreeLE_congr (hasDegreeLE_zero _) (fun w => by rw [h0, zero_mul])
  refine hasDegreeLE_congr key (fun w => ?_)
  rw [hf w, hg w, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun S _ => Finset.sum_congr rfl (fun T _ => ?_))
  rw [← chi_mul_chi]
  ring

lemma hasDegreeLE_pow {f : Cube β → ℝ} {k : ℕ} (hf : HasDegreeLE f k) (n : ℕ) :
    HasDegreeLE (fun w => f w ^ n) (n * k) := by
  induction n with
  | zero => exact hasDegreeLE_congr (hasDegreeLE_const 1 _) (fun w => by simp)
  | succ n ih =>
    have h := hasDegreeLE_mul ih hf
    have h' : n * k + k = (n + 1) * k := by ring
    rw [← h']
    exact hasDegreeLE_congr h (fun w => by rw [pow_succ])

lemma hasDegreeLE_prod {α : Type*} (s : Finset α) (F : α → Cube β → ℝ) {k : ℕ}
    (h : ∀ j ∈ s, HasDegreeLE (F j) k) :
    HasDegreeLE (fun w => ∏ j ∈ s, F j w) (s.card * k) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact hasDegreeLE_congr (hasDegreeLE_const 1 _) (fun w => by simp)
  | insert j s hj ih =>
    have h1 := hasDegreeLE_mul (h j (Finset.mem_insert_self j s))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))
    have h' : k + s.card * k = (insert j s).card * k := by
      rw [Finset.card_insert_of_notMem hj]
      ring
    rw [← h']
    exact hasDegreeLE_congr h1 (fun w => by rw [Finset.prod_insert hj])

/-- A real polynomial of a function of degree at most `1` has degree at most its `natDegree`. -/
lemma hasDegreeLE_polyEval (Q : Polynomial ℝ) {g : Cube β → ℝ} (hg : HasDegreeLE g 1) :
    HasDegreeLE (fun w => Q.eval (g w)) Q.natDegree := by
  have key : HasDegreeLE
      (fun w => ∑ n ∈ Finset.range (Q.natDegree + 1), Q.coeff n * g w ^ n) Q.natDegree := by
    apply hasDegreeLE_sum
    intro n hn
    refine hasDegreeLE_const_mul _ (hasDegreeLE_mono ?_ (hasDegreeLE_pow hg n))
    have := Finset.mem_range.mp hn
    omega
  exact hasDegreeLE_congr key (fun w => Polynomial.eval_eq_sum_range (g w))

/-- The indicator of a coordinate has degree at most `1`. -/
lemma hasDegreeLE_indicator (b : β) :
    HasDegreeLE (fun w : Cube β => if w b then (1 : ℝ) else 0) 1 := by
  have h1 : HasDegreeLE (fun w : Cube β => 1 / 2 + (-1 / 2) * chi {b} w) 1 :=
    hasDegreeLE_add (hasDegreeLE_const _ _)
      (hasDegreeLE_const_mul _ (hasDegreeLE_chi {b} (by simp)))
  refine hasDegreeLE_congr h1 (fun w => ?_)
  cases h : w b <;> simp [chi, h] <;> norm_num

end Row
end AaronsonAmbainis
