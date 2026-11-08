/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Compatible mass functions

Three mass functions `π₁`, `π₂` and `π₃` on `ℕ` are compatible at level `N` if they are the
marginals of a nonnegative function on the triples `(a, b, c)` of natural numbers with
`a + b + c = N`. For probability distributions, this says that there are random variables `X₁`, `X₂`
and `X₃` with distributions `π₁`, `π₂` and `π₃` such that `X₁ + X₂ + X₃ = N`.

## Main definitions

* `ArithmeticTriangleRemovalInVectorSpaces.sumTriples N`: the triples of natural numbers with sum
  `N`.
* `ArithmeticTriangleRemovalInVectorSpaces.marginal N J g`: the push-forward of `J` along `g`.
* `ArithmeticTriangleRemovalInVectorSpaces.Compatible N π₁ π₂ π₃`: `π₁`, `π₂` and `π₃` are
  compatible at level `N`.

## Main statements

* `ArithmeticTriangleRemovalInVectorSpaces.Compatible.add` and
  `ArithmeticTriangleRemovalInVectorSpaces.Compatible.smul`: compatible triples form a convex cone.
* `ArithmeticTriangleRemovalInVectorSpaces.Compatible.comm₁₂` and
  `ArithmeticTriangleRemovalInVectorSpaces.Compatible.comm₂₃`: compatibility does not depend on the
  order of the mass functions.
* `ArithmeticTriangleRemovalInVectorSpaces.Compatible.shift`: adding `d` to the third variable
  raises the level by `d`.
* `ArithmeticTriangleRemovalInVectorSpaces.compatible_layer`: the triples `(0, b, N - b)` with
  weights `f b`.
-/

public section

open Finset

namespace ArithmeticTriangleRemovalInVectorSpaces

/-- The triples `(a, b, c)` of natural numbers with `a + b + c = N`. -/
def sumTriples (N : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (range (N + 1) ×ˢ range (N + 1) ×ˢ range (N + 1)).filter fun (a, b, c) ↦ a + b + c = N

@[simp]
lemma mem_sumTriples {N a b c : ℕ} : (a, b, c) ∈ sumTriples N ↔ a + b + c = N := by
  simp only [sumTriples, mem_filter, mem_product, mem_range]
  grind

/-- The push-forward of `J`, restricted to the triples with sum `N`, along `g`. -/
@[expose] def marginal (N : ℕ) (J : ℕ × ℕ × ℕ → ℝ) (g : ℕ × ℕ × ℕ → ℕ) (k : ℕ) : ℝ :=
  ∑ x ∈ sumTriples N with g x = k, J x

/-- Three mass functions on `ℕ` are compatible at level `N` if they are the marginals of a
nonnegative function on the triples with sum `N`. -/
@[expose] def Compatible (N : ℕ) (π₁ π₂ π₃ : ℕ → ℝ) : Prop :=
  ∃ J : ℕ × ℕ × ℕ → ℝ, (∀ x, 0 ≤ J x) ∧ marginal N J (fun (a, _, _) ↦ a) = π₁ ∧
    marginal N J (fun (_, b, _) ↦ b) = π₂ ∧ marginal N J (fun (_, _, c) ↦ c) = π₃

variable {N : ℕ} {J J' : ℕ × ℕ × ℕ → ℝ} {g : ℕ × ℕ × ℕ → ℕ} {π₁ π₂ π₃ π₁' π₂' π₃' : ℕ → ℝ}

private lemma marginal_add : marginal N (J + J') g = marginal N J g + marginal N J' g := by
  ext k
  simp [marginal, sum_add_distrib]

lemma marginal_smul (r : ℝ) : marginal N (r • J) g = r • marginal N J g := by
  ext k
  simp [marginal, mul_sum]

/-- Precomposing `J` with an involution of the triples that preserves `sumTriples N` amounts to
precomposing `g` with it. -/
private lemma marginal_comp {e : ℕ × ℕ × ℕ → ℕ × ℕ × ℕ} (he : ∀ x, e (e x) = x)
    (hs : ∀ x, e x ∈ sumTriples N ↔ x ∈ sumTriples N) :
    marginal N (J ∘ e) g = marginal N J (g ∘ e) := by
  ext k
  refine sum_nbij' e e ?_ ?_ (fun x _ ↦ he x) (fun x _ ↦ he x) (fun _ _ ↦ rfl)
  all_goals
    intro x hx
    simpa [hs, he] using hx

lemma compatible_zero : Compatible N 0 0 0 :=
  ⟨0, fun _ ↦ le_rfl, by ext; simp [marginal], by ext; simp [marginal], by ext; simp [marginal]⟩

lemma Compatible.add (h : Compatible N π₁ π₂ π₃) (h' : Compatible N π₁' π₂' π₃') :
    Compatible N (π₁ + π₁') (π₂ + π₂') (π₃ + π₃') := by
  obtain ⟨J, hJ, rfl, rfl, rfl⟩ := h
  obtain ⟨J', hJ', rfl, rfl, rfl⟩ := h'
  exact ⟨J + J', fun x ↦ add_nonneg (hJ x) (hJ' x), marginal_add, marginal_add, marginal_add⟩

lemma Compatible.smul (h : Compatible N π₁ π₂ π₃) {r : ℝ} (hr : 0 ≤ r) :
    Compatible N (r • π₁) (r • π₂) (r • π₃) := by
  obtain ⟨J, hJ, rfl, rfl, rfl⟩ := h
  exact ⟨r • J, fun x ↦ mul_nonneg hr (hJ x), marginal_smul r, marginal_smul r, marginal_smul r⟩

lemma Compatible.comm₁₂ (h : Compatible N π₁ π₂ π₃) : Compatible N π₂ π₁ π₃ := by
  obtain ⟨J, hJ, rfl, rfl, rfl⟩ := h
  have hcomp (g) := marginal_comp (N := N) (J := J) (g := g) (e := fun (a, b, c) ↦ (b, a, c))
    (fun _ ↦ rfl) (by simp [add_comm])
  exact ⟨_, fun x ↦ hJ _, hcomp _, hcomp _, hcomp _⟩

lemma Compatible.comm₂₃ (h : Compatible N π₁ π₂ π₃) : Compatible N π₁ π₃ π₂ := by
  obtain ⟨J, hJ, rfl, rfl, rfl⟩ := h
  have hcomp (g) := marginal_comp (N := N) (J := J) (g := g) (e := fun (a, b, c) ↦ (a, c, b))
    (fun _ ↦ rfl) (by simp [add_right_comm])
  exact ⟨_, fun x ↦ hJ _, hcomp _, hcomp _, hcomp _⟩

lemma Compatible.comm₁₃ (h : Compatible N π₁ π₂ π₃) : Compatible N π₃ π₂ π₁ :=
  h.comm₁₂.comm₂₃.comm₁₂

/-- The function `J` with `d` added to the third variable. -/
private def shiftThird (d : ℕ) (J : ℕ × ℕ × ℕ → ℝ) : ℕ × ℕ × ℕ → ℝ :=
  fun (a, b, c) ↦ if d ≤ c then J (a, b, c - d) else 0

private lemma marginal_shiftThird (d k : ℕ) :
    marginal (N + d) (shiftThird d J) g k =
      ∑ x ∈ sumTriples N with g (x + (0, 0, d)) = k, J x := by
  rw [marginal, ← sum_filter_of_ne (p := fun (_, _, c) ↦ d ≤ c), filter_filter]
  · refine sum_nbij' (· - (0, 0, d)) (· + (0, 0, d)) ?_ ?_ ?_ ?_ ?_
    all_goals
      rintro ⟨a, b, c⟩ hx
      simp only [mem_filter, mem_sumTriples, Prod.mk_sub_mk, Prod.mk_add_mk, add_zero,
        tsub_zero] at hx ⊢
    · obtain ⟨h₁, rfl, h₃⟩ := hx
      rw [Nat.sub_add_cancel h₃]
      grind
    · grind
    · obtain ⟨-, -, h₃⟩ := hx
      rw [Nat.sub_add_cancel h₃]
    · simp
    · obtain ⟨-, -, h₃⟩ := hx
      simp [shiftThird, h₃]
  · rintro ⟨a, b, c⟩ - hne
    by_contra h
    simp [shiftThird, h] at hne

/-- Adding `d` to the third variable raises the level by `d`. -/
lemma Compatible.shift (h : Compatible N π₁ π₂ π₃) (d : ℕ) :
    Compatible (N + d) π₁ π₂ fun c ↦ if d ≤ c then π₃ (c - d) else 0 := by
  obtain ⟨J, hJ, rfl, rfl, rfl⟩ := h
  refine ⟨shiftThird d J, ?_, ?_, ?_, ?_⟩
  · rintro ⟨a, b, c⟩
    unfold shiftThird
    grind
  · ext k
    rw [marginal_shiftThird]
    rfl
  · ext k
    rw [marginal_shiftThird]
    rfl
  · ext k
    rw [marginal_shiftThird, marginal]
    by_cases hk : d ≤ k
    · simp only [hk, ↓reduceIte]
      congr 1
      ext ⟨a, b, c⟩
      simp only [mem_filter]
      grind
    · simp only [hk, ↓reduceIte]
      apply sum_eq_zero
      rintro ⟨a, b, c⟩ hx
      simp only [mem_filter] at hx
      grind

/-- The triples `(0, b, N - b)` with weights `f b`. -/
lemma compatible_layer {f : ℕ → ℝ} (hf : ∀ k, 0 ≤ f k) :
    Compatible N (fun a ↦ if a = 0 then ∑ k ∈ range (N + 1), f k else 0)
      (fun b ↦ if b ≤ N then f b else 0) fun c ↦ if c ≤ N then f (N - c) else 0 := by
  refine ⟨fun (a, b, _) ↦ if a = 0 then f b else 0, ?_, ?_, ?_, ?_⟩
  · rintro ⟨a, b, c⟩
    grind
  · ext a
    simp only [marginal]
    by_cases ha : a = 0
    · simp only [ha, ↓reduceIte]
      subst ha
      refine sum_nbij' (fun (_, b, _) ↦ b) (fun b ↦ (0, b, N - b)) ?_ ?_ ?_ ?_ ?_
      · rintro ⟨a, b, c⟩ hx
        simp only [mem_filter, mem_sumTriples, mem_range] at hx ⊢
        grind
      · intro b hb
        simp only [mem_range] at hb
        simp only [mem_filter, mem_sumTriples]
        grind
      · rintro ⟨a, b, c⟩ hx
        simp only [mem_filter, mem_sumTriples] at hx
        grind
      · intro b _
        rfl
      · rintro ⟨a, b, c⟩ hx
        simp only [mem_filter, mem_sumTriples] at hx
        grind
    · simp only [ha, ↓reduceIte]
      apply sum_eq_zero
      rintro ⟨a', b, c⟩ hx
      simp only [mem_filter] at hx
      grind
  · ext b
    simp only [marginal]
    by_cases hb : b ≤ N
    · simp only [hb, ↓reduceIte]
      rw [sum_eq_single_of_mem (0, b, N - b) (by simp; grind)]
      · simp
      · rintro ⟨a, b', c⟩ hx hne
        simp only [mem_filter, mem_sumTriples] at hx
        grind
    · simp only [hb, ↓reduceIte]
      apply sum_eq_zero
      rintro ⟨a, b', c⟩ hx
      simp only [mem_filter, mem_sumTriples] at hx
      grind
  · ext c
    simp only [marginal]
    by_cases hc : c ≤ N
    · simp only [hc, ↓reduceIte]
      rw [sum_eq_single_of_mem (0, N - c, c) (by simp; grind)]
      · simp
      · rintro ⟨a, b, c'⟩ hx hne
        simp only [mem_filter, mem_sumTriples] at hx
        grind
    · simp only [hc, ↓reduceIte]
      apply sum_eq_zero
      rintro ⟨a, b, c'⟩ hx
      simp only [mem_filter, mem_sumTriples] at hx
      grind

end ArithmeticTriangleRemovalInVectorSpaces
