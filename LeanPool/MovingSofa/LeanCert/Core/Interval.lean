/-
Copyright (c) 2024 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Topology.Order.Basic
/-!
# Abstract Interval Interface

This file defines the abstract notion of intervals as subsets of ℝ,
with semantic properties. This provides the mathematical foundation
that `IntervalReal` will implement computationally.

## Main definitions

* Lemmas about `Set.Icc` (closed intervals) relevant to interval arithmetic
* Convexity and integrability properties

## Design notes

We primarily use `Set.Icc a b` from Mathlib as our semantic interval type.
This file collects lemmas and abstractions useful for verified numerics.
-/

/-! ### Interval membership and operations -/

@[expose] public section

namespace LeanCert.Core

/-- A real number is in the interval [a, b] -/
abbrev memIcc (x a b : ℝ) : Prop := a ≤ x ∧ x ≤ b

theorem mem_Icc_iff (x a b : ℝ) : memIcc x a b ↔ x ∈ Set.Icc a b := Iff.rfl

/-! ### Interval arithmetic semantics

These lemmas establish the semantic foundation for interval arithmetic:
if x ∈ [a, b] and y ∈ [c, d], then x ⊕ y ∈ [a ⊕ c, b ⊕ d] (for appropriate ⊕).
-/

/-- Addition preserves interval membership -/
theorem add_mem_Icc {x y a b c d : ℝ} (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc c d) :
    x + y ∈ Set.Icc (a + c) (b + d) := by
  simp only [Set.mem_Icc] at *
  constructor <;> linarith

/-- Negation reverses interval bounds -/
theorem neg_mem_Icc {x a b : ℝ} (hx : x ∈ Set.Icc a b) :
    -x ∈ Set.Icc (-b) (-a) := by
  simp only [Set.mem_Icc] at *
  constructor <;> linarith

/-- Subtraction on intervals -/
theorem sub_mem_Icc {x y a b c d : ℝ} (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc c d) :
    x - y ∈ Set.Icc (a - d) (b - c) := by
  simp only [Set.mem_Icc] at *
  constructor <;> linarith

/-! ### Convexity -/

/-- Closed intervals are convex -/
theorem Icc_convex (a b : ℝ) : Convex ℝ (Set.Icc a b) := convex_Icc a b

/-! ### Compactness -/

/-- Nonempty closed bounded intervals are compact -/
theorem Icc_compact (a b : ℝ) : IsCompact (Set.Icc a b) := isCompact_Icc

/-! ### Continuous functions on intervals -/

/-- A continuous function on a compact interval attains its bounds -/
theorem continuous_Icc_bounds {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : Continuous f) :
    ∃ (lo hi : ℝ), (∀ x ∈ Set.Icc a b, lo ≤ f x ∧ f x ≤ hi) ∧
      (∃ x ∈ Set.Icc a b, f x = lo) ∧ (∃ x ∈ Set.Icc a b, f x = hi) := by
  have hne : (Set.Icc a b).Nonempty := Set.nonempty_Icc.mpr hab
  have hcpt : IsCompact (Set.Icc a b) := isCompact_Icc
  obtain ⟨xmin, hxmin_mem, hxmin⟩ := hcpt.exists_isMinOn hne hf.continuousOn
  obtain ⟨xmax, hxmax_mem, hxmax⟩ := hcpt.exists_isMaxOn hne hf.continuousOn
  exact ⟨f xmin, f xmax,
    fun x hx => ⟨hxmin hx, hxmax hx⟩,
    ⟨xmin, hxmin_mem, rfl⟩,
    ⟨xmax, hxmax_mem, rfl⟩⟩

end LeanCert.Core
