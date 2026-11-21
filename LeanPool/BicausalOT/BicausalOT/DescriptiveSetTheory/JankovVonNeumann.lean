/-
Copyright (c) 2026 KT. Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KT. Wu
-/
/-
  ε-optimal Selection — proved by pointwise choice

  The selection is made pointwise by choice. The index type `α` carries no
  measurable or topological structure here, so the selection is not claimed to be
  measurable. The analytically measurable selector on Polish spaces is
  `exists_eps_optimal_selector`.
-/
module

public import LeanPool.BicausalOT.BicausalOT.DescriptiveSetTheory.AnalyticSet
public import Mathlib.Algebra.Order.Module.Field
public import Mathlib.Data.EReal.Inv
public import Mathlib.Tactic.Measurability
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.MeasureTheory.Measure.Prod


/-!
# JankovVonNeumann

Pointwise ε-optimal selection by choice, with no measurability claim on the selection.
-/

@[expose] public section

open MeasureTheory Set ENNReal

noncomputable section

/-- Pointwise ε-optimal element in a nonempty set. -/
theorem eps_optimal_element
    {α : Type*} (S : Set α) (h_ne : S.Nonempty)
    (f : α → ENNReal) (ε : ENNReal) (hε : 0 < ε) :
    ∃ a ∈ S, f a ≤ (⨅ (x : α) (_ : x ∈ S), f x) + ε := by
  by_contra h
  simp only [not_exists, not_and, not_le] at h
  obtain ⟨a, ha⟩ := h_ne
  have hlt := h a ha
  have : (⨅ (x : α) (_ : x ∈ S), f x) + ε ≤ ⨅ (x : α) (_ : x ∈ S), f x :=
    le_iInf fun x => le_iInf fun hx => le_of_lt (h x hx)
  by_cases htop : (⨅ (x : α) (_ : x ∈ S), f x) = ⊤
  · simp [htop] at hlt
  · exact absurd this (not_le.mpr (ENNReal.lt_add_right htop hε.ne'))

/-- Pointwise ε-optimal selection: for each `a`, choose `m ∈ S a` with
`f a m ≤ inf + ε`. The function `sel` is not claimed to be measurable; for an analytically
measurable selector on Polish spaces see `exists_eps_optimal_selector`. -/
theorem eps_optimal_selection
    {α β : Type*} [MeasurableSpace β]
    (S : α → Set (Measure β))
    (h_ne : ∀ a, (S a).Nonempty)
    (f : α → Measure β → ENNReal)
    (ε : ENNReal) (hε : 0 < ε) :
    ∃ (sel : α → Measure β),
      (∀ a, sel a ∈ S a) ∧
      (∀ a, f a (sel a) ≤ (⨅ (m : Measure β) (_ : m ∈ S a), f a m) + ε) := by
  have key : ∀ a, ∃ m ∈ S a, f a m ≤ (⨅ (m : Measure β) (_ : m ∈ S a), f a m) + ε :=
    fun a => eps_optimal_element (S a) (h_ne a) (f a) ε hε
  choose sel hsel_mem hsel_opt using key
  exact ⟨sel, hsel_mem, hsel_opt⟩

end
