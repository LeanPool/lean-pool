/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Riemann sums of a continuous weight against a bounded density

Freezing a continuous weight at the left endpoint of each cell of a partition changes the
integral of the weight against a bounded density by at most the weight's modulus of continuity
at the mesh, times the density bound, times the length of the interval.

## Main statements

* `LevyStochCalc.abs_riemann_weighted_sub_integral_le` — the Riemann-sum error bound.
-/

@[expose] public section

namespace LevyStochCalc

open MeasureTheory

/-- **Riemann-sum error for a continuous weight against a bounded density.** -/
theorem abs_riemann_weighted_sub_integral_le
    {T ε δ M Kg : ℝ} (hε0 : 0 ≤ ε)
    {g h : ℝ → ℝ} (hgc : Continuous g) (hh : Measurable h)
    (hhM : ∀ s, |h s| ≤ M) (hgb : ∀ s ∈ Set.Icc (0 : ℝ) T, |g s| ≤ Kg)
    (hgmod : ∀ x ∈ Set.Icc (0 : ℝ) T, ∀ y ∈ Set.Icc (0 : ℝ) T, |x - y| ≤ δ → |g x - g y| ≤ ε)
    {m : ℕ} (t : ℕ → ℝ) (ht0 : t 0 = 0) (htm : t m = T)
    (htmono : ∀ i, i < m → t i ≤ t (i + 1)) (htmesh : ∀ i, i < m → t (i + 1) - t i ≤ δ)
    (htIcc : ∀ i, i ≤ m → t i ∈ Set.Icc (0 : ℝ) T) :
    |(∑ i ∈ Finset.range m, g (t i) * ∫ s in t i..t (i + 1), h s)
        - ∫ s in (0 : ℝ)..T, g s * h s| ≤ ε * M * T := by
  classical
  have hvol : ∀ a b : ℝ, volume (Set.uIoc a b) ≠ ⊤ := fun a b => by
    simp [Set.uIoc, Real.volume_Ioc]
  have hhint : ∀ a b : ℝ, IntervalIntegrable h volume a b := by
    intro a b
    refine intervalIntegrable_iff.mpr
      (MeasureTheory.Measure.integrableOn_of_bounded (M := M) (hvol a b)
        hh.aestronglyMeasurable ?_)
    exact Filter.Eventually.of_forall fun s => by rw [Real.norm_eq_abs]; exact hhM s
  have hghint : ∀ i, i < m →
      IntervalIntegrable (fun s => g s * h s) volume (t i) (t (i + 1)) := by
    intro i hi
    refine intervalIntegrable_iff.mpr
      (MeasureTheory.Measure.integrableOn_of_bounded (M := Kg * M) (hvol _ _)
        (hgc.measurable.mul hh).aestronglyMeasurable ?_)
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_uIoc fun s hs => ?_
    have hsI : s ∈ Set.Icc (0 : ℝ) T := by
      rw [Set.uIoc_of_le (htmono i hi)] at hs
      exact ⟨((htIcc i hi.le).1).trans hs.1.le, hs.2.trans (htIcc (i + 1) hi).2⟩
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hgb s hsI) (hhM s) (abs_nonneg _)
      ((abs_nonneg (g s)).trans (hgb s hsI))
  have hsplit : ∫ s in (0 : ℝ)..T, g s * h s
      = ∑ i ∈ Finset.range m, ∫ s in t i..t (i + 1), g s * h s := by
    rw [← ht0, ← htm]
    exact (intervalIntegral.sum_integral_adjacent_intervals hghint).symm
  rw [hsplit, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ i ∈ Finset.range m,
      |g (t i) * (∫ s in t i..t (i + 1), h s) - ∫ s in t i..t (i + 1), g s * h s|
        ≤ ε * M * (t (i + 1) - t i) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hle : t i ≤ t (i + 1) := htmono i hi
    have hrw : g (t i) * (∫ s in t i..t (i + 1), h s) - ∫ s in t i..t (i + 1), g s * h s
        = ∫ s in t i..t (i + 1), (g (t i) - g s) * h s := by
      rw [← intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_sub ((hhint (t i) (t (i + 1))).const_mul (g (t i)))
          (hghint i hi)]
      exact intervalIntegral.integral_congr fun s _ => by ring
    rw [hrw]
    have hbound : ∀ s ∈ Set.uIoc (t i) (t (i + 1)), ‖(g (t i) - g s) * h s‖ ≤ ε * M := by
      intro s hs
      rw [Set.uIoc_of_le hle] at hs
      have hsI : s ∈ Set.Icc (0 : ℝ) T :=
        ⟨((htIcc i hi.le).1).trans hs.1.le, hs.2.trans (htIcc (i + 1) hi).2⟩
      have hdist : |t i - s| ≤ δ := by
        rw [abs_of_nonpos (by linarith [hs.1] : t i - s ≤ 0)]
        linarith [hs.2, htmesh i hi]
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hgmod (t i) (htIcc i hi.le) s hsI hdist) (hhM s) (abs_nonneg _) hε0
    refine (intervalIntegral.norm_integral_le_of_norm_le_const hbound).trans ?_
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ t (i + 1) - t i)]
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum, Finset.sum_range_sub (fun i => t i) m, ht0, htm, sub_zero]

end LevyStochCalc
