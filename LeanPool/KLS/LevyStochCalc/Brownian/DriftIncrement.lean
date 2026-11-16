/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Increments of the integral of a bounded function

The drift part of an Itô process is `t ↦ ∫_0^t b_s ds`. Its increment across a cell is the
integral over that cell, and is bounded by the bound on `b` times the cell length.

## Main statements

* `LevyStochCalc.integrableOn_of_bounded_of_measurable` — a bounded measurable function is
  integrable on any set of finite measure.
* `LevyStochCalc.setIntegral_Icc_sub_Icc` — `∫_{[0,b]} − ∫_{[0,a]} = ∫_{(a,b]}`.
* `LevyStochCalc.abs_setIntegral_Ioc_le` — `|∫_{(a,b]} f| ≤ B·(b − a)`.
* `LevyStochCalc.abs_setIntegral_Icc_sub_le` — `t ↦ ∫_{[0,t]} f` is `B`-Lipschitz.
* `LevyStochCalc.continuous_setIntegral_Icc` — hence continuous.
* `LevyStochCalc.measurable_setIntegral` — the integral over a fixed set is measurable in
  the parameter.
* `LevyStochCalc.measurable_setIntegral_Ioc` — the window integral is measurable in the
  parameter.
-/

@[expose] public section

namespace LevyStochCalc

open MeasureTheory

/-- A bounded measurable function is integrable on any set of finite measure. -/
theorem integrableOn_of_bounded_of_measurable {f : ℝ → ℝ} (hf : Measurable f) {B : ℝ}
    (hB : ∀ s, |f s| ≤ B) {s : Set ℝ} (hs : volume s ≠ ⊤) :
    MeasureTheory.IntegrableOn f s volume := by
  refine MeasureTheory.Measure.integrableOn_of_bounded (M := B) hs hf.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun u => by rw [Real.norm_eq_abs]; exact hB u

/-- The increment of `t ↦ ∫_{[0,t]} f` across `(a, b]` is the integral over `(a, b]`. -/
theorem setIntegral_Icc_sub_Icc {f : ℝ → ℝ} (hf : Measurable f) {B : ℝ}
    (hB : ∀ s, |f s| ≤ B) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫ s in Set.Icc (0 : ℝ) b, f s ∂volume) - ∫ s in Set.Icc (0 : ℝ) a, f s ∂volume
      = ∫ s in Set.Ioc a b, f s ∂volume := by
  have hsplit : Set.Icc (0 : ℝ) b = Set.Icc (0 : ℝ) a ∪ Set.Ioc a b := by
    rw [Set.Icc_union_Ioc_eq_Icc ha hab]
  have hdisj : Disjoint (Set.Icc (0 : ℝ) a) (Set.Ioc a b) :=
    Set.disjoint_left.mpr fun x hx hx' => absurd hx.2 (not_le.mpr hx'.1)
  have hint1 : MeasureTheory.IntegrableOn f (Set.Icc (0 : ℝ) a) volume :=
    integrableOn_of_bounded_of_measurable hf hB (by simp)
  have hint2 : MeasureTheory.IntegrableOn f (Set.Ioc a b) volume :=
    integrableOn_of_bounded_of_measurable hf hB (by simp)
  rw [hsplit, MeasureTheory.setIntegral_union hdisj measurableSet_Ioc hint1 hint2,
    add_sub_cancel_left]

/-- The integral of a function bounded by `B` over `(a, b]` is at most `B·(b − a)` in size. -/
theorem abs_setIntegral_Ioc_le {f : ℝ → ℝ} (hf : Measurable f) {B : ℝ}
    (hB : ∀ s, |f s| ≤ B) {a b : ℝ} (hab : a ≤ b) :
    |∫ s in Set.Ioc a b, f s ∂volume| ≤ B * (b - a) := by
  have hB0 : (0 : ℝ) ≤ B := (abs_nonneg (f a)).trans (hB a)
  have hint : MeasureTheory.IntegrableOn f (Set.Ioc a b) volume :=
    integrableOn_of_bounded_of_measurable hf hB (by simp)
  have habs : |∫ s in Set.Ioc a b, f s ∂volume| ≤ ∫ s in Set.Ioc a b, |f s| ∂volume := by
    simpa [Real.norm_eq_abs] using
      MeasureTheory.norm_integral_le_integral_norm (μ := volume.restrict (Set.Ioc a b)) f
  refine habs.trans ?_
  have hle : ∫ s in Set.Ioc a b, |f s| ∂volume ≤ ∫ _s in Set.Ioc a b, B ∂volume := by
    refine MeasureTheory.setIntegral_mono_on hint.abs
      (MeasureTheory.integrableOn_const (by simp [Real.volume_Ioc])) measurableSet_Ioc
      fun u _ => hB u
  refine hle.trans ?_
  rw [MeasureTheory.setIntegral_const, Real.volume_real_Ioc_of_le hab, smul_eq_mul]
  exact le_of_eq (mul_comm _ _)


/-- The integral of a jointly measurable function over a fixed set is measurable in the
parameter. -/
theorem measurable_setIntegral {Ω : Type*} [MeasurableSpace Ω] {f : Ω → ℝ → ℝ}
    (hf : Measurable (Function.uncurry f)) (s : Set ℝ) :
    Measurable fun ω => ∫ t in s, f ω t ∂volume :=
  (MeasureTheory.StronglyMeasurable.integral_prod_right
    (ν := volume.restrict s) hf.stronglyMeasurable).measurable

/-- The integral of a jointly measurable function over a fixed window is measurable in the
parameter. -/
theorem measurable_setIntegral_Ioc {Ω : Type*} [MeasurableSpace Ω] {f : Ω → ℝ → ℝ}
    (hf : Measurable (Function.uncurry f)) (a b : ℝ) :
    Measurable fun ω => ∫ s in Set.Ioc a b, f ω s ∂volume :=
  measurable_setIntegral hf (Set.Ioc a b)

/-- The integral of a bounded function over `[0, t]` is `B`-Lipschitz in `t`. -/
theorem abs_setIntegral_Icc_sub_le {f : ℝ → ℝ} (hf : Measurable f) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ s, |f s| ≤ B) (t t' : ℝ) :
    |(∫ s in Set.Icc (0 : ℝ) t', f s ∂volume) - ∫ s in Set.Icc (0 : ℝ) t, f s ∂volume|
      ≤ B * |t' - t| := by
  have hIcc : ∀ u : ℝ, 0 ≤ u →
      (∫ s in Set.Icc (0 : ℝ) u, f s ∂volume) = ∫ s in Set.Ioc (0 : ℝ) u, f s ∂volume := by
    intro u _
    rw [MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioc_ae_eq_Icc]
  have hempty : ∀ u : ℝ, u < 0 → (∫ s in Set.Icc (0 : ℝ) u, f s ∂volume) = 0 := by
    intro u hu
    rw [Set.Icc_eq_empty (not_le.mpr hu), MeasureTheory.setIntegral_empty]
  have key : ∀ a b : ℝ, a ≤ b →
      |(∫ s in Set.Icc (0 : ℝ) b, f s ∂volume) - ∫ s in Set.Icc (0 : ℝ) a, f s ∂volume|
        ≤ B * (b - a) := by
    intro a b hab
    rcases lt_or_ge b 0 with hb | hb
    · rw [hempty b hb, hempty a (lt_of_le_of_lt hab hb)]
      simpa using mul_nonneg hB0 (by linarith)
    · rcases lt_or_ge a 0 with ha | ha
      · rw [hempty a ha, sub_zero, hIcc b hb]
        refine le_trans (abs_setIntegral_Ioc_le hf hB hb) ?_
        have : (0 : ℝ) ≤ -a := by linarith
        nlinarith
      · rw [setIntegral_Icc_sub_Icc hf hB ha hab]
        exact abs_setIntegral_Ioc_le hf hB hab
  rcases le_total t t' with h | h
  · rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ t' - t)]
    exact key t t' h
  · rw [abs_sub_comm ((∫ s in Set.Icc (0 : ℝ) t', f s ∂volume)),
      abs_sub_comm t' t, abs_of_nonneg (by linarith : (0 : ℝ) ≤ t - t')]
    exact key t' t h

/-- The integral of a bounded measurable function over `[0, t]` is continuous in `t`. -/
theorem continuous_setIntegral_Icc {f : ℝ → ℝ} (hf : Measurable f) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ s, |f s| ≤ B) :
    Continuous fun t => ∫ s in Set.Icc (0 : ℝ) t, f s ∂volume := by
  have hlip : LipschitzWith (Real.toNNReal B)
      fun t => ∫ s in Set.Icc (0 : ℝ) t, f s ∂volume := by
    refine LipschitzWith.of_dist_le_mul fun t t' => ?_
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal B hB0]
    exact abs_setIntegral_Icc_sub_le hf hB0 hB t' t
  exact hlip.continuous


end LevyStochCalc
