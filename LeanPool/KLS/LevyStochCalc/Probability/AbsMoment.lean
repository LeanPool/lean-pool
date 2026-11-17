/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# First absolute moment from a second-moment bound

On a probability space the first absolute moment of a real random variable is bounded by the
square root of its second moment.

## Main statements

* `LevyStochCalc.integral_abs_le_sqrt_of_integral_sq_le` — `𝔼|f| ≤ √V` whenever `𝔼f² ≤ V`.
* `LevyStochCalc.integral_abs_le_of_bounded` — `𝔼|f| ≤ K` for `|f| ≤ K`.
* `LevyStochCalc.integral_abs_add_four_le` — the triangle inequality for four summands.
-/

@[expose] public section

namespace LevyStochCalc

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- On a probability space, `𝔼|f| ≤ √V` for any bound `V` on the second moment `𝔼f²`. -/
theorem integral_abs_le_sqrt_of_integral_sq_le {P : Measure Ω} [IsProbabilityMeasure P]
    {f : Ω → ℝ} (hf : Integrable (fun ω => |f ω|) P)
    (hf2 : Integrable (fun ω => f ω ^ 2) P) {V : ℝ} (hV : ∫ ω, f ω ^ 2 ∂P ≤ V) :
    ∫ ω, |f ω| ∂P ≤ Real.sqrt V := by
  have hsqnn : (0 : ℝ) ≤ ∫ ω, f ω ^ 2 ∂P := integral_nonneg fun ω => sq_nonneg _
  have hV0 : 0 ≤ V := hsqnn.trans hV
  have hs0 : 0 ≤ Real.sqrt V := Real.sqrt_nonneg V
  have hssq : Real.sqrt V ^ 2 = V := Real.sq_sqrt hV0
  rcases eq_or_lt_of_le hs0 with hs_eq | hs_pos
  · have hVzero : V = 0 := by rw [← hssq, ← hs_eq]; ring
    have h2 : ∫ ω, f ω ^ 2 ∂P = 0 := le_antisymm (hVzero ▸ hV) hsqnn
    have hae : (fun ω => f ω ^ 2) =ᵐ[P] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg _) hf2).mp h2
    have hzero : ∫ ω, |f ω| ∂P = 0 := by
      refine integral_eq_zero_of_ae ?_
      filter_upwards [hae] with ω hω
      simp [abs_eq_zero.mpr (sq_eq_zero_iff.mp hω)]
    rw [hzero]
    exact hs0
  · have h2s : (0 : ℝ) < 2 * Real.sqrt V := by linarith
    have hsne : Real.sqrt V ≠ 0 := ne_of_gt hs_pos
    have hyoung : ∀ ω : Ω, |f ω| ≤ (f ω ^ 2 + Real.sqrt V ^ 2) / (2 * Real.sqrt V) := by
      intro ω
      rw [le_div_iff₀ h2s]
      nlinarith [sq_nonneg (|f ω| - Real.sqrt V), sq_abs (f ω)]
    calc ∫ ω, |f ω| ∂P
        ≤ ∫ ω, (f ω ^ 2 + Real.sqrt V ^ 2) / (2 * Real.sqrt V) ∂P :=
          integral_mono hf ((hf2.add (integrable_const _)).div_const _) hyoung
      _ = ((∫ ω, f ω ^ 2 ∂P) + Real.sqrt V ^ 2) / (2 * Real.sqrt V) := by
          rw [integral_div, integral_add hf2 (integrable_const _)]
          simp
      _ ≤ (V + V) / (2 * Real.sqrt V) := by rw [hssq]; gcongr
      _ = Real.sqrt V := by
          rw [div_eq_iff (ne_of_gt h2s)]
          have hmul : Real.sqrt V * (2 * Real.sqrt V) = 2 * Real.sqrt V ^ 2 := by ring
          rw [hmul, hssq]
          ring

/-- On a probability space, a measurable function bounded in absolute value by `K` is integrable
with `𝔼|f| ≤ K`. -/
theorem integral_abs_le_of_bounded {P : Measure Ω} [IsProbabilityMeasure P] {f : Ω → ℝ}
    (hf : Measurable f) {K : ℝ} (hK0 : 0 ≤ K) (hK : ∀ ω, |f ω| ≤ K) :
    Integrable f P ∧ ∫ ω, |f ω| ∂P ≤ K := by
  have hint : Integrable f P := by
    refine (integrable_const K).mono hf.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hK0]
    exact hK ω
  refine ⟨hint, ?_⟩
  calc ∫ ω, |f ω| ∂P ≤ ∫ _ω : Ω, K ∂P :=
        integral_mono hint.abs (integrable_const _) hK
    _ = K := by simp


/-- A four-term triangle inequality under the integral. -/
theorem integral_abs_add_four_le {P : Measure Ω}
    {a b c d : Ω → ℝ} (ha : Integrable a P) (hb : Integrable b P) (hc : Integrable c P)
    (hd : Integrable d P) {A B C D : ℝ} (hA : ∫ ω, |a ω| ∂P ≤ A)
    (hB : ∫ ω, |b ω| ∂P ≤ B) (hC : ∫ ω, |c ω| ∂P ≤ C) (hD : ∫ ω, |d ω| ∂P ≤ D) :
    ∫ ω, |a ω + b ω + c ω + d ω| ∂P ≤ A + B + C + D := by
  have hab : Integrable (fun ω => |a ω| + |b ω|) P := ha.abs.add hb.abs
  have habc : Integrable (fun ω => |a ω| + |b ω| + |c ω|) P := hab.add hc.abs
  have habcd : Integrable (fun ω => |a ω| + |b ω| + |c ω| + |d ω|) P := habc.add hd.abs
  have htri : ∀ ω, |a ω + b ω + c ω + d ω| ≤ |a ω| + |b ω| + |c ω| + |d ω| := by
    intro ω
    refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
    exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
  calc ∫ ω, |a ω + b ω + c ω + d ω| ∂P
      ≤ ∫ ω, (|a ω| + |b ω| + |c ω| + |d ω|) ∂P :=
        integral_mono (((ha.add hb).add hc).add hd).abs habcd htri
    _ = ∫ ω, (|a ω| + |b ω| + |c ω|) ∂P + ∫ ω, |d ω| ∂P := integral_add habc hd.abs
    _ = ∫ ω, (|a ω| + |b ω|) ∂P + ∫ ω, |c ω| ∂P + ∫ ω, |d ω| ∂P := by
        rw [integral_add hab hc.abs]
    _ = ∫ ω, |a ω| ∂P + ∫ ω, |b ω| ∂P + ∫ ω, |c ω| ∂P + ∫ ω, |d ω| ∂P := by
        rw [integral_add ha.abs hb.abs]
    _ ≤ A + B + C + D := add_le_add (add_le_add (add_le_add hA hB) hC) hD


end LevyStochCalc
