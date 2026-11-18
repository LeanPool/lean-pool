/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import LeanPool.KLS.LevyStochCalc.Brownian.ItoProcess

/-!
# Continuous adapted versions of an Itô process

The Itô integral is defined time by time, so the process `t ↦ X_t` it produces has no path
regularity built in. `IsItoVersion` names a continuous adapted process agreeing with the Itô
process at each time; such a version has jointly measurable paths, so it can be composed with a
continuous function and fed back into a time integral or an Itô integral.

## Main statements

* `LevyStochCalc.Brownian.Ito.IsItoVersion` — a continuous adapted version of an Itô process.
* `LevyStochCalc.Brownian.Ito.IsItoVersion.measurable_uncurry` — its joint measurability.
* `LevyStochCalc.Brownian.Ito.IsItoVersion.progressivelyMeasurable_comp` — a continuous function
  of it is progressively measurable.
* `LevyStochCalc.Brownian.Ito.IsItoVersion.sub_ae` — its increment splits into drift and
  martingale parts.
* `LevyStochCalc.Brownian.Ito.IsItoVersion.integral_abs_sub_le` and
  `LevyStochCalc.Brownian.Ito.IsItoVersion.integral_sq_sub_le` — the increment moments carried
  over from `itoProcess`.
-/

@[expose] public section

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

section Version

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

/-- A continuous adapted process agreeing at each nonnegative time with the Itô process
`X₀ + ∫ b ds + ∫ H dW`. -/
structure IsItoVersion (X₀ : Ω → ℝ) (bdrift : Ω → ℝ → ℝ) (X : ℝ → Ω → ℝ) : Prop where
  /-- every path is continuous -/
  continuous_path : ∀ ω : Ω, Continuous fun t => X t ω
  /-- the process is adapted -/
  adapted : ∀ t : ℝ, @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ t) (X t)
  /-- at each nonnegative time it agrees almost surely with the Itô process -/
  ae_eq : ∀ t : ℝ, 0 ≤ t → X t =ᵐ[P] itoProcess W ℱ hℱ H hm hp hq X₀ bdrift t

variable {W ℱ hℱ H hm hp hq} {X₀ : Ω → ℝ} {bdrift : Ω → ℝ → ℝ} {X : ℝ → Ω → ℝ}

/-- A version's paths are jointly measurable in the sample point and the time. -/
theorem IsItoVersion.measurable_uncurry (h : IsItoVersion W ℱ hℱ H hm hp hq X₀ bdrift X) :
    Measurable (Function.uncurry fun ω s => X s ω) := by
  have hjoint : Measurable (Function.uncurry X) :=
    measurable_uncurry_of_continuous_of_measurable h.continuous_path
      fun t => ((h.adapted t).mono (ℱ.le t)).measurable
  exact hjoint.comp measurable_swap

/-- A version's time slices are measurable. -/
theorem IsItoVersion.measurable (h : IsItoVersion W ℱ hℱ H hm hp hq X₀ bdrift X) (t : ℝ) :
    Measurable (X t) := ((h.adapted t).mono (ℱ.le t)).measurable

/-- A continuous function of a version is progressively measurable. -/
theorem IsItoVersion.progressivelyMeasurable_comp
    (h : IsItoVersion W ℱ hℱ H hm hp hq X₀ bdrift X) {φ : ℝ → ℝ} (hφ : Continuous φ) :
    Probability.ProgressivelyMeasurable ℱ fun ω s => φ (X s ω) := by
  refine Probability.ProgressivelyMeasurable.of_isStronglyProgressive ?_
  refine MeasureTheory.StronglyAdapted.isStronglyProgressive_of_continuous
    (fun t => hφ.comp_stronglyMeasurable (h.adapted t)) fun ω => ?_
  exact hφ.comp (h.continuous_path ω)

/-- A continuous function of a version is jointly measurable. -/
theorem IsItoVersion.measurable_uncurry_comp
    (h : IsItoVersion W ℱ hℱ H hm hp hq X₀ bdrift X) {φ : ℝ → ℝ} (hφ : Measurable φ) :
    Measurable (Function.uncurry fun ω s => φ (X s ω)) :=
  hφ.comp h.measurable_uncurry

/-- A version agrees with the Itô process at every time of a countable family, simultaneously. -/
theorem IsItoVersion.ae_eq_all (h : IsItoVersion W ℱ hℱ H hm hp hq X₀ bdrift X)
    (t : ℕ → ℝ) (ht : ∀ i, 0 ≤ t i) :
    ∀ᵐ ω ∂P, ∀ i : ℕ, X (t i) ω = itoProcess W ℱ hℱ H hm hp hq X₀ bdrift (t i) ω :=
  MeasureTheory.ae_all_iff.mpr fun i => h.ae_eq (t i) (ht i)

/-- The increment of a version splits into the drift's window integral and the Itô integral's
increment. -/
theorem IsItoVersion.sub_ae (h : IsItoVersion W ℱ hℱ H hm hp hq X₀ bdrift X)
    (hbm : Measurable (Function.uncurry bdrift)) {B : ℝ}
    (hB : ∀ (ω : Ω) (s : ℝ), |bdrift ω s| ≤ B) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    ∀ᵐ ω ∂P, X v ω - X u ω
      = (∫ s in Set.Ioc u v, bdrift ω s ∂volume)
        + (stochasticIntegralBrownian W ℱ hℱ H hm hp hq v ω
          - stochasticIntegralBrownian W ℱ hℱ H hm hp hq u ω) := by
  filter_upwards [h.ae_eq v (hu.trans huv), h.ae_eq u hu] with ω hv hu'
  rw [hv, hu']
  exact itoProcess_sub W ℱ hℱ H hm hp hq X₀ bdrift hbm hB hu huv ω


section Moments

variable {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)

include hC0 hCH in
/-- The first absolute moment of a version's increment. -/
theorem IsItoVersion.integral_abs_sub_le (h : IsItoVersion W ℱ hℱ H hm hp hq X₀ bdrift X)
    (hbm : Measurable (Function.uncurry bdrift))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ (ω : Ω) (s : ℝ), |bdrift ω s| ≤ B)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    MeasureTheory.Integrable (fun ω : Ω => |X v ω - X u ω|) P
      ∧ ∫ ω, |X v ω - X u ω| ∂P ≤ B * (v - u) + C * Real.sqrt (v - u) := by
  rcases eq_or_lt_of_le huv with rfl | hlt
  · refine ⟨by simp, ?_⟩
    simp
  · obtain ⟨hint, hle⟩ := integral_abs_itoProcess_sub_le W ℱ hℱ H hm hp hq hC0 hCH X₀ bdrift
      hbm hB0 hB hu hlt
    have hae : (fun ω : Ω => |X v ω - X u ω|)
        =ᵐ[P] fun ω => |itoProcess W ℱ hℱ H hm hp hq X₀ bdrift v ω
          - itoProcess W ℱ hℱ H hm hp hq X₀ bdrift u ω| := by
      filter_upwards [h.ae_eq v (hu.trans huv), h.ae_eq u hu] with ω hv hu'
      rw [hv, hu']
    exact ⟨hint.congr hae.symm, by rw [MeasureTheory.integral_congr_ae hae]; exact hle⟩

include hC0 hCH in
/-- The second moment of a version's increment. -/
theorem IsItoVersion.integral_sq_sub_le (h : IsItoVersion W ℱ hℱ H hm hp hq X₀ bdrift X)
    (hbm : Measurable (Function.uncurry bdrift))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ (ω : Ω) (s : ℝ), |bdrift ω s| ≤ B)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    MeasureTheory.Integrable (fun ω : Ω => (X v ω - X u ω) ^ 2) P
      ∧ ∫ ω, (X v ω - X u ω) ^ 2 ∂P ≤ 2 * (B * (v - u)) ^ 2 + 2 * (C ^ 2 * (v - u)) := by
  rcases eq_or_lt_of_le huv with rfl | hlt
  · refine ⟨by simp, ?_⟩
    simp
  · obtain ⟨hint, hle⟩ := integral_sq_itoProcess_sub_le W ℱ hℱ H hm hp hq hC0 hCH X₀ bdrift
      hbm hB0 hB hu hlt
    have hae : (fun ω : Ω => (X v ω - X u ω) ^ 2)
        =ᵐ[P] fun ω => (itoProcess W ℱ hℱ H hm hp hq X₀ bdrift v ω
          - itoProcess W ℱ hℱ H hm hp hq X₀ bdrift u ω) ^ 2 := by
      filter_upwards [h.ae_eq v (hu.trans huv), h.ae_eq u hu] with ω hv hu'
      rw [hv, hu']
    exact ⟨hint.congr hae.symm, by rw [MeasureTheory.integral_congr_ae hae]; exact hle⟩

end Moments

end Version

end LevyStochCalc.Brownian.Ito
