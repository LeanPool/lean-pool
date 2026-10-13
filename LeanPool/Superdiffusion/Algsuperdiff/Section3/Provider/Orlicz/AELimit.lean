/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Probability.IndependentSums.WeakOrlicz

/-!
# AELimit

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Uniform one-sided Gamma tails under almost-everywhere limits

At a fixed threshold, pointwise convergence puts the target upper-tail event
almost everywhere inside the increasing union of the eventual upper-tail
events of the approximating sequence.  Continuity from below and the uniform
tail estimate then preserve the amplitude exactly.  The argument is purely
set-theoretic and does not require measurability of the random variables.

## Main result

* `Algsuperdiff.Section3.Provider.Orlicz.isBigOWith_gammaSigma_of_ae_tendsto_uniform`
  preserves a uniform one-sided `Gamma_sigma` weak-tail bound under
  almost-everywhere pointwise convergence.
-/

namespace Algsuperdiff.Section3.Provider.Orlicz

open MeasureTheory
open HCPolySupport.IndependentSums

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A uniform one-sided stretched-exponential tail bound is preserved under
almost-everywhere pointwise convergence, with its amplitude unchanged. -/
theorem isBigOWith_gammaSigma_of_ae_tendsto_uniform
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {W : ℕ → Ω → ℝ} {S : Ω → ℝ} {A σ : ℝ}
    (hlim : ∀ᵐ ω ∂μ, Filter.Tendsto (fun n => W n ω) Filter.atTop (nhds (S ω)))
    (hW : ∀ n, IsBigOWith μ (gammaSigma σ) (W n) A) :
    IsBigOWith μ (gammaSigma σ) S A := by
  rw [isBigOWith_gammaSigma_iff]
  intro t ht
  set c : ℝ := A * t with hc
  set E : ℕ → Set Ω := fun n => upperTailEvent (W n) c with hE
  set U : ℕ → Set Ω := fun N => {ω | ∀ n, N ≤ n → ω ∈ E n} with hU
  have hU_mono : Monotone U := by
    intro N M hNM ω hω n hMn
    exact hω n (hNM.trans hMn)
  have htarget : upperTailEvent S c ≤ᵐ[μ] ⋃ N, U N := by
    filter_upwards [hlim] with ω hω hωS
    have heventually : ∀ᶠ n in Filter.atTop, c < W n ω :=
      (tendsto_order.1 hω).1 c hωS
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 heventually
    refine Set.mem_iUnion.2 ⟨N, ?_⟩
    intro n hNn
    show c < W n ω
    exact hN n hNn
  have hE_bound :
      ∀ n, μ (E n) ≤ ENNReal.ofReal (Real.exp (-(t ^ σ))) := by
    intro n
    have htail := (isBigOWith_gammaSigma_iff.mp (hW n)) ht
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ (E n))]
    exact ENNReal.ofReal_le_ofReal (by simpa [E, c] using! htail)
  have hU_bound :
      ∀ N, μ (U N) ≤ ENNReal.ofReal (Real.exp (-(t ^ σ))) := by
    intro N
    refine (measure_mono ?_).trans (hE_bound N)
    intro ω hω
    change ∀ n, N ≤ n → ω ∈ E n at hω
    exact hω N le_rfl
  have hunion_bound :
      μ (⋃ N, U N) ≤ ENNReal.ofReal (Real.exp (-(t ^ σ))) := by
    rw [hU_mono.measure_iUnion]
    exact iSup_le hU_bound
  have hfinite :
      μ (upperTailEvent S c) ≤ ENNReal.ofReal (Real.exp (-(t ^ σ))) :=
    (measure_mono_ae htarget).trans hunion_bound
  have hreal :=
    (ENNReal.toReal_le_toReal (measure_ne_top μ _) ENNReal.ofReal_ne_top).mpr hfinite
  rw [ENNReal.toReal_ofReal (Real.exp_pos _).le] at hreal
  simpa [hc, measureReal_def] using hreal

end Algsuperdiff.Section3.Provider.Orlicz
