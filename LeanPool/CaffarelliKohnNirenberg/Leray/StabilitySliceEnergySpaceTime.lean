/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityProductSwap
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Stability Slice Energy Space Time

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Filter
open scoped ENNReal
noncomputable section

namespace CKN

/-- A uniform slice energy bound survives strong `L³` convergence in the
space-first product convention of `def:sws` (`thm:stability`). -/
theorem stability_essSup_slice_energy_lt_top_spaceTime
    {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [NormedAddCommGroup E]
    (μ : Measure α) [SFinite μ] (ν : Measure β) [SFinite ν]
    (F : ℕ → α × β → E) (G : α × β → E)
    (hF : ∀ n, AEStronglyMeasurable (F n) (μ.prod ν))
    (hG : AEStronglyMeasurable G (μ.prod ν))
    (hconv : Tendsto (fun n => eLpNorm (F n - G) 3 (μ.prod ν)) atTop (nhds 0))
    (M : ℝ≥0∞) (hM : M < ⊤)
    (hbound : ∀ n,
      essSup (fun t => ∫⁻ x, ‖F n (x, t)‖ₑ ^ (2 : ℝ) ∂μ) ν ≤ M) :
    essSup (fun t => ∫⁻ x, ‖G (x, t)‖ₑ ^ (2 : ℝ) ∂μ) ν < ⊤ := by
  have hswap := stability_eLpNorm_tendsto_swap μ ν 3 F G
    (fun n => (hF n).sub hG) hconv
  have hslice (n : ℕ) :
      ∀ᵐ t ∂ν, AEMeasurable (fun x => ‖F n (x, t)‖ₑ ^ (2 : ℝ)) μ := by
    filter_upwards [(hF n).prodMk_right] with t ht
    exact ht.enorm.pow_const (2 : ℝ)
  exact stability_essSup_slice_energy_lt_top μ ν
    (fun n z => F n (z.2, z.1)) (fun z => G (z.2, z.1))
    hswap hslice M hM hbound

end CKN
