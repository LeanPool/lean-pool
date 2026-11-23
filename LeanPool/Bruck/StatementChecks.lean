/-
Copyright (c) 2026 Fang, Hu, Li, Tang, and Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pengcheng Fang, Tao Hu, Yanyang Li, Quanyu Tang, Haiqi Zhang
-/

module

public import LeanPool.Bruck.HyperOrderComparison

/-! # Comparison with the Taylor-series and circle-mean definitions of Brück's conjecture -/

public section

open Filter Real

namespace Bruck

/-- Sharing with multiplicities means that the Taylor expansions of the two shifted functions
vanish to the same order at every point. Nonconstancy of `f` suffices for this formulation. -/
theorem sharesCM_iff_iteratedDeriv_vanishing {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hnon : ¬ ∀ z, f z = f 0) (a : ℂ) :
    SharesCM f (deriv f) a ↔ ∀ (z : ℂ) (n : ℕ),
      (∀ k < n, iteratedDeriv k (fun w => f w - a) z = 0) ↔
      (∀ k < n, iteratedDeriv k (fun w => deriv f w - a) z = 0) := by
  have hfne : f ≠ fun _ => a := fun h => hnon fun z => by rw [h]
  simp_rw [← natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero ((hf.sub_const a).analyticAt _),
    ← natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero ((hf.deriv.sub_const a).analyticAt _)]
  constructor
  · intro h z n
    rw [h.2.2 z]
  · intro h
    have hord (z : ℂ) := ENat.eq_of_forall_natCast_le_iff (h z)
    refine ⟨hfne, ?_, hord⟩
    intro hder
    apply hfne
    funext z
    apply sub_eq_zero.mp
    apply apply_eq_zero_of_analyticOrderAt_ne_zero (f := fun w => f w - a)
    rw [hord z, hder]
    simp [← Pi.zero_def]

/-- For a nonconstant entire function the hyper-order is the limsup of the twice-truncated
logarithm of the circle mean of `log⁺ ‖f‖`, divided by `log r`. -/
theorem hyperOrder_eq_limsup_circleAverage_posLog {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hnon : ¬ ∀ z, f z = f 0) :
    hyperOrder f = limsup (fun r => ENNReal.ofReal
      (log⁺ (log⁺ (circleAverage (fun z => log⁺ ‖f z‖) 0 r)) / log r)) atTop := by
  apply limsup_congr
  have hT := characteristic_tendsto_atTop hf hnon
  filter_upwards [hT.eventually_ge_atTop 1,
    (tendsto_log_atTop.comp hT).eventually_ge_atTop 1] with r hr hlog
  change 1 ≤ log (ValueDistribution.characteristic f ⊤ r) at hlog
  rw [← characteristic_eq_circleAverage_posLog hf r,
    posLog_eq_log (hr.trans (le_abs_self _)), posLog_eq_log (hlog.trans (le_abs_self _))]

end Bruck
