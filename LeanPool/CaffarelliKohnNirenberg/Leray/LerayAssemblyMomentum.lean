/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayHopfLimitMomentum
public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityPressureFixedMultiplier

/-!
# Leray Assembly Momentum

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Filter
noncomputable section

namespace CKN.Leray

/-- The four terms of the regularized momentum identity pass to their
limits separately. -/
theorem lerayAssembly_momentum_four_terms
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (A B C P : ℕ → α → ℝ)
    (a b c p : α → ℝ)
    (hA : ∀ n, Integrable (A n) μ)
    (hB : ∀ n, Integrable (B n) μ)
    (hC : ∀ n, Integrable (C n) μ)
    (hP : ∀ n, Integrable (P n) μ)
    (ha : Integrable a μ) (hb : Integrable b μ)
    (hc : Integrable c μ) (hp : Integrable p μ)
    (hAc : Tendsto (fun n => ∫ x, A n x ∂μ) atTop (nhds (∫ x, a x ∂μ)))
    (hBc : Tendsto (fun n => ∫ x, B n x ∂μ) atTop (nhds (∫ x, b x ∂μ)))
    (hCc : Tendsto (fun n => ∫ x, C n x ∂μ) atTop (nhds (∫ x, c x ∂μ)))
    (hPc : Tendsto (fun n => ∫ x, P n x ∂μ) atTop (nhds (∫ x, p x ∂μ)))
    (hreg : ∀ n, ∫ x, -A n x - B n x + C n x - P n x ∂μ = 0) :
    ∫ x, -a x - b x + c x - p x ∂μ = 0 := by
  have hsplitN (n : ℕ) :
      (∫ x, -A n x - B n x + C n x - P n x ∂μ) =
        -(∫ x, A n x ∂μ) - (∫ x, B n x ∂μ) +
          (∫ x, C n x ∂μ) - (∫ x, P n x ∂μ) := by
    change (∫ x, (-A n - B n + C n - P n) x ∂μ) = _
    rw [integral_sub' (((hA n).neg.sub (hB n)).add (hC n)) (hP n),
      integral_add' ((hA n).neg.sub (hB n)) (hC n),
      integral_sub' (hA n).neg (hB n), integral_neg']
  have hsplit :
      (∫ x, -a x - b x + c x - p x ∂μ) =
        -(∫ x, a x ∂μ) - (∫ x, b x ∂μ) +
          (∫ x, c x ∂μ) - (∫ x, p x ∂μ) := by
    change (∫ x, (-a - b + c - p) x ∂μ) = _
    rw [integral_sub' ((ha.neg.sub hb).add hc) hp,
      integral_add' (ha.neg.sub hb) hc,
      integral_sub' ha.neg hb, integral_neg']
  have hconv := ((hAc.neg.sub hBc).add hCc).sub hPc
  have hzero : Tendsto
      (fun n => -(∫ x, A n x ∂μ) - (∫ x, B n x ∂μ) +
        (∫ x, C n x ∂μ) - (∫ x, P n x ∂μ)) atTop (nhds 0) := by
    simpa only [← hsplitN, hreg] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
  rw [hsplit]
  exact tendsto_nhds_unique hconv hzero

end CKN.Leray
