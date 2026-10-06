/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorIntrinsicSlopeCanonical

/-!
# High-contrast homogenization: Provider.Regularity.CorrectorIntrinsicSlopeDiagonal

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# A summable diagonal principle for intrinsic slope

Uniform summable control of successive finite-volume averages identifies the
large-cube diagonal limit.  This is the topology/series mechanism needed to
turn the good-tail telescope of the corrector into its intrinsic slope.
-/

namespace HCPolySupport
namespace HighContrast

noncomputable section

/-- If every row converges, its diagonal tends to zero, and all successive row
increments are controlled by one summable sequence shifted by the row index,
then the row limits tend to zero along the diagonal. -/
theorem tendsto_zero_of_summable_successive_norm_le_of_diagonal_tendsto
    {d : ℕ} (x : ℕ → ℕ → Vec d) (L : ℕ → Vec d)
    (epsilon : ℕ → ℝ) (C : ℝ)
    (hsum : Summable epsilon)
    (hrow : ∀ q, Filter.Tendsto (x q) Filter.atTop (nhds (L q)))
    (hdiag : Filter.Tendsto (fun q => x q 0) Filter.atTop (nhds 0))
    (hstep : ∀ q k,
      ‖x q (k + 1) - x q k‖ ≤ C * epsilon (q + k)) :
    Filter.Tendsto L Filter.atTop (nhds 0) := by
  have hshiftSummable : ∀ q, Summable (fun k => epsilon (q + k)) := by
    intro q
    simpa only [add_comm] using (summable_nat_add_iff q).2 hsum
  have hbound : ∀ q,
      ‖L q - x q 0‖ ≤ C * ∑' k, epsilon (k + q) := by
    intro q
    have hcontrol : ∀ k,
        dist (x q k) (x q (k + 1)) ≤ C * epsilon (q + k) := by
      intro k
      simpa only [dist_eq_norm, norm_sub_rev] using hstep q k
    have hcontrolSummable : Summable (fun k => C * epsilon (q + k)) :=
      (hshiftSummable q).mul_left C
    have hdist := dist_le_tsum_of_dist_le_of_tendsto₀
      (fun k => C * epsilon (q + k)) hcontrol hcontrolSummable (hrow q)
    calc
      ‖L q - x q 0‖ = dist (x q 0) (L q) := by
        rw [dist_eq_norm, norm_sub_rev]
      _ ≤ ∑' k, C * epsilon (q + k) := hdist
      _ = C * ∑' k, epsilon (q + k) := tsum_mul_left
      _ = C * ∑' k, epsilon (k + q) := by
        congr 2
        funext k
        rw [add_comm]
  have htail : Filter.Tendsto
      (fun q => ∑' k, epsilon (k + q)) Filter.atTop (nhds 0) := by
    exact _root_.tendsto_sum_nat_add epsilon
  have hupper : Filter.Tendsto
      (fun q => C * ∑' k, epsilon (k + q)) Filter.atTop (nhds 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul htail
  have hdiff : Filter.Tendsto (fun q => L q - x q 0)
      Filter.atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero'
      (Filter.Eventually.of_forall fun q => norm_nonneg (L q - x q 0))
      (Filter.Eventually.of_forall hbound) hupper
  have hadd := hdiff.add hdiag
  simpa only [sub_add_cancel, zero_add] using hadd

end

end HighContrast
end HCPolySupport
