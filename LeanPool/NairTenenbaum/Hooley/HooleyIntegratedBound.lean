/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Hooley.HooleyIntegratingFactor

/-! # An integrated bound for the transformed Hooley moment series

The derivative majorant is integrable on every compact interval to the right
of one. The resulting bound is unconditional and keeps the prime-series
estimates separate from the analytic differential argument.
-/

@[expose] public section

namespace NairTenenbaum

open Real Polynomial MeasureTheory

/-- A majorant for the reduced Hooley moment used in differential integration. -/
noncomputable def hooleyReducedMomentMajorant (Q : ℤ[X]) (t : ℝ) (q : ℕ) (s : ℝ) : ℝ :=
  (hooleyPrimeErrorConstant Q q ^ (t / q) / ((q : ℝ) - 1)) *
    rootPrimeDirichletSum Q s ^ (1 - t / q) *
    Real.exp (((2 : ℝ) ^ t - (2 : ℝ) ^ (t / q)) / ((q : ℝ) - 1) * rootPrimePowerSum Q s)

theorem intervalIntegrable_hooleyReducedMomentMajorant {Q : ℤ[X]} (hQ : NoFixedPrimeDivisor Q)
    {t a b : ℝ} {q : ℕ} (hq : 0 < q) (htq : t ≤ q) (ha : 1 < a) (hab : a ≤ b) :
    IntervalIntegrable (hooleyReducedMomentMajorant Q t q) volume a b := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hθ : 0 ≤ 1 - t / q := sub_nonneg.mpr ((div_le_one hq').mpr htq)
  have hsub : Set.uIcc a b ⊆ Set.Ioi 1 := by
    rw [Set.uIcc_of_le hab]
    intro s hs
    exact ha.trans_le hs.1
  have hanti : AntitoneOn (fun s => rootPrimeDirichletSum Q s ^ (1 - t / q)) (Set.uIcc a b) := by
    intro s hs u hu hsu
    exact Real.rpow_le_rpow (rootPrimeDirichletSum_nonneg Q u)
      (antitoneOn_rootPrimeDirichletSum hQ (hsub hs) (hsub hu) hsu) hθ
  have hi : IntervalIntegrable (fun s => rootPrimeDirichletSum Q s ^ (1 - t / q)) volume a b :=
    hanti.intervalIntegrable
  have hc : ContinuousOn (rootPrimePowerSum Q) (Set.uIcc a b) :=
    fun s hs => (hasDerivAt_rootPrimePowerSum hQ (hsub hs)).continuousAt.continuousWithinAt
  have H := (hi.mul_continuousOn (hc.const_mul
    (((2 : ℝ) ^ t - (2 : ℝ) ^ (t / q)) / ((q : ℝ) - 1))).rexp).const_mul
      (hooleyPrimeErrorConstant Q q ^ (t / q) / ((q : ℝ) - 1))
  unfold hooleyReducedMomentMajorant
  simpa only [mul_assoc] using H

theorem hooleyReducedMoment_le_endpoint_add_integral {Q : ℤ[X]} (hQ : NoFixedPrimeDivisor Q)
    {t a b : ℝ} (ht : 0 ≤ t) {q : ℕ} (hq : 2 < q) (htq : t ≤ q) (ha : 1 < a) (hab : a ≤ b) :
    hooleyReducedMoment Q t q a ≤ hooleyReducedMoment Q t q b +
      ∫ s in a..b, hooleyReducedMomentMajorant Q t q s := by
  have hc : ContinuousOn (fun s => -hooleyReducedMoment Q t q s) (Set.Icc a b) := by
    intro s hs
    exact (differentiableAt_hooleyReducedMoment hQ ht (by omega : 0 < q)
      (ha.trans_le hs.1)).continuousAt.neg.continuousWithinAt
  have hi : IntegrableOn (hooleyReducedMomentMajorant Q t q) (Set.Icc a b) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp
      (intervalIntegrable_hooleyReducedMomentMajorant hQ (by omega) htq ha hab)
  have H := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le hab hc
    (fun s hs => (differentiableAt_hooleyReducedMoment hQ ht (by omega : 0 < q)
      (ha.trans hs.1)).hasDerivAt.neg.hasDerivWithinAt) hi
    (fun s hs => neg_deriv_hooleyReducedMoment_le hQ ht hq htq (ha.trans hs.1))
  linarith

end NairTenenbaum
