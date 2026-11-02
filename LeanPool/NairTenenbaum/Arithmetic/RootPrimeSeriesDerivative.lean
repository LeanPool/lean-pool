/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Hooley.HooleyDivisorEulerBound

/-! # The prime root series and its logarithmic derivative

The two prime series in the weighted mean argument are related by `R′=-P`.
This identity also permits using the exact prime series as an integrating
factor in the differential inequality.
-/

@[expose] public section

namespace NairTenenbaum

open Real Polynomial MeasureTheory

theorem rootPrimeLogWeight_antitone (Q : ℤ[X]) {p : ℕ} (hp : p.Prime)
    {σ τ : ℝ} (hστ : σ ≤ τ) : rootPrimeLogWeight Q τ p ≤ rootPrimeLogWeight Q σ p := by
  unfold rootPrimeLogWeight
  apply div_le_div_of_nonneg_left
    (mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg p))
    (Real.rpow_pos_of_pos (by exact_mod_cast hp.pos) _)
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp.one_le) hστ

theorem hasDerivAt_rootPrimePowerTerm (Q : ℤ[X]) {p : ℕ} (hp : p.Prime) (σ : ℝ) :
    HasDerivAt (fun s : ℝ => (rootCount Q p : ℝ) * (p : ℝ) ^ (-s))
      (-rootPrimeLogWeight Q σ p) σ := by
  have H := (HasDerivAt.const_rpow (by exact_mod_cast hp.pos : (0 : ℝ) < p)
    (hasDerivAt_id σ).neg).const_mul (rootCount Q p : ℝ)
  convert H using 1
  · rfl
  · dsimp
    rw [rootPrimeLogWeight, div_eq_mul_inv, Real.rpow_neg (Nat.cast_nonneg p)]
    ring

theorem hasDerivAt_rootPrimePowerSum {Q : ℤ[X]} (hQ : NoFixedPrimeDivisor Q)
    {σ : ℝ} (hσ : 1 < σ) :
    HasDerivAt (rootPrimePowerSum Q) (-rootPrimeDirichletSum Q σ) σ := by
  let b := (1 + σ) / 2
  have hb : 1 < b := by dsimp [b]; linarith
  have hbσ : b < σ := by dsimp [b]; linarith
  have H := hasDerivAt_tsum_of_isPreconnected (summable_rootPrimeLogWeight hQ hb)
    isOpen_Ioi (convex_Ioi b).isPreconnected
    (fun (p : Nat.Primes) s _ => hasDerivAt_rootPrimePowerTerm Q p.2 s)
    (fun p s hs => by
      rw [norm_neg, Real.norm_eq_abs, abs_of_nonneg (rootPrimeLogWeight_nonneg Q s p.2)]
      exact rootPrimeLogWeight_antitone Q p.2 hs.le)
    hbσ (summable_rootPrimePowerWeight hQ hσ) hbσ
  unfold rootPrimePowerSum rootPrimeDirichletSum
  simpa only [tsum_neg] using H

theorem antitoneOn_rootPrimeDirichletSum {Q : ℤ[X]} (hQ : NoFixedPrimeDivisor Q) :
    AntitoneOn (rootPrimeDirichletSum Q) (Set.Ioi 1) := by
  intro s hs t ht hst
  exact Summable.tsum_le_tsum (fun p : Nat.Primes => rootPrimeLogWeight_antitone Q p.2 hst)
    (summable_rootPrimeLogWeight hQ ht) (summable_rootPrimeLogWeight hQ hs)

end NairTenenbaum
