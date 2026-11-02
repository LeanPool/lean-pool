/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Arithmetic.ScalarPrimeSplit
public import LeanPool.NairTenenbaum.DivisorSums.PrimeFactorLogGain

/-! # Logarithmic mass of the canonical rough parts -/

@[expose] public section

namespace NairTenenbaum

open Finset Real

theorem sum_log_roughPart {ι : Type*} (S : Finset ι) (n : ι → ℕ+) (z : ℝ) :
    (∑ i ∈ S, Real.log (roughPart (n i) z : ℕ)) =
      (∑ i ∈ S, Real.log (n i : ℕ)) - ∑ i ∈ S, Real.log (smoothPart (n i) z : ℕ) := by
  simp only [log_roughPart, sum_sub_distrib]

theorem roughPart_logMass_le_divisorHits {ι : Type*} (S : Finset ι) (n : ι → ℕ+)
    {k : ℕ} (hk : 2 ≤ k) {A C y : ℝ} (hy : 1 ≤ y) (hC : 1 ≤ C)
    (hA : A < C ^ k) (hA' : 2 * A < C ^ (k - 1))
    (hsize : ∀ i ∈ S, (n i : ℝ) ≤ A * y ^ k) :
    (∑ i ∈ S, Real.log (roughPart (n i) (C * y) : ℕ)) ≤
      (((k : ℝ) - 1) * S.card - (S.filter (fun i => 0 < dyadicDivisorCount (n i) y)).card) *
        Real.log (Nat.maxPrimeFac (∏ i ∈ S, (n i : ℕ))) := by
  refine rough_logMass_le_divisorHits S (fun i => (n i : ℕ))
    (fun i => (smoothPart (n i) (C * y) : ℕ)) (fun i => (roughPart (n i) (C * y) : ℕ))
    (fun i _ => (smoothPart (n i) (C * y)).ne_zero)
    (fun i _ => (roughPart (n i) (C * y)).ne_zero) ?_ hk hy hC hA hA' hsize ?_
  · intro i _
    exact_mod_cast smoothPart_mul_roughPart (n i) (C * y)
  · exact fun i _ p hp => cutoff_lt_of_mem_roughPart (n i) (C * y) hp

/-- A quantitative lower bound for the rough mass yields the required type
of exponential gain. The lower bound and its error remain explicit inputs. -/
theorem maxPrimeFac_prod_ge_exp_divisorHits {ι : Type*} (S : Finset ι) (hS : S.Nonempty)
    (n : ι → ℕ+) {k : ℕ} (hk : 2 ≤ k) {A C y E : ℝ} (hy : 1 ≤ y) (hC : 1 ≤ C)
    (hA : A < C ^ k) (hA' : 2 * A < C ^ (k - 1))
    (hsize : ∀ i ∈ S, (n i : ℝ) ≤ A * y ^ k)
    (hlower : ((k : ℝ) - 1) * S.card * Real.log y - E ≤
      ∑ i ∈ S, Real.log (roughPart (n i) (C * y) : ℕ))
    (herror : E ≤ ((S.filter (fun i => 0 < dyadicDivisorCount (n i) y)).card : ℝ) * Real.log y /
        2) :
    y * Real.exp (((S.filter (fun i => 0 < dyadicDivisorCount (n i) y)).card : ℝ) *
      Real.log y / (2 * (((k : ℝ) - 1) * S.card))) ≤
        (Nat.maxPrimeFac (∏ i ∈ S, (n i : ℕ)) : ℝ) := by
  have hP : 1 ≤ Nat.maxPrimeFac (∏ i ∈ S, (n i : ℕ)) :=
    Nat.one_le_maxPrimeFac_iff.mpr (Nat.pos_of_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i _ => (n
        i).ne_zero)))
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hcard : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  apply exp_gain_of_logMass_bounds (by
    exact_mod_cast hP) hy (mul_pos (by linarith) hcard) (by positivity) _
    hlower (roughPart_logMass_le_divisorHits S n hk hy hC hA hA' hsize) herror
  have HH : ((S.filter (fun i => 0 < dyadicDivisorCount (n i) y)).card : ℝ) ≤ S.card := by
    exact_mod_cast card_filter_le S (fun i => 0 < dyadicDivisorCount (n i) y)
  nlinarith

end NairTenenbaum
