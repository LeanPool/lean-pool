/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Log.Witness.TupleSeed
public import Mathlib.RingTheory.LaurentSeries

import LeanPool.HyperellipticCurves.ForMathlib.PowerSeriesField
import LeanPool.HyperellipticCurves.Series.HenselRoot

/-!
# Curve points escaping to infinity

Points of the curve `y² = f(x)` over the Laurent series field `K⸨s⸩` with `x = s^(-2n)`:
writing `N = 2g + 1`, the curve equation reads `y² = s^(-2Nn) · f*(s^(2n))`, where `f*` is
the reversed curve polynomial (`Polynomial.reverse`, and `Polynomial.eval₂_reverse_mul_pow`
is the identity used); its value at `s^(2n)` is a power series with constant term `1`,
hence a square (`ChabautyColeman.exists_sq_eq_of_sub_one_mem`), so
`y = s^(-Nn) · √(f*(s^(2n)))` (`ChabautyColeman.exists_infinityPoint`) — Hensel's lemma is
all it takes.

These are the points at which the cusp-descent engine evaluates the fold conditions
(blueprint `lem:cusp-descent`): `ChabautyColeman.aeval_family_ne_zero`
(`LeanPool.HyperellipticCurves.Log.Fold.FoldDescent`) instantiates the all-at-infinity family at the
common
descent rates from `exists_infinityPoint`, and `LeanPool.HyperellipticCurves.Log.Fold.FoldWitness`
turns the
resulting nonvanishing into the all-genus fold witness.
-/

@[expose] public section

open Polynomial IsLocalRing

namespace ChabautyColeman

universe u

variable {K : Type u} [Field K] {f : K[X]} {g : ℕ}

/-! ### The points escaping to infinity -/

/-- The constant term of a polynomial substituted into a positive power of `X`. -/
theorem constantCoeff_aeval_X_pow {R : Type*} [CommSemiring R] {m : ℕ} (hm : m ≠ 0) (p : R[X]) :
    PowerSeries.constantCoeff (aeval (PowerSeries.X ^ m : PowerSeries R) p) = p.coeff 0 := by
  rw [aeval_def, hom_eval₂, PowerSeries.algebraMap_eq, PowerSeries.constantCoeff_comp_C,
    map_pow, PowerSeries.constantCoeff_X, zero_pow hm, eval₂_id, ← coeff_zero_eq_eval_zero]

/-- Substituting a power of the uniformizer into a polynomial commutes with the embedding of
power series into Laurent series. -/
theorem ofPowerSeries_aeval_X_pow {R : Type*} [CommSemiring R] (p : R[X]) (m : ℕ) :
    HahnSeries.ofPowerSeries ℤ R (aeval (PowerSeries.X ^ m : PowerSeries R) p)
      = aeval (HahnSeries.single (m : ℤ) (1 : R)) p := by
  have hcomp : (HahnSeries.ofPowerSeries ℤ R).comp (algebraMap R (PowerSeries R))
      = algebraMap R (LaurentSeries R) :=
    RingHom.ext fun a ↦ (HahnSeries.algebraMap_apply' ℤ a).symm
  rw [aeval_def, hom_eval₂, hcomp, HahnSeries.ofPowerSeries_X_pow, aeval_def]

/-- Power-series images in the Laurent series have nonnegative order. -/
theorem zero_le_orderTop_ofPowerSeries {R : Type*} [Semiring R] (e : PowerSeries R) :
    0 ≤ (HahnSeries.ofPowerSeries ℤ R e).orderTop := by
  refine HahnSeries.le_orderTop_iff_forall.mpr fun j hj ↦ ?_
  have hj0 : j < 0 := mod_cast hj
  rw [HahnSeries.ofPowerSeries_apply]
  exact HahnSeries.embDomain_of_notMem_range fun ⟨m, hm⟩ ↦ by
    rw [show (Nat.castOrderEmbedding m : ℤ) = (m : ℤ) from rfl] at hm
    lia

/-- **A point of the curve escaping to infinity at rate `n`**: over `K⸨s⸩` the curve
`y ^ 2 = f x` has a point with `x = s ^ (-2n)`. Its `y`-coordinate is `s ^ (-n · deg f)` times
the Hensel square root of the reversed curve polynomial at `s ^ (2n)`, which has constant
term `1` because `f` is monic; the last clause records that this square root is
`1 + O(s ^ (2n))`. -/
theorem exists_infinityPoint (hf : f.Monic) (h2 : (2 : K) ≠ 0) {n : ℕ} (hn : n ≠ 0) :
    ∃ y : LaurentSeries K, y ≠ 0
      ∧ y ^ 2 = aeval (HahnSeries.single (-2 * n : ℤ) (1 : K)) f
      ∧ ((2 * n : ℤ) : WithTop ℤ) ≤
        (HahnSeries.single (f.natDegree * n : ℤ) 1 * y - 1).orderTop := by
  have h2' : IsUnit (2 : PowerSeries K) := by
    rw [← map_ofNat (PowerSeries.C (R := K)) 2]
    exact (isUnit_iff_ne_zero.mpr h2).map _
  set N := f.natDegree with hN
  set c : PowerSeries K := aeval (PowerSeries.X ^ (2 * n)) f.reverse with hc
  have hcc : PowerSeries.constantCoeff c = 1 := by
    rw [hc, constantCoeff_aeval_X_pow (by lia), coeff_zero_reverse, hf.leadingCoeff]
  obtain ⟨d, hd, hd1⟩ := exists_sq_eq_of_sub_one_mem h2' (c := c) (by
    rw [PowerSeries.maximalIdeal_eq_span_X, Ideal.mem_span_singleton, PowerSeries.X_dvd_iff,
      map_sub, hcc, map_one, sub_self])
  have hd0 : d ≠ 0 := by
    intro h0
    rw [PowerSeries.maximalIdeal_eq_span_X, Ideal.mem_span_singleton, PowerSeries.X_dvd_iff,
      h0] at hd1
    simp at hd1
  -- the reversed curve polynomial at `s ^ (2n)`, seen in `K⸨s⸩`
  have hcmap : HahnSeries.ofPowerSeries ℤ K c
      = aeval (HahnSeries.single (2 * n : ℤ) (1 : K)) f.reverse := by
    rw [hc, ofPowerSeries_aeval_X_pow]
    push_cast
    rfl
  refine ⟨HahnSeries.single (-(N * n) : ℤ) 1 * HahnSeries.ofPowerSeries ℤ K d, ?_, ?_, ?_⟩
  · refine mul_ne_zero (fun h0 ↦ ?_) fun h0 ↦ hd0 (HahnSeries.ofPowerSeries_injective (Γ := ℤ) ?_)
    · simpa using congrArg (fun z : LaurentSeries K ↦ z.coeff (-(N * n) : ℤ)) h0
    · rw [h0, map_zero]
  · let : Invertible (HahnSeries.single (-2 * n : ℤ) (1 : K)) :=
      ⟨HahnSeries.single (2 * n : ℤ) 1, by rw [HahnSeries.single_mul_single]; norm_num,
        by rw [HahnSeries.single_mul_single]; norm_num⟩
    have hrev := eval₂_reverse_mul_pow (algebraMap K (LaurentSeries K))
      (HahnSeries.single (-2 * n : ℤ) (1 : K)) f
    rw [← aeval_def, ← aeval_def, invOf_eq_right_inv
      (show HahnSeries.single (-2 * n : ℤ) (1 : K) * HahnSeries.single (2 * n : ℤ) 1 = 1 by
        rw [HahnSeries.single_mul_single]; norm_num), ← hcmap, ← hN] at hrev
    rw [← hrev, mul_pow, HahnSeries.single_pow, ← map_pow, hd, HahnSeries.single_pow, one_pow,
      one_pow, show (2 : ℕ) • (-(N * n) : ℤ) = N • (-2 * n : ℤ) by ring]
    ring
  · -- the square root is `1 + O(s ^ (2n))`
    have hsingle : HahnSeries.single (N * n : ℤ) (1 : K)
        * (HahnSeries.single (-(N * n) : ℤ) 1 * HahnSeries.ofPowerSeries ℤ K d)
        = HahnSeries.ofPowerSeries ℤ K d := by
      rw [← mul_assoc, HahnSeries.single_mul_single]
      norm_num
    rw [hsingle]
    -- `X ^ (2n)` divides `c - 1`
    obtain ⟨q, hq⟩ : (Polynomial.X : K[X]) ∣ f.reverse - Polynomial.C 1 := by
      simpa [coeff_zero_reverse, hf.leadingCoeff] using
        Polynomial.X_dvd_sub_C (p := f.reverse)
    have hcdvd : (PowerSeries.X : PowerSeries K) ^ (2 * n) ∣ c - 1 := by
      refine ⟨aeval (PowerSeries.X ^ (2 * n)) q, ?_⟩
      have := congrArg (aeval (PowerSeries.X ^ (2 * n) : PowerSeries K)) hq
      simpa [hc, ← map_pow] using this
    -- hence `X ^ (2n)` divides `d - 1`, since `d + 1` is a unit
    have hdunit : IsUnit (d + 1) := by
      rw [PowerSeries.isUnit_iff_constantCoeff]
      have hdc : PowerSeries.constantCoeff d = 1 := by
        have := (PowerSeries.X_dvd_iff.mp
          (Ideal.mem_span_singleton.mp (PowerSeries.maximalIdeal_eq_span_X (k := K) ▸ hd1)))
        rwa [map_sub, map_one, sub_eq_zero] at this
      rw [map_add, hdc, map_one, one_add_one_eq_two]
      exact isUnit_iff_ne_zero.mpr h2
    have hddvd : (PowerSeries.X : PowerSeries K) ^ (2 * n) ∣ d - 1 := by
      refine (IsUnit.dvd_mul_right hdunit).mp ?_
      have hfac : (d - 1) * (d + 1) = c - 1 := by linear_combination hd
      rwa [hfac]
    obtain ⟨e, he⟩ := hddvd
    have himg : HahnSeries.ofPowerSeries ℤ K d - 1
        = HahnSeries.single (2 * n : ℤ) 1 * HahnSeries.ofPowerSeries ℤ K e := by
      have hXpow : HahnSeries.ofPowerSeries ℤ K (PowerSeries.X ^ (2 * n))
          = HahnSeries.single (2 * n : ℤ) 1 := by simp
      rw [← hXpow, ← map_mul, ← he]
      simp
    rw [himg, HahnSeries.orderTop_mul, HahnSeries.orderTop_single one_ne_zero]
    exact le_add_of_nonneg_right (zero_le_orderTop_ofPowerSeries e)

end ChabautyColeman

end
