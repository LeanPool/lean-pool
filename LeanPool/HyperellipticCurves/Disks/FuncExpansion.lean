/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Disks.OmegaExpansion
public import LeanPool.HyperellipticCurves.Disks.OrdMatch

import LeanPool.HyperellipticCurves.ForMathlib.Polynomial
import LeanPool.HyperellipticCurves.ForMathlib.PowerSeries

/-!
# Expansion of a function on a residue disk

Toward `thm:spec`: the expansion on a residue disk of a *function* `P + Q·y` (as opposed to the
differential `h dx/y` of `LeanPool.HyperellipticCurves.Disks.OmegaExpansion`). On the generic disk
at
`(a, b)` the coordinate
substitution `x = a + z`, `y = b·η(z)` (`η = diskSeriesGeneric f a`) turns `P + Q·y` into the power
series `funcExpansionGeneric = P(a+z) + Q(a+z)·b·η(z)` over `O`.

Reduction commutes with this expansion (`map_funcExpansionGeneric`), so the reduced series is the
residue-curve local expansion of the reduced function — the analytic side of the specialization of
a principal divisor. The reduction relies on `map_sqrtSeries` (a ring hom commutes with the
square-root recursion) and `map_diskSeriesGeneric`.
-/

@[expose] public section

open Polynomial PowerSeries Finset

namespace ChabautyColeman

variable {O κ : Type*} [CommRing O] [CommRing κ]

/-! ### Reduction commutes with the square-root series -/

/-- A ring hom commutes with the square-root recursion `sqrtAux`. -/
theorem map_sqrtAux (ρ : O →+* κ) (c : O⟦X⟧) (a₀ v : O) (n : ℕ) :
    ρ (sqrtAux c a₀ v n) = sqrtAux ((PowerSeries.map ρ) c) (ρ a₀) (ρ v) n := by
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    obtain _ | m := n
    · rw [sqrtAux_zero, sqrtAux_zero]
    · rw [sqrtAux_succ, sqrtAux_succ, map_mul, map_sub, ← PowerSeries.coeff_map]
      congr 2
      rw [map_sum]
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      by_cases hlt : x.1 < m + 1 ∧ x.2 < m + 1
      · rw [dite_eq_left hlt, dite_eq_left hlt, map_mul, IH x.1 hlt.1, IH x.2 hlt.2]
      · rw [dite_eq_right hlt, dite_eq_right hlt, map_zero]

theorem map_sqrtSeries (ρ : O →+* κ) (c : O⟦X⟧) (a₀ v : O) :
    (PowerSeries.map ρ) (sqrtSeries c a₀ v) = sqrtSeries ((PowerSeries.map ρ) c) (ρ a₀) (ρ v) := by
  ext n
  rw [PowerSeries.coeff_map, coeff_sqrtSeries, coeff_sqrtSeries, map_sqrtAux]

theorem map_diskSeriesGeneric (ρ : O →+* κ) (f : O[X]) (a : O) (hfa : IsUnit (f.eval a))
    (h2 : IsUnit (2 : O)) :
    (PowerSeries.map ρ) (diskSeriesGeneric f a) = diskSeriesGeneric (f.map ρ) (ρ a) := by
  rw [diskSeriesGeneric, map_sqrtSeries, diskSeriesGeneric, map_mul, ← polynomial_map_coe,
    map_taylor, PowerSeries.map_C, hfa.map_ringInverse ρ, map_one, h2.map_ringInverse ρ, map_ofNat,
    eval_map_apply]

/-! ### The generic-disk function expansion -/

/-- The generic-disk expansion of the function `P + Q·y` at `(a, b)`: the power series
`N(z) = P(a+z) + Q(a+z)·b·η(z)` over `O`, where `η = diskSeriesGeneric f a` (so on the disk
`x = a + z` and `y = b·η(z)`). -/
noncomputable def funcExpansionGeneric (f P Q : O[X]) (a b : O) : O⟦X⟧ :=
  (taylor a P : O⟦X⟧) + (taylor a Q : O⟦X⟧) * PowerSeries.C b * diskSeriesGeneric f a

@[simp] theorem constantCoeff_funcExpansionGeneric (f P Q : O[X]) (a b : O) :
    constantCoeff (funcExpansionGeneric f P Q a b) = P.eval a + Q.eval a * b := by
  rw [funcExpansionGeneric, map_add, map_mul, map_mul, constantCoeff_diskSeriesGeneric,
    ← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply,
    Polynomial.coeff_coe, Polynomial.coeff_coe, taylor_coeff_zero, taylor_coeff_zero,
    constantCoeff_C]
  ring

/-- Reduction commutes with the generic function expansion: the reduced series is the residue-curve
local expansion of the reduced function `P_bar + Q_bar·y`. -/
theorem map_funcExpansionGeneric (ρ : O →+* κ) (f P Q : O[X]) (a b : O) (hfa : IsUnit (f.eval a))
    (h2 : IsUnit (2 : O)) :
    (PowerSeries.map ρ) (funcExpansionGeneric f P Q a b)
      = funcExpansionGeneric (f.map ρ) (P.map ρ) (Q.map ρ) (ρ a) (ρ b) := by
  rw [funcExpansionGeneric, funcExpansionGeneric, map_add, map_mul, map_mul,
    ← polynomial_map_coe, ← polynomial_map_coe, map_taylor, map_taylor, PowerSeries.map_C,
    map_diskSeriesGeneric ρ f a hfa h2]

/-! ### The Weierstrass-disk function expansion -/

/-- The Weierstrass-disk expansion of the function `P + Q·y` at `(ω, 0)`: the power series
`P(x(z)) + Q(x(z))·z`, where `x(z) = weierstrassSeries` is the coordinate series and `z = y`
is the disk parameter. -/
noncomputable def funcExpansionWeierstrass (P Q : O[X]) {f : O[X]} (hf : f.Monic)
    (hdeg : 0 < f.natDegree) {ω : O} (hω : f.eval ω = 0) (hu : IsUnit (f.derivative.eval ω)) :
    O⟦X⟧ :=
  aeval (weierstrassSeries hf hdeg hω hu) P
    + aeval (weierstrassSeries hf hdeg hω hu) Q * PowerSeries.X

@[simp] theorem constantCoeff_funcExpansionWeierstrass (P Q : O[X]) {f : O[X]} (hf : f.Monic)
    (hdeg : 0 < f.natDegree) {ω : O} (hω : f.eval ω = 0) (hu : IsUnit (f.derivative.eval ω)) :
    constantCoeff (funcExpansionWeierstrass P Q hf hdeg hω hu) = P.eval ω := by
  rw [funcExpansionWeierstrass, map_add, map_mul, PowerSeries.constantCoeff_aeval,
    constantCoeff_weierstrassSeries,
    PowerSeries.constantCoeff_X, mul_zero, add_zero]

/-! ### Order matching for the generic function expansion

The reduced generic expansion is a *sum*, so — unlike the differential case — its order is not a
single root multiplicity. The order is pinned down via the **conjugate**: the product of the
expansion of `P + Q·y` and of `P - Q·y` is the taylor series of the norm polynomial `P² - f·Q²`
(`funcExpansionGeneric_mul_conj`), so the two orders sum to `rootMult` of the reduced norm
(`order_map_funcExpansionGeneric_add_conj`). When the conjugate does not vanish at the point (the
generic one-branch case) the order of `P + Q·y` is exactly that root multiplicity. -/

/-- `η² = f(a+z)/f(a)` for the generic parametrizing series. -/
theorem diskSeriesGeneric_sq {f : O[X]} {a : O} (hfa : IsUnit (f.eval a)) (h2 : IsUnit (2 : O)) :
    (diskSeriesGeneric f a) ^ 2
      = (taylor a f : O⟦X⟧) * PowerSeries.C (Ring.inverse (f.eval a)) := by
  apply sqrtSeries_sq
  · rw [one_pow, map_mul, ← coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe,
      taylor_coeff_zero, constantCoeff_C, Ring.mul_inverse_cancel _ hfa]
  · rw [mul_one, Ring.mul_inverse_cancel 2 h2]

/-- Derivative of the generic parametrizing series, in cross-multiplied (denominator-free)
form: `2·η·η′·f(a) = (f')(a+z)`, by differentiating `η² = f(a+z)/f(a)`. -/
theorem two_mul_diskSeriesGeneric_mul_derivative {f : O[X]} {a : O}
    (hfa : IsUnit (f.eval a)) (h2 : IsUnit (2 : O)) :
    2 * diskSeriesGeneric f a * PowerSeries.derivative (diskSeriesGeneric f a)
        * PowerSeries.C (f.eval a)
      = (taylor a f.derivative : O⟦X⟧) := by
  have h := congrArg (PowerSeries.derivative) (diskSeriesGeneric_sq hfa h2)
  rw [Derivation.leibniz_pow, Derivation.leibniz, PowerSeries.derivative_C, smul_zero,
    zero_add, PowerSeries.derivative_coe, derivative_taylor] at h
  have hcancel : (PowerSeries.C (Ring.inverse (f.eval a)) : O⟦X⟧)
      * PowerSeries.C (f.eval a) = 1 := by
    rw [← map_mul, Ring.inverse_mul_cancel _ hfa, map_one]
  calc 2 * diskSeriesGeneric f a * PowerSeries.derivative (diskSeriesGeneric f a)
        * PowerSeries.C (f.eval a)
      = ((2 : ℕ) • (diskSeriesGeneric f a) ^ (2 - 1)
          • PowerSeries.derivative (diskSeriesGeneric f a)) * PowerSeries.C (f.eval a) := by
        simp only [smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat]
        ring
    _ = (PowerSeries.C (Ring.inverse (f.eval a)) • (taylor a f.derivative : O⟦X⟧))
          * PowerSeries.C (f.eval a) := by rw [h]
    _ = (taylor a f.derivative : O⟦X⟧)
          * (PowerSeries.C (Ring.inverse (f.eval a)) * PowerSeries.C (f.eval a)) := by
        rw [smul_eq_mul]
        ring
    _ = (taylor a f.derivative : O⟦X⟧) := by rw [hcancel, mul_one]

/-- The generic function expansion times its conjugate is the taylor series of the norm
polynomial `P² - f·Q²`. -/
theorem funcExpansionGeneric_mul_conj {f : O[X]} (P Q : O[X]) {a b : O} (hb : b ^ 2 = f.eval a)
    (hfa : IsUnit (f.eval a)) (h2 : IsUnit (2 : O)) :
    funcExpansionGeneric f P Q a b * funcExpansionGeneric f P (-Q) a b
      = (taylor a (P ^ 2 - f * Q ^ 2) : O⟦X⟧) := by
  have hη := diskSeriesGeneric_sq (f := f) (a := a) hfa h2
  have hbfa : (PowerSeries.C b : O⟦X⟧) ^ 2 * PowerSeries.C (Ring.inverse (f.eval a)) = 1 := by
    rw [← map_pow, ← map_mul, hb, Ring.mul_inverse_cancel _ hfa, map_one]
  have hpoly : taylor a (P ^ 2 - f * Q ^ 2) = (taylor a P) ^ 2 - taylor a f * (taylor a Q) ^ 2 := by
    rw [map_sub, taylor_mul, taylor_pow, taylor_pow]
  rw [funcExpansionGeneric, funcExpansionGeneric, map_neg, Polynomial.coe_neg, hpoly,
    Polynomial.coe_sub, Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_pow]
  linear_combination (-(taylor a Q : O⟦X⟧) ^ 2 * PowerSeries.C b ^ 2) * hη +
    (-(taylor a Q : O⟦X⟧) ^ 2 * (taylor a f : O⟦X⟧)) * hbfa

section

open IsLocalRing

variable [IsLocalRing O]

/-- The reduced generic function expansion is a unit (order `0`) iff the function `P + Q·y` does
not vanish at the reduced point `(ā, b_bar)`. -/
theorem order_map_funcExpansionGeneric_eq_zero_iff (f P Q : O[X]) (a b : O) :
    ((funcExpansionGeneric f P Q a b).map (residue O)).order = 0
      ↔ residue O (P.eval a + Q.eval a * b) ≠ 0 := by
  have hcc : constantCoeff ((funcExpansionGeneric f P Q a b).map (residue O))
      = residue O (P.eval a + Q.eval a * b) := by
    rw [PowerSeries.constantCoeff_map, constantCoeff_funcExpansionGeneric]
  rw [← hcc, ne_eq, ← order_ne_zero_iff_constCoeff_eq_zero, not_ne_iff]

/-- **Norm decomposition of the order.** The orders of the reduced function expansion and its
conjugate sum to the root multiplicity of the reduced norm polynomial `P² - f·Q²`. -/
theorem order_map_funcExpansionGeneric_add_conj {f : O[X]} (P Q : O[X]) {a b : O}
    (hb : b ^ 2 = f.eval a) (hfa : IsUnit (f.eval a)) (h2 : IsUnit (2 : O))
    (hN : (P ^ 2 - f * Q ^ 2).map (residue O) ≠ 0) :
    ((funcExpansionGeneric f P Q a b).map (residue O)).order
        + ((funcExpansionGeneric f P (-Q) a b).map (residue O)).order
      = ((P ^ 2 - f * Q ^ 2).map (residue O)).rootMultiplicity (residue O a) := by
  rw [← order_mul, ← map_mul, funcExpansionGeneric_mul_conj P Q hb hfa h2,
    ← polynomial_map_coe, map_taylor, PSeries.order_coe_taylor hN]

/-- **Order matching, generic chart (one-branch case).** If the conjugate function `P - Q·y` does
not vanish at `(ā, b_bar)`, the order of the reduced expansion of `P + Q·y` is the root multiplicity
of
the reduced norm polynomial. -/
theorem order_map_funcExpansionGeneric {f : O[X]} (P Q : O[X]) {a b : O} (hb : b ^ 2 = f.eval a)
    (hfa : IsUnit (f.eval a)) (h2 : IsUnit (2 : O))
    (hN : (P ^ 2 - f * Q ^ 2).map (residue O) ≠ 0)
    (hconj : residue O (P.eval a - Q.eval a * b) ≠ 0) :
    ((funcExpansionGeneric f P Q a b).map (residue O)).order
      = ((P ^ 2 - f * Q ^ 2).map (residue O)).rootMultiplicity (residue O a) := by
  have h0 : ((funcExpansionGeneric f P (-Q) a b).map (residue O)).order = 0 := by
    rwa [order_map_funcExpansionGeneric_eq_zero_iff, eval_neg, neg_mul, ← sub_eq_add_neg]
  rw [← order_map_funcExpansionGeneric_add_conj P Q hb hfa h2 hN, h0, add_zero]

end

/-! ### Order matching for the Weierstrass function expansion

At a Weierstrass point the two conjugate branches coincide (the point equals its conjugate), so —
unlike the generic chart — the individual order is not separated by a one-branch argument; the clean
statement is the norm decomposition, whose right-hand side carries the factor `2` (`x - ω` has a
double zero). -/

/-- The Weierstrass function expansion times its conjugate is `aeval x(z) (P² - f·Q²)` (using
`z² = f(x(z))`, i.e. `weierstrassSeries_eval`). -/
theorem funcExpansionWeierstrass_mul_conj (P Q : O[X]) {f : O[X]} (hf : f.Monic)
    (hdeg : 0 < f.natDegree) {ω : O} (hω : f.eval ω = 0) (hu : IsUnit (f.derivative.eval ω)) :
    funcExpansionWeierstrass P Q hf hdeg hω hu * funcExpansionWeierstrass P (-Q) hf hdeg hω hu
      = aeval (weierstrassSeries hf hdeg hω hu) (P ^ 2 - f * Q ^ 2) := by
  rw [funcExpansionWeierstrass, funcExpansionWeierstrass, map_neg, map_sub, map_mul, map_pow,
    map_pow, weierstrassSeries_eval]
  ring

section

open IsLocalRing

variable [IsLocalRing O]

/-- The reduced Weierstrass function expansion is a unit (order `0`) iff `P + Q·y` does not vanish
at `(ω, 0)`, i.e. `P(ω) ≠ 0`. -/
theorem order_map_funcExpansionWeierstrass_eq_zero_iff (P Q : O[X]) {f : O[X]} (hf : f.Monic)
    (hdeg : 0 < f.natDegree) {ω : O} (hω : f.eval ω = 0) (hu : IsUnit (f.derivative.eval ω)) :
    ((funcExpansionWeierstrass P Q hf hdeg hω hu).map (residue O)).order = 0
      ↔ residue O (P.eval ω) ≠ 0 := by
  have hcc : constantCoeff ((funcExpansionWeierstrass P Q hf hdeg hω hu).map (residue O))
      = residue O (P.eval ω) := by
    rw [PowerSeries.constantCoeff_map, constantCoeff_funcExpansionWeierstrass]
  rw [← hcc, ne_eq, ← order_ne_zero_iff_constCoeff_eq_zero, not_ne_iff]

/-- **Norm decomposition of the order (Weierstrass chart).** The orders of the reduced function
expansion and its conjugate sum to `2·rootMult` of the reduced norm polynomial. -/
theorem order_map_funcExpansionWeierstrass_add_conj (P Q : O[X]) {f : O[X]} (hf : f.Monic)
    (hdeg : 0 < f.natDegree) {ω : O} (hω : f.eval ω = 0) (hu : IsUnit (f.derivative.eval ω))
    (hN : (P ^ 2 - f * Q ^ 2).map (residue O) ≠ 0) :
    ((funcExpansionWeierstrass P Q hf hdeg hω hu).map (residue O)).order
        + ((funcExpansionWeierstrass P (-Q) hf hdeg hω hu).map (residue O)).order
      = ((P ^ 2 - f * Q ^ 2).map (residue O)).rootMultiplicity (residue O ω) • (2 : ℕ∞) := by
  set ρ := residue O
  set ws := weierstrassSeries hf hdeg hω hu with hws
  have hsc : constantCoeff ((PowerSeries.map ρ) ws) = ρ ω := by simp [hws]
  have hord2 : ((PowerSeries.map ρ) ws - PowerSeries.C (ρ ω)).order = 2 :=
    order_map_weierstrassSeries_sub_C hf hdeg hω hu
  rw [← order_mul, ← map_mul, funcExpansionWeierstrass_mul_conj, PowerSeries.map_aeval,
    order_aeval_of_order_sub hsc hN, hord2]

end

end ChabautyColeman
