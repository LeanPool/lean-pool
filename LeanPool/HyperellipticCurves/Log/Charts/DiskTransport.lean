/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.ForMathlib.FractionRingDerivative
public import LeanPool.HyperellipticCurves.ForMathlib.Polynomial
public import LeanPool.HyperellipticCurves.Log.Analytic.OmegaPrime
public import LeanPool.HyperellipticCurves.Log.Charts.PhiChart

/-!
# Taylor expansion and the `z`-derivative on `Frac(K⟦z⟧)`

The two analytic tools the per-disk trace identity is stated with.

## Main definitions

* `ChabautyColeman.taylorSeriesHom`: Taylor expansion at `a` as a ring homomorphism
  `R[X] →+* R⟦z⟧` (injective, with the expected values on constants and on `X`).
* `ChabautyColeman.kzDeriv`: the `z`-derivative on `Frac(K⟦z⟧)`, the quotient-rule extension
  (`IsFractionRing.deriv`) of the power-series derivative, with its calculus API — additivity,
  the product, quotient and power rules, `aeval` of a polynomial, and inverses.

Both are consumed by the per-disk capstones `LeanPool.HyperellipticCurves.Log.Trace.TraceKz` and its
Weierstrass and infinity mirrors. A function-field route, which expands a *global* chart along a
ring homomorphism `F_K →+* Frac(K⟦z⟧)`, is formalized in `upstream
HyperellipticCurves.Archive.DiskExpand`;
the main theorems do not depend on it.
-/

@[expose] public section

open Polynomial
open scoped PowerSeries

namespace ChabautyColeman

section TaylorSeries

variable {R : Type*} [CommRing R]

/-- The "Taylor expansion at `a`" ring homomorphism `R[X] →+* R⟦X⟧`: shift the variable
by `a` and regard the result as a power series. Sends `p` to `(taylor a p : R⟦X⟧)`. -/
noncomputable def taylorSeriesHom (a : R) : R[X] →+* PowerSeries R :=
  (Polynomial.coeToPowerSeries.ringHom).comp (taylorAlgHom a).toRingHom

theorem taylorSeriesHom_apply (a : R) (p : R[X]) :
    taylorSeriesHom a p = (taylor a p : PowerSeries R) := rfl

theorem taylorSeriesHom_injective (a : R) : Function.Injective (taylorSeriesHom a) :=
  fun _ _ h ↦ taylor_injective a (Polynomial.coe_inj.mp h)

theorem taylorSeriesHom_C (a c : R) :
    taylorSeriesHom a (C c) = PowerSeries.C c := by
  rw [taylorSeriesHom_apply, taylor_C, Polynomial.coe_C]

theorem taylorSeriesHom_X (a : R) :
    taylorSeriesHom a X = PowerSeries.C a + PowerSeries.X := by
  rw [taylorSeriesHom_apply, taylor_X, Polynomial.coe_add, Polynomial.coe_X, Polynomial.coe_C,
    add_comm]

end TaylorSeries

section KzDeriv

variable {K : Type*} [Field K]

variable (K) in
/-- The `z`-derivative on `Frac(K⟦z⟧)`: the quotient-rule extension
(`IsFractionRing.deriv`) of the power-series derivative. -/
noncomputable def kzDeriv : FractionRing (PowerSeries K) → FractionRing (PowerSeries K) :=
  IsFractionRing.deriv fun s : PowerSeries K ↦ PowerSeries.derivative s

theorem kzDeriv_hmul (p q : PowerSeries K) :
    PowerSeries.derivative (p * q)
      = PowerSeries.derivative p * q + p * PowerSeries.derivative q := by
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  ring

theorem kzDeriv_algebraMap (G : PowerSeries K) :
    kzDeriv K (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) G)
      = algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
          (PowerSeries.derivative G) :=
  IsFractionRing.deriv_algebraMap kzDeriv_hmul G

theorem kzDeriv_add (x y : FractionRing (PowerSeries K)) :
    kzDeriv K (x + y) = kzDeriv K x + kzDeriv K y :=
  IsFractionRing.deriv_add (map_add _) kzDeriv_hmul x y

theorem kzDeriv_mul (x y : FractionRing (PowerSeries K)) :
    kzDeriv K (x * y) = kzDeriv K x * y + x * kzDeriv K y :=
  IsFractionRing.deriv_mul kzDeriv_hmul x y

theorem kzDeriv_div (p : PowerSeries K) {q : PowerSeries K} (hq : q ≠ 0) :
    kzDeriv K (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) p
        / algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) q)
      = (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) (PowerSeries.derivative p)
          * algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) q
        - algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) p
          * algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
              (PowerSeries.derivative q))
        / algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) (q ^ 2) :=
  IsFractionRing.deriv_div kzDeriv_hmul p hq

end KzDeriv

section KzDerivMore

variable {K : Type*} [Field K]

theorem kzDeriv_one : kzDeriv K (1 : FractionRing (PowerSeries K)) = 0 := by
  have h := kzDeriv_algebraMap (K := K) 1
  rwa [map_one, Derivation.map_one_eq_zero, map_zero] at h

theorem kzDeriv_pow_succ (x : FractionRing (PowerSeries K)) (n : ℕ) :
    kzDeriv K (x ^ (n + 1)) = (n + 1 : ℕ) * x ^ n * kzDeriv K x := by
  induction n with
  | zero => rw [pow_one, pow_zero]; push_cast; ring
  | succ n ih =>
    rw [pow_succ, kzDeriv_mul, ih, pow_succ]
    push_cast
    ring

theorem kzDeriv_algebraMap_base (a : K) :
    kzDeriv K (algebraMap K (FractionRing (PowerSeries K)) a) = 0 := by
  rw [IsScalarTower.algebraMap_apply K (PowerSeries K) (FractionRing (PowerSeries K)),
    kzDeriv_algebraMap, PowerSeries.algebraMap_eq, PowerSeries.derivative_C, map_zero]

/-- The chain rule for `kzDeriv` through polynomial evaluation. -/
theorem kzDeriv_aeval (x₀ : FractionRing (PowerSeries K)) (p : K[X]) :
    kzDeriv K (aeval x₀ p) = aeval x₀ (Polynomial.derivative p) * kzDeriv K x₀ := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, kzDeriv_add, hp, hq, derivative_add, map_add]; ring
  | monomial n a =>
    rcases n with _ | n
    · rw [monomial_zero_left, aeval_C, kzDeriv_algebraMap_base, derivative_C, map_zero, zero_mul]
    · rw [aeval_monomial, kzDeriv_mul, kzDeriv_algebraMap_base, zero_mul, zero_add,
        kzDeriv_pow_succ, derivative_monomial, aeval_monomial, Nat.add_sub_cancel, map_mul]
      push_cast
      ring

theorem kzDeriv_inv {x : FractionRing (PowerSeries K)} (hx : x ≠ 0) :
    kzDeriv K x⁻¹ = -(x⁻¹ ^ 2) * kzDeriv K x := by
  have h0 := congrArg (kzDeriv K) (inv_mul_cancel₀ hx)
  rw [kzDeriv_mul, kzDeriv_one] at h0
  calc kzDeriv K x⁻¹ = kzDeriv K x⁻¹ * x * x⁻¹ := by
        rw [mul_assoc, mul_inv_cancel₀ hx, mul_one]
    _ = -(x⁻¹ ^ 2) * kzDeriv K x := by
        rw [show kzDeriv K x⁻¹ * x = -(x⁻¹ * kzDeriv K x) by linear_combination h0]
        ring

end KzDerivMore

end ChabautyColeman

end
