/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Curve.HypRing
public import LeanPool.HyperellipticCurves.ForMathlib.Separable
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Defs

import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# The coordinate ring as integral closure, and the Dedekind property

For squarefree `f` (and `2 ≠ 0` in `K`), an element `a + b·y` of `F_K = K(x)[Y]/(Y² - f)`
is integral over `K[x]` if and only if `a` and `b` are polynomials, i.e. iff it lies in
the image of the coordinate ring `A_K` (`ChabautyColeman.HypField.isIntegral_iff`).
Consequently `A_K` is the integral closure of `K[x]` in `F_K`
(`ChabautyColeman.HypRing.instIsIntegralClosure`), and — `F_K/K(x)` being separable of
degree 2 — a Dedekind domain (`ChabautyColeman.HypRing.instIsDedekindDomain`); freeness
over `K[x]` with basis `(1, y)` is definitional in the `QuadraticAlgebra` implementation.

The key computational inputs are `RatFunc.exists_algebraMap_eq_of_sq_mul_squarefree`
and `Algebra.IsSeparable.of_finrank_le_two` from `LeanPool.HyperellipticCurves.ForMathlib`.

Blueprint nodes: `lem:integral-char`, `thm:hypring-dedekind`.
-/

@[expose] public section

open Polynomial


namespace ChabautyColeman

open QuadraticAlgebra

variable {K : Type*} [Field K] {f : K[X]}

namespace HypField

/-- `y` is integral over `K[x]`: it satisfies the monic polynomial `Y² - f`. -/
theorem isIntegral_y : IsIntegral K[X] (y f) := by
  refine ⟨X ^ 2 - C f, monic_X_pow_sub_C f two_ne_zero, ?_⟩
  simp [eval₂_sub, eval₂_pow]

/-- Elements of the coordinate ring are integral over `K[x]`. -/
theorem _root_.ChabautyColeman.HypRing.isIntegral_toHypField (w : HypRing K f) :
    IsIntegral K[X] (HypRing.toHypField f w) := by
  rw [HypRing.toHypField_apply]
  exact isIntegral_algebraMap.add (isIntegral_algebraMap.mul isIntegral_y)

/-- Integral characterization: for `f` squarefree (and `2 ≠ 0` in `K`),
`a + b·y ∈ F_K` is integral over `K[x]` iff `a` and `b` are polynomials,
i.e. iff `a + b·y` lies in the image of the coordinate ring. -/
theorem isIntegral_iff (hf : Squarefree f) (h2 : (2 : K) ≠ 0) {z : HypField K f} :
    IsIntegral K[X] z ↔ z ∈ (HypRing.toHypField f).range := by
  refine ⟨fun hz ↦ ?_, fun ⟨w, hw⟩ ↦ hw ▸ HypRing.isIntegral_toHypField w⟩
  have hzs : IsIntegral K[X] (star z) := by
    simpa using hz.map ((iota f).toAlgHom.restrictScalars K[X])
  -- integral elements of `K(x)` inside `F_K` are polynomials
  have hdesc {r : RatFunc K} (h : IsIntegral K[X] (algebraMap (RatFunc K) (HypField K f) r)) :
      ∃ p : K[X], algebraMap K[X] (RatFunc K) p = r :=
    IsIntegrallyClosed.isIntegral_iff.mp (isIntegral_algebraMap_iff.mp h)
  obtain ⟨p, hp⟩ := hdesc ((algebraMap_trace_eq_add_star z).symm ▸ hz.add hzs)
  rw [trace_def] at hp
  obtain ⟨n, hn⟩ := hdesc (mul_star_eq_norm f z ▸ hz.mul hzs)
  have h2R : (2 : RatFunc K) ≠ 0 := fun h ↦
    h2 ((algebraMap K (RatFunc K)).injective (by rw [map_ofNat, map_zero]; exact h))
  have hre : algebraMap K[X] (RatFunc K) (C (2 : K)⁻¹ * p) = z.re := by
    rw [map_mul, hp, RatFunc.algebraMap_C, map_inv₀, map_ofNat, zero_mul, add_zero,
      inv_mul_cancel_left₀ h2R]
  have him : z.im ^ 2 * algebraMap K[X] (RatFunc K) f =
      algebraMap K[X] _ ((C (2 : K)⁻¹ * p) ^ 2 - n) := by
    rw [map_sub, map_pow, hre, hn, norm_eq]
    ring
  obtain ⟨q, hq⟩ := RatFunc.exists_algebraMap_eq_of_sq_mul_squarefree hf him
  exact ⟨⟨C (2 : K)⁻¹ * p, q⟩, by ext <;> simp [hre, hq]⟩

end HypField

/-! ### The Dedekind property (blueprint node `thm:hypring-dedekind`)

`A_K` is the integral closure of the PID `K[x]` in the finite separable field extension
`F_K/K(x)`, hence a Dedekind domain by `IsIntegralClosure.isDedekindDomain`. The
hypotheses on `f` enter through `Fact` instances, so that everything is available to
instance search; `NeZero (2 : K)` encodes `2 ∈ K^×`.
-/

namespace HypRing

noncomputable instance instAlgebraHypField : Algebra (HypRing K f) (HypField K f) :=
  (toHypField f).toAlgebra

instance instIsScalarTowerHypField : IsScalarTower K[X] (HypRing K f) (HypField K f) :=
  IsScalarTower.of_algebraMap_eq' (toHypField f).comp_algebraMap.symm

/-- The coordinate ring is the integral closure of `K[x]` in `F_K`. -/
instance instIsIntegralClosure [NeZero (2 : K)] [Fact (Squarefree f)] :
    IsIntegralClosure (HypRing K f) K[X] (HypField K f) where
  algebraMap_injective := toHypField_injective f
  isIntegral_iff := HypField.isIntegral_iff Fact.out two_ne_zero

end HypRing

instance HypField.instIsSeparable [NeZero (2 : K)] [Fact (Odd f.natDegree)] :
    Algebra.IsSeparable (RatFunc K) (HypField K f) :=
  .of_finrank_le_two _ _ two_ne_zero (QuadraticAlgebra.finrank_eq_two _ _).le

/-- The coordinate ring of an odd-degree hyperelliptic curve `y² = f(x)` with
squarefree `f` over a field of characteristic ≠ 2 is a Dedekind domain. -/
instance HypRing.instIsDedekindDomain [NeZero (2 : K)] [Fact (Odd f.natDegree)]
    [Fact (Squarefree f)] : IsDedekindDomain (HypRing K f) :=
  IsIntegralClosure.isDedekindDomain K[X] (RatFunc K) (HypField K f) _

/-- The function field `F_K` is the fraction field of the coordinate ring `A_K` (the integral
closure of `K[x]` in `F_K`). -/
instance HypRing.instIsFractionRing [NeZero (2 : K)] [Fact (Odd f.natDegree)]
    [Fact (Squarefree f)] : IsFractionRing (HypRing K f) (HypField K f) :=
  IsIntegralClosure.isFractionRing_of_finite_extension K[X] (RatFunc K) (HypField K f) (HypRing K f)

end ChabautyColeman

end
