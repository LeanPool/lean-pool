/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.ForMathlib.Polynomial
public import LeanPool.HyperellipticCurves.ForMathlib.PowerSeries
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Reflection at the infinity disk: evaluation at the pole coordinate

On the residue disk around infinity the coordinate `x` becomes `1/u(z)`, for the pole
coordinate `u` solving `u = z²·F(u)`, `F = reverse f`. Since `x` has a pole at `z = 0`, its
values live in the fraction field `Frac(K⟦z⟧)` from the start, and this file proves the two
facts that control them: the solution `u` is nonzero with vanishing constant coefficient
(`ChabautyColeman.ne_zero_of_eq_X_sq_mul`), and `p ↦ p(1/u)` kills no nonzero polynomial
(`ChabautyColeman.aeval_inv_eq_zero_iff`).

Injectivity is by **reflection**: clearing denominators turns the value into
`(reflect (deg p) p)(u)` (`Polynomial.eval₂_reflect_eq_zero_iff`), whose constant
coefficient is the leading one of `p`, and evaluation at a series with vanishing constant
coefficient detects the constant coefficient
(`ChabautyColeman.aeval_ne_zero_of_coeff_zero_ne_zero`).

The evaluation homomorphisms assembled from these facts — `ChabautyColeman.invAevalFracHom`,
`ChabautyColeman.invAevalRatFuncHom`, the square certificate
`ChabautyColeman.sq_inv_pow_mul_X` and the expansion homomorphism
`ChabautyColeman.inftyExpand` — live in `upstream HyperellipticCurves.Archive.InftyExpand`.

The lemmas are stated for an abstract solution `u` of `u = z²·F(u)` over `K`; the
application takes `u := PowerSeries.map ψ (infSeries hf)`.

Blueprint node: `thm:omega-prime-global`, clause (c) (infinity transport).
-/

@[expose] public section

open Polynomial PowerSeries

namespace ChabautyColeman

section InftyExpandHom

variable {K : Type*} [Field K] {fK : K[X]} {u : K⟦X⟧} {g : ℕ}

/-- Evaluation at a series with vanishing constant coefficient detects the constant
coefficient. -/
theorem aeval_ne_zero_of_coeff_zero_ne_zero (hu0 : PowerSeries.constantCoeff u = 0) {q : K[X]}
    (hq : q.coeff 0 ≠ 0) : aeval u q ≠ 0 := fun h ↦ hq (by
  have hc := congrArg PowerSeries.constantCoeff h
  rwa [PowerSeries.constantCoeff_aeval, hu0, map_zero, ← Polynomial.coeff_zero_eq_eval_zero] at hc)

/-- The solution of `u = z²·F(u)`, `F = reverse fK`, is a nonzero series with vanishing
constant coefficient: its coefficient at `z²` is the reverse's constant one, the leading
coefficient of the monic `fK`. -/
theorem ne_zero_of_eq_X_sq_mul (hfKm : fK.Monic)
    (hueq : u = PowerSeries.X ^ 2 * aeval u fK.reverse) :
    PowerSeries.constantCoeff u = 0 ∧ u ≠ 0 := by
  have hu0 : PowerSeries.constantCoeff u = 0 := by
    rw [hueq, map_mul, map_pow, constantCoeff_X]
    ring
  refine ⟨hu0, fun h0 ↦ ?_⟩
  rw [h0] at hueq
  have hzero : aeval (0 : K⟦X⟧) fK.reverse = 0 :=
    (mul_eq_zero.mp hueq.symm).resolve_left (pow_ne_zero 2 PowerSeries.X_ne_zero)
  have hc := congrArg PowerSeries.constantCoeff hzero
  rw [PowerSeries.constantCoeff_aeval, map_zero, ← Polynomial.coeff_zero_eq_eval_zero,
    coeff_zero_reverse, hfKm.leadingCoeff] at hc
  exact one_ne_zero hc

/-- **Evaluation at `1/u(z)` is injective on `K[X]`**: clearing denominators reflects the
polynomial, and evaluation at `u` detects the reflected constant coefficient — the leading
one of `p`. -/
theorem aeval_inv_eq_zero_iff (hfKm : fK.Monic)
    (hueq : u = PowerSeries.X ^ 2 * aeval u fK.reverse) {p : K[X]} :
    aeval ((algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) u)⁻¹) p = 0
      ↔ p = 0 := by
  obtain ⟨hu0, hune⟩ := ne_zero_of_eq_X_sq_mul hfKm hueq
  have hxne : algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) u ≠ 0 := fun h ↦
    hune (IsFractionRing.injective (PowerSeries K) (FractionRing (PowerSeries K))
      (by rw [h, map_zero]))
  refine ⟨fun hp ↦ ?_, fun hp ↦ by rw [hp, map_zero]⟩
  by_contra hp0
  let : Invertible (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) u) :=
    invertibleOfNonzero hxne
  have hiff := eval₂_reflect_eq_zero_iff (algebraMap K (FractionRing (PowerSeries K)))
    (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) u) p.natDegree
    (p.reflect p.natDegree) (natDegree_reflect_le.trans (by simp))
  rw [reflect_reflect] at hiff
  have h1 : Polynomial.eval₂ (algebraMap K (FractionRing (PowerSeries K)))
      (⅟(algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) u)) p = 0 := by
    rwa [invOf_eq_inv, ← Polynomial.aeval_def]
  have h2 := hiff.mp h1
  have h3 : Polynomial.eval₂ (algebraMap K (FractionRing (PowerSeries K)))
      (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) u) (p.reflect p.natDegree)
      = algebraMap (PowerSeries K) (FractionRing (PowerSeries K))
        (aeval u (p.reflect p.natDegree)) :=
    (aeval_def _ _).symm.trans (aeval_algebraMap_apply _ u (p.reflect p.natDegree))
  rw [h3] at h2
  refine aeval_ne_zero_of_coeff_zero_ne_zero hu0 (q := p.reflect p.natDegree) ?_
    (IsFractionRing.injective (PowerSeries K) (FractionRing (PowerSeries K))
      (by rw [h2, map_zero]))
  rw [coeff_reflect, revAt_le (Nat.zero_le _), Nat.sub_zero]
  exact fun h ↦ hp0 (leadingCoeff_eq_zero.mp h)

end InftyExpandHom

end ChabautyColeman

end
