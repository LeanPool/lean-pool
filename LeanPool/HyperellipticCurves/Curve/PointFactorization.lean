/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import LeanPool.HyperellipticCurves.Curve.Jacobian
public import LeanPool.HyperellipticCurves.Curve.PointValuation
public import Mathlib.RingTheory.DedekindDomain.Factorization

import LeanPool.HyperellipticCurves.Curve.IntegralClosure
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.Nullstellensatz

/-!
# Point factorization of divisors over an algebraically closed field

Over an algebraically closed field every nonzero prime ideal of the coordinate ring
`HypRing κ f` is a point ideal (`ChabautyColeman.exists_pointIdeal_eq_of_isPrime` — the
Nullstellensatz for the curve, via Zariski's lemma and `IsAlgClosed.lift`), and every principal
ideal of a Dedekind domain factors as the finite product of its height-one primes with
`emultiplicity` exponents (`ChabautyColeman.span_singleton_eq_finprod_heightOneSpectrum`).
Together: the divisor of a function `h_bar` on the reduced curve is the product of the point
ideals of its zeros with the intrinsic multiplicities — the target of the per-disk point sums
(`LeanPool.HyperellipticCurves.Specialization.DiskPointSum`) in the reduction homomorphism
`thm:redJ-hom`.
-/

@[expose] public section

open Polynomial

namespace ChabautyColeman

/-- Nullstellensatz for the coordinate ring: over an algebraically closed field, every nonzero
prime ideal of `HypRing κ f` is a point ideal `(x - x₀, y - y₀)`. -/
theorem exists_pointIdeal_eq_of_isPrime {κ : Type*} [Field κ] [IsAlgClosed κ] {f : κ[X]}
    [NeZero (2 : κ)] [Fact (Odd f.natDegree)] [Fact (Squarefree f)]
    {𝔭 : Ideal (HypRing κ f)} (hp : 𝔭.IsPrime) (hp0 : 𝔭 ≠ ⊥) :
    ∃ (x₀ y₀ : κ) (_ : y₀ ^ 2 = f.eval x₀), 𝔭 = pointIdeal f x₀ y₀ := by
  have hmax : 𝔭.IsMaximal := hp.isMaximal hp0
  let : Field (HypRing κ f ⧸ 𝔭) := Ideal.Quotient.field 𝔭
  -- `HypRing κ f` is a finite-type `κ`-algebra (module-finite over `κ[X]`, itself f.t. over `κ`).
  have : Algebra.FiniteType κ (HypRing κ f) :=
    Algebra.FiniteType.trans (S := κ[X]) inferInstance inferInstance
  -- Zariski's lemma: the residue field is finite, hence algebraic, over `κ`.
  have : Algebra.IsAlgebraic κ (HypRing κ f ⧸ 𝔭) := by
    have := finite_of_finite_type_of_isJacobsonRing κ (HypRing κ f ⧸ 𝔭)
    exact Algebra.IsAlgebraic.of_finite κ _
  -- A field extension of a field is torsion-free (needed by `IsAlgClosed.lift`).
  let : Module.IsTorsionFree κ (HypRing κ f ⧸ 𝔭) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (algebraMap κ _).injective
  -- Embed the residue field into `κ` (algebraically closed), giving `ψ : HypRing κ f →ₐ[κ] κ`.
  let φ : (HypRing κ f ⧸ 𝔭) →ₐ[κ] κ := IsAlgClosed.lift
  let ψ : HypRing κ f →ₐ[κ] κ := φ.comp (Ideal.Quotient.mkₐ κ 𝔭)
  set x₀ : κ := ψ (algebraMap κ[X] (HypRing κ f) X) with hx₀
  set y₀ : κ := ψ (HypRing.y f) with hy₀
  -- `ψ ∘ algebraMap` is evaluation at `x₀`.
  have key (p : κ[X]) : ψ (algebraMap κ[X] (HypRing κ f) p) = p.eval x₀ := by
    have hcomp : ψ.comp (IsScalarTower.toAlgHom κ κ[X] (HypRing κ f))
        = (Polynomial.aeval x₀ : κ[X] →ₐ[κ] κ) := by
      apply Polynomial.algHom_ext
      simp [hx₀]
    have h2 := AlgHom.congr_fun hcomp p
    simpa [Polynomial.coe_aeval_eq_eval] using h2
  -- The curve equation `y₀² = f(x₀)`.
  have hcurve : y₀ ^ 2 = f.eval x₀ := by
    have : ψ (HypRing.y f ^ 2) = f.eval x₀ := by rw [HypRing.y_sq]; exact key f
    rw [hy₀, ← map_pow]; exact this
  refine ⟨x₀, y₀, hcurve, ?_⟩
  -- `pointIdeal ≤ 𝔭`: both generators vanish under `ψ`, i.e. lie in `𝔭 = ker ψ`.
  have hφinj : Function.Injective φ := φ.toRingHom.injective
  have hmem (z : HypRing κ f) (hz : ψ z = 0) : z ∈ 𝔭 := by
    have : Ideal.Quotient.mk 𝔭 z = 0 := hφinj (by simpa [ψ] using hz)
    rwa [Ideal.Quotient.eq_zero_iff_mem] at this
  have hle : pointIdeal f x₀ y₀ ≤ 𝔭 := by
    rw [pointIdeal, Ideal.span_le]
    rintro g (rfl | rfl)
    · refine hmem _ ?_
      rw [key]; simp
    · refine hmem _ ?_
      rw [map_sub, hy₀]
      simp [ψ]
  exact ((pointIdeal_isMaximal hcurve).eq_of_le hmax.ne_top hle).symm

/-- Factorization of a principal ideal in a Dedekind domain, with the exponent of each height-one
prime `v` given by the (`ℕ`-truncated) multiplicity of `v.asIdeal` in `(r)`. -/
theorem span_singleton_eq_finprod_heightOneSpectrum {R : Type*} [CommRing R]
    [IsDedekindDomain R] {r : R} (hr : r ≠ 0) :
    Ideal.span {r} = ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum R,
      v.asIdeal ^ (emultiplicity v.asIdeal (Ideal.span {r})).toNat := by
  have hI : Ideal.span {r} ≠ 0 := by rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  conv_lhs => rw [← Ideal.finprod_heightOneSpectrum_pow_multiplicity hI]
  refine finprod_congr fun v ↦ ?_
  congr 1

end ChabautyColeman
