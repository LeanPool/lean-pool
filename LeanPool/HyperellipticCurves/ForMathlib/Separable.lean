/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Polynomial.GaussLemma

import Mathlib.FieldTheory.Minpoly.Finite
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

/-!
# Separability of small-degree extensions, and squarefreeness in the fraction field

`Algebra.IsSeparable.of_finrank_le_two`: in characteristic ≠ 2, any field extension of
degree at most 2 is separable. Intended for eventual upstreaming to Mathlib; note that
Mathlib's generic criterion `Irreducible.separable` is restricted to characteristic 0,
and the derivative-degree API (`Polynomial.degree_derivative` etc.) requires
torsion-free coefficients, so a direct coefficient computation is used.

`Polynomial.Monic.squarefree_map_fraction_map`: a monic squarefree polynomial over an
integrally closed domain stays squarefree over the fraction field (Gauss's lemma).
-/

@[expose] public section

open Polynomial

/-- In characteristic ≠ 2, any field extension of degree at most 2 is separable:
the minimal polynomial of an element has degree 1 or 2, so its derivative has a
leading coefficient 1 or 2 and in particular does not vanish. -/
theorem Algebra.IsSeparable.of_finrank_le_two (F L : Type*) [Field F] [Field L] [Algebra F L]
    [FiniteDimensional F L] (h2 : (2 : F) ≠ 0) (h : Module.finrank F L ≤ 2) :
    Algebra.IsSeparable F L := by
  refine ⟨fun x ↦ ?_⟩
  have hx : IsIntegral F x := .of_finite F x
  have hmon := minpoly.monic hx
  rw [IsSeparable, separable_iff_derivative_ne_zero (minpoly.irreducible hx)]
  have hd : (minpoly F x).natDegree = 1 ∨ (minpoly F x).natDegree = 2 := by
    lia [(minpoly.natDegree_le x).trans h, minpoly.natDegree_pos hx]
  intro hder
  rcases hd with hd | hd
  · have h0 := congrArg (fun q : F[X] ↦ q.coeff 0) hder
    have hc : (minpoly F x).coeff 1 = 1 := hd ▸ hmon.coeff_natDegree
    simp [coeff_derivative, hc] at h0
  · have h0 := congrArg (fun q : F[X] ↦ q.coeff 1) hder
    have hc : (minpoly F x).coeff 2 = 1 := hd ▸ hmon.coeff_natDegree
    simp only [coeff_derivative, coeff_zero, hc, one_mul, Nat.cast_one,
      one_add_one_eq_two] at h0
    exact h2 h0

namespace Polynomial

/-- **Squarefreeness ascends to the fraction field** for a monic polynomial over an
integrally closed domain: a repeated monic factor over the fraction field lifts to a
repeated factor by Gauss's lemma. -/
theorem Monic.squarefree_map_fraction_map {R K : Type*} [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] [Field K] [Algebra R K] [IsFractionRing R K] {g : R[X]}
    (hg : g.Monic) (hsq : Squarefree g) : Squarefree (g.map (algebraMap R K)) := fun q hq ↦ by
  have hq0 : q ≠ 0 := by
    rintro rfl
    exact (hg.map (algebraMap R K)).ne_zero (zero_dvd_iff.mp (by simpa using hq))
  have hqm := monic_mul_leadingCoeff_inv hq0
  have hassoc : Associated q (q * C q.leadingCoeff⁻¹) :=
    ⟨(isUnit_C.mpr (inv_ne_zero (leadingCoeff_ne_zero.mpr hq0)).isUnit).unit, rfl⟩
  have hdvd := (hassoc.mul_mul hassoc).symm.dvd.trans hq
  obtain ⟨Q, hQ⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd K hg ((dvd_mul_right _ _).trans hdvd)
  rw [hqm.leadingCoeff, map_one, mul_one] at hQ
  have hQm : Q.Monic := monic_of_injective (IsFractionRing.injective R K) (hQ ▸ hqm)
  refine hassoc.symm.isUnit (hQ ▸ ((hsq Q ?_).map (mapRingHom (algebraMap R K))))
  exact hg.dvd_of_fraction_map_dvd_fraction_map (K := K) (hQm.mul hQm)
    (by rwa [Polynomial.map_mul, hQ])

end Polynomial

end
