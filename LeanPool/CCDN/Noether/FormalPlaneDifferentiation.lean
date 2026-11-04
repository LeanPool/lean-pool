/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Inverse

/-! Tangent differentiation on formal plane branches. Vanishing of successive
tangent derivatives implies local multiplicity below the characteristic. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The polynomial tangent vector field, with coordinate j as local parameter. -/
def planeTangent {K : Type*} [CommRing K] (f : MvPolynomial (Fin 2) K) (j : Fin 2) :
    Derivation K (MvPolynomial (Fin 2) K) (MvPolynomial (Fin 2) K) :=
  (pderiv j.rev f) • pderiv j - (pderiv j f) • pderiv j.rev

/-- The tangent vector field of `f` with local parameter coordinate `j` applied to `h` is
`∂_{j.rev} f * ∂_j h - ∂_j f * ∂_{j.rev} h`. -/
lemma planeTangent_apply {K : Type*} [CommRing K]
    (f h : MvPolynomial (Fin 2) K) (j : Fin 2) :
    planeTangent f j h = pderiv j.rev f * pderiv j h - pderiv j f * pderiv j.rev h := rfl

private lemma powerSeries_plane_chain {K : Type*} [Field K]
    (ψ : MvPolynomial (Fin 2) K →ₐ[K] PowerSeries K)
    (h : MvPolynomial (Fin 2) K) (j : Fin 2) :
    PowerSeries.derivative (ψ h) =
      ψ (pderiv j h) * PowerSeries.derivative (ψ (X j)) +
      ψ (pderiv j.rev h) * PowerSeries.derivative (ψ (X j.rev)) := by
  have hC (c : K) : ψ (C c) = PowerSeries.C c := ψ.commutes c
  induction h using MvPolynomial.induction_on with
  | C c => simp [hC]
  | add h l hh hl => simp only [map_add, hh, hl]; ring
  | mul_X h k hh =>
    fin_cases j <;> fin_cases k <;>
      simp [map_mul, Derivation.leibniz, smul_eq_mul, hh] <;> ring

/-- Tangent differentiation becomes a unit times formal differentiation at a
smooth point whose chosen coordinate is the parameter. -/
private theorem formal_plane_tangent {K : Type*} [Field K]
    (f : MvPolynomial (Fin 2) K)
    (ψ : MvPolynomial (Fin 2) K →ₐ[K] PowerSeries K) (hψ : ψ f = 0)
    (j : Fin 2) (a : K) (hparam : ψ (X j - C a) = PowerSeries.X)
    (h : MvPolynomial (Fin 2) K) :
    ψ (planeTangent f j h) = ψ (pderiv j.rev f) * PowerSeries.derivative (ψ h) := by
  have hdX : PowerSeries.derivative (ψ (X j)) = 1 := by
    have he := congrArg PowerSeries.derivative hparam
    have hC : ψ (C a) = PowerSeries.C a := ψ.commutes a
    simpa only [map_sub, hC, PowerSeries.derivative_C, sub_zero, PowerSeries.derivative_X] using he
  have hf := powerSeries_plane_chain ψ f j
  rw [hψ, map_zero, hdX, mul_one] at hf
  rw [powerSeries_plane_chain ψ h j, hdX, mul_one, planeTangent_apply, map_sub, map_mul, map_mul]
  linear_combination ψ (pderiv j.rev h) * hf

/-- A unit multiple of d/dX detects multiplicity from its successive constant
terms, as long as the positive integers below the requested order are invertible. -/
private lemma powerSeries_weighted_derivatives_vanishing {K : Type*} [Field K]
    (u : PowerSeries K) (hu : IsUnit u) (N : ℕ)
    (hchar : ∀ n, 0 < n → n < N → (n : K) ≠ 0)
    (g : PowerSeries K)
    (hzero : ∀ r < N,
      PowerSeries.constantCoeff ((fun h => u * PowerSeries.derivative h)^[r] g) = 0) :
    PowerSeries.X ^ N ∣ g := by
  induction N generalizing g with
  | zero => simp
  | succ N ih =>
    have ht : PowerSeries.X ^ N ∣ u * PowerSeries.derivative g := by
      apply ih (fun n hn hnN => hchar n hn (by omega))
      intro r hr
      have hh := hzero (r + 1) (by omega)
      simpa only [Function.iterate_succ_apply] using hh
    have hd := hu.dvd_mul_left.mp ht
    apply PowerSeries.X_pow_dvd_iff.mpr
    intro n hn
    cases n with
    | zero =>
      simpa only [Function.iterate_zero, id_eq, PowerSeries.coeff_zero_eq_constantCoeff] using
        hzero 0 (by omega)
    | succ n =>
      have he := PowerSeries.X_pow_dvd_iff.mp hd n (by omega)
      rw [PowerSeries.coeff_derivative] at he
      exact (mul_eq_zero.mp he).resolve_right (by
        simpa only [Nat.cast_add, Nat.cast_one] using hchar (n + 1) (by omega) hn)

/-- Polynomial tangent derivatives give local divisibility. -/
theorem formal_plane_multiplicity_of_tangent {K : Type*} [Field K]
    (f : MvPolynomial (Fin 2) K)
    (ψ : MvPolynomial (Fin 2) K →ₐ[K] PowerSeries K) (hψ : ψ f = 0)
    (z : Fin 2 → K) (hconst : ∀ h, PowerSeries.constantCoeff (ψ h) = eval z h)
    (j : Fin 2) (hparam : ψ (X j - C (z j)) = PowerSeries.X)
    (hsmooth : eval z (pderiv j.rev f) ≠ 0)
    (g : MvPolynomial (Fin 2) K) (N : ℕ)
    (hchar : ∀ n, 0 < n → n < N → (n : K) ≠ 0)
    (hzero : ∀ r < N, eval z ((planeTangent f j)^[r] g) = 0) :
    PowerSeries.X ^ N ∣ ψ g := by
  let u := ψ (pderiv j.rev f)
  have hu : IsUnit u := by
    rw [PowerSeries.isUnit_iff_constantCoeff, hconst]
    exact isUnit_iff_ne_zero.mpr hsmooth
  apply powerSeries_weighted_derivatives_vanishing u hu N hchar
  have hiter (r : ℕ) :
      ((fun h => u * PowerSeries.derivative h)^[r] (ψ g)) = ψ ((planeTangent f j)^[r] g) := by
    induction r with
    | zero => rfl
    | succ r hr =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hr]
      exact (formal_plane_tangent f ψ hψ j (z j) hparam _).symm
  intro r hr
  rw [hiter, hconst]
  exact hzero r hr

end
end CCDN
