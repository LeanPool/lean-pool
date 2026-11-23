/-
Copyright (c) 2026 Carlo Perassi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carlo Perassi
-/
module

public import LeanPool.SharpSymmetryBounds.FamilyQuadratic

/-!
# The blow-up substitution

The substitution `(X, Y) ↦ (t Y, Y)` and the passage from an irreducible strict transform to an
irreducible equation.
-/

@[expose] public section

namespace CurveSymmetry

open MvPolynomial

/-- Substitution `(X,Y) ↦ (tY,Y)`, with target coordinates ordered `(Y,t)`. -/
noncomputable def blowup : BPoly →+* BPoly :=
  eval₂Hom C (fun i : Fin 2 => if i = 0 then X 1 * X 0 else X 0)

lemma blowup_monomial (s : Exponent) (c : ℂ) :
    blowup (monomial s c) = monomial (exponent (s 0 + s 1) (s 0)) c := by
  simp only [blowup, eval₂Hom_monomial]
  rw [Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two]
  simp only [Fin.isValue, ↓reduceIte, show (1 : Fin 2) ≠ 0 by decide, monomial_exponent]
  rw [pow_add, mul_pow]
  ring

lemma coeff_blowup (P : BPoly) (a b : ℕ) :
    (blowup P).coeff (exponent (a + b) a) = P.coeff (exponent a b) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial s c =>
      rw [blowup_monomial]
      have he : exponent (s 0 + s 1) (s 0) = exponent (a + b) a ↔ s = exponent a b := by
        simp only [exponent_eq_iff, exponent_zero, exponent_one]
        omega
      simp [coeff_monomial, he]
  | add P Q hP hQ => simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hP, hQ]

lemma blowup_injective : Function.Injective blowup := by
  intro P Q he
  ext s
  have hs : s = exponent (s 0) (s 1) := exponent_eq_iff.mpr ⟨rfl, rfl⟩
  rw [hs]
  exact (coeff_blowup P (s 0) (s 1)).symm.trans
    ((congrArg (fun R : BPoly => R.coeff (exponent (s 0 + s 1) (s 0))) he).trans
      (coeff_blowup Q (s 0) (s 1)))

lemma unit_of_blowup_dvd_power {P : BPoly} (hY : ¬ (X 1 : BPoly) ∣ P)
    {m : ℕ} (hdiv : blowup P ∣ (X 0 : BPoly) ^ m) : IsUnit P := by
  rw [X_pow_eq_monomial] at hdiv
  obtain ⟨s, c, hs, hc, he⟩ := dvd_monomial_one_iff_exists.mp hdiv
  have hs1 : s 1 = 0 := by
    have h := hs 1
    simpa using h
  have hP : P = C c * X 1 ^ s 0 := by
    apply blowup_injective
    rw [he]
    have hs' : s = exponent (s 0) 0 := exponent_eq_iff.mpr ⟨rfl, hs1⟩
    rw [hs', monomial_exponent]
    simp [blowup]
  by_cases hzero : s 0 = 0
  · rw [hP, hzero, pow_zero, mul_one]
    exact hc.map C
  · exfalso
    apply hY
    rw [hP]
    exact (dvd_pow_self (X 1 : BPoly) hzero).mul_left _

/-- Removing the exceptional coordinate factor from an irreducible strict transform
preserves irreducibility of the original equation. -/
theorem irreducible_of_blowup {P H : BPoly} {m : ℕ}
    (hunit : ¬ IsUnit P) (hY : ¬ (X 1 : BPoly) ∣ P) (hH : Irreducible H)
    (he : blowup P = (X 0 : BPoly) ^ m * H) : Irreducible P := by
  refine ⟨hunit, ?_⟩
  intro A B hAB
  have hd : H ∣ blowup A * blowup B := by
    rw [← map_mul, ← hAB, he]
    exact dvd_mul_left H _
  have hprime : Prime H := UniqueFactorizationMonoid.irreducible_iff_prime.mp hH
  have hY_A : ¬ (X 1 : BPoly) ∣ A := fun h => hY (hAB ▸ h.mul_right B)
  have hY_B : ¬ (X 1 : BPoly) ∣ B := fun h => hY (hAB ▸ h.mul_left A)
  rcases hprime.dvd_or_dvd hd with hA | hB
  · obtain ⟨Q, hQ⟩ := hA
    have hmul : (X 0 : BPoly) ^ m = Q * blowup B := by
      apply mul_left_cancel₀ hH.ne_zero
      have h := he
      rw [hAB, map_mul, hQ] at h
      linear_combination -h
    exact Or.inr (unit_of_blowup_dvd_power hY_B ⟨Q, by rw [hmul, mul_comm]⟩)
  · obtain ⟨Q, hQ⟩ := hB
    have hmul : (X 0 : BPoly) ^ m = Q * blowup A := by
      apply mul_left_cancel₀ hH.ne_zero
      have h := he
      rw [hAB, map_mul, hQ] at h
      linear_combination -h
    exact Or.inl (unit_of_blowup_dvd_power hY_A ⟨Q, by rw [hmul, mul_comm]⟩)

end CurveSymmetry
