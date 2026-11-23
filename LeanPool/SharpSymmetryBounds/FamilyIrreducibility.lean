/-
Copyright (c) 2026 Carlo Perassi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carlo Perassi
-/
module

public import LeanPool.SharpSymmetryBounds.Blowup

/-!
# Irreducibility of the extremal family

Every member of the family `Re(z^m (|z|^2 + α)) = 0` with nonreal `α` is geometrically irreducible.
-/

@[expose] public section

namespace CurveSymmetry

open MvPolynomial

/-- Complexification of twice `Re(z^m (|z|^2 + α))`. -/
noncomputable def familyPolynomial (m : ℕ) (α : ℂ) : BPoly :=
  X 0 ^ m * (C α + X 0 * X 1) + X 1 ^ m * (C (star α) + X 0 * X 1)

lemma familyPolynomial_not_isUnit {m : ℕ} (hm : 0 < m) (α : ℂ) :
    ¬ IsUnit (familyPolynomial m α) := by
  intro hu
  have h := hu.map (eval₂Hom (RingHom.id ℂ) (fun _ : Fin 2 => (0 : ℂ)))
  simp [familyPolynomial, hm.ne'] at h

lemma familyPolynomial_not_dvd_Y {m : ℕ} (hm : 0 < m) {α : ℂ} (ha : α ≠ 0) :
    ¬ (X 1 : BPoly) ∣ familyPolynomial m α := by
  intro h
  have he := map_dvd (eval₂Hom (RingHom.id ℂ) (fun i : Fin 2 => if i = 0 then 1 else 0)) h
  simp [familyPolynomial, hm.ne', ha] at he

lemma familyPolynomial_blowup (m : ℕ) (α : ℂ) :
    blowup (familyPolynomial m α) = (X 0 : BPoly) ^ m * toNested.symm (familyQuadratic m α) := by
  apply toNested.injective
  simp only [familyPolynomial, map_add, map_mul, map_pow]
  have h0 : blowup (X 0) = X 1 * X 0 := by simp [blowup]
  have h1 : blowup (X 1) = X 0 := by simp [blowup]
  have hC : ∀ c : ℂ, blowup (C c) = C c := by intro c; simp [blowup]
  rw [h0, h1, hC, hC, toNested.apply_symm_apply]
  simp only [map_mul, toNested_C, toNested_X_zero, toNested_X_one,
    familyQuadratic, familyA, familyB, map_add, map_pow, map_one]
  ring

/-- Every nonreal-parameter family polynomial is geometrically irreducible.
The proof works already for `m ≥ 1` and does not need modulus one. -/
theorem familyPolynomial_irreducible {m : ℕ} (hm : 0 < m) {α : ℂ} (ha : α ≠ star α) :
    Irreducible (familyPolynomial m α) := by
  have hα : α ≠ 0 := by intro h; apply ha; simp [h]
  exact irreducible_of_blowup (familyPolynomial_not_isUnit hm α)
    (familyPolynomial_not_dvd_Y hm hα)
    ((familyQuadratic_irreducible hm ha).map toNested.symm.toMulEquiv)
    (familyPolynomial_blowup m α)

end CurveSymmetry
