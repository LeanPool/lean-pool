/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Polynomials.PolynomialStructure
public import LeanPool.NairTenenbaum.Progressions.AffineNoFixedPrime

/-! # Irreducibility survives the affine primitive-part reduction -/

@[expose] public section

namespace NairTenenbaum

open Polynomial

theorem affineRestriction_irreducible_map {Q : ℤ[X]}
    (hQ : Irreducible (Q.map (Int.castRingHom ℚ))) {M : ℤ} (hM : M ≠ 0) (a : ℤ) :
    Irreducible ((affineRestriction Q M a).map (Int.castRingHom ℚ)) := by
  have hM' : (M : ℚ) ≠ 0 := by exact_mod_cast hM
  let : Invertible (M : ℚ) := invertibleOfNonzero hM'
  have H := (MulEquiv.irreducible_iff (algEquivCMulXAddC (M : ℚ) (a : ℚ))).mpr hQ
  unfold affineRestriction
  rw [Polynomial.map_comp]
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
      Int.coe_castRingHom]
  simpa only [algEquivCMulXAddC_apply, ← comp_eq_aeval] using H

theorem affineRestriction_primPart_irreducible_map {Q : ℤ[X]}
    (hQ : Irreducible (Q.map (Int.castRingHom ℚ))) {M : ℤ} (hM : M ≠ 0) (a : ℤ) :
    Irreducible ((affineRestriction Q M a).primPart.map (Int.castRingHom ℚ)) := by
  let R := affineRestriction Q M a
  have HR : Irreducible (R.map (Int.castRingHom ℚ)) := affineRestriction_irreducible_map hQ hM a
  have hR : R ≠ 0 := by intro hz; simp [hz] at HR
  have hc : R.content ≠ 0 := mt content_eq_zero_iff.mp hR
  have hunit : IsUnit (C (R.content : ℚ)) := isUnit_C.mpr (isUnit_iff_ne_zero.mpr (by
    exact_mod_cast hc))
  have Heq : R.map (Int.castRingHom ℚ) = C (R.content : ℚ) * R.primPart.map (Int.castRingHom ℚ) :=
      by
    conv_lhs => rw [R.eq_C_content_mul_primPart]
    rw [Polynomial.map_mul, Polynomial.map_C]
    rfl
  rw [Heq] at HR
  exact (irreducible_isUnit_mul hunit).mp HR

theorem exists_affine_primitive_reduction {Q : ℤ[X]}
    (hQ : Irreducible (Q.map (Int.castRingHom ℚ))) :
    ∃ M : ℕ, 0 < M ∧ ∀ a : ℤ,
      NoFixedPrimeDivisor (affineRestriction Q M a).primPart ∧
      Irreducible ((affineRestriction Q M a).primPart.map (Int.castRingHom ℚ)) := by
  have hD : Q.discr ≠ 0 := discr_ne_zero_of_separable_map hQ.separable
  have hM := fixedPrimeRemovalModulus_pos hD
  refine ⟨fixedPrimeRemovalModulus Q, hM, fun a => ⟨affine_primPart_noFixedPrimeDivisor hD a, ?_⟩⟩
  exact affineRestriction_primPart_irreducible_map hQ (by exact_mod_cast hM.ne') a

end NairTenenbaum
