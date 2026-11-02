/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.NumberFields.ResidueHomKernels
public import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind

/-! # The conductor comparison for arbitrary coprime moduli

The quotient comparison used by Kummer–Dedekind works for every modulus
coprime to the conductor exponent, not only for prime moduli.
-/

@[expose] public section

namespace NairTenenbaum

open Polynomial NumberField Ideal KummerDedekind

variable {K : Type*} [Field K] [NumberField K] (θ : 𝓞 K) {n : ℕ}

omit [NumberField K] in
theorem conductor_sup_span_eq_top (hn : n.Coprime (RingOfIntegers.exponent θ)) :
    (conductor ℤ θ).comap (algebraMap ℤ (𝓞 K)) ⊔ Ideal.span {(n : ℤ)} = ⊤ := by
  have H := (Ideal.isCoprime_span_singleton_iff
    (RingOfIntegers.exponent θ : ℤ) (n : ℤ)).mpr hn.symm.isCoprime
  rw [RingOfIntegers.exponent, Int.ideal_span_absNorm_eq_self] at H
  exact (isCoprime_iff_codisjoint.mp H).eq_top

/-- The equivalence between the polynomial quotient and the residue algebra. -/
noncomputable def residuePolynomialQuotientEquiv
    (hn : n.Coprime (RingOfIntegers.exponent θ)) :
    (ZMod n)[X] ⧸ Ideal.span {Polynomial.map (Int.castRingHom (ZMod n)) (minpoly ℤ θ)} ≃+*
      𝓞 K ⧸ Ideal.span {(n : 𝓞 K)} :=
  (quotientEquivAlgOfEq ℤ (by simp [Ideal.map_span, Polynomial.map_map])).toRingEquiv.trans
    ((quotientEquiv _ _ (mapEquiv (Int.quotientSpanNatEquivZMod n)) rfl).symm.trans
      ((quotMapEquivQuotQuotMap (conductor_sup_span_eq_top θ hn) θ.isIntegral).symm.trans
        (quotientEquivAlgOfEq ℤ (by simp [map_span])).toRingEquiv))

theorem residuePolynomialQuotientEquiv_mk (hn : n.Coprime (RingOfIntegers.exponent θ))
    (Q : ℤ[X]) :
    residuePolynomialQuotientEquiv θ hn
      ((Ideal.Quotient.mk (Ideal.span {Polynomial.map (Int.castRingHom (ZMod n)) (minpoly ℤ θ)}))
        (Polynomial.map (Int.castRingHom (ZMod n)) Q)) =
      (Ideal.Quotient.mk (Ideal.span {(n : 𝓞 K)})) (aeval θ Q) := by
  simp only [residuePolynomialQuotientEquiv, algebraMap_int_eq,
    RingEquiv.trans_apply, AlgEquiv.coe_toRingEquiv, quotientEquivAlgOfEq_mk,
    quotientEquiv_symm_apply, quotientMap_mk, RingHom.coe_coe, mapEquiv_symm_apply,
    Polynomial.map_map, Int.quotientSpanNatEquivZMod_comp_castRingHom]
  exact congr_arg (quotientEquivAlgOfEq ℤ (by simp [map_span]))
    (quotMapEquivQuotQuotMap_symm_apply (conductor_sup_span_eq_top θ hn) θ.isIntegral Q)

end NairTenenbaum
