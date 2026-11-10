/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

-- Import paths adapted for Lean Pool; local option overrides removed.

public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.RingTheory.Trace.Defs

import Mathlib.Algebra.QuadraticAlgebra.NormDeterminant

/-!
# Complements to the `QuadraticAlgebra` API

Everything in this file is stated for general `QuadraticAlgebra R a b` and is intended
for eventual upstreaming to Mathlib:

* `re`/`im`/`star` of `algebraMap` over a general base `S`, and `star` as an `S`-algebra
  automorphism (`QuadraticAlgebra.starAlgEquiv`);
* `ω²` and `star ω` (`QuadraticAlgebra.omega_sq`, `QuadraticAlgebra.star_omega`);
* functoriality in the coefficient ring with a prescribed target (`QuadraticAlgebra.mapRingHomTo`);
* the field-theoretic norm and trace of `QuadraticAlgebra R a b` over `R`
  (`QuadraticAlgebra.algebraNorm_eq_norm`, `QuadraticAlgebra.algebraTrace_eq`).
-/

@[expose] public section

namespace QuadraticAlgebra

variable {R : Type*} [CommRing R] {a b : R} {S : Type*} [CommSemiring S] [Algebra S R]

instance : FaithfulSMul R (QuadraticAlgebra R a b) :=
  (faithfulSMul_iff_algebraMap_injective R _).mpr algebraMap_injective

theorem eq_zero_iff {z : QuadraticAlgebra R a b} : z = 0 ↔ z.re = 0 ∧ z.im = 0 := by
  simp [QuadraticAlgebra.ext_iff]

@[simp]
theorem mk_eq_zero {p q : R} : (⟨p, q⟩ : QuadraticAlgebra R a b) = 0 ↔ p = 0 ∧ q = 0 :=
  eq_zero_iff

/-- A nonzero element has a nonzero component. -/
theorem not_re_eq_zero_and_im_eq_zero {z : QuadraticAlgebra R a b} (hz : z ≠ 0) :
    ¬(z.re = 0 ∧ z.im = 0) := fun h ↦ hz (eq_zero_iff.mpr h)

/-- An element without imaginary part is the image of its real part. -/
theorem eq_algebraMap_re {z : QuadraticAlgebra R a b} (him : z.im = 0) :
    z = algebraMap R (QuadraticAlgebra R a b) z.re := by
  ext
  · simp
  · simp [him]

@[simp]
theorem re_algebraMap (s : S) :
    (algebraMap S (QuadraticAlgebra R a b) s).re = algebraMap S R s := rfl

@[simp]
theorem im_algebraMap (s : S) : (algebraMap S (QuadraticAlgebra R a b) s).im = 0 := rfl

@[simp]
theorem star_algebraMap (s : S) :
    star (algebraMap S (QuadraticAlgebra R a b) s) = algebraMap S _ s := by
  ext <;> simp [re_star, im_star]

/-- `star` as an `S`-algebra automorphism of `QuadraticAlgebra R a b`,
for any base `S` of the coefficient ring `R`. -/
def starAlgEquiv : QuadraticAlgebra R a b ≃ₐ[S] QuadraticAlgebra R a b :=
  AlgEquiv.ofRingEquiv (f := starRingAut) star_algebraMap

@[simp]
theorem starAlgEquiv_apply (z : QuadraticAlgebra R a b) :
    (starAlgEquiv (S := S)) z = star z := rfl

@[simp]
theorem starAlgEquiv_symm :
    (starAlgEquiv (S := S) (R := R) (a := a) (b := b)).symm = starAlgEquiv := rfl

/-- The defining equation of the generator: `ω² = a + b·ω`. -/
theorem omega_sq : (ω : QuadraticAlgebra R a b) ^ 2 = algebraMap R _ a + b • ω := by
  rw [sq, omega_mul_omega_eq_add, Algebra.algebraMap_eq_smul_one]

/-- Conjugation sends `ω` to the other root `b - ω` of the defining equation. -/
@[simp]
theorem star_omega : star (ω : QuadraticAlgebra R a b) = algebraMap R _ b - ω := by
  ext <;> simp [omega]

section map

variable {R' : Type*} [CommRing R'] {a' b' : R'}

/-- Functoriality of `QuadraticAlgebra` in the coefficient ring: a ring homomorphism
mapping the defining coefficients to the defining coefficients induces a ring
homomorphism, componentwise. Unlike `QuadraticAlgebra.mapRingHom`, whose target is
`QuadraticAlgebra R' (φ a) (φ b)`, the target coefficients `a'`, `b'` are prescribed and the
identities `φ a = a'`, `φ b = b'` are hypotheses, so the map lands in a type indexed by given data
(a polynomial `g` with `f.map φ = g`) without a cast. -/
def mapRingHomTo (φ : R →+* R') (ha : φ a = a') (hb : φ b = b') :
    QuadraticAlgebra R a b →+* QuadraticAlgebra R' a' b' where
  toFun z := ⟨φ z.re, φ z.im⟩
  map_one' := by ext <;> simp
  map_mul' z w := by ext <;> simp [← ha, ← hb]
  map_zero' := by ext <;> simp
  map_add' z w := by ext <;> simp

@[simp]
theorem re_mapRingHomTo (φ : R →+* R') (ha : φ a = a') (hb : φ b = b')
    (z : QuadraticAlgebra R a b) : (mapRingHomTo φ ha hb z).re = φ z.re := rfl

@[simp]
theorem im_mapRingHomTo (φ : R →+* R') (ha : φ a = a') (hb : φ b = b')
    (z : QuadraticAlgebra R a b) : (mapRingHomTo φ ha hb z).im = φ z.im := rfl

/-- The induced map is injective as soon as the coefficient map is: it acts componentwise. -/
theorem mapRingHomTo_injective {φ : R →+* R'} (hφ : Function.Injective φ) (ha : φ a = a')
    (hb : φ b = b') : Function.Injective (mapRingHomTo φ ha hb) := by
  subst ha hb
  exact mapRingHom_injective φ a b hφ

end map

section normTrace

/-- The norm of `QuadraticAlgebra R a b` agrees with the field-theoretic
(determinant) norm of the algebra `QuadraticAlgebra R a b` over `R`. -/
theorem algebraNorm_eq_norm (z : QuadraticAlgebra R a b) :
    Algebra.norm R z = z.norm := by
  rw [Algebra.norm_apply, ← det_toLinearMap_eq_norm]
  congr 1

/-- The field-theoretic trace of `QuadraticAlgebra R a b` over `R`, computed in the
basis `1, ω`. -/
theorem algebraTrace_eq (z : QuadraticAlgebra R a b) :
    Algebra.trace R (QuadraticAlgebra R a b) z = 2 * z.re + b * z.im := by
  classical
  rw [Algebra.trace_eq_matrix_trace (basis a b), Matrix.trace_fin_two]
  simp [Algebra.leftMulMatrix_eq_repr_mul, basis, Module.Basis.coe_ofEquivFun]
  ring

end normTrace

end QuadraticAlgebra

end
