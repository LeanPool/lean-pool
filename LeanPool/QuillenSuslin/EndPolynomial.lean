/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.PolynomialAlgebra

import Mathlib.RingTheory.TotallySplit

/-!
# Endomorphisms of an extended polynomial module

For a commutative ring `A`, an `A`-module `N` with endomorphism ring `R = End_A N` and a
commutative `A`-algebra `B`, the polynomials over `B ⊗[A] R` act on `B[X] ⊗[A] N`: the
coefficient `b ⊗ φ` acts by `p ⊗ n ↦ b p ⊗ φ n` and `X` by multiplication. This gives a ring
homomorphism `endPoly : (B ⊗[A] R)[X] → End_{B[X]}(B[X] ⊗[A] N)`, bijective when `N` is finitely
presented and `B` is flat over `A`. It is natural in `B` and is compatible with the reduction
`X ↦ 0`. This is the identification `End_{B[X]}(B[X] ⊗ N) ≅ (B ⊗ End N)[X]` used by Quillen to
apply his dilation lemma to automorphisms of extended modules (Quillen 1976, proof of
Theorem 1, p. 168).

## Main results

* `endCoeff`, `endPoly`: the actions of `B ⊗[A] R` and `(B ⊗[A] R)[X]`.
* `endPoly_bijective`: bijectivity for flat `B` and finitely presented `N`.
* `endPoly_natural`: naturality in `B`.
* `reduce_endPoly`: compatibility with the reduction `B[X] ⊗[A] N → B ⊗[A] N`.
* `endCoeff_injective`: `B ⊗[A] R → End_B(B ⊗[A] N)` is injective for flat `B`.

## References

* D. Quillen, *Projective modules over polynomial rings*, Invent. Math. 36 (1976), 167–171.
-/

@[expose] public noncomputable section

universe u v w

open Polynomial TensorProduct

namespace LeanPool.QuillenSuslin

variable {A : Type u} [CommRing A] (N : Type v) [AddCommGroup N] [Module A N]

section Coeff

variable (T : Type w) [CommRing T] [Algebra A T] {B : Type*} [CommRing B] [Algebra A B]

/-- The action of `B ⊗[A] End_A N` on `T ⊗[A] N` along an algebra map `σ : B → T`:
`b ⊗ φ` acts by `t ⊗ n ↦ σ b t ⊗ φ n`. -/
def endCoeff (σ : B →ₐ[A] T) : B ⊗[A] Module.End A N →ₐ[A] Module.End T (T ⊗[A] N) :=
  Algebra.TensorProduct.lift
    (((Algebra.ofId T (Module.End T (T ⊗[A] N))).restrictScalars A).comp σ)
    (Module.End.baseChangeHom A T N) fun x _ => by
      simpa using Algebra.commute_algebraMap_left (σ x) _

variable {T}

theorem endCoeff_tmul_apply (σ : B →ₐ[A] T) (b : B) (φ : Module.End A N) (t : T) (n : N) :
    endCoeff N T σ (b ⊗ₜ φ) (t ⊗ₜ n) = (σ b * t) ⊗ₜ φ n := by
  rw [endCoeff, Algebra.TensorProduct.lift_tmul, mul_apply_eq_comp]
  change σ b • (φ.baseChange T (t ⊗ₜ n)) = _
  rw [LinearMap.baseChange_tmul, smul_tmul', smul_eq_mul]

end Coeff

section Poly

variable (B : Type w) [CommRing B] [Algebra A B]

/-- The action of `(B ⊗[A] End_A N)[X]` on `B[X] ⊗[A] N`. -/
def endPoly : (B ⊗[A] Module.End A N)[X] →+* Module.End B[X] (B[X] ⊗[A] N) :=
  eval₂RingHom' (endCoeff N B[X] (CAlgHom : B →ₐ[A] B[X])).toRingHom
    (algebraMap B[X] (Module.End B[X] (B[X] ⊗[A] N)) X) fun _ =>
      Algebra.commute_algebraMap_right _ _

theorem endPoly_monomial_tmul_apply (i : ℕ) (b : B) (φ : Module.End A N) (p : B[X]) (n : N) :
    endPoly N B (monomial i (b ⊗ₜ φ)) (p ⊗ₜ n) = (X ^ i * (C b * p)) ⊗ₜ φ n := by
  change (eval₂ (endCoeff N B[X] (CAlgHom : B →ₐ[A] B[X])).toRingHom
    (algebraMap B[X] (Module.End B[X] (B[X] ⊗[A] N)) X) (monomial i (b ⊗ₜ φ))) (p ⊗ₜ n) = _
  rw [eval₂_monomial, ← map_pow, mul_apply_eq_comp, Module.algebraMap_end_apply, smul_tmul',
    smul_eq_mul]
  change endCoeff N B[X] (CAlgHom : B →ₐ[A] B[X]) (b ⊗ₜ φ) _ = _
  rw [endCoeff_tmul_apply, mul_left_comm]
  rfl

/-- Two additive maps out of `(B ⊗[A] R)[X]` agree once they agree on the monomials
`(b ⊗ φ) Xⁱ`. -/
theorem polyTensor_induction {motive : (B ⊗[A] Module.End A N)[X] → Prop}
    (hadd : ∀ p q, motive p → motive q → motive (p + q))
    (hmon : ∀ (i : ℕ) (b : B) (φ : Module.End A N), motive (monomial i (b ⊗ₜ φ)))
    (q : (B ⊗[A] Module.End A N)[X]) : motive q := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => exact hadd p q hp hq
  | monomial i t =>
    induction t using TensorProduct.inductionOn with
    | tmul b φ => exact hmon i b φ
    | add t₁ t₂ h₁ h₂ => simpa [map_add] using hadd _ _ h₁ h₂

/-- The coefficient map `B ⊗[A] R → B' ⊗[A] R` induced by an algebra map `β : B → B'`. -/
abbrev coeffMap {B' : Type*} [CommRing B'] [Algebra A B'] (β : B →ₐ[A] B') :
    B ⊗[A] Module.End A N →+* B' ⊗[A] Module.End A N :=
  (Algebra.TensorProduct.map β (AlgHom.id A (Module.End A N))).toRingHom

/-- The map `B[X] ⊗[A] N → B'[X] ⊗[A] N` induced by an algebra map `β : B → B'`. -/
abbrev polyTensorMap {B' : Type*} [CommRing B'] [Algebra A B'] (β : B →ₐ[A] B') :
    B[X] ⊗[A] N →ₗ[A] B'[X] ⊗[A] N :=
  (mapAlgHom β).toLinearMap.rTensor N

/-- Naturality of `endPoly` in the algebra `B`. -/
theorem endPoly_natural {B' : Type*} [CommRing B'] [Algebra A B'] (β : B →ₐ[A] B')
    (q : (B ⊗[A] Module.End A N)[X]) (x : B[X] ⊗[A] N) :
    polyTensorMap N B β (endPoly N B q x) =
      endPoly N B' (q.map (coeffMap N B β)) (polyTensorMap N B β x) := by
  induction q using polyTensor_induction generalizing x with
  | hadd p q hp hq => simp only [map_add, LinearMap.add_apply, Polynomial.map_add, hp, hq]
  | hmon i b φ =>
    induction x using TensorProduct.inductionOn with
    | tmul p n =>
      simp only [polyTensorMap, map_monomial, endPoly_monomial_tmul_apply, LinearMap.rTensor_tmul,
        AlgHom.toLinearMap_apply, coe_mapAlgHom, coeffMap, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq]
      simp [Polynomial.map_mul]
    | add x y hx hy => simp only [map_add, hx, hy]

/-- The reduction `B[X] ⊗[A] N → B ⊗[A] N` along `X ↦ 0`. -/
def reduce : B[X] ⊗[A] N →ₗ[A] B ⊗[A] N :=
  ((aeval (0 : B)).restrictScalars A).toLinearMap.rTensor N

@[simp]
theorem reduce_tmul (p : B[X]) (n : N) : reduce N B (p ⊗ₜ[A] n) = p.eval 0 ⊗ₜ[A] n := by
  simp [reduce, aeval_def, eval₂_eq_eval_map]

theorem reduce_smul (z : B[X]) (x : B[X] ⊗[A] N) :
    reduce N B (z • x) = z.eval 0 • reduce N B x := by
  induction x using TensorProduct.inductionOn with
  | tmul p n => rw [smul_tmul', reduce_tmul, reduce_tmul, smul_tmul', smul_eq_mul, smul_eq_mul,
      eval_mul]
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

theorem reduce_polyTensorMap {B' : Type*} [CommRing B'] [Algebra A B'] (β : B →ₐ[A] B')
    (x : B[X] ⊗[A] N) :
    reduce N B' (polyTensorMap N B β x) = β.toLinearMap.rTensor N (reduce N B x) := by
  induction x using TensorProduct.inductionOn with
  | tmul p n =>
    simp only [polyTensorMap, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, reduce_tmul,
      ← coeff_zero_eq_eval_zero, coe_mapAlgHom, coeff_map, RingHom.coe_coe]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

theorem reduce_surjective : Function.Surjective (reduce (A := A) N B) :=
  LinearMap.rTensor_surjective _ fun b => ⟨(C b : B[X]), by simp⟩

/-- `endPoly` is compatible with the reduction `X ↦ 0`: the reduction of `q` acting on
`B[X] ⊗[A] N` is its constant coefficient acting on `B ⊗[A] N`. -/
theorem reduce_endPoly (q : (B ⊗[A] Module.End A N)[X]) (x : B[X] ⊗[A] N) :
    reduce N B (endPoly N B q x) = endCoeff N B (AlgHom.id A B) (q.coeff 0) (reduce N B x) := by
  induction q using polyTensor_induction generalizing x with
  | hadd p q hp hq => simp only [map_add, LinearMap.add_apply, coeff_add, hp, hq]
  | hmon i b φ =>
    induction x using TensorProduct.inductionOn with
    | tmul p n =>
      rw [endPoly_monomial_tmul_apply, reduce_tmul, reduce_tmul, coeff_monomial,
        Finsupp.single_apply]
      split_ifs with h
      · subst h
        rw [endCoeff_tmul_apply]
        simp
      · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h
        simp
    | add x y hx hy => simp only [map_add, hx, hy]

/-- The linear identification `(B ⊗[A] R)[X] ≅ B[X] ⊗[A] R`. -/
def polyTensorEquiv : (B ⊗[A] Module.End A N)[X] ≃ₗ[A] B[X] ⊗[A] Module.End A N :=
  (polyEquivTensor A (B ⊗[A] Module.End A N)).toLinearEquiv ≪≫ₗ
    TensorProduct.rightComm A B (Module.End A N) A[X] ≪≫ₗ
      ((polyEquivTensor A B).symm.toLinearEquiv.rTensor (Module.End A N))

theorem polyTensorEquiv_monomial (i : ℕ) (b : B) (φ : Module.End A N) :
    polyTensorEquiv N B (monomial i (b ⊗ₜ φ)) = monomial i b ⊗ₜ φ := by
  simp only [polyTensorEquiv, LinearEquiv.trans_apply, AlgEquiv.toLinearEquiv_apply]
  rw [show polyEquivTensor A (B ⊗[A] Module.End A N) (monomial i (b ⊗ₜ φ)) =
      (b ⊗ₜ φ) ⊗ₜ (X ^ i : A[X]) by simp [eval₂_monomial, Algebra.TensorProduct.tmul_pow],
    TensorProduct.rightComm_tmul, LinearEquiv.rTensor_tmul]
  simp [polyEquivTensor_symm_apply_tmul_eq_smul, ← C_mul_X_pow_eq_monomial, smul_eq_C_mul]

theorem endPoly_bijective [Module.Flat A B] [Module.FinitePresentation A N] :
    Function.Bijective (endPoly (A := A) N B) := by
  have : Module.Flat A B[X] := Module.Flat.trans A B B[X]
  let Φ := (Module.FinitePresentation.isBaseChange_map A N N B[X]).equiv
  have key : ∀ q, endPoly N B q = Φ (polyTensorEquiv N B q) := by
    intro q
    induction q using polyTensor_induction with
    | hadd p q hp hq => rw [map_add, hp, hq, map_add, map_add]
    | hmon i b φ =>
      rw [polyTensorEquiv_monomial, IsBaseChange.equiv_tmul]
      refine LinearMap.ext fun x => ?_
      induction x using TensorProduct.inductionOn with
      | tmul p n =>
        rw [endPoly_monomial_tmul_apply, LinearMap.smul_apply, LinearMap.baseChangeHom_apply,
          LinearMap.baseChange_tmul, smul_tmul', smul_eq_mul, ← C_mul_X_pow_eq_monomial]
        congr 1
        ring
      | add x y hx hy => rw [map_add, hx, hy, map_add]
  have h : ⇑(endPoly N B) = Φ ∘ polyTensorEquiv N B := funext key
  rw [h]
  exact Φ.bijective.comp (polyTensorEquiv N B).bijective

theorem endCoeff_injective [Module.Flat A B] [Module.FinitePresentation A N] :
    Function.Injective (endCoeff N B (AlgHom.id A B)) := by
  let Φ := (Module.FinitePresentation.isBaseChange_map A N N B).equiv
  have key : ∀ t, endCoeff N B (AlgHom.id A B) t = Φ t := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul b φ =>
      rw [IsBaseChange.equiv_tmul]
      refine LinearMap.ext fun x => ?_
      induction x using TensorProduct.inductionOn with
      | tmul c n =>
        rw [endCoeff_tmul_apply, LinearMap.smul_apply, LinearMap.baseChangeHom_apply,
          LinearMap.baseChange_tmul, smul_tmul', smul_eq_mul, AlgHom.id_apply]
      | add x y hx hy => rw [map_add, hx, hy, map_add]
    | add s t hs ht => rw [map_add, hs, ht, map_add]
  have h : ⇑(endCoeff N B (AlgHom.id A B)) = Φ := funext key
  rw [h]
  exact Φ.injective

end Poly

end LeanPool.QuillenSuslin

