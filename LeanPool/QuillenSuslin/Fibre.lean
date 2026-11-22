/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.QuillenSuslin.Extended
public import LeanPool.QuillenSuslin.EndPolynomial


/-!
# The fibre at zero and normalised extension isomorphisms

For an `A[X]`-module `M`, its fibre at zero is the `A`-module `M(0) = A ⊗[A[X]] M`, with `A` an
`A[X]`-algebra through evaluation at `0` (`fibre`). For a commutative `A`-algebra `B` the
reduction `B[X] ⊗[A[X]] M → B ⊗[A] M(0)`, `p ⊗ m ↦ p(0) ⊗ (1 ⊗ m)`, is the base change to `B`
of the specialisation at zero (`fibreMap`). If `M` becomes extended after base change to `B`,
there is an isomorphism `B[X] ⊗[A] M(0) ≅ B[X] ⊗[A[X]] M` that reduces to the identity at zero
(`exists_normalized_equiv`), the normalisation needed in Quillen's patching argument (Quillen
1976, proof of Theorem 1, p. 168).

## References

* D. Quillen, *Projective modules over polynomial rings*, Invent. Math. 36 (1976), 167–171.
-/

@[expose] public noncomputable section

universe u v w

open Polynomial TensorProduct

namespace LeanPool.QuillenSuslin

/-- A commutative ring `R` as an `R[X]`-algebra through evaluation at zero. -/
abbrev evalZeroAlgebra (R : Type*) [CommRing R] : Algebra R[X] R := (evalRingHom 0).toAlgebra

variable (A : Type u) [CommRing A] (M : Type v) [AddCommGroup M] [Module A[X] M]

/-- The fibre `M(0) = A ⊗[A[X]] M` of an `A[X]`-module at zero. -/
abbrev fibre : Type (max u v) :=
  @TensorProduct A[X] _ A M _ _ (evalZeroAlgebra A).toModule _

instance : Module A (fibre A M) :=
  letI := evalZeroAlgebra A
  inferInstanceAs (Module A (A ⊗[A[X]] M))

instance [Module.FinitePresentation A[X] M] : Module.FinitePresentation A (fibre A M) :=
  letI := evalZeroAlgebra A
  instFinitePresentationTensorProduct

/-- The image `1 ⊗ m` of `m ∈ M` in the fibre. -/
def fibreMk (m : M) : fibre A M :=
  @TensorProduct.tmul A[X] _ A M _ _ (evalZeroAlgebra A).toModule _ 1 m

section FibreMap

variable (B : Type w) [CommRing B] [Algebra A B]

/-- `B` as an `A[X]`-algebra through `A[X] → A → B`, evaluating at zero. -/
abbrev evalZeroAlgebra' : Algebra A[X] B := ((algebraMap A B).comp (evalRingHom 0)).toAlgebra

theorem isScalarTower_evalZero₁ :
    letI := Polynomial.algebra A B
    letI := evalZeroAlgebra B
    letI := evalZeroAlgebra' A B
    IsScalarTower A[X] B[X] B := by
  let _ := Polynomial.algebra A B
  let _ := evalZeroAlgebra B
  let _ := evalZeroAlgebra' A B
  refine IsScalarTower.of_algebraMap_eq fun p => ?_
  change algebraMap A B (p.eval 0) = (p.map (algebraMap A B)).eval 0
  rw [← coeff_zero_eq_eval_zero, ← coeff_zero_eq_eval_zero, coeff_map]

theorem isScalarTower_evalZero₂ :
    letI := evalZeroAlgebra A
    letI := evalZeroAlgebra' A B
    IsScalarTower A[X] A B := by
  let _ := evalZeroAlgebra A
  let _ := evalZeroAlgebra' A B
  exact IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The fibre at zero of the base change `B[X] ⊗[A[X]] M` is `B ⊗[A] M(0)`. -/
def fibreEquiv :
    letI := Polynomial.algebra A B
    letI := evalZeroAlgebra B
    (B ⊗[B[X]] (B[X] ⊗[A[X]] M)) ≃ₗ[B] B ⊗[A] fibre A M :=
  letI := Polynomial.algebra A B
  letI := evalZeroAlgebra B
  letI := evalZeroAlgebra A
  letI := evalZeroAlgebra' A B
  haveI := isScalarTower_evalZero₁ A B
  haveI := isScalarTower_evalZero₂ A B
  AlgebraTensorModule.cancelBaseChange A[X] B[X] B B M ≪≫ₗ
    (AlgebraTensorModule.cancelBaseChange A[X] A B B M).symm

/-- The reduction `B[X] ⊗[A[X]] M → B ⊗[A] M(0)` at zero. -/
def fibreMap (y : letI := Polynomial.algebra A B; B[X] ⊗[A[X]] M) : B ⊗[A] fibre A M :=
  letI := Polynomial.algebra A B
  letI := evalZeroAlgebra B
  fibreEquiv A M B ((1 : B) ⊗ₜ[B[X]] y)

theorem fibreMap_add (y z : letI := Polynomial.algebra A B; B[X] ⊗[A[X]] M) :
    fibreMap A M B (y + z) = fibreMap A M B y + fibreMap A M B z := by
  simp only [fibreMap, tmul_add, map_add]

theorem fibreMap_tmul (p : B[X]) (m : M) :
    fibreMap A M B (letI := Polynomial.algebra A B; p ⊗ₜ[A[X]] m) = p.eval 0 ⊗ₜ fibreMk A M m := by
  let _ := Polynomial.algebra A B
  let _ := evalZeroAlgebra B
  let _ := evalZeroAlgebra A
  let _ := evalZeroAlgebra' A B
  have := isScalarTower_evalZero₁ A B
  have := isScalarTower_evalZero₂ A B
  simp only [fibreMap, fibreEquiv, LinearEquiv.trans_apply,
    AlgebraTensorModule.cancelBaseChange_tmul, AlgebraTensorModule.cancelBaseChange_symm_tmul]
  rw [Algebra.smul_def, mul_one]
  rfl

theorem fibreMap_smul (z : B[X]) (y : letI := Polynomial.algebra A B; B[X] ⊗[A[X]] M) :
    fibreMap A M B (z • y) = z.eval 0 • fibreMap A M B y := by
  let _ := Polynomial.algebra A B
  induction y using TensorProduct.inductionOn with
  | tmul p m => rw [smul_tmul', smul_eq_mul, fibreMap_tmul, fibreMap_tmul, eval_mul, smul_tmul',
      smul_eq_mul]
  | add x y hx hy => rw [smul_add, fibreMap_add, hx, hy, fibreMap_add, smul_add]

theorem fibreMap_surjective : Function.Surjective (fibreMap A M B) := by
  let _ := Polynomial.algebra A B
  let _ := evalZeroAlgebra B
  intro x
  obtain ⟨y, hy⟩ := surjective_tmul_evalZero (A := B) rfl (B[X] ⊗[A[X]] M)
    ((fibreEquiv A M B).symm x)
  refine ⟨y, ?_⟩
  simp only at hy
  rw [fibreMap, hy, LinearEquiv.apply_symm_apply]

/-- Naturality of the reduction at zero in the algebra `B`. -/
theorem fibreMap_natural {B' : Type*} [CommRing B'] [Algebra A B'] (β : B →ₐ[A] B')
    (ℓ : (letI := Polynomial.algebra A B; B[X] ⊗[A[X]] M) →+
      (letI := Polynomial.algebra A B'; B'[X] ⊗[A[X]] M))
    (hℓ : ∀ (p : B[X]) (m : M), ℓ (letI := Polynomial.algebra A B; p ⊗ₜ[A[X]] m) =
      (letI := Polynomial.algebra A B'; p.map β ⊗ₜ[A[X]] m))
    (y : letI := Polynomial.algebra A B; B[X] ⊗[A[X]] M) :
    fibreMap A M B' (ℓ y) = β.toLinearMap.rTensor (fibre A M) (fibreMap A M B y) := by
  let _ := Polynomial.algebra A B
  induction y using TensorProduct.inductionOn with
  | tmul p m =>
    rw [hℓ, fibreMap_tmul, fibreMap_tmul, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply,
      ← coeff_zero_eq_eval_zero, ← coeff_zero_eq_eval_zero, coeff_map]
    rfl
  | add x y hx hy => rw [map_add, fibreMap_add, hx, hy, fibreMap_add, map_add]

theorem isScalarTower_evalZero₃ :
    letI := evalZeroAlgebra B
    IsScalarTower B B[X] B := by
  let _ := evalZeroAlgebra B
  exact IsScalarTower.of_algebraMap_eq fun b => (eval_C (x := 0) (a := b)).symm

/-- **Normalised extension isomorphisms.** If `M` becomes extended after base change to `B`,
there is a `B[X]`-linear isomorphism `B[X] ⊗[A] M(0) ≅ B[X] ⊗[A[X]] M` reducing to the identity
of `B ⊗[A] M(0)` at zero. -/
theorem exists_normalized_equiv (h : IsExtendedAfter A B M) :
    ∃ u : (B[X] ⊗[A] fibre A M) ≃ₗ[B[X]] (letI := Polynomial.algebra A B; B[X] ⊗[A[X]] M),
      ∀ x, fibreMap A M B (u x) = reduce (fibre A M) B x := by
  let _ := Polynomial.algebra A B
  let _ := evalZeroAlgebra B
  have := isScalarTower_evalZero₃ B
  obtain ⟨N', _, _, ⟨e⟩⟩ := h
  let Γ : B ⊗[B[X]] (B[X] ⊗[B] N') ≃ₗ[B] N' :=
    AlgebraTensorModule.cancelBaseChange B B[X] B B N' ≪≫ₗ TensorProduct.lid B N'
  let Fe := e.baseChange B[X] B _ _
  let κ : N' ≃ₗ[B] B ⊗[A] fibre A M := Γ.symm ≪≫ₗ Fe.symm ≪≫ₗ fibreEquiv A M B
  have hΓ : ∀ w, Γ.symm w = (1 : B) ⊗ₜ ((1 : B[X]) ⊗ₜ w) := fun w => by
    rw [LinearEquiv.symm_apply_eq]
    simp [Γ]
  have hκ : ∀ w, κ w = fibreMap A M B (e.symm ((1 : B[X]) ⊗ₜ w)) := fun w => by
    simp only [κ, LinearEquiv.trans_apply, hΓ, Fe, LinearEquiv.baseChange_symm_tmul]
    rfl
  refine ⟨(AlgebraTensorModule.cancelBaseChange A B B[X] B[X] (fibre A M)).symm ≪≫ₗ
    κ.symm.baseChange B B[X] _ _ ≪≫ₗ e.symm, fun x => ?_⟩
  induction x using TensorProduct.inductionOn with
  | tmul p n =>
    simp only [LinearEquiv.trans_apply, AlgebraTensorModule.cancelBaseChange_symm_tmul,
      LinearEquiv.baseChange_tmul]
    have key : ∀ (q : B[X]) (w : N'), e.symm (q ⊗ₜ w) = q • e.symm ((1 : B[X]) ⊗ₜ w) :=
      fun q w => by
        rw [← LinearEquiv.map_smul]
        congr 1
        simp [smul_tmul']
    rw [key, fibreMap_smul, ← hκ, LinearEquiv.apply_symm_apply, reduce_tmul, smul_tmul']
    congr 1
    exact mul_one _
  | add x y hx hy => rw [map_add, fibreMap_add, hx, hy, map_add]

end FibreMap

end LeanPool.QuillenSuslin

