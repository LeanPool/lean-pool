/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.PolynomialAlgebra

import Mathlib.Tactic.ReduceModChar

/-!
# Extended modules

A module `M` over an `A`-algebra `R` is *extended from `A`* when it is isomorphic to `R ⊗[A] N`
for an `A`-module `N` in the universe of `M` (Quillen 1976, p. 168; Lombardi–Quitté,
Section XVI.1). For an `A`-algebra `B`, an `A[X]`-module `M` is *extended after base change to
`B`* when `B[X] ⊗[A[X]] M` is extended from `B`; similarly over `A[X₁, …, Xₙ]`.

## Main results

* `IsExtendedFrom`, `IsExtendedAfter`, `IsExtendedAfterMv`: the three predicates.
* `isExtendedFrom_iff_evalZero`: an `A[X]`-module `M` is extended from `A` exactly when
  `M ≅ A[X] ⊗[A] M(0)`, with `M(0) = A ⊗[A[X]] M` along evaluation at `0` (Quillen 1976,
  p. 168; Lombardi–Quitté, Fact XVI.1.1).
* `IsExtendedFrom.isExtendedAfter`, `IsExtendedFrom.isExtendedAfterMv`: extended modules stay
  extended after base change.

## References

* D. Quillen, *Projective modules over polynomial rings*, Invent. Math. 36 (1976), 167–171.
* H. Lombardi, C. Quitté, *Commutative Algebra: Constructive Methods*, Springer, 2015.
-/

@[expose] public section

universe u v w w'

open Polynomial TensorProduct

namespace LeanPool.QuillenSuslin

/-- An `R`-module is extended from `A` when it is isomorphic to `R ⊗[A] N` for some `A`-module
`N` in the universe of `M`. -/
def IsExtendedFrom (A : Type u) (R : Type w) [CommRing A] [CommRing R] [Algebra A R]
    (M : Type v) [AddCommGroup M] [Module R M] : Prop :=
  ∃ (N : Type v) (_ : AddCommGroup N) (_ : Module A N), Nonempty (M ≃ₗ[R] R ⊗[A] N)

/-- For an `A`-algebra `B` and an `A[X]`-module `M`, the base change `B[X] ⊗[A[X]] M`
along `A[X] → B[X]` is extended from `B`. -/
def IsExtendedAfter (A : Type u) [CommRing A] (B : Type w) [CommRing B] [Algebra A B]
    (M : Type v) [AddCommGroup M] [Module A[X] M] : Prop :=
  letI : Algebra A[X] B[X] := Polynomial.algebra A B
  IsExtendedFrom B B[X] (B[X] ⊗[A[X]] M)

/-- For an `A`-algebra `B` and an `A[X₁, …, Xₙ]`-module `M`, the base change along
`A[X₁, …, Xₙ] → B[X₁, …, Xₙ]` is extended from `B`. -/
def IsExtendedAfterMv (A : Type u) [CommRing A] (B : Type w) [CommRing B] [Algebra A B] (n : ℕ)
    (M : Type v) [AddCommGroup M] [Module (MvPolynomial (Fin n) A) M] : Prop :=
  letI : Algebra (MvPolynomial (Fin n) A) (MvPolynomial (Fin n) B) :=
    MvPolynomial.algebraMvPolynomial
  IsExtendedFrom B (MvPolynomial (Fin n) B) (MvPolynomial (Fin n) B ⊗[MvPolynomial (Fin n) A] M)

section IsExtendedFrom

variable {A : Type u} {R : Type w} [CommRing A] [CommRing R] [Algebra A R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- An `R`-module isomorphic to `R ⊗[A] N` for an `A`-module `N` that is small in the universe
of `M` is extended from `A`. -/
theorem IsExtendedFrom.of_linearEquiv_tensor {N : Type w'} [AddCommGroup N] [Module A N]
    [Small.{v} N] (e : M ≃ₗ[R] R ⊗[A] N) : IsExtendedFrom A R M :=
  ⟨Shrink.{v} N, inferInstance, inferInstance,
    ⟨e ≪≫ₗ (AlgebraTensorModule.congr (LinearEquiv.refl R R) (Shrink.linearEquiv A N)).symm⟩⟩

/-- Being extended is invariant under linear isomorphism. -/
theorem isExtendedFrom_congr {M' : Type v} [AddCommGroup M'] [Module R M'] (e : M' ≃ₗ[R] M) :
    IsExtendedFrom A R M' ↔ IsExtendedFrom A R M :=
  ⟨fun ⟨N, _, _, ⟨f⟩⟩ => ⟨N, _, _, ⟨e.symm ≪≫ₗ f⟩⟩, fun ⟨N, _, _, ⟨f⟩⟩ => ⟨N, _, _, ⟨e ≪≫ₗ f⟩⟩⟩

/-- A module `R ⊗[A] N` is extended. -/
theorem isExtendedFrom_tensor (N : Type v) [AddCommGroup N] [Module A N] :
    IsExtendedFrom A R (R ⊗[A] N) :=
  .of_linearEquiv_tensor (LinearEquiv.refl _ _)

end IsExtendedFrom

section EvalZero

variable {A : Type u} [CommRing A]

/-- With `A` an `A[X]`-algebra through evaluation at `0`, the tower `A → A[X] → A` is the
identity. -/
theorem isScalarTower_evalZero [Algebra A[X] A] (hA : algebraMap A[X] A = evalRingHom 0) :
    IsScalarTower A A[X] A :=
  .of_algebraMap_eq' (by ext a; simp [hA])

/-- The specialisation map `M → M(0) = A ⊗[A[X]] M` is surjective. -/
theorem surjective_tmul_evalZero [Algebra A[X] A] (hA : algebraMap A[X] A = evalRingHom 0)
    (M : Type v) [AddCommGroup M] [Module A[X] M] :
    Function.Surjective fun m : M => (1 : A) ⊗ₜ[A[X]] m := by
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul a m =>
    refine ⟨C a • m, ?_⟩
    simp only
    rw [← smul_tmul, Algebra.smul_def, hA, coe_evalRingHom, eval_C, mul_one]
  | add x y hx hy =>
    obtain ⟨m, rfl⟩ := hx
    obtain ⟨n, rfl⟩ := hy
    exact ⟨m + n, tmul_add _ _ _⟩

/-- **3.1.** An `A[X]`-module is extended from `A` if and only if it is extended from its
specialisation `M(0) = A ⊗[A[X]] M` at `X = 0`, for `A` an `A[X]`-algebra through evaluation at
`0` (Quillen 1976, p. 168; Lombardi–Quitté, Fact XVI.1.1). -/
theorem isExtendedFrom_iff_evalZero [Algebra A[X] A] (hA : algebraMap A[X] A = evalRingHom 0)
    (M : Type v) [AddCommGroup M] [Module A[X] M] :
    IsExtendedFrom A A[X] M ↔ Nonempty (M ≃ₗ[A[X]] A[X] ⊗[A] (A ⊗[A[X]] M)) := by
  have := isScalarTower_evalZero hA
  constructor
  · rintro ⟨N, _, _, ⟨e⟩⟩
    let φ : (A ⊗[A[X]] M) ≃ₗ[A] N :=
      AlgebraTensorModule.congr (LinearEquiv.refl A A) e ≪≫ₗ
        AlgebraTensorModule.cancelBaseChange A A[X] A A N ≪≫ₗ TensorProduct.lid A N
    exact ⟨e ≪≫ₗ AlgebraTensorModule.congr (LinearEquiv.refl A[X] A[X]) φ.symm⟩
  · rintro ⟨e⟩
    have : Small.{v} (A ⊗[A[X]] M) := small_of_surjective (surjective_tmul_evalZero hA M)
    exact .of_linearEquiv_tensor e

end EvalZero

section BaseChange

variable {A : Type u} [CommRing A] {B : Type w} [CommRing B] [Algebra A B]

attribute [local instance] Polynomial.algebra

/-- `IsExtendedAfter A B M` is invariant under `A[X]`-linear isomorphism of `M`. -/
theorem isExtendedAfter_congr {M M' : Type v} [AddCommGroup M] [Module A[X] M]
    [AddCommGroup M'] [Module A[X] M'] (e : M' ≃ₗ[A[X]] M) :
    IsExtendedAfter A B M' ↔ IsExtendedAfter A B M :=
  isExtendedFrom_congr (e.baseChange A[X] B[X] M' M)

/-- Base change along `A → B` preserves extended modules:
`B[X] ⊗[A[X]] (A[X] ⊗[A] N) ≅ B[X] ⊗[B] (B ⊗[A] N)`. -/
theorem IsExtendedFrom.isExtendedAfter {M : Type v} [AddCommGroup M] [Module A[X] M]
    (h : IsExtendedFrom A A[X] M) : IsExtendedAfter A B M := by
  obtain ⟨N, _, _, ⟨e⟩⟩ := h
  exact .of_linearEquiv_tensor (e.baseChange A[X] B[X] _ _ ≪≫ₗ
    AlgebraTensorModule.cancelBaseChange A A[X] B[X] B[X] N ≪≫ₗ
    (AlgebraTensorModule.cancelBaseChange A B B[X] B[X] N).symm)

end BaseChange

section BaseChangeMv

variable {A : Type u} [CommRing A] {B : Type w} [CommRing B] [Algebra A B] {n : ℕ}

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- `IsExtendedAfterMv A B n M` is invariant under `A[X₁, …, Xₙ]`-linear isomorphism of `M`. -/
theorem isExtendedAfterMv_congr {M M' : Type v} [AddCommGroup M]
    [Module (MvPolynomial (Fin n) A) M] [AddCommGroup M'] [Module (MvPolynomial (Fin n) A) M']
    (e : M' ≃ₗ[MvPolynomial (Fin n) A] M) :
    IsExtendedAfterMv A B n M' ↔ IsExtendedAfterMv A B n M :=
  isExtendedFrom_congr (e.baseChange _ (MvPolynomial (Fin n) B) M' M)

/-- Base change along `A → B` preserves modules extended from `A` over `A[X₁, …, Xₙ]`. -/
theorem IsExtendedFrom.isExtendedAfterMv {M : Type v} [AddCommGroup M]
    [Module (MvPolynomial (Fin n) A) M] (h : IsExtendedFrom A (MvPolynomial (Fin n) A) M) :
    IsExtendedAfterMv A B n M := by
  obtain ⟨N, _, _, ⟨e⟩⟩ := h
  exact .of_linearEquiv_tensor (e.baseChange (MvPolynomial (Fin n) A) _ _ _ ≪≫ₗ
    AlgebraTensorModule.cancelBaseChange A (MvPolynomial (Fin n) A) (MvPolynomial (Fin n) B)
      (MvPolynomial (Fin n) B) N ≪≫ₗ
    (AlgebraTensorModule.cancelBaseChange A B (MvPolynomial (Fin n) B)
      (MvPolynomial (Fin n) B) N).symm)

end BaseChangeMv

end LeanPool.QuillenSuslin

