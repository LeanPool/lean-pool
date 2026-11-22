/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.QuillenSuslin.MvTransport
public import LeanPool.QuillenSuslin.PatchingDescent

import Mathlib.RingTheory.MvPolynomial.Localization

/-!
# Quillen patching in several variables

A finitely presented `A[X₁, …, Xₙ]`-module that is extended after localising at every maximal
ideal of `A` is extended from `A` (Quillen 1976, Theorem 1′, p. 169).

The proof is by induction on `n`. For `n = 0` every module is extended. For the inductive step
write `R = A[X₁, …, Xₙ₊₁] ≅ B[X]` with `B = A[X₁, …, Xₙ]` and move `M` to the `B[X]`-module
`M' = B[X] ⊗[R] M`. For a maximal ideal `m` of `A`, the ring `L = A_m[X₁, …, Xₙ]` is a
localisation of `B` at the image of `A ∖ m`, and the hypothesis at `m` becomes an isomorphism
`L[X] ⊗[B[X]] M' ≅ L[X] ⊗[A_m] Q`. Relative patching over `B` shows that `M'` is extended from
`B`, so `M' ≅ B[X] ⊗[B] M'(0)`; reducing the isomorphisms at `X = 0` shows that `M'(0)` satisfies
the hypothesis in `n` variables, so it is extended from `A` by induction, and so is `M`.

## Main results

* `isExtendedFrom_mvPolynomial_of_forall_isMaximal`: Quillen patching in `n` variables.

## References

* D. Quillen, *Projective modules over polynomial rings*, Invent. Math. 36 (1976), 167–171.
-/

@[expose] public noncomputable section

universe u v

open Polynomial TensorProduct

namespace LeanPool.QuillenSuslin

variable {A : Type u} [CommRing A]

/-- The algebra structure of `A[X₀, …, Xₙ]` on `A[X₁, …, Xₙ][X]` given by
`MvPolynomial.finSuccEquiv`. -/
abbrev finSuccAlgebra (A : Type u) [CommRing A] (n : ℕ) :
    Algebra (MvPolynomial (Fin (n + 1)) A) (MvPolynomial (Fin n) A)[X] :=
  (MvPolynomial.finSuccEquiv A n).toRingHom.toAlgebra

theorem isScalarTower_finSuccAlgebra (n : ℕ) :
    letI := finSuccAlgebra A n
    IsScalarTower A (MvPolynomial (Fin (n + 1)) A) (MvPolynomial (Fin n) A)[X] :=
  letI := finSuccAlgebra A n
  .of_algebraMap_eq fun a => ((MvPolynomial.finSuccEquiv A n).commutes a).symm

theorem bijective_finSuccAlgebra (n : ℕ) :
    Function.Bijective (letI := finSuccAlgebra A n;
      algebraMap (MvPolynomial (Fin (n + 1)) A) (MvPolynomial (Fin n) A)[X]) :=
  (MvPolynomial.finSuccEquiv A n).bijective

/-- The hypothesis of Quillen patching in `n + 1` variables over an `A`-algebra `A'`, moved to
`M' = B[X] ⊗[R] M`: with `L = A'[X₁, …, Xₙ]`, there is an isomorphism
`L[X] ⊗[B[X]] M' ≅ L[X] ⊗[A'] Q`. -/
theorem exists_equiv_of_isExtendedAfterMv (n : ℕ) {A' : Type u} [CommRing A'] [Algebra A A']
    {M : Type v} [AddCommGroup M] [Module (MvPolynomial (Fin (n + 1)) A) M]
    (h : IsExtendedAfterMv A A' (n + 1) M) :
    letI := finSuccAlgebra A n
    letI : Algebra (MvPolynomial (Fin n) A) (MvPolynomial (Fin n) A') :=
      MvPolynomial.algebraMvPolynomial
    letI := Polynomial.algebra (MvPolynomial (Fin n) A) (MvPolynomial (Fin n) A')
    ∃ (Q : Type (max u v)) (_ : AddCommGroup Q) (_ : Module A' Q),
      Nonempty ((MvPolynomial (Fin n) A')[X] ⊗[(MvPolynomial (Fin n) A)[X]]
        ((MvPolynomial (Fin n) A)[X] ⊗[MvPolynomial (Fin (n + 1)) A] M)
          ≃ₗ[(MvPolynomial (Fin n) A')[X]] (MvPolynomial (Fin n) A')[X] ⊗[A'] Q) := by
  let _ := finSuccAlgebra A n
  let _ : Algebra (MvPolynomial (Fin n) A) (MvPolynomial (Fin n) A') :=
    MvPolynomial.algebraMvPolynomial
  let _ := Polynomial.algebra (MvPolynomial (Fin n) A) (MvPolynomial (Fin n) A')
  let _ : Algebra (MvPolynomial (Fin (n + 1)) A) (MvPolynomial (Fin (n + 1)) A') :=
    MvPolynomial.algebraMvPolynomial
  obtain ⟨Q, _, _, ⟨e⟩⟩ := h
  exact ⟨Q, _, _, ⟨extensionEquivTransport (P := (MvPolynomial (Fin n) A)[X])
    (MvPolynomial.finSuccEquiv A' n) (fun r => by
      rw [Polynomial.algebraMap_def, MvPolynomial.algebraMap_def, RingHom.algebraMap_toAlgebra]
      exact finSuccEquiv_map (algebraMap A A') n r) e⟩⟩

/-- The inductive step of Quillen patching in several variables. -/
theorem isExtendedFrom_mvPolynomial_succ (n : ℕ)
    (ih : ∀ (N : Type v) [AddCommGroup N] [Module (MvPolynomial (Fin n) A) N]
      [Module.FinitePresentation (MvPolynomial (Fin n) A) N],
      (∀ (m : Ideal A) [m.IsMaximal], IsExtendedAfterMv A (Localization.AtPrime m) n N) →
        IsExtendedFrom A (MvPolynomial (Fin n) A) N)
    (M : Type v) [AddCommGroup M] [Module (MvPolynomial (Fin (n + 1)) A) M]
    [Module.FinitePresentation (MvPolynomial (Fin (n + 1)) A) M]
    (h : ∀ (m : Ideal A) [m.IsMaximal], IsExtendedAfterMv A (Localization.AtPrime m) (n + 1) M) :
    IsExtendedFrom A (MvPolynomial (Fin (n + 1)) A) M := by
  let B := MvPolynomial (Fin n) A
  let _ := finSuccAlgebra A n
  have := isScalarTower_finSuccAlgebra (A := A) n
  have hbij := bijective_finSuccAlgebra (A := A) n
  let M' := B[X] ⊗[MvPolynomial (Fin (n + 1)) A] M
  have hM' : IsExtendedFrom B B[X] M' := by
    refine isExtendedFrom_of_forall_isMaximal_isLocalization (A := A) fun m _ => ?_
    let _ : Algebra B (MvPolynomial (Fin n) (Localization.AtPrime m)) :=
      MvPolynomial.algebraMvPolynomial
    obtain ⟨Q, _, _, ⟨e⟩⟩ := exists_equiv_of_isExtendedAfterMv n (h m)
    exact ⟨MvPolynomial (Fin n) (Localization.AtPrime m), _, _,
      MvPolynomial.isLocalization m.primeCompl (Localization.AtPrime m),
      IsExtendedAfter.of_equiv_tensor e⟩
  let _ := evalZeroAlgebra B
  obtain ⟨e₁⟩ := (isExtendedFrom_iff_evalZero rfl M').mp hM'
  have : Small.{v} M' := small_of_surjective (surjective_tmul_of_bijective hbij M)
  have : Small.{v} (fibre B M') := small_of_surjective (surjective_tmul_evalZero rfl M')
  let N := Shrink.{v} (fibre B M')
  let eN : N ≃ₗ[B] fibre B M' := Shrink.linearEquiv B _
  have : Module.FinitePresentation B N := Module.FinitePresentation.of_equiv eN.symm
  have hN : ∀ (m : Ideal A) [m.IsMaximal], IsExtendedAfterMv A (Localization.AtPrime m) n N := by
    intro m _
    let _ : Algebra B (MvPolynomial (Fin n) (Localization.AtPrime m)) :=
      MvPolynomial.algebraMvPolynomial
    obtain ⟨Q, _, _, ⟨e⟩⟩ := exists_equiv_of_isExtendedAfterMv n (h m)
    exact .of_linearEquiv_tensor
      (AlgebraTensorModule.congr (LinearEquiv.refl _ _) eN ≪≫ₗ fibreEquivOfEquiv e)
  obtain ⟨N₀, _, _, ⟨e₀⟩⟩ := ih N hN
  let e' : M' ≃ₗ[B[X]] B[X] ⊗[A] N₀ := e₁ ≪≫ₗ
    AlgebraTensorModule.congr (LinearEquiv.refl B[X] B[X]) (eN.symm ≪≫ₗ e₀) ≪≫ₗ
      AlgebraTensorModule.cancelBaseChange A B B[X] B[X] N₀
  exact ⟨N₀, _, _, ⟨linearEquivOfBijective hbij e'⟩⟩

/-- **3.5.** Quillen patching in `n` variables: a finitely presented `A[X₁, …, Xₙ]`-module that
is extended after localising at every maximal ideal of `A` is extended from `A` (Quillen 1976,
Theorem 1′, p. 169). -/
theorem isExtendedFrom_mvPolynomial_of_forall_isMaximal (n : ℕ) (M : Type v) [AddCommGroup M]
    [Module (MvPolynomial (Fin n) A) M] [Module.FinitePresentation (MvPolynomial (Fin n) A) M]
    (h : ∀ (m : Ideal A) [m.IsMaximal], IsExtendedAfterMv A (Localization.AtPrime m) n M) :
    IsExtendedFrom A (MvPolynomial (Fin n) A) M := by
  induction n generalizing M with
  | zero =>
    exact isExtendedFrom_of_bijective
      ⟨MvPolynomial.C_injective _ _, MvPolynomial.C_surjective _⟩ M
  | succ n ih => exact isExtendedFrom_mvPolynomial_succ n (fun N _ _ _ hN => ih N hN) M h

end LeanPool.QuillenSuslin
