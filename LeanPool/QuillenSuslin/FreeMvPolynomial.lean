/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.QuillenSuslin.Bass
public import LeanPool.QuillenSuslin.QuillenLemmaTwo
public import LeanPool.QuillenSuslin.QuillenPatchingMv
public import Mathlib.RingTheory.DedekindDomain.Basic

import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Flat.TorsionFree

/-!
# The Quillen–Suslin theorem

Over a principal ideal domain `k`, every finitely generated projective module over
`k[X₁, …, Xₙ]` is free (Quillen 1976, Theorem 4, p. 169; Suslin 1976).

The proof is Quillen's induction on `n`, for all principal ideal domains at once. For `n = 0` the
ring is `k` itself. For the inductive step put `A = k[X₁, …, Xₙ]` and identify
`k[X₁, …, Xₙ₊₁]` with `A[T]` through `MvPolynomial.finSuccEquiv`. The ring
`B = k⟨T⟩[X₁, …, Xₙ]` is a polynomial ring in `n` variables over the principal ideal domain
`k⟨T⟩` (Quillen's Lemma 2), and there are ring maps `A[T] → B → A⟨T⟩` whose composite is the
localisation map: `T` goes to the class of `T` in `k⟨T⟩`, and a monic polynomial of `k[T]`
stays monic in `A[T]`. By induction `B ⊗[A[T]] P` is free over `B`, so
`A⟨T⟩ ⊗[A[T]] P ≅ A⟨T⟩ ⊗[B] (B ⊗[A[T]] P)` is free over `A⟨T⟩`, and Horrocks' theorem in
Quillen's form (`free_of_free_monicLocalization`) shows that `P` is free over `A[T]`.

The induction is run for modules in the universe of `k`; a finitely generated module is small
in that universe, which gives the general case.

Over a Dedekind domain `B`, every finitely generated projective `B[X₁, …, Xₙ]`-module is
extended from `B` (Quillen 1976, Theorem 4′, p. 170): the localisations of `B` at its maximal
ideals are principal ideal domains, and Quillen patching in `n` variables applies.

## Main results

* `toMonicCoeff`, `fromMonicCoeff`: the ring maps `A[T] → k⟨T⟩[X₁, …, Xₙ] → A⟨T⟩`.
* `free_mvPolynomial`: the Quillen–Suslin theorem.
* `isExtendedFrom_mvPolynomial`: the extended form over a Dedekind domain.

## References

* D. Quillen, *Projective modules over polynomial rings*, Invent. Math. 36 (1976), 167–171.
* A. A. Suslin, *Projective modules over polynomial rings are free*, Dokl. Akad. Nauk SSSR 229
  (1976), 1063–1066.
* T. Y. Lam, *Serre's Problem on Projective Modules*, Springer, 2006.
-/

@[expose] public noncomputable section

universe u v

open Polynomial TensorProduct

namespace LeanPool.QuillenSuslin

variable (k : Type u) [CommRing k] (n : ℕ)

/-- The ring map `A[T] → k⟨T⟩[X₁, …, Xₙ]`, for `A = k[X₁, …, Xₙ]`, which maps the coefficients
of `A` along `k → k⟨T⟩` and sends `T` to the class of `T` in `k⟨T⟩`. -/
def toMonicCoeff :
    (MvPolynomial (Fin n) k)[X] →+* MvPolynomial (Fin n) (Localization (monicSubmonoid k)) :=
  Polynomial.eval₂RingHom (MvPolynomial.map (algebraMap k (Localization (monicSubmonoid k))))
    (MvPolynomial.C (algebraMap k[X] (Localization (monicSubmonoid k)) X))

/-- The ring map `k⟨T⟩[X₁, …, Xₙ] → A⟨T⟩`, for `A = k[X₁, …, Xₙ]`, which is the map
`k⟨T⟩ → A⟨T⟩` on coefficients and sends `Xᵢ` to the class of the constant polynomial `Xᵢ`. -/
def fromMonicCoeff : MvPolynomial (Fin n) (Localization (monicSubmonoid k)) →+*
    Localization (monicSubmonoid (MvPolynomial (Fin n) k)) :=
  letI := Polynomial.algebra k (MvPolynomial (Fin n) k)
  letI := monicLocalizationAlgebra (A := k) (MvPolynomial (Fin n) k)
  MvPolynomial.eval₂Hom (algebraMap _ _)
    fun i => algebraMap (MvPolynomial (Fin n) k)[X] _ (C (MvPolynomial.X i))

/-- The composite `A[T] → k⟨T⟩[X₁, …, Xₙ] → A⟨T⟩` is the localisation map. -/
theorem fromMonicCoeff_comp_toMonicCoeff :
    (fromMonicCoeff k n).comp (toMonicCoeff k n) =
      algebraMap (MvPolynomial (Fin n) k)[X]
        (Localization (monicSubmonoid (MvPolynomial (Fin n) k))) := by
  let _ := Polynomial.algebra k (MvPolynomial (Fin n) k)
  let _ := monicLocalizationAlgebra (A := k) (MvPolynomial (Fin n) k)
  have := isScalarTower_monicLocalization (A := k) (MvPolynomial (Fin n) k)
  have := isScalarTower_monicLocalization' (A := k) (MvPolynomial (Fin n) k)
  refine Polynomial.ringHom_ext (fun a => ?_) ?_
  · refine RingHom.congr_fun (MvPolynomial.ringHom_ext
      (f := ((fromMonicCoeff k n).comp (toMonicCoeff k n)).comp C)
      (g := (algebraMap (MvPolynomial (Fin n) k)[X]
        (Localization (monicSubmonoid (MvPolynomial (Fin n) k)))).comp C)
      (fun c => ?_) (fun i => ?_)) a
    · simp only [toMonicCoeff, fromMonicCoeff, RingHom.comp_apply, coe_eval₂RingHom, eval₂_C,
        MvPolynomial.map_C, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]
      rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply k
        (MvPolynomial (Fin n) k)[X]]
      rfl
    · simp [toMonicCoeff, fromMonicCoeff]
  · simp only [toMonicCoeff, fromMonicCoeff, RingHom.comp_apply, coe_eval₂RingHom, eval₂_X,
      MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply k[X]
      (MvPolynomial (Fin n) k)[X]]
    simp

/-- A finitely generated projective module over `k[X₁, …, Xₙ]` with `n = 0` is free. -/
theorem free_mvPolynomial_zero (k : Type u) [CommRing k] [IsDomain k] [IsPrincipalIdealRing k]
    (P : Type v) [AddCommGroup P] [Module (MvPolynomial (Fin 0) k) P]
    [Module.Finite (MvPolynomial (Fin 0) k) P] [Module.Projective (MvPolynomial (Fin 0) k) P] :
    Module.Free (MvPolynomial (Fin 0) k) P := by
  have : IsPrincipalIdealRing (MvPolynomial (Fin 0) k) :=
    IsPrincipalIdealRing.of_surjective (MvPolynomial.C : k →+* _) (MvPolynomial.C_surjective _)
  exact Module.free_of_finite_type_torsion_free'

/-- Let `A[X] → B → A⟨X⟩` be ring maps whose composite is the localisation map. If every
finitely generated projective `B`-module is free, then so is every finitely generated projective
`A[X]`-module (by Horrocks' theorem in Quillen's form). -/
theorem free_of_factor_monicLocalization {A : Type u} [CommRing A] {B : Type u} [CommRing B]
    (φ : A[X] →+* B) (ψ : B →+* Localization (monicSubmonoid A))
    (hψφ : ψ.comp φ = algebraMap A[X] (Localization (monicSubmonoid A)))
    (hB : ∀ (Q : Type (max u v)) [AddCommGroup Q] [Module B Q] [Module.Finite B Q]
      [Module.Projective B Q], Module.Free B Q)
    (P : Type v) [AddCommGroup P] [Module A[X] P] [Module.Finite A[X] P]
    [Module.Projective A[X] P] : Module.Free A[X] P := by
  let _ : Algebra A[X] B := φ.toAlgebra
  let _ : Algebra B (Localization (monicSubmonoid A)) := ψ.toAlgebra
  have : IsScalarTower A[X] B (Localization (monicSubmonoid A)) :=
    .of_algebraMap_eq fun x => (RingHom.congr_fun hψφ x).symm
  have := hB (B ⊗[A[X]] P)
  exact free_of_free_monicLocalization P (Module.Free.of_equiv
    (AlgebraTensorModule.cancelBaseChange A[X] B (Localization (monicSubmonoid A))
      (Localization (monicSubmonoid A)) P))

/-- The inductive step of the Quillen–Suslin theorem, for modules in the universe of `k`. -/
theorem free_mvPolynomial_succ (n : ℕ)
    (ih : ∀ (K : Type u) [CommRing K] [IsDomain K] [IsPrincipalIdealRing K] (Q : Type u)
      [AddCommGroup Q] [Module (MvPolynomial (Fin n) K) Q]
      [Module.Finite (MvPolynomial (Fin n) K) Q] [Module.Projective (MvPolynomial (Fin n) K) Q],
      Module.Free (MvPolynomial (Fin n) K) Q)
    (k : Type u) [CommRing k] [IsDomain k] [IsPrincipalIdealRing k]
    (P : Type u) [AddCommGroup P] [Module (MvPolynomial (Fin (n + 1)) k) P]
    [Module.Finite (MvPolynomial (Fin (n + 1)) k) P]
    [Module.Projective (MvPolynomial (Fin (n + 1)) k) P] :
    Module.Free (MvPolynomial (Fin (n + 1)) k) P := by
  let _ := finSuccAlgebra k n
  have hbij := bijective_finSuccAlgebra (A := k) n
  obtain ⟨_, _⟩ := isPrincipalIdealRing_monicLocalization k
  have := free_of_factor_monicLocalization (toMonicCoeff k n) (fromMonicCoeff k n)
    (fromMonicCoeff_comp_toMonicCoeff k n) (fun Q _ _ _ _ => ih _ Q)
    ((MvPolynomial (Fin n) k)[X] ⊗[MvPolynomial (Fin (n + 1)) k] P)
  have : Module.Free (MvPolynomial (Fin (n + 1)) k) (MvPolynomial (Fin n) k)[X] :=
    Module.Free.of_equiv (LinearEquiv.ofBijective (Algebra.linearMap _ _) hbij)
  have : Module.Free (MvPolynomial (Fin (n + 1)) k)
      ((MvPolynomial (Fin n) k)[X] ⊗[MvPolynomial (Fin (n + 1)) k] P) :=
    Module.Free.trans (S := (MvPolynomial (Fin n) k)[X])
  exact Module.Free.of_equiv (equivBaseChangeOfBijective hbij P).symm

/-- The Quillen–Suslin theorem for modules in the universe of `k`. -/
theorem free_mvPolynomial_of_univ (n : ℕ) : ∀ (k : Type u) [CommRing k] [IsDomain k]
    [IsPrincipalIdealRing k] (P : Type u) [AddCommGroup P] [Module (MvPolynomial (Fin n) k) P]
    [Module.Finite (MvPolynomial (Fin n) k) P] [Module.Projective (MvPolynomial (Fin n) k) P],
    Module.Free (MvPolynomial (Fin n) k) P := by
  induction n with
  | zero => exact fun k _ _ _ P _ _ _ _ => free_mvPolynomial_zero k P
  | succ n ih => exact fun k _ _ _ P _ _ _ _ => free_mvPolynomial_succ n ih k P

/-- **5.2.** The Quillen–Suslin theorem: over a principal ideal domain `k`, every finitely
generated projective `k[X₁, …, Xₙ]`-module is free (Quillen 1976, Theorem 4, p. 169;
Suslin 1976). -/
theorem free_mvPolynomial (k : Type u) [CommRing k] [IsDomain k] [IsPrincipalIdealRing k] (n : ℕ)
    (P : Type v) [AddCommGroup P] [Module (MvPolynomial (Fin n) k) P]
    [Module.Finite (MvPolynomial (Fin n) k) P] [Module.Projective (MvPolynomial (Fin n) k) P] :
    Module.Free (MvPolynomial (Fin n) k) P := by
  have : Small.{u} P := Module.Finite.small (MvPolynomial (Fin n) k) P
  let e : Shrink.{u} P ≃ₗ[MvPolynomial (Fin n) k] P := Shrink.linearEquiv _ P
  have : Module.Finite (MvPolynomial (Fin n) k) (Shrink.{u} P) := Module.Finite.equiv e.symm
  have : Module.Projective (MvPolynomial (Fin n) k) (Shrink.{u} P) :=
    Module.Projective.of_equiv e.symm
  have := free_mvPolynomial_of_univ n k (Shrink.{u} P)
  exact Module.Free.of_equiv e

/-- A free `R`-module is extended from `A`, for every `A`-algebra `R`. -/
theorem IsExtendedFrom.of_free {A : Type u} {R : Type*} [CommRing A] [CommRing R] [Algebra A R]
    {M : Type (max u v)} [AddCommGroup M] [Module R M] [Module.Free R M] : IsExtendedFrom A R M :=
  .of_linearEquiv_tensor ((Module.Free.chooseBasis R M).repr ≪≫ₗ
    (finsuppScalarRight A R R _).symm)

/-- **5.3.** Over a Dedekind domain `B`, every finitely generated projective
`B[X₁, …, Xₙ]`-module is extended from `B` (Quillen 1976, Theorem 4′, p. 170): at a maximal
ideal `m`, the local Dedekind domain `B_m` is a principal ideal domain, so the base change of the
module to `B_m[X₁, …, Xₙ]` is free by the Quillen–Suslin theorem, and Quillen patching in `n`
variables concludes. -/
theorem isExtendedFrom_mvPolynomial (B : Type u) [CommRing B] [IsDedekindDomain B] (n : ℕ)
    (P : Type v) [AddCommGroup P] [Module (MvPolynomial (Fin n) B) P]
    [Module.Finite (MvPolynomial (Fin n) B) P] [Module.Projective (MvPolynomial (Fin n) B) P] :
    IsExtendedFrom B (MvPolynomial (Fin n) B) P := by
  have := Module.finitePresentation_of_projective (MvPolynomial (Fin n) B) P
  refine isExtendedFrom_mvPolynomial_of_forall_isMaximal n P fun m _ => ?_
  let _ : Algebra (MvPolynomial (Fin n) B) (MvPolynomial (Fin n) (Localization.AtPrime m)) :=
    MvPolynomial.algebraMvPolynomial
  have := free_mvPolynomial (Localization.AtPrime m) n
    (MvPolynomial (Fin n) (Localization.AtPrime m) ⊗[MvPolynomial (Fin n) B] P)
  exact IsExtendedFrom.of_free

end LeanPool.QuillenSuslin
