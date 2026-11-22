/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.QuillenSuslin.QuillenIdeal
public import Mathlib.RingTheory.Localization.AtPrime.Basic

import Mathlib.RingTheory.Localization.Algebra

/-!
# Quillen's patching theorem

A finitely presented `A[X]`-module that is extended after localising at every maximal ideal of
`A` is extended from `A` (Quillen 1976, Theorem 1, p. 168). An extension isomorphism over `A_m`
descends to some `A_s` with `s ∉ m`, since the modules are finitely presented; so the Quillen
ideal lies in no maximal ideal and contains `1`.

## Main results

* `exists_mem_isExtendedAfter_away_of_isLocalization`: descent from `S⁻¹A` to some `A_s`.
* `exists_notMem_isExtendedAfter_away`: descent from `A_m` to some `A_s`.
* `isExtendedFrom_of_isExtendedAfter_away_one`: extension after inverting `1` is extension.
* `isExtendedFrom_of_forall_isMaximal`: Quillen's patching theorem.

## References

* D. Quillen, *Projective modules over polynomial rings*, Invent. Math. 36 (1976), 167–171.
-/

@[expose] public noncomputable section

universe u v

open Polynomial TensorProduct

namespace LeanPool.QuillenSuslin

section Localization

variable {A : Type u} [CommRing A]
variable (S : Submonoid A) (B : Type*) [CommRing B] [Algebra A B] [IsLocalization S B]

/-- The localization of an extended module along a coefficient submonoid. -/
theorem isLocalizedModule_locP' (N : Type*) [AddCommGroup N] [Module A N] :
    letI := Polynomial.algebra A B
    IsLocalizedModule (S.map C) (locP B N) :=
  isLocalizedModule_locP_of_isLocalization S B N

/-- Base change along the localization of the polynomial coefficients. -/
theorem isLocalizedModule_mk_polynomial' (M : Type*) [AddCommGroup M] [Module A[X] M] :
    letI := Polynomial.algebra A B
    IsLocalizedModule (S.map C) (TensorProduct.mk A[X] B[X] M 1) :=
  isLocalizedModule_mk_polynomial_of_isLocalization S B M

end Localization

theorem bijective_of_isLocalizedModule_powers_one {R M M' : Type*} [CommRing R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M'] (f : M →ₗ[R] M')
    [IsLocalizedModule (Submonoid.powers (1 : R)) f] : Function.Bijective f := by
  have h1 : ∀ c : Submonoid.powers (1 : R), (c : R) = 1 := fun c => by
    obtain ⟨n, hn⟩ := c.2
    rw [← hn]; exact one_pow n
  refine ⟨fun x y hxy => ?_, fun y => ?_⟩
  · obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers (1 : R)) hxy
    simpa [Submonoid.smul_def, h1] using hc
  · obtain ⟨⟨x, c⟩, hc⟩ := IsLocalizedModule.surj (Submonoid.powers (1 : R)) f y
    exact ⟨x, by simpa [Submonoid.smul_def, h1] using hc.symm⟩

section Descent

variable {B : Type u} [CommRing B] {M : Type v} [AddCommGroup M] [Module B[X] M]

/-- An extension isomorphism over `S⁻¹B[X]` descends to `B_s[X]` for some `s ∈ S`, for `M`
finitely presented. -/
theorem exists_mem_isExtendedAfter_away_of_isLocalization [Module.FinitePresentation B[X] M]
    (S : Submonoid B) (L : Type*) [CommRing L] [Algebra B L] [IsLocalization S L]
    (h : IsExtendedAfter B L M) :
    ∃ s ∈ S, IsExtendedAfter B (Localization.Away s) M := by
  let _ := Polynomial.algebra B L
  obtain ⟨u, -⟩ := exists_normalized_equiv B M L h
  have := isLocalizedModule_locP_of_isLocalization S L (fibre B M)
  have := isLocalizedModule_mk_polynomial_of_isLocalization S L M
  obtain ⟨r, hr, l', -⟩ := Module.FinitePresentation.exists_lift_equiv_of_isLocalizedModule
    (S.map C) (locP L (fibre B M)) (TensorProduct.mk B[X] L[X] M 1)
    (u.restrictScalars B[X])
  obtain ⟨s, hs, rfl⟩ := hr
  refine ⟨s, hs, ?_⟩
  let Bs := Localization.Away s
  let _ := Polynomial.algebra B Bs
  have := isLocalizedModule_locP s Bs (fibre B M)
  have := isLocalizedModule_mk_polynomial s Bs M
  have := isLocalization_polynomial_away s Bs
  let e := (IsLocalizedModule.iso (Submonoid.powers (C s)) (locP Bs (fibre B M))).symm ≪≫ₗ
    l'.restrictScalars B[X] ≪≫ₗ
      IsLocalizedModule.iso (Submonoid.powers (C s)) (TensorProduct.mk B[X] Bs[X] M 1)
  exact isExtendedAfter_of_equiv (e.extendScalarsOfIsLocalization (Submonoid.powers (C s)) Bs[X])

/-- An `B[X]`-module that is extended after inverting `1` is extended. -/
theorem isExtendedFrom_of_isExtendedAfter_away_one
    (h : IsExtendedAfter B (Localization.Away (1 : B)) M) : IsExtendedFrom B B[X] M := by
  obtain ⟨u, -⟩ := exists_normalized_equiv B M _ h
  let L := Localization.Away (1 : B)
  let _ := Polynomial.algebra B L
  have hP : IsLocalizedModule (Submonoid.powers (1 : B[X])) (locP L (fibre B M)) := by
    have := isLocalizedModule_locP (1 : B) L (fibre B M)
    rwa [map_one] at this
  have hM : IsLocalizedModule (Submonoid.powers (1 : B[X])) (TensorProduct.mk B[X] L[X] M 1) := by
    have := isLocalizedModule_mk_polynomial (1 : B) L M
    rwa [map_one] at this
  let eP := LinearEquiv.ofBijective (locP (A := B) L (fibre B M))
    (bijective_of_isLocalizedModule_powers_one _)
  let eM := LinearEquiv.ofBijective (TensorProduct.mk B[X] L[X] M 1)
    (bijective_of_isLocalizedModule_powers_one _)
  exact .of_polynomial_linearEquiv (eM ≪≫ₗ u.symm.restrictScalars B[X] ≪≫ₗ eP.symm)

end Descent

variable {A : Type u} [CommRing A] {M : Type v} [AddCommGroup M] [Module A[X] M]

/-- An extension isomorphism over `A_p[X]` descends to `A_s[X]` for some `s ∉ p`, for `M`
finitely presented. -/
theorem exists_notMem_isExtendedAfter_away [Module.FinitePresentation A[X] M] (p : Ideal A)
    [p.IsPrime] (h : IsExtendedAfter A (Localization.AtPrime p) M) :
    ∃ s ∉ p, IsExtendedAfter A (Localization.Away s) M :=
  exists_mem_isExtendedAfter_away_of_isLocalization p.primeCompl _ h

variable (M) in
/-- **3.4.** Quillen patching: a finitely presented `A[X]`-module that is extended at every
maximal ideal of `A` is extended (Quillen 1976, Theorem 1, p. 168). -/
theorem isExtendedFrom_of_forall_isMaximal [Module.FinitePresentation A[X] M]
    (h : ∀ (m : Ideal A) [m.IsMaximal], IsExtendedAfter A (Localization.AtPrime m) M) :
    IsExtendedFrom A A[X] M := by
  obtain ⟨I, hI⟩ := exists_ideal_isExtendedAfter_away (A := A) M
  have htop : I = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := I.exists_le_maximal hne
    obtain ⟨s, hs, hext⟩ := exists_notMem_isExtendedAfter_away m (@h m hm)
    exact hs (hle ((hI s).mpr hext))
  exact isExtendedFrom_of_isExtendedAfter_away_one ((hI 1).mp (htop ▸ Submodule.mem_top))

end LeanPool.QuillenSuslin

