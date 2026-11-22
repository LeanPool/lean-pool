/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.QuillenSuslin.QuillenPatching

/-!
# Quillen patching relative to a base ring

Quillen's patching argument works over any localisation, not only at a prime ideal: an extension
isomorphism over `S⁻¹B[X]` descends to `B_s[X]` for some `s ∈ S`, since the modules involved are
finitely presented (`exists_mem_isExtendedAfter_away_of_isLocalization`). Combined with the
Quillen ideal, this gives a relative form of patching for an `A`-algebra `B`: a finitely
presented `B[X]`-module that becomes extended after inverting some `s ∉ m` of `A`, for every
maximal ideal `m` of `A`, is extended from `B` (`isExtendedFrom_of_forall_isMaximal_algebra`).
This relative form drives the induction on the number of variables in Quillen's Theorem 1′
(Quillen 1976, p. 169).

## Main results

* `exists_mem_isExtendedAfter_away_of_isLocalization`: descent from `S⁻¹B` to some `B_s`.
* `isExtendedFrom_of_isExtendedAfter_away_one`: extension after inverting `1` is extension.
* `isExtendedFrom_of_forall_isMaximal_algebra`: relative Quillen patching.

## References

* D. Quillen, *Projective modules over polynomial rings*, Invent. Math. 36 (1976), 167–171.
-/

@[expose] public noncomputable section

universe u v

open Polynomial TensorProduct

namespace LeanPool.QuillenSuslin

variable {B : Type u} [CommRing B] {M : Type v} [AddCommGroup M] [Module B[X] M]

/-- An extension isomorphism over `S⁻¹B[X]` descends to `B_s[X]` for some `s ∈ S`, for `M`
finitely presented. -/
theorem exists_mem_isExtendedAfter_away_of_isLocalization [Module.FinitePresentation B[X] M]
    (S : Submonoid B) (L : Type*) [CommRing L] [Algebra B L] [IsLocalization S L]
    (h : IsExtendedAfter B L M) :
    ∃ s ∈ S, IsExtendedAfter B (Localization.Away s) M := by
  let _ := Polynomial.algebra B L
  obtain ⟨u, -⟩ := exists_normalized_equiv B M L h
  have := isLocalizedModule_locP' S L (fibre B M)
  have := isLocalizedModule_mk_polynomial' S L M
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

/-- A `B[X]`-module that is extended after inverting `1` is extended. -/
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

/-- **Relative Quillen patching.** Let `B` be an `A`-algebra and `M` a finitely presented
`B[X]`-module. If for every maximal ideal `m` of `A` some `s ∉ m` is such that `M` becomes
extended after inverting the image of `s` in `B`, then `M` is extended from `B`. -/
theorem isExtendedFrom_of_forall_isMaximal_algebra {A : Type*} [CommRing A] [Algebra A B]
    [Module.FinitePresentation B[X] M]
    (h : ∀ m : Ideal A, m.IsMaximal →
      ∃ s ∉ m, IsExtendedAfter B (Localization.Away (algebraMap A B s)) M) :
    IsExtendedFrom B B[X] M := by
  obtain ⟨I, hI⟩ := exists_ideal_isExtendedAfter_away (A := B) M
  have htop : I.comap (algebraMap A B) = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := (I.comap (algebraMap A B)).exists_le_maximal hne
    obtain ⟨s, hs, hext⟩ := h m hm
    exact hs (hle ((hI _).mpr hext))
  have h1 : (1 : A) ∈ I.comap (algebraMap A B) := htop ▸ Submodule.mem_top
  rw [Ideal.mem_comap, map_one] at h1
  exact isExtendedFrom_of_isExtendedAfter_away_one ((hI 1).mp h1)

/-- **Relative Quillen patching, local form.** Let `B` be an `A`-algebra and `M` a finitely
presented `B[X]`-module. If for every maximal ideal `m` of `A`, `M` becomes extended over a
localisation of `B` at the image of `A ∖ m`, then `M` is extended from `B`. -/
theorem isExtendedFrom_of_forall_isMaximal_isLocalization {A : Type*} [CommRing A]
    [Algebra A B] [Module.FinitePresentation B[X] M]
    (h : ∀ (m : Ideal A) [m.IsMaximal], ∃ (L : Type u) (_ : CommRing L) (_ : Algebra B L)
      (_ : IsLocalization (m.primeCompl.map (algebraMap A B)) L), IsExtendedAfter B L M) :
    IsExtendedFrom B B[X] M := by
  refine isExtendedFrom_of_forall_isMaximal_algebra (A := A) fun m hm => ?_
  obtain ⟨L, _, _, _, hL⟩ := @h m hm
  obtain ⟨t, ht, hext⟩ := exists_mem_isExtendedAfter_away_of_isLocalization
    (m.primeCompl.map (algebraMap A B)) L hL
  obtain ⟨s, hs, rfl⟩ := ht
  exact ⟨s, hs, hext⟩

end LeanPool.QuillenSuslin
