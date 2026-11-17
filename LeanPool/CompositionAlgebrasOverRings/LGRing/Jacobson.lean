/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import LeanPool.CompositionAlgebrasOverRings.LGRing.Defs
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.Jacobson.Radical

/-!
# `R` is LG iff `R ⧸ Jac(R)` is LG

The Jacobson-quotient half of `GPR 11.21` (`GN 2.1(b)`): `R` is an LG-ring iff `R ⧸ Jac(R)` is.
The other half of `GPR 11.21` (finite products of LG-rings are LG) is not covered here — see
`LGRing/Products.lean`.

## Main results

* `isLGRing_iff_isLGRing_quotient_jacobson` : `IsLGRing R ↔ IsLGRing (R ⧸ Ring.jacobson R)`.

## Proof idea

Every maximal ideal `𝔪` of `R` **contains** `Jac(R)` (it is the intersection of all of them), so
maximal ideals of `R` correspond exactly to maximal ideals of `R ⧸ Jac(R)`, via `𝔪 ↦ 𝔪.map π` and
back via `comap π`, where `π : R → R ⧸ Jac(R)` is the quotient map — and the residue fields agree on
the nose: `R ⧸ 𝔪 ≅ (R ⧸ Jac(R)) ⧸ 𝔪.map π` (`residueFieldQuotientJacobsonEquiv`, which is mathlib's
third isomorphism theorem `DoubleQuot.quotQuotEquivQuotOfLE`, applicable because `Jac(R) ≤ 𝔪`).
Transporting a witness for `p.RepresentsUnit` back and forth along this isomorphism and along
`MvPolynomial.map π` (`aeval_comp_residueFieldQuotientJacobsonEquiv`, `aeval_map_quotient`) turns
"`p` represents a unit at every residue field of `R`" into "`p`'s image represents a unit at every
residue field of `R ⧸ Jac(R)`" and back (`represents_unit_quotient_jacobson_of_forall`,
`represents_unit_of_forall_quotient_jacobson`).

The one place this needs more than bookkeeping: going from "`p`'s image represents a unit over
`R ⧸ Jac(R)`" back to "`p` represents a unit over `R`" needs that a witness whose *image* is a
unit modulo `Jac(R)` was *already* a unit in `R` (`isUnit_of_isUnit_image_jacobson`) — this is
specific to the Jacobson radical (it is false for a general quotient) and is where `1 - j` being a
unit for `j ∈ Jac(R)` actually gets used.

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, 11.21(i).
* [GN] Gille, Neher, *Group schemes over LG-rings and applications to cancellation theorems and
  Azumaya algebras*, European Journal of Mathematics **11** (2025), article 42, §2.1(b).
-/

@[expose] public section

universe u v

/-- If the image of `x` under `R → R ⧸ Jac(R)` is a unit, so is `x` itself. This is specific to
the Jacobson radical: `xz ≡ 1 mod Jac(R)` gives `xz - 1 ∈ Jac(R)`, hence `xz` is a unit (elements
of `1 + Jac(R)` are always units), hence (commutativity) `x` is a unit. -/
theorem isUnit_of_isUnit_image_jacobson {R : Type u} [CommRing R] (x : R)
    (h : IsUnit (Ideal.Quotient.mk (Ring.jacobson R) x)) : IsUnit x := by
  obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (↑h.unit⁻¹ : R ⧸ Ring.jacobson R)
  have hxz : Ideal.Quotient.mk (Ring.jacobson R) (x * z) =
      Ideal.Quotient.mk (Ring.jacobson R) 1 := by
    rw [map_mul, hz, map_one]; exact h.mul_val_inv
  have hmem : x * z - 1 ∈ Ring.jacobson R := Ideal.Quotient.eq.mp hxz
  have hunit_xz : IsUnit (x * z) := by
    apply Ideal.isUnit_of_sub_one_mem_jacobson_bot; rwa [Ideal.jacobson_bot]
  exact isUnit_of_mul_isUnit_left hunit_xz

/-- The residue field of `R` at a maximal ideal `𝔪` agrees with the residue field of
`R ⧸ Jac(R)` at the corresponding maximal ideal `𝔪.map π` (`π` the quotient-by-`Jac(R)` map).
This is mathlib's third isomorphism theorem `DoubleQuot.quotQuotEquivQuotOfLE`, which applies
because `Jac(R) ≤ 𝔪`. -/
noncomputable def residueFieldQuotientJacobsonEquiv {R : Type u} [CommRing R] (𝔪 : Ideal R)
    [h𝔪 : 𝔪.IsMaximal] :
    R ⧸ 𝔪 ≃+*
      (R ⧸ Ring.jacobson R) ⧸ Ideal.map (Ideal.Quotient.mk (Ring.jacobson R)) 𝔪 :=
  (DoubleQuot.quotQuotEquivQuotOfLE <| by
    rw [Ring.jacobson_eq_sInf_isMaximal]; exact sInf_le h𝔪).symm

@[simp]
theorem residueFieldQuotientJacobsonEquiv_apply {R : Type u} [CommRing R] (𝔪 : Ideal R)
    [𝔪.IsMaximal] (r : R) :
    residueFieldQuotientJacobsonEquiv 𝔪 (Ideal.Quotient.mk 𝔪 r) =
      Ideal.Quotient.mk (Ideal.map (Ideal.Quotient.mk (Ring.jacobson R)) 𝔪)
        (Ideal.Quotient.mk (Ring.jacobson R) r) :=
  rfl

/-- `aeval` commutes with `residueFieldQuotientJacobsonEquiv`: evaluating `p` at a point of
`R ⧸ 𝔪` and transporting the result along the equivalence agrees with reducing `p`'s coefficients
mod `Jac(R)` first and evaluating at the transported point. -/
theorem aeval_comp_residueFieldQuotientJacobsonEquiv {R : Type u} [CommRing R] {n : ℕ}
    (p : MvPolynomial (Fin n) R) (𝔪 : Ideal R) [𝔪.IsMaximal] (s : Fin n → R ⧸ 𝔪) :
    residueFieldQuotientJacobsonEquiv 𝔪 (MvPolynomial.aeval s p) =
      MvPolynomial.aeval (fun i ↦ residueFieldQuotientJacobsonEquiv 𝔪 (s i))
        (MvPolynomial.map (Ideal.Quotient.mk (Ring.jacobson R)) p) := by
  simp only [MvPolynomial.aeval_def]
  have heq := MvPolynomial.hom_eval₂ p (algebraMap R (R ⧸ 𝔪))
    (residueFieldQuotientJacobsonEquiv 𝔪).toRingHom s
  simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe] at heq
  rw [heq, MvPolynomial.eval₂_map]
  congr 1

/-- `aeval` commutes with reduction mod any ideal `J`: evaluating `p` at a point of `R` and then
reducing mod `J` agrees with reducing `p`'s coefficients mod `J` first and evaluating at the
reduced point. -/
theorem aeval_map_quotient {R : Type u} [CommRing R] (J : Ideal R) {n : ℕ}
    (p : MvPolynomial (Fin n) R) (t : Fin n → R) :
    Ideal.Quotient.mk J (MvPolynomial.aeval t p) =
      MvPolynomial.aeval (fun i ↦ Ideal.Quotient.mk J (t i))
        (MvPolynomial.map (Ideal.Quotient.mk J) p) := by
  simp only [MvPolynomial.aeval_def]
  rw [MvPolynomial.hom_eval₂, MvPolynomial.eval₂_map]
  congr 1

/-- If `p` represents a unit at every residue field of `R`, its image under `R → R ⧸ Jac(R)`
represents a unit at every residue field of `R ⧸ Jac(R)`: every maximal ideal `𝔐` of
`R ⧸ Jac(R)` is `𝔪.map π` for `𝔪 := comap π 𝔐` maximal in `R`, and the residue fields agree via
`residueFieldQuotientJacobsonEquiv`. -/
theorem represents_unit_quotient_jacobson_of_forall {R : Type u} [CommRing R] {n : ℕ}
    (p : MvPolynomial (Fin n) R)
    (hwit : ∀ (𝔪 : Ideal R) [𝔪.IsMaximal], p.RepresentsUnit (R ⧸ 𝔪)) :
    ∀ (𝔐 : Ideal (R ⧸ Ring.jacobson R)) [𝔐.IsMaximal],
      (MvPolynomial.map (Ideal.Quotient.mk (Ring.jacobson R)) p).RepresentsUnit
        ((R ⧸ Ring.jacobson R) ⧸ 𝔐) := by
  set J := Ring.jacobson R with hJdef
  set π := Ideal.Quotient.mk J with hπdef
  have hsurj : Function.Surjective π := Ideal.Quotient.mk_surjective
  intro 𝔐 hmax𝔐
  have h𝔪max : (Ideal.comap π 𝔐).IsMaximal := Ideal.comap_isMaximal_of_surjective π hsurj
  have hcm : Ideal.map π (Ideal.comap π 𝔐) = 𝔐 :=
    Ideal.map_comap_of_surjective π hsurj 𝔐
  rw [← hcm]
  obtain ⟨s, hs⟩ := hwit (Ideal.comap π 𝔐)
  refine ⟨fun i ↦ residueFieldQuotientJacobsonEquiv (Ideal.comap π 𝔐) (s i), ?_⟩
  rw [← aeval_comp_residueFieldQuotientJacobsonEquiv]
  exact hs.map _

/-- Conversely, if the image of `p` under `R → R ⧸ Jac(R)` represents a unit at every residue
field of `R ⧸ Jac(R)`, then `p` itself represents a unit at every residue field of `R`: for `𝔪`
maximal in `R`, `𝔪.map π` is maximal in `R ⧸ Jac(R)` (`Jac(R) ≤ 𝔪` supplies the kernel
hypothesis), and the residue fields agree via `residueFieldQuotientJacobsonEquiv`. -/
theorem represents_unit_of_forall_quotient_jacobson {R : Type u} [CommRing R] {n : ℕ}
    (p : MvPolynomial (Fin n) R)
    (hwit : ∀ (𝔐 : Ideal (R ⧸ Ring.jacobson R)) [𝔐.IsMaximal],
      (MvPolynomial.map (Ideal.Quotient.mk (Ring.jacobson R)) p).RepresentsUnit
        ((R ⧸ Ring.jacobson R) ⧸ 𝔐)) :
    ∀ (𝔪 : Ideal R) [𝔪.IsMaximal], p.RepresentsUnit (R ⧸ 𝔪) := by
  set J := Ring.jacobson R with hJdef
  set π := Ideal.Quotient.mk J with hπdef
  have hsurj : Function.Surjective π := Ideal.Quotient.mk_surjective
  intro 𝔪 hmax𝔪
  have hJm : J ≤ 𝔪 := by
    rw [hJdef, Ring.jacobson_eq_sInf_isMaximal]; exact sInf_le hmax𝔪
  have hker : RingHom.ker π = J := Ideal.mk_ker
  have hkerle : RingHom.ker π ≤ 𝔪 := by rw [hker]; exact hJm
  have hmax𝔐 : (𝔪.map π).IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le hsurj hkerle
  obtain ⟨s, hs⟩ := hwit (𝔪.map π)
  set e := residueFieldQuotientJacobsonEquiv 𝔪
  refine ⟨fun i ↦ e.symm (s i), ?_⟩
  have heq := aeval_comp_residueFieldQuotientJacobsonEquiv p 𝔪 (fun i ↦ e.symm (s i))
  simp only [RingEquiv.apply_symm_apply, e] at heq
  have hunit_e : IsUnit (e (MvPolynomial.aeval (fun i ↦ e.symm (s i)) p)) := heq ▸ hs
  simpa using hunit_e.map e.symm.toMonoidHom

/-- **`GPR 11.21(i)`**: `R` is an LG-ring iff `R ⧸ Jac(R)` is. -/
theorem isLGRing_iff_isLGRing_quotient_jacobson {R : Type u} [CommRing R] :
    IsLGRing R ↔ IsLGRing (R ⧸ Ring.jacobson R) := by
  set J := Ring.jacobson R with hJdef
  set π := Ideal.Quotient.mk J with hπdef
  have hsurj : Function.Surjective π := Ideal.Quotient.mk_surjective
  constructor
  · intro hLG n q
    constructor
    · rintro ⟨s, hs⟩ 𝔐 _
      refine ⟨fun i ↦ Ideal.Quotient.mk 𝔐 (s i), ?_⟩
      have heq := MvPolynomial.comp_aeval_apply
        (f := s) (φ := Algebra.ofId (R ⧸ J) ((R ⧸ J) ⧸ 𝔐)) (p := q)
      simp only [Algebra.ofId_apply] at heq
      exact heq ▸ hs.map (algebraMap (R ⧸ J) ((R ⧸ J) ⧸ 𝔐))
    · intro hRHS
      obtain ⟨p, hp⟩ := MvPolynomial.map_surjective π hsurj q
      subst hp
      obtain ⟨t, ht⟩ := (hLG n p).mpr (represents_unit_of_forall_quotient_jacobson p hRHS)
      refine ⟨fun i ↦ π (t i), ?_⟩
      rw [← aeval_map_quotient]
      exact ht.map π
  · intro hLG n p
    constructor
    · rintro ⟨s, hs⟩ 𝔪 _
      refine ⟨fun i ↦ Ideal.Quotient.mk 𝔪 (s i), ?_⟩
      have heq := MvPolynomial.comp_aeval_apply
        (f := s) (φ := Algebra.ofId R (R ⧸ 𝔪)) (p := p)
      simp only [Algebra.ofId_apply] at heq
      exact heq ▸ hs.map (algebraMap R (R ⧸ 𝔪))
    · intro hRHS
      obtain ⟨tbar, htbar⟩ := (hLG n (MvPolynomial.map π p)).mpr
        (represents_unit_quotient_jacobson_of_forall p hRHS)
      choose t ht using fun i ↦ hsurj (tbar i)
      refine ⟨t, isUnit_of_isUnit_image_jacobson _ ?_⟩
      rw [aeval_map_quotient J p t, funext ht]
      exact htbar
