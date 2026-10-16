/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import LeanPool.CompositionAlgebrasOverRings.LGRing.Examples
public import LeanPool.CompositionAlgebrasOverRings.LGRing.Jacobson
public import LeanPool.CompositionAlgebrasOverRings.LGRing.Products
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# Semilocal rings are LG-rings

`GPR 11.22`: a commutative ring with only finitely many maximal ideals is an LG-ring. This is the
workhorse instance for the rest of the development — local rings, Artinian rings and fields are
all semilocal.

Semilocality is expressed in mathlib's way, as `[Finite (MaximalSpectrum R)]`.

## Main results

* `IsLGRing.of_ringEquiv` : the LG property transfers along a ring isomorphism.
* `IsLGRing.quotient_span_one_sub_of_isIdempotentElem` : an idempotent factor of an LG ring is
  LG.
* `isLGRing_of_finite_maximalSpectrum` : **`GPR 11.22`**, semilocal implies LG.
* `isLGRing_of_isLocalRing` : every commutative local ring is LG.

## Proof idea

Assemble the two halves of `GPR 11.21`. Writing `𝔪₁, …, 𝔪ₖ` for the maximal ideals,
`Jac(R) = 𝔪₁ ⊓ ⋯ ⊓ 𝔪ₖ` is a *finite* intersection, so the Chinese Remainder Theorem
(`Ideal.quotientInfEquivQuotientProd`, applied `k` times) identifies `R ⧸ Jac(R)` with a finite
product of the residue fields `R ⧸ 𝔪ᵢ`. Fields are LG (`isLGRing_of_field`), binary products of
LG-rings are LG (`isLGRing_prod_iff`), so `R ⧸ Jac(R)` is LG, and `R` itself is LG by
`isLGRing_iff_isLGRing_quotient_jacobson`.

The induction is on a `Finset` of maximal ideals rather than on a cardinality, which keeps
everything inside `R`: `isLGRing_quotient_biInf` proves `R ⧸ (⨅ 𝔪 ∈ s, 𝔪)` is LG for every finite
set `s` of maximal ideals, with the empty set giving the zero ring
(`isLGRing_of_subsingleton`, in `LGRing/Examples.lean`).

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, 11.22.
* [GN] Gille, Neher, *Group schemes over LG-rings and applications to cancellation theorems and
  Azumaya algebras*, European Journal of Mathematics **11** (2025), article 42, §2.1.
-/

@[expose] public section

universe u

/-- The LG property transfers along a ring isomorphism: maximal ideals correspond
(`Ideal.map_isMaximal_of_equiv`), the residue fields correspond (`Ideal.quotientEquiv`), and
`MvPolynomial.map` transports polynomials both ways. -/
theorem IsLGRing.of_ringEquiv {R : Type u} [CommRing R] {S : Type u} [CommRing S] (e : R ≃+* S)
    (hR : IsLGRing R) : IsLGRing S := by
  intro n q
  obtain ⟨p, rfl⟩ := MvPolynomial.map_surjective e.toRingHom e.surjective q
  refine ⟨fun ⟨t, ht⟩ 𝔐 _ ↦ ?_, fun hRHS ↦ ?_⟩
  · exact ⟨fun i ↦ algebraMap S (S ⧸ 𝔐) (t i),
      (MvPolynomial.comp_aeval_apply (f := t) (φ := Algebra.ofId S (S ⧸ 𝔐))
        (p := MvPolynomial.map e.toRingHom p)) ▸ ht.map (algebraMap S (S ⧸ 𝔐))⟩
  · have hp : p.RepresentsUnit R := by
      refine (hR n p).mpr fun 𝔪 _ ↦ ?_
      have : (Ideal.map (e : R →+* S) 𝔪).IsMaximal := Ideal.map_isMaximal_of_equiv e
      refine MvPolynomial.RepresentsUnit.ofMapOfComm e.toRingHom
        (Ideal.quotientEquiv 𝔪 (Ideal.map (e : R →+* S) 𝔪) e rfl) ?_ (hRHS _)
      exact RingHom.ext fun x ↦ by simp [Ideal.Quotient.algebraMap_eq]
    obtain ⟨s, hs⟩ := hp
    exact MvPolynomial.RepresentsUnit.mapOfComm e.toRingHom e.toRingHom
      (by ext x; simp) ⟨s, hs⟩

/-- An idempotent factor of an LG ring is LG.

The complementary ideals `(1 - e)` and `(e)` have zero intersection, so the Chinese remainder
theorem identifies the original ring with the product of the two quotient rings. The assertion
then follows from `GPR 11.21(ii)`. -/
theorem IsLGRing.quotient_span_one_sub_of_isIdempotentElem {R : Type u} [CommRing R]
    (hLG : IsLGRing R) {e : R} (he : IsIdempotentElem e) :
    IsLGRing (R ⧸ Ideal.span {1 - e}) := by
  let I : Ideal R := Ideal.span {1 - e}
  let J : Ideal R := Ideal.span {e}
  have hcop : IsCoprime I J := by
    change IsCoprime (Ideal.span {1 - e}) (Ideal.span {e})
    rw [Ideal.isCoprime_span_singleton_iff]
    exact ⟨1, 1, by ring⟩
  have hinf : I ⊓ J = ⊥ := by
    calc
      I ⊓ J = I * J := (Ideal.mul_eq_inf_of_isCoprime hcop).symm
      _ = Ideal.span {(1 - e) * e} := by
        simp only [I, J, Ideal.span_singleton_mul_span_singleton]
      _ = ⊥ := by simp only [sub_mul, one_mul, he.eq, sub_self, Set.singleton_zero,
        Ideal.span_zero]
  let eprod : R ≃+* (R ⧸ I) × (R ⧸ J) :=
    (RingEquiv.quotientBot R).symm |>.trans
      ((Ideal.quotEquivOfEq hinf.symm).trans
        (Ideal.quotientInfEquivQuotientProd I J hcop))
  have hprod : IsLGRing ((R ⧸ I) × (R ⧸ J)) :=
    IsLGRing.of_ringEquiv eprod hLG
  exact (isLGRing_prod_iff.mp hprod).1

/-- For any finite set `s` of maximal ideals of `R`, the quotient `R ⧸ (⨅ 𝔪 ∈ s, 𝔪)` is an
LG-ring. Induction on `s`: the empty set gives the zero ring, and the induction step splits off
one maximal ideal by the Chinese Remainder Theorem and applies `isLGRing_prod_iff`. -/
theorem isLGRing_quotient_biInf {R : Type u} [CommRing R] (s : Finset (Ideal R))
    (hs : ∀ 𝔪 ∈ s, 𝔪.IsMaximal) : IsLGRing (R ⧸ (⨅ 𝔪 ∈ s, 𝔪)) := by
  classical
  induction s using Finset.induction with
  | empty =>
    have htop : (⨅ 𝔪 ∈ (∅ : Finset (Ideal R)), 𝔪) = ⊤ := by simp
    rw [htop]
    have : Subsingleton (R ⧸ (⊤ : Ideal R)) := Ideal.Quotient.subsingleton_iff.mpr rfl
    exact isLGRing_of_subsingleton _
  | insert 𝔪 t h𝔪t ih =>
    have h𝔪 : 𝔪.IsMaximal := hs 𝔪 (Finset.mem_insert_self _ _)
    have ht : ∀ 𝔫 ∈ t, 𝔫.IsMaximal :=
      fun 𝔫 h𝔫 ↦ hs 𝔫 (Finset.mem_insert_of_mem h𝔫)
    have hcop : IsCoprime 𝔪 (⨅ 𝔫 ∈ t, 𝔫) :=
      Ideal.isCoprime_biInf fun 𝔫 h𝔫 ↦
        have := ht 𝔫 h𝔫
        Ideal.isCoprime_of_isMaximal (by rintro rfl; exact h𝔪t h𝔫)
    have hinsert : (⨅ 𝔫 ∈ insert 𝔪 t, 𝔫) = 𝔪 ⊓ (⨅ 𝔫 ∈ t, 𝔫) := by
      rw [Finset.iInf_insert]
    rw [hinsert]
    refine
      IsLGRing.of_ringEquiv
        (Ideal.quotientInfEquivQuotientProd 𝔪 (⨅ 𝔫 ∈ t, 𝔫) hcop).symm ?_
    refine isLGRing_prod_iff.mpr ⟨?_, ih ht⟩
    let : Field (R ⧸ 𝔪) := Ideal.Quotient.field 𝔪
    exact isLGRing_of_field _

/-- **`GPR 11.22`**: every semilocal ring is an LG-ring. Semilocality is mathlib's
`[Finite (MaximalSpectrum R)]`: `R` has only finitely many maximal ideals. -/
theorem isLGRing_of_finite_maximalSpectrum (R : Type u) [CommRing R]
    [Finite (MaximalSpectrum R)] : IsLGRing R := by
  classical
  have h : {𝔪 : Ideal R | 𝔪.IsMaximal}.Finite :=
    (Set.finite_range (MaximalSpectrum.asIdeal : MaximalSpectrum R → Ideal R)).subset
      fun 𝔪 h𝔪 ↦ ⟨⟨𝔪, h𝔪⟩, rfl⟩
  rw [isLGRing_iff_isLGRing_quotient_jacobson]
  have hjac : Ring.jacobson R = ⨅ 𝔪 ∈ h.toFinset, 𝔪 := by
    rw [Ring.jacobson_eq_sInf_isMaximal]
    refine le_antisymm (le_iInf fun 𝔪 ↦ le_iInf fun h𝔪 ↦ sInf_le (h.mem_toFinset.mp h𝔪))
      (le_sInf fun 𝔪 h𝔪 ↦ iInf_le_of_le 𝔪 (iInf_le_of_le (h.mem_toFinset.mpr h𝔪) le_rfl))
  rw [hjac]
  exact isLGRing_quotient_biInf _ fun 𝔪 h𝔪 ↦ (h.mem_toFinset.mp h𝔪)

/-- Every commutative local ring is an LG ring, since it has a unique maximal ideal and hence is
semilocal. -/
theorem isLGRing_of_isLocalRing (R : Type u) [CommRing R] [IsLocalRing R] : IsLGRing R :=
  isLGRing_of_finite_maximalSpectrum R
