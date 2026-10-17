/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import LeanPool.CompositionAlgebrasOverRings.LGRing.ValueIdeal
public import Mathlib.Algebra.Group.Pi.Units
public import Mathlib.RingTheory.Ideal.Prod

/-!
# Products of LG-rings

The product half of `GPR 11.21` (`GN 2.1(a)`): `R₁ × R₂` is an LG-ring iff `R₁` and `R₂` both
are. The Jacobson-quotient half is in `LGRing/Jacobson.lean`; the two combine in
`LGRing/Semilocal.lean` to give `GPR 11.22`.

A second, unrelated result closes the file: an **arbitrary** product of fields is an LG-ring. That
is not a corollary of the binary statement — induction on `isLGRing_prod_iff` reaches only finite
products — and its proof runs through the value-ideal criterion instead.

## Main results

* `MvPolynomial.RepresentsUnit.mapOfComm`, `MvPolynomial.RepresentsUnit.ofMapOfComm` : transport
  of `RepresentsUnit` along a commuting square of ring homomorphisms (`aeval_map_comm`, in
  `LGRing/Defs.lean`), forwards and (when the vertical map is an isomorphism) backwards. Every
  transport below, and every one in `LGRing/Semilocal.lean`, is an instance of these.
* `Ideal.prodQuotientFstEquiv`, `Ideal.prodQuotientSndEquiv` : the residue fields of `R₁ × R₂` at
  `Ideal.prod 𝔪 ⊤` and `Ideal.prod ⊤ 𝔪` are those of `R₁` at `𝔪` and of `R₂` at `𝔪`.
* `isLGRing_prod_iff` : **`GPR 11.21(ii)`**, `IsLGRing (R₁ × R₂) ↔ IsLGRing R₁ ∧ IsLGRing R₂`.
* `isLGRing_pi_of_forall_field`, `isLGRing_pi_field` : an arbitrary product `∏ᵢ Kᵢ` of fields — in
  particular `F^I` for a field `F` and any index set `I` — is an LG-ring.

## Proof idea

The maximal ideals of `R₁ × R₂` are exactly `Ideal.prod 𝔪 ⊤` and `Ideal.prod ⊤ 𝔪` for `𝔪` maximal
in `R₁` resp. `R₂` — `Ideal.ideal_prod_prime` classifies the primes, and maximality transfers both
ways along `Ideal.comap_isMaximal_of_surjective` and `Ideal.map_fst_prod` — with the
corresponding residue fields those of the factors.

For `⇐`, given `p` over `R₁ × R₂` representing a unit at every residue field, its images
`MvPolynomial.map (RingHom.fst _ _) p` and `map (RingHom.snd _ _) p` represent units at every
residue field of `R₁` resp. `R₂`; the LG hypotheses give witnesses `s₁, s₂`, and
`fun i ↦ (s₁ i, s₂ i)` is a witness over `R₁ × R₂`, because `IsUnit` in a product is
componentwise (`Prod.isUnit_iff`).

For `⟹`, the point is that a polynomial over `R₁` must be *promoted* to one over `R₁ × R₂` that
carries no information about `R₂`. There is no ring homomorphism `R₁ → R₁ × R₂` to push it
through — `r ↦ (r, 1)` is not additive and `r ↦ (r, 0)` is not unital — but
`MvPolynomial.map (RingHom.fst _ _)` is surjective, so `p₁` has *some* preimage `q`, and the
orthogonal idempotents of `R₁ × R₂` assemble it into

  `p := C (1, 0) * q + C (0, 1)`,

for which `map fst p = p₁` while `map snd p = 1`. Then `p` represents a unit at every residue
field of `R₁ × R₂`: on the `R₁` side because `p₁` does, and on the `R₂` side for free, the
constant `1` representing a unit anywhere. The LG hypothesis for `R₁ × R₂` yields a witness, whose
first components witness `p₁` over `R₁`.

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, 11.21(ii).
* [GN] Gille, Neher, *Group schemes over LG-rings and applications to cancellation theorems and
  Azumaya algebras*, European Journal of Mathematics **11** (2025), article 42, §2.1(a),
  Example 2.2.
* [EG] Estes, Guralnick, *Module equivalences: local to global when primitive polynomials represent
  units*, Journal of Algebra **77** (1982), 138–157.
-/

@[expose] public section

universe u v

/-! ### Transport of `RepresentsUnit` along a square of ring homomorphisms -/

/-- Pushing a `RepresentsUnit` witness forward along a commuting square. -/
theorem MvPolynomial.RepresentsUnit.mapOfComm {R : Type*} [CommRing R] {R' : Type*} [CommRing R']
    (φ : R →+* R') {S : Type*} [CommRing S] [Algebra R S] {S' : Type*} [CommRing S']
    [Algebra R' S'] (ψ : S →+* S')
    (hcomm : ψ.comp (algebraMap R S) = (algebraMap R' S').comp φ)
    {n : ℕ} {p : MvPolynomial (Fin n) R} (h : p.RepresentsUnit S) :
    (MvPolynomial.map φ p).RepresentsUnit S' := by
  obtain ⟨s, hs⟩ := h
  exact ⟨fun i ↦ ψ (s i), (MvPolynomial.aeval_map_comm φ ψ hcomm s p) ▸ hs.map ψ⟩

/-- Pulling a `RepresentsUnit` witness *back* along a commuting square whose vertical map is an
isomorphism. This is the direction that needs `ψ` invertible: the witness is transported by
`e.symm` and the resulting unit is recognised by applying `e`. -/
theorem MvPolynomial.RepresentsUnit.ofMapOfComm {R : Type*} [CommRing R] {R' : Type*} [CommRing R']
    (φ : R →+* R') {S : Type*} [CommRing S] [Algebra R S] {S' : Type*} [CommRing S']
    [Algebra R' S'] (e : S ≃+* S')
    (hcomm : e.toRingHom.comp (algebraMap R S) = (algebraMap R' S').comp φ)
    {n : ℕ} {p : MvPolynomial (Fin n) R} (h : (MvPolynomial.map φ p).RepresentsUnit S') :
    p.RepresentsUnit S := by
  obtain ⟨t, ht⟩ := h
  refine ⟨fun i ↦ e.symm (t i), ?_⟩
  have key := MvPolynomial.aeval_map_comm φ e.toRingHom hcomm (fun i ↦ e.symm (t i)) p
  simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingEquiv.apply_symm_apply] at key
  rw [key] at ht
  simpa using ht.map e.symm.toRingHom

/-! ### Maximal ideals and residue fields of a product -/

namespace Ideal

variable {R₁ : Type u} [CommRing R₁] {R₂ : Type u} [CommRing R₂]

theorem comap_fst_eq_prod_top (𝔪 : Ideal R₁) :
    Ideal.comap (RingHom.fst R₁ R₂) 𝔪 = Ideal.prod 𝔪 ⊤ := by
  ext x; simp

theorem comap_snd_eq_top_prod (𝔪 : Ideal R₂) :
    Ideal.comap (RingHom.snd R₁ R₂) 𝔪 = Ideal.prod ⊤ 𝔪 := by
  ext x; simp

theorem prod_top_isMaximal (𝔪 : Ideal R₁) [𝔪.IsMaximal] :
    (Ideal.prod 𝔪 (⊤ : Ideal R₂)).IsMaximal := by
  rw [← comap_fst_eq_prod_top]
  exact Ideal.comap_isMaximal_of_surjective _ Prod.fst_surjective

theorem top_prod_isMaximal (𝔪 : Ideal R₂) [𝔪.IsMaximal] :
    (Ideal.prod (⊤ : Ideal R₁) 𝔪).IsMaximal := by
  rw [← comap_snd_eq_top_prod]
  exact Ideal.comap_isMaximal_of_surjective _ Prod.snd_surjective

theorem isMaximal_of_prod_top_isMaximal {𝔭 : Ideal R₁}
    (h : (Ideal.prod 𝔭 (⊤ : Ideal R₂)).IsMaximal) : 𝔭.IsMaximal := by
  have := h
  have hle : RingHom.ker (RingHom.fst R₁ R₂) ≤ Ideal.prod 𝔭 (⊤ : Ideal R₂) := by
    intro x hx
    simp only [RingHom.mem_ker, RingHom.coe_fst] at hx
    simp [Ideal.mem_prod, hx]
  have hmax := Ideal.IsMaximal.map_of_surjective_of_ker_le
    (f := RingHom.fst R₁ R₂) Prod.fst_surjective hle
  rwa [Ideal.map_fst_prod] at hmax

theorem isMaximal_of_top_prod_isMaximal {𝔭 : Ideal R₂}
    (h : (Ideal.prod (⊤ : Ideal R₁) 𝔭).IsMaximal) : 𝔭.IsMaximal := by
  have := h
  have hle : RingHom.ker (RingHom.snd R₁ R₂) ≤ Ideal.prod (⊤ : Ideal R₁) 𝔭 := by
    intro x hx
    simp only [RingHom.mem_ker, RingHom.coe_snd] at hx
    simp [Ideal.mem_prod, hx]
  have hmax := Ideal.IsMaximal.map_of_surjective_of_ker_le
    (f := RingHom.snd R₁ R₂) Prod.snd_surjective hle
  rwa [Ideal.map_snd_prod] at hmax

/-- The residue field of `R₁ × R₂` at `Ideal.prod 𝔪 ⊤` is the residue field of `R₁` at `𝔪`:
apply the first isomorphism theorem to `R₁ × R₂ → R₁ → R₁ ⧸ 𝔪`, whose kernel is `Ideal.prod 𝔪 ⊤`
by `Ideal.comap_fst_eq_prod_top`. -/
noncomputable def prodQuotientFstEquiv (𝔪 : Ideal R₁) :
    ((R₁ × R₂) ⧸ Ideal.prod 𝔪 (⊤ : Ideal R₂)) ≃+* R₁ ⧸ 𝔪 :=
  have hsurj : Function.Surjective ((Ideal.Quotient.mk 𝔪).comp (RingHom.fst R₁ R₂)) :=
    Ideal.Quotient.mk_surjective.comp Prod.fst_surjective
  have hker : Ideal.prod 𝔪 (⊤ : Ideal R₂) =
      RingHom.ker ((Ideal.Quotient.mk 𝔪).comp (RingHom.fst R₁ R₂)) := by
    rw [← RingHom.comap_ker, Ideal.mk_ker, comap_fst_eq_prod_top]
  (Ideal.quotEquivOfEq hker).trans (RingHom.quotientKerEquivOfSurjective hsurj)

@[simp]
theorem prodQuotientFstEquiv_apply (𝔪 : Ideal R₁) (x : R₁ × R₂) :
    prodQuotientFstEquiv (R₂ := R₂) 𝔪
        (Ideal.Quotient.mk (Ideal.prod 𝔪 (⊤ : Ideal R₂)) x) =
      Ideal.Quotient.mk 𝔪 x.1 := by
  simp only [prodQuotientFstEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk, RingHom.comp_apply, RingHom.coe_fst]

/-- The residue field of `R₁ × R₂` at `Ideal.prod ⊤ 𝔪` is the residue field of `R₂` at `𝔪`. -/
noncomputable def prodQuotientSndEquiv (𝔪 : Ideal R₂) :
    ((R₁ × R₂) ⧸ Ideal.prod (⊤ : Ideal R₁) 𝔪) ≃+* R₂ ⧸ 𝔪 :=
  have hsurj : Function.Surjective ((Ideal.Quotient.mk 𝔪).comp (RingHom.snd R₁ R₂)) :=
    Ideal.Quotient.mk_surjective.comp Prod.snd_surjective
  have hker : Ideal.prod (⊤ : Ideal R₁) 𝔪 =
      RingHom.ker ((Ideal.Quotient.mk 𝔪).comp (RingHom.snd R₁ R₂)) := by
    rw [← RingHom.comap_ker, Ideal.mk_ker, comap_snd_eq_top_prod]
  (Ideal.quotEquivOfEq hker).trans (RingHom.quotientKerEquivOfSurjective hsurj)

@[simp]
theorem prodQuotientSndEquiv_apply (𝔪 : Ideal R₂) (x : R₁ × R₂) :
    prodQuotientSndEquiv (R₁ := R₁) 𝔪 (Ideal.Quotient.mk (Ideal.prod (⊤ : Ideal R₁) 𝔪) x) =
      Ideal.Quotient.mk 𝔪 x.2 := by
  simp only [prodQuotientSndEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk, RingHom.comp_apply, RingHom.coe_snd]

theorem prodQuotientFstEquiv_comm (𝔪 : Ideal R₁) :
    (prodQuotientFstEquiv (R₂ := R₂) 𝔪).toRingHom.comp
        (algebraMap (R₁ × R₂) ((R₁ × R₂) ⧸ Ideal.prod 𝔪 (⊤ : Ideal R₂))) =
      (algebraMap R₁ (R₁ ⧸ 𝔪)).comp (RingHom.fst R₁ R₂) :=
  RingHom.ext fun x ↦ by simp [Ideal.Quotient.algebraMap_eq]

theorem prodQuotientSndEquiv_comm (𝔪 : Ideal R₂) :
    (prodQuotientSndEquiv (R₁ := R₁) 𝔪).toRingHom.comp
        (algebraMap (R₁ × R₂) ((R₁ × R₂) ⧸ Ideal.prod (⊤ : Ideal R₁) 𝔪)) =
      (algebraMap R₂ (R₂ ⧸ 𝔪)).comp (RingHom.snd R₁ R₂) :=
  RingHom.ext fun x ↦ by simp [Ideal.Quotient.algebraMap_eq]

end Ideal

/-! ### `GPR 11.21(ii)` -/

section Main

variable {R₁ : Type u} [CommRing R₁] {R₂ : Type u} [CommRing R₂]

/-- **`GPR 11.21(ii)`**: a binary product of rings is an LG-ring iff both factors are. -/
theorem isLGRing_prod_iff : IsLGRing (R₁ × R₂) ↔ IsLGRing R₁ ∧ IsLGRing R₂ := by
  constructor
  · intro hLG
    refine ⟨fun n p₁ ↦ ⟨fun ⟨s, hs⟩ 𝔪 _ ↦ ?_, fun hRHS ↦ ?_⟩,
      fun n p₂ ↦ ⟨fun ⟨s, hs⟩ 𝔪 _ ↦ ?_, fun hRHS ↦ ?_⟩⟩
    · exact ⟨fun i ↦ algebraMap R₁ (R₁ ⧸ 𝔪) (s i),
        (MvPolynomial.comp_aeval_apply (f := s) (φ := Algebra.ofId R₁ (R₁ ⧸ 𝔪)) (p := p₁)) ▸
          hs.map (algebraMap R₁ (R₁ ⧸ 𝔪))⟩
    · -- Promote `p₁` to a polynomial over `R₁ × R₂` that is the constant `1` on the `R₂` side.
      obtain ⟨q, hq⟩ := MvPolynomial.map_surjective (RingHom.fst R₁ R₂) Prod.fst_surjective p₁
      set p : MvPolynomial (Fin n) (R₁ × R₂) :=
        MvPolynomial.C ((1 : R₁), (0 : R₂)) * q + MvPolynomial.C ((0 : R₁), (1 : R₂)) with hp
      have hfst : MvPolynomial.map (RingHom.fst R₁ R₂) p = p₁ := by simp [hp, hq]
      have hsnd : MvPolynomial.map (RingHom.snd R₁ R₂) p = 1 := by simp [hp]
      have hall : ∀ (M : Ideal (R₁ × R₂)) [M.IsMaximal], p.RepresentsUnit ((R₁ × R₂) ⧸ M) := by
        intro M hM
        rcases (Ideal.ideal_prod_prime M).mp hM.isPrime with ⟨𝔭, _, rfl⟩ | ⟨𝔭, _, rfl⟩
        · have : 𝔭.IsMaximal := Ideal.isMaximal_of_prod_top_isMaximal hM
          exact MvPolynomial.RepresentsUnit.ofMapOfComm (RingHom.fst R₁ R₂)
            (Ideal.prodQuotientFstEquiv (R₂ := R₂) 𝔭) (Ideal.prodQuotientFstEquiv_comm 𝔭)
            (hfst ▸ hRHS 𝔭)
        · have : 𝔭.IsMaximal := Ideal.isMaximal_of_top_prod_isMaximal hM
          refine MvPolynomial.RepresentsUnit.ofMapOfComm (RingHom.snd R₁ R₂)
            (Ideal.prodQuotientSndEquiv (R₁ := R₁) 𝔭) (Ideal.prodQuotientSndEquiv_comm 𝔭) ?_
          rw [hsnd]
          exact ⟨fun _ ↦ 0, by simp⟩
      obtain ⟨s, hs⟩ := (hLG n p).mpr hall
      exact hfst ▸ MvPolynomial.RepresentsUnit.mapOfComm (S := R₁ × R₂) (S' := R₁)
        (RingHom.fst R₁ R₂) (RingHom.fst R₁ R₂) (by ext x; simp) ⟨s, hs⟩
    · exact ⟨fun i ↦ algebraMap R₂ (R₂ ⧸ 𝔪) (s i),
        (MvPolynomial.comp_aeval_apply (f := s) (φ := Algebra.ofId R₂ (R₂ ⧸ 𝔪)) (p := p₂)) ▸
          hs.map (algebraMap R₂ (R₂ ⧸ 𝔪))⟩
    · obtain ⟨q, hq⟩ := MvPolynomial.map_surjective (RingHom.snd R₁ R₂) Prod.snd_surjective p₂
      set p : MvPolynomial (Fin n) (R₁ × R₂) :=
        MvPolynomial.C ((0 : R₁), (1 : R₂)) * q + MvPolynomial.C ((1 : R₁), (0 : R₂)) with hp
      have hsnd : MvPolynomial.map (RingHom.snd R₁ R₂) p = p₂ := by simp [hp, hq]
      have hfst : MvPolynomial.map (RingHom.fst R₁ R₂) p = 1 := by simp [hp]
      have hall : ∀ (M : Ideal (R₁ × R₂)) [M.IsMaximal], p.RepresentsUnit ((R₁ × R₂) ⧸ M) := by
        intro M hM
        rcases (Ideal.ideal_prod_prime M).mp hM.isPrime with ⟨𝔭, _, rfl⟩ | ⟨𝔭, _, rfl⟩
        · have : 𝔭.IsMaximal := Ideal.isMaximal_of_prod_top_isMaximal hM
          refine MvPolynomial.RepresentsUnit.ofMapOfComm (RingHom.fst R₁ R₂)
            (Ideal.prodQuotientFstEquiv (R₂ := R₂) 𝔭) (Ideal.prodQuotientFstEquiv_comm 𝔭) ?_
          rw [hfst]
          exact ⟨fun _ ↦ 0, by simp⟩
        · have : 𝔭.IsMaximal := Ideal.isMaximal_of_top_prod_isMaximal hM
          exact MvPolynomial.RepresentsUnit.ofMapOfComm (RingHom.snd R₁ R₂)
            (Ideal.prodQuotientSndEquiv (R₁ := R₁) 𝔭) (Ideal.prodQuotientSndEquiv_comm 𝔭)
            (hsnd ▸ hRHS 𝔭)
      obtain ⟨s, hs⟩ := (hLG n p).mpr hall
      exact hsnd ▸ MvPolynomial.RepresentsUnit.mapOfComm (S := R₁ × R₂) (S' := R₂)
        (RingHom.snd R₁ R₂) (RingHom.snd R₁ R₂) (by ext x; simp) ⟨s, hs⟩
  · rintro ⟨h₁, h₂⟩ n p
    refine ⟨fun ⟨s, hs⟩ M _ ↦ ?_, fun hRHS ↦ ?_⟩
    · exact ⟨fun i ↦ algebraMap (R₁ × R₂) ((R₁ × R₂) ⧸ M) (s i),
        (MvPolynomial.comp_aeval_apply (f := s)
          (φ := Algebra.ofId (R₁ × R₂) ((R₁ × R₂) ⧸ M)) (p := p)) ▸
          hs.map (algebraMap (R₁ × R₂) ((R₁ × R₂) ⧸ M))⟩
    · obtain ⟨s₁, hs₁⟩ : (MvPolynomial.map (RingHom.fst R₁ R₂) p).RepresentsUnit R₁ := by
        refine (h₁ n _).mpr fun 𝔪 _ ↦ ?_
        have := Ideal.prod_top_isMaximal (R₂ := R₂) 𝔪
        exact MvPolynomial.RepresentsUnit.mapOfComm (RingHom.fst R₁ R₂)
          (Ideal.prodQuotientFstEquiv (R₂ := R₂) 𝔪).toRingHom
          (Ideal.prodQuotientFstEquiv_comm 𝔪) (hRHS _)
      obtain ⟨s₂, hs₂⟩ : (MvPolynomial.map (RingHom.snd R₁ R₂) p).RepresentsUnit R₂ := by
        refine (h₂ n _).mpr fun 𝔪 _ ↦ ?_
        have := Ideal.top_prod_isMaximal (R₁ := R₁) 𝔪
        exact MvPolynomial.RepresentsUnit.mapOfComm (RingHom.snd R₁ R₂)
          (Ideal.prodQuotientSndEquiv (R₁ := R₁) 𝔪).toRingHom
          (Ideal.prodQuotientSndEquiv_comm 𝔪) (hRHS _)
      refine ⟨fun i ↦ (s₁ i, s₂ i), Prod.isUnit_iff.mpr ⟨?_, ?_⟩⟩
      · have hcomm : (RingHom.fst R₁ R₂).comp (algebraMap (R₁ × R₂) (R₁ × R₂))
            = (algebraMap R₁ R₁).comp (RingHom.fst R₁ R₂) := by ext x; simp
        have key := MvPolynomial.aeval_map_comm (RingHom.fst R₁ R₂) (RingHom.fst R₁ R₂) hcomm
          (fun i ↦ ((s₁ i, s₂ i) : R₁ × R₂)) p
        exact cast (congrArg IsUnit key) hs₁
      · have hcomm : (RingHom.snd R₁ R₂).comp (algebraMap (R₁ × R₂) (R₁ × R₂))
            = (algebraMap R₂ R₂).comp (RingHom.snd R₁ R₂) := by ext x; simp
        have key := MvPolynomial.aeval_map_comm (RingHom.snd R₁ R₂) (RingHom.snd R₁ R₂) hcomm
          (fun i ↦ ((s₁ i, s₂ i) : R₁ × R₂)) p
        exact cast (congrArg IsUnit key) hs₂

end Main

/-! ### Arbitrary products of fields -/

section PiFields

variable {ι : Type v} (K : ι → Type u) [∀ i, Field (K i)]

/-- **An arbitrary product of fields is an LG-ring** (`GN 2.2`, from `EG`).

By the value-ideal criterion it suffices to turn an equation `1 = Σⱼ cⱼ · p(tⱼ)` — finitely many
points `tⱼ` of `(∏ᵢ Kᵢ)ⁿ` whose values at `p` generate the unit ideal — into a single point where
`p` is a unit. Read that equation off at one index `i`: the `i`-th components sum to `1 ≠ 0` in the
field `Kᵢ`, so *some* `j` has `p(tⱼ)ᵢ ≠ 0`. Choosing such a `j = j(i)` for every `i` and splicing,
`s x i := t (j i) x i`, gives a point whose value has `p(s)ᵢ = p(t (j i))ᵢ ≠ 0` in every
coordinate — and a unit in a product is exactly a coordinatewise unit.

A product of fields is von Neumann regular, so this also follows from
`IsVonNeumannRegular.isLGRing` in `LGRing/ZeroDimensional.lean`; the direct argument is kept
because it is elementary — no idempotents, no value ideal beyond its unwinding — and because it is
what makes the shape of the general statement visible.

The splicing step is legitimate because evaluation commutes with each projection
`∏ᵢ Kᵢ → Kᵢ` (`MvPolynomial.aeval_map_comm`): the `i`-th coordinate of a value depends on the
`i`-th coordinates of the point and on nothing else. This is the whole reason the argument needs
the factors to be *fields* only coordinatewise, with no compatibility between them. -/
theorem isLGRing_pi_of_forall_field : IsLGRing (∀ i, K i) := by
  rw [isLGRing_iff_forall_valueIdeal_eq_top]
  intro n p htop
  -- Evaluation in the `i`-th coordinate only sees the `i`-th coordinate of the point.
  have key : ∀ (u : Fin n → ∀ i, K i) (i : ι),
      MvPolynomial.aeval (fun x ↦ u x i) (MvPolynomial.map (Pi.evalRingHom K i) p)
        = MvPolynomial.aeval u p i :=
    fun u i ↦ MvPolynomial.aeval_map_comm (Pi.evalRingHom K i) (Pi.evalRingHom K i)
      (by ext x; simp) u p
  obtain ⟨k, c, t, hsum⟩ := MvPolynomial.exists_sum_mul_aeval_eq_one htop
  have hne : ∀ i : ι, ∃ j : Fin k, MvPolynomial.aeval (t j) p i ≠ 0 := by
    intro i
    have h1 : ∑ j : Fin k, c j i * MvPolynomial.aeval (t j) p i = (1 : K i) := by
      simpa using congrFun hsum i
    have h2 : ∑ j : Fin k, c j i * MvPolynomial.aeval (t j) p i ≠ 0 := by
      rw [h1]; exact one_ne_zero
    obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero h2
    exact ⟨j, fun h ↦ hj (by rw [h, mul_zero])⟩
  choose j hj using hne
  refine ⟨fun x i ↦ t (j i) x i, Pi.isUnit_iff.mpr fun i ↦ isUnit_iff_ne_zero.mpr ?_⟩
  rw [← key _ i, key (t (j i)) i]
  exact hj i

/-- **`F^I` is an LG-ring** for a field `F` and an arbitrary index set `I` (`GN 2.2`, from `EG`);
the constant-family case of `isLGRing_pi_of_forall_field`. -/
theorem isLGRing_pi_field (F : Type u) [Field F] (I : Type v) : IsLGRing (I → F) :=
  isLGRing_pi_of_forall_field fun _ ↦ F

end PiFields
