/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import LeanPool.CompositionAlgebrasOverRings.LGRing.Defs

/-!
# Examples of LG rings

## Main results

* `isLGRing_of_subsingleton` : the zero ring is an LG-ring (`GN 2.2(a)`).
* `isLGRing_of_field` : every field is an LG-ring (`GPR 11.20`, remarked immediately after the
  definition).

## Implementation notes

`GPR 11.22` continues: semilocal rings are LG, via `GPR 11.21` (`R/Jac(R)` is a finite product of
fields for `R` semilocal, and both the Jacobson-quotient and finite-product cases of the LG
property transfer). Both halves of `GPR 11.21` are now proved — `LGRing/Jacobson.lean` and
`LGRing/Products.lean` — and `GPR 11.22` itself is `isLGRing_of_finite_maximalSpectrum` in
`LGRing/Semilocal.lean`, which is where this theorem is used.

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, 11.20, 11.21,
  11.22.
* [GN] Gille, Neher, *Group schemes over LG-rings and applications to cancellation theorems and
  Azumaya algebras*, European Journal of Mathematics **11** (2025), article 42, Example 2.2(a).
* [EG] Estes, Guralnick, *Module equivalences: local to global when primitive polynomials represent
  units*, Journal of Algebra **77** (1982), 138–157.
-/

@[expose] public section

universe u

/-- **The zero ring is an LG-ring** (`GN 2.2(a)`).

Both sides of the defining biconditional are trivially true: the zero ring has no maximal ideal at
all, so the right-hand side is vacuous, and every element of the zero ring — in particular every
value of `p` — is a unit, so the left-hand side holds outright. -/
theorem isLGRing_of_subsingleton (R : Type u) [CommRing R] [Subsingleton R] : IsLGRing R :=
  fun _ _ ↦ ⟨fun _ _ _ ↦ ⟨fun _ ↦ 0, isUnit_of_subsingleton _⟩,
    fun _ ↦ ⟨fun _ ↦ 0, isUnit_of_subsingleton _⟩⟩

/-- Every field is an LG-ring (`GPR 11.20`): the unique maximal ideal is `⊥`, with `K ⧸ ⊥ ≅ K`, so
the defining biconditional is trivial in each direction — the forward direction always holds
(units push forward along any algebra map), and the reverse direction follows by transporting the
witness back along `K ⧸ ⊥ ≅ K`. -/
theorem isLGRing_of_field (K : Type u) [Field K] : IsLGRing K := by
  intro n p
  constructor
  · rintro ⟨s, hs⟩ 𝔪 _
    refine ⟨fun i ↦ algebraMap K (K ⧸ 𝔪) (s i), ?_⟩
    have heq := MvPolynomial.comp_aeval_apply (f := s) (φ := Algebra.ofId K (K ⧸ 𝔪)) (p := p)
    simp only [Algebra.ofId_apply] at heq
    exact heq ▸ hs.map (algebraMap K (K ⧸ 𝔪))
  · intro hLG
    obtain ⟨s, hs⟩ := @hLG ⊥ Ideal.bot_isMaximal
    refine ⟨fun i ↦ (AlgEquiv.quotientBot K K) (s i), ?_⟩
    have heq := MvPolynomial.comp_aeval_apply
      (f := s) (φ := (AlgEquiv.quotientBot K K).toAlgHom) (p := p)
    exact heq ▸ hs.map (AlgEquiv.quotientBot K K).toRingEquiv.toRingHom
