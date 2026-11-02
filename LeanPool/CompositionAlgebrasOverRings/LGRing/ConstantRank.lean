/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import LeanPool.CompositionAlgebrasOverRings.LGRing.Unimodular
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-!
# Constant-rank projective modules over an LG-ring are free (`GN 2.6(b)`, `GPR 11.24`)

This is *the* motto of LG-rings, made precise: over an LG-ring, a finitely generated projective
module whose rank is the same at every prime is free.

## Main results

* `Module.nontrivial_quotient_tensor_of_rankAtStalk_pos` : positive rank at a maximal ideal makes
  the residue-field fibre nonzero — the bridge from `Module.rankAtStalk` to the hypothesis of
  `IsLGRing.exists_isUnimodular`.
* `Module.free_of_isLGRing_of_rankAtStalk_eq` : **`GN 2.6(b)`**, by induction on the rank.

## Proof idea

Induct on the common rank `d`, with `M` generalized.

At `d = 0` the module is a subsingleton (`Module.rankAtStalk_eq_zero_iff_subsingleton`), hence
free. At `d + 1` the rank is positive at every prime, so every residue-field fibre is nonzero and
`GN 2.6(a)` (`IsLGRing.exists_isUnimodular`, `LGRing/Unimodular.lean`) produces a unimodular
`m ∈ M`. That splits `M ≃ R × ker l` (`LinearMap.equivProdKerOfApplyEqOne`), and
`Module.rankAtStalk_prod` together with `Module.rankAtStalk_self` turns the rank equation into
`rankAtStalk (ker l) = d` — constant again, one lower. The induction hypothesis makes `ker l`
free, and `R × ker l` is then free, hence so is `M`.

The complement is `ker l`, a `Submodule R M`: it lives in the same universe as `M`, which is what
lets the induction quantify over a single `Type v`.

## Implementation notes

The rank is `Module.rankAtStalk`, mathlib's rank of the localization at a prime. Everything the
induction needs — additivity over products, invariance under equivalence, the value at `R`, and
vanishing exactly on subsingletons — is already in
`Mathlib.RingTheory.Spectrum.Prime.FreeLocus`, so this file adds no rank theory of its own.

The one genuinely new bridge is `Module.nontrivial_quotient_tensor_of_rankAtStalk_pos`: the LG
axiom speaks about residue fields `R ⧸ 𝔪`, whereas `rankAtStalk` is defined through localizations
`R_𝔪`. `Module.rankAtStalk_baseChange` relates them — base changing `M` to the field `R ⧸ 𝔪` and
reading the rank at that field's unique prime `⊥` gives back the rank of `M` at `𝔪`, because
`⊥` pulls back along `R → R ⧸ 𝔪` to `𝔪`. Over a field every module is free, so that rank is a
`finrank`, and a positive `finrank` forces nontriviality.

## References

* [GN] Gille, Neher, *Group schemes over LG-rings and applications to cancellation theorems and
  Azumaya algebras*, European Journal of Mathematics **11** (2025), article 42, Lemma 2.6(b),
  also stated as 2.1(c).
* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, 11.24.
-/

@[expose] public section

universe u v

open scoped TensorProduct

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- Positive rank at a maximal ideal makes the residue-field fibre nonzero.

This is the bridge from `Module.rankAtStalk`, which is defined through the localization `R_𝔪`, to
the hypothesis of `IsLGRing.exists_isUnimodular`, which — like the LG axiom itself — speaks about
the residue field `R ⧸ 𝔪`. See the module docstring. -/
theorem Module.nontrivial_quotient_tensor_of_rankAtStalk_pos [Module.Finite R M]
    [Module.Projective R M] (𝔪 : Ideal R) (h𝔪 : 𝔪.IsMaximal)
    (h : 0 < Module.rankAtStalk (R := R) M ⟨𝔪, h𝔪.isPrime⟩) :
    Nontrivial ((R ⧸ 𝔪) ⊗[R] M) := by
  let : Field (R ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  refine Module.nontrivial_of_finrank_pos (R := R ⧸ 𝔪) ?_
  have hcomap : (PrimeSpectrum.comap (algebraMap R (R ⧸ 𝔪)) ⊥ : PrimeSpectrum R) =
      ⟨𝔪, h𝔪.isPrime⟩ := by
    refine PrimeSpectrum.ext ?_
    change Ideal.comap (algebraMap R (R ⧸ 𝔪)) ⊥ = 𝔪
    rw [← RingHom.ker_eq_comap_bot, Ideal.Quotient.algebraMap_eq]
    exact Ideal.mk_ker
  have := Module.rankAtStalk_baseChange (R := R) (M := M) (S := R ⧸ 𝔪) ⊥
  rw [hcomap, Module.rankAtStalk_eq_finrank_of_free] at this
  simp only [Pi.natCast_apply, Nat.cast_id] at this
  omega

/-- **`GN 2.6(b)`, `GPR 11.24`.** Over an LG-ring, a finitely generated projective module of
constant rank is free.

The rank is `Module.rankAtStalk`, and "constant" means literally the constant function `d`. See
the module docstring for the induction. -/
theorem Module.free_of_isLGRing_of_rankAtStalk_eq (hLG : IsLGRing R) (d : ℕ) :
    ∀ (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M],
      Module.rankAtStalk (R := R) M = (fun _ ↦ d) → Module.Free R M := by
  induction d with
  | zero =>
    intro M _ _ _ _ h
    have : Subsingleton M := Module.rankAtStalk_eq_zero_iff_subsingleton.mp h
    exact Module.Free.of_subsingleton R M
  | succ d ih =>
    intro M _ _ _ _ h
    rcases subsingleton_or_nontrivial R with hR | hR
    · have : Subsingleton M := Module.subsingleton R M
      exact Module.Free.of_subsingleton R M
    -- Positive rank everywhere, so `GN 2.6(a)` produces a unimodular element.
    obtain ⟨m, hm⟩ := hLG.exists_isUnimodular (M := M) fun 𝔪 h𝔪 ↦
      Module.nontrivial_quotient_tensor_of_rankAtStalk_pos 𝔪 h𝔪 (by
        rw [h]; exact Nat.succ_pos d)
    obtain ⟨l, hl⟩ := Module.isUnimodular_iff.mp hm
    set e := LinearMap.equivProdKerOfApplyEqOne l m hl with he
    have : Module.Finite R (LinearMap.ker l) := Module.Finite.of_linearEquiv_prod e
    have : Module.Projective R (LinearMap.ker l) := Module.Projective.of_linearEquiv_prod e
    -- The complement has constant rank `d`, one lower.
    have hker : Module.rankAtStalk (R := R) (LinearMap.ker l) = (fun _ ↦ d) := by
      have hprod := Module.rankAtStalk_prod (R := R) R (LinearMap.ker l)
      have hM := Module.rankAtStalk_eq_of_equiv e
      rw [hprod, Module.rankAtStalk_self] at hM
      funext p
      have := congrFun (hM.symm.trans h) p
      simp only [Pi.add_apply, Pi.one_apply] at this
      omega
    have := ih (LinearMap.ker l) hker
    exact Module.Free.of_equiv (R := R) (M := R × (LinearMap.ker l)) e.symm
