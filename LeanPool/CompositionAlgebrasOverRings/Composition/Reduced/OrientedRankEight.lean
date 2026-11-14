/-
Copyright (c) 2026 Skip Garibaldi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Skip Garibaldi
-/
module

public import LeanPool.CompositionAlgebrasOverRings.Composition.Reduced.Orientation
public import LeanPool.CompositionAlgebrasOverRings.Composition.Reduced.RankEight

/-!
# Reduced octonion algebras are oriented twisted Zorn algebras (`GPR 22.15`)

`GPR 22.14` attaches to an orientation `θ : ⋀³ M ≅ k` of a finitely generated projective module
`M` of rank three its two associated vector products, and with them the algebra `Zor(M, θ)` of
twisted Zorn vector matrices. `GPR 22.15` (Petersson) says that up to isomorphism these are exactly
the reduced octonion algebras, an isomorphism `Zor(M, θ) ≅ C` matching the matrix unit `e₁₁` with
a given elementary idempotent `c`.

The ingredients are proved elsewhere. `Composition/Reduced/Orientation.lean` builds the pair of
an orientation, `Module.VectorProductPair.ofOrientation`, and shows that on a finite projective
module of constant rank three **every** vector-product pair arises this way from exactly one
orientation, its volume form `u ∧ v ∧ w ↦ ⟨u × v, w⟩`
(`Module.VectorProductPair.ofOrientation_orientation`). `Composition/Reduced/TwistedZorn.lean`
shows that the twisted Zorn algebra of any pair is a reduced composition algebra, and
`Composition/Reduced/RankEight.lean` proves the converse with the pair *read off* from Peirce
multiplication on `M = C₂₁`, with no orientation in sight
(`IsElementaryIdempotent.isomorphic_twistedZor_of_rankAtStalk_eq_eight`). This file combines them:
for the Peirce pair the volume form is `n_C(uv, w)`, which is the orientation `GPR (22.15.3)`
writes down.

⚠ **Not `GPR`'s proof.** `GPR 22.15` shows that `θ` is bijective using the algebra: over a field,
`θ = 0` would force `M² = 0`, which linearized right alternativity rules out, and over a local
ring one passes to the residue field. It then identifies the dual product using the Moufang
identities. The argument in `Composition/Reduced/Orientation.lean` needs only the vector-product
axioms, so it applies to every pair on a constant-rank-three module, not only to Peirce pairs.

⚠ **Orientation** means `GPR`'s notion, a linear isomorphism `⋀³ M ≃ k` (`GPR 21.8`, `22.14`), not
mathlib's `Orientation`, which is a ray of volume forms.

## Main results

* `ConicAlgebra.IsElementaryIdempotent.exists_orientation_isometryEquiv_twistedZor` :
  **`GPR 22.15`** for a given elementary idempotent, with the orientation `GPR (22.15.3)` and the
  normalization `GPR (22.15.1)`.
* `ConicAlgebra.IsElementaryIdempotent.exists_orientation_isomorphic_twistedZor`,
  `ConicAlgebra.IsElementaryIdempotent.exists_isomorphic_twistedZor_ofOrientation` : the
  isomorphism alone, on the Peirce component and in `GPR`'s form "for some `M` and `θ`".
* `ConicAlgebra.exists_isomorphic_twistedZor_ofOrientation_iff` : **`GPR 22.15`**, both
  directions: the algebras `Zor(M, θ)` are exactly the composition algebras of constant rank
  eight with an elementary idempotent.

## References

* [GPR] Garibaldi, Petersson, Racine, *Albert Algebras over Commutative Rings*, 21.8, 22.7,
  22.14, 22.15.
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace ConicAlgebra.IsElementaryIdempotent

variable {k : Type u} {A : Type v} [CommRing k] [NonAssocRing A] [Module k A]
  [SMulCommClass k A A] [IsScalarTower k A A] [IsAlternative A]
  {C : ConicAlgebra k A} {c : A}

/-- The Peirce-coordinate equivalence sends the matrix unit `e₁₁` of `GPR (22.14.7)` to the
idempotent `c`. -/
theorem twistedZorEquiv_matrixUnit (hc : C.IsElementaryIdempotent c)
    (hmul : C.IsMultiplicative) (hreg : C.norm.IsGPRRegular) :
    hc.twistedZorEquiv hmul hreg
      (((1, 0), (0, 0)) : TwistedZor (hc.peirceVectorProductPair hmul hreg)) = c := by
  change peirceElement c 1 0 ((hc.offDiagonalDuality hmul hreg).symm 0) 0 = c
  simp [peirceElement]

/-- The volume form of the Peirce vector products is `(u, v, w) ↦ n_C(uv, w)`, the trilinear form
of `GPR (22.15.3)`. -/
theorem crossAlternating_peirceVectorProductPair (hc : C.IsElementaryIdempotent c)
    (hmul : C.IsMultiplicative) (hreg : C.norm.IsGPRRegular)
    (u v w : ZornTwistingModule (k := k) c) :
    (hc.peirceVectorProductPair hmul hreg).crossAlternating ![u, v, w] =
      QuadraticMap.polar C.norm ((u : A) * v) w :=
  rfl

/-- **`GPR 22.15` (Petersson), oriented form.** Let `C` be a composition algebra of constant rank
eight with an elementary idempotent `c`, and let `M = C₂₁` be its lower-left Peirce component
(finite projective of constant rank three). The trilinear form `(u, v, w) ↦ n_C(uv, w)` of
`GPR (22.15.3)` is an orientation `θ` of `M`, and the Peirce coordinates are an isomorphism
`Zor(M, θ) ≅ C` sending the matrix unit `e₁₁` to `c` (`GPR (22.15.1)`, read in the inverse
direction). -/
theorem exists_orientation_isometryEquiv_twistedZor [Module.Finite k A] [Module.Projective k A]
    (hc : C.IsElementaryIdempotent c) (hcomp : C.IsComposition.{u, v, u})
    (hA : Module.rankAtStalk (R := k) A = fun _ ↦ 8) :
    letI : Module.Finite k (ZornTwistingModule (k := k) c) :=
      IsAlternative.finite_peirceComponent true false
    letI : Module.Projective k (ZornTwistingModule (k := k) c) :=
      IsAlternative.projective_peirceComponent hc.mul_self true false
    ∃ θ : (⋀[k]^3 (ZornTwistingModule (k := k) c)) ≃ₗ[k] k,
      (∀ u v w : ZornTwistingModule (k := k) c,
        θ (exteriorPower.ιMulti k 3 ![u, v, w]) = QuadraticMap.polar C.norm ((u : A) * v) w) ∧
      ∃ e : (twistedZor (Module.VectorProductPair.ofOrientation
          (hc.rankAtStalk_twistingModule_eq_three_of_isComposition hcomp hA) θ)).norm.IsometryEquiv
          C.norm,
        e 1 = 1 ∧ (∀ x y, e (x * y) = e x * e y) ∧
          e (((1, 0), (0, 0)) : TwistedZor (Module.VectorProductPair.ofOrientation
            (hc.rankAtStalk_twistingModule_eq_three_of_isComposition hcomp hA) θ)) = c := by
  let : Module.Finite k (ZornTwistingModule (k := k) c) :=
    IsAlternative.finite_peirceComponent true false
  let : Module.Projective k (ZornTwistingModule (k := k) c) :=
    IsAlternative.projective_peirceComponent hc.mul_self true false
  let hreg := hcomp.isGPRRegular_of_rankAtStalk_ne_one hA (by omega)
  let P := hc.peirceVectorProductPair hcomp.isMultiplicative hreg
  have hM : Module.rankAtStalk (R := k) (ZornTwistingModule (k := k) c) = fun _ ↦ 3 :=
    hc.rankAtStalk_twistingModule_eq_three_of_isComposition hcomp hA
  refine ⟨P.orientation hM, fun u v w ↦ P.orientation_ιMulti hM _, ?_⟩
  rw [P.ofOrientation_orientation hM]
  exact ⟨hc.twistedZorIsometryEquiv hcomp.isMultiplicative hreg,
    hc.twistedZorEquiv_one hcomp.isMultiplicative hreg,
    hc.twistedZorEquiv_mul hcomp.isMultiplicative hreg,
    hc.twistedZorEquiv_matrixUnit hcomp.isMultiplicative hreg⟩

/-- **`GPR 22.15` (Petersson), oriented form, isomorphism only.** A reduced composition algebra of
constant rank eight is isomorphic to `Zor(M, θ)` for its lower-left Peirce component `M` and some
orientation `θ` of `M`. -/
theorem exists_orientation_isomorphic_twistedZor [Module.Finite k A] [Module.Projective k A]
    (hc : C.IsElementaryIdempotent c) (hcomp : C.IsComposition.{u, v, u})
    (hA : Module.rankAtStalk (R := k) A = fun _ ↦ 8) :
    letI : Module.Finite k (ZornTwistingModule (k := k) c) :=
      IsAlternative.finite_peirceComponent true false
    letI : Module.Projective k (ZornTwistingModule (k := k) c) :=
      IsAlternative.projective_peirceComponent hc.mul_self true false
    ∃ θ : (⋀[k]^3 (ZornTwistingModule (k := k) c)) ≃ₗ[k] k,
      (twistedZor (Module.VectorProductPair.ofOrientation
        (hc.rankAtStalk_twistingModule_eq_three_of_isComposition hcomp hA) θ)).Isomorphic C := by
  obtain ⟨θ, -, e, h₁, hmul, -⟩ := hc.exists_orientation_isometryEquiv_twistedZor hcomp hA
  exact ⟨θ, e, h₁, hmul⟩

/-- **`GPR 22.15` (Petersson), in `GPR`'s words.** Every reduced composition algebra of constant
rank eight is isomorphic to `Zor(M, θ)` for some finitely generated projective module `M` of
constant rank three and some orientation `θ` of `M`. -/
theorem exists_isomorphic_twistedZor_ofOrientation [Module.Finite k A] [Module.Projective k A]
    (hc : C.IsElementaryIdempotent c) (hcomp : C.IsComposition.{u, v, u})
    (hA : Module.rankAtStalk (R := k) A = fun _ ↦ 8) :
    ∃ (M : Type v) (_ : AddCommGroup M) (_ : Module k M) (_ : Module.Finite k M)
      (_ : Module.Projective k M) (hM : Module.rankAtStalk (R := k) M = fun _ ↦ 3)
      (θ : (⋀[k]^3 M) ≃ₗ[k] k),
        (twistedZor (Module.VectorProductPair.ofOrientation hM θ)).Isomorphic C := by
  let : Module.Finite k (ZornTwistingModule (k := k) c) :=
    IsAlternative.finite_peirceComponent true false
  let : Module.Projective k (ZornTwistingModule (k := k) c) :=
    IsAlternative.projective_peirceComponent hc.mul_self true false
  obtain ⟨θ, h⟩ := hc.exists_orientation_isomorphic_twistedZor hcomp hA
  exact ⟨ZornTwistingModule (k := k) c, inferInstance, inferInstance, inferInstance,
    inferInstance, _, θ, h⟩

end ConicAlgebra.IsElementaryIdempotent

namespace ConicAlgebra

variable {k : Type u} [CommRing k]

/-- Twisted Zorn vector matrices on a finite projective module of constant rank three have
constant rank eight: `1 + 3 + 1 + 3`. -/
theorem rankAtStalk_twistedZor {M : Type v} [AddCommGroup M] [Module k M] [Module.Finite k M]
    [Module.Projective k M] (P : Module.VectorProductPair k M)
    (hM : Module.rankAtStalk (R := k) M = fun _ ↦ 3) :
    Module.rankAtStalk (R := k) (TwistedZor P) = fun _ ↦ 8 := by
  change Module.rankAtStalk (R := k) ((k × Module.Dual k M) × (k × M)) = _
  rw [Module.rankAtStalk_prod, Module.rankAtStalk_prod, Module.rankAtStalk_prod,
    TauCeti.Module.rankAtStalk_dual, hM]
  ext p
  have := p.nontrivial
  simp

variable {A : Type v} [NonAssocRing A] [Module k A] [SMulCommClass k A A] [IsScalarTower k A A]
  [IsAlternative A] [Module.Finite k A] [Module.Projective k A]

/-- **`GPR 22.15` (Petersson).** Up to isomorphism, the reduced octonion algebras are precisely
the algebras `Zor(M, θ)` of twisted Zorn vector matrices, for `M` finitely generated projective of
constant rank three and `θ` an orientation of `M`. A reduced octonion algebra is expressed as a
composition algebra of constant rank eight with an elementary idempotent; by `GPR 22.7` these are
the idempotents `GPR 22.6` asks for (absolutely primitive ones) when `k ≠ 0`. The direction `→` is
`IsElementaryIdempotent.exists_isomorphic_twistedZor_ofOrientation`; the direction `←` is the
first half of `GPR 22.15`'s proof (`isComposition_twistedZor`,
`hasElementaryIdempotent_twistedZor`), together with the rank count `rankAtStalk_twistedZor`. -/
theorem exists_isomorphic_twistedZor_ofOrientation_iff (C : ConicAlgebra k A) :
    (∃ (M : Type v) (_ : AddCommGroup M) (_ : Module k M) (_ : Module.Finite k M)
        (_ : Module.Projective k M) (hM : Module.rankAtStalk (R := k) M = fun _ ↦ 3)
        (θ : (⋀[k]^3 M) ≃ₗ[k] k),
          (twistedZor (Module.VectorProductPair.ofOrientation hM θ)).Isomorphic C) ↔
      C.IsComposition.{u, v, u} ∧ C.HasElementaryIdempotent ∧
        Module.rankAtStalk (R := k) A = fun _ ↦ 8 := by
  constructor
  · rintro ⟨M, _, _, _, _, hM, θ, h⟩
    refine ⟨h.symm.isComposition isComposition_twistedZor, ?_, ?_⟩
    · exact h.hasElementaryIdempotent_iff.mp (hasElementaryIdempotent_twistedZor _)
    · obtain ⟨e, -, -⟩ := h
      rw [← Module.rankAtStalk_eq_of_equiv e.toLinearEquiv]
      exact rankAtStalk_twistedZor _ hM
  · rintro ⟨hcomp, ⟨c, hc⟩, hA⟩
    exact hc.exists_isomorphic_twistedZor_ofOrientation hcomp hA

end ConicAlgebra
