/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.NumberFields.ConductorQuotient
public import Mathlib.Algebra.CharZero.Infinite

/-! # Residue roots give ideals of prime norm

For a modulus coprime to the conductor exponent, Kummer–Dedekind identifies
the quotient of the ring of integers with the quotient by the reduced minimal
polynomial. Evaluation at a residue root gives an ideal of that norm; at a
prime modulus this ideal is maximal.
-/

@[expose] public section

namespace NairTenenbaum

open Polynomial NumberField Ideal

variable {K : Type*} [Field K] [NumberField K]
variable (θ : 𝓞 K) {p : ℕ}

/-- The residue-algebra homomorphism induced by a polynomial root. -/
noncomputable def residueRootHom (hp : p.Coprime (RingOfIntegers.exponent θ))
    (a : ResidueRoots (minpoly ℤ θ) p) : 𝓞 K →+* ZMod p :=
  (AdjoinRoot.lift (RingHom.id (ZMod p)) a.1 (by
    simpa only [eval₂_id, eval_map] using a.2)).comp
      ((residuePolynomialQuotientEquiv θ hp).symm.toRingHom.comp
        (Ideal.Quotient.mk (Ideal.span {(p : 𝓞 K)})))

@[simp] theorem residueRootHom_apply_generator (hp : p.Coprime (RingOfIntegers.exponent θ))
    (a : ResidueRoots (minpoly ℤ θ) p) : residueRootHom θ hp a θ = a.1 := by
  have H := residuePolynomialQuotientEquiv_mk θ hp (X : ℤ[X])
  simp only [Polynomial.map_X, aeval_X] at H
  change (AdjoinRoot.lift (RingHom.id (ZMod p)) a.1
    (by simpa only [eval₂_id, eval_map] using a.2))
      ((residuePolynomialQuotientEquiv θ hp).symm
        ((Ideal.Quotient.mk (Ideal.span {(p : 𝓞 K)})) θ)) = a.1
  rw [← H, RingEquiv.symm_apply_apply]
  exact AdjoinRoot.lift_root _

theorem residueRootHom_injective (hp : p.Coprime (RingOfIntegers.exponent θ)) :
    Function.Injective (residueRootHom θ hp) := by
  intro a b hab
  apply Subtype.ext
  have H := congrArg (fun f : 𝓞 K →+* ZMod p => f θ) hab
  simpa only [residueRootHom_apply_generator] using H

/-- The ideal obtained as the kernel of the residue-root homomorphism. -/
noncomputable def residueRootIdeal (hp : p.Coprime (RingOfIntegers.exponent θ))
    (a : ResidueRoots (minpoly ℤ θ) p) : Ideal (𝓞 K) :=
  RingHom.ker (residueRootHom θ hp a)

@[simp] theorem residueRootIdeal_absNorm (hp : p.Coprime (RingOfIntegers.exponent θ))
    (a : ResidueRoots (minpoly ℤ θ) p) : Ideal.absNorm (residueRootIdeal θ hp a) = p := by
  rw [Ideal.absNorm_apply]
  exact cardQuot_ker_zmod _

theorem residueRootIdeal_injective (hp : p.Coprime (RingOfIntegers.exponent θ)) :
    Function.Injective (residueRootIdeal θ hp) :=
  (zmod_ringHom_ker_injective p).comp (residueRootHom_injective θ hp)

theorem rootCount_minpoly_le_card_ideals_norm (hp : p.Coprime (RingOfIntegers.exponent θ)) :
    rootCount (minpoly ℤ θ) p ≤ Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = p} := by
  let : Finite {I : Ideal (𝓞 K) // Ideal.absNorm I = p} :=
    (Ideal.finite_setOfPred_absNorm_eq p).to_subtype
  let f : ResidueRoots (minpoly ℤ θ) p → {I : Ideal (𝓞 K) // Ideal.absNorm I = p} :=
    fun a => ⟨residueRootIdeal θ hp a, residueRootIdeal_absNorm θ hp a⟩
  exact Nat.card_le_card_of_injective f (fun a b h =>
    residueRootIdeal_injective θ hp (congrArg Subtype.val h))

end NairTenenbaum
