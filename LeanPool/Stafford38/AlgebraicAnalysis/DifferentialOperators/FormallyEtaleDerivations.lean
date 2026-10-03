/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import Mathlib.RingTheory.Etale.Kaehler

/-!
# Derivations through formally étale algebras

The base-change equivalence for Kähler differentials extends derivations uniquely.
Localizations and separable field extensions use this common construction.
-/

@[expose] public section

namespace AlgebraicAnalysis.DifferentialOperators.FormallyEtaleDerivations

open TensorProduct

noncomputable section

universe u

variable (k A B : Type u)
variable [CommRing k] [CommRing A] [CommRing B]
variable [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
variable [Algebra.FormallyEtale A B]

/-- Extend a `k`-derivation through a formally étale algebra `A → B`, by the
formally-etale base-change equivalence for Kähler differentials. -/
noncomputable def extendDerivation
    (D : Derivation k A B) : Derivation k B B := by
  let base : B ⊗[A] KaehlerDifferential k A →ₗ[B] B :=
    D.liftKaehlerDifferential.liftBaseChange B
  let pull : KaehlerDifferential k B →ₗ[B] B :=
    base.comp
      (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale
        k A B).symm.toLinearMap
  exact KaehlerDifferential.linearMapEquivDerivation k B pull

@[simp]
theorem extendDerivation_compAlgebraMap
    (D : Derivation k A B) :
    (extendDerivation k A B D).compAlgebraMap A = D := by
  apply Derivation.ext
  intro a
  simp [extendDerivation,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap,
    Derivation.liftKaehlerDifferential_comp_D]

/-- A derivation of a formally étale algebra is uniquely determined by its restriction
to the original algebra. -/
theorem derivation_ext_of_compAlgebraMap_eq
    {D₁ D₂ : Derivation k B B}
    (h : D₁.compAlgebraMap A = D₂.compAlgebraMap A) :
    D₁ = D₂ := by
  let e := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k A B
  have hbase :
      (D₁.liftKaehlerDifferential.restrictScalars A).comp
          (KaehlerDifferential.map k k A B) =
        (D₂.liftKaehlerDifferential.restrictScalars A).comp
          (KaehlerDifferential.map k k A B) := by
    apply Derivation.liftKaehlerDifferential_unique
    apply Derivation.ext
    intro x
    simpa [KaehlerDifferential.map_D,
      Derivation.liftKaehlerDifferential_comp_D] using
      Derivation.congr_fun h x
  have hpull :
      D₁.liftKaehlerDifferential.comp e.toLinearMap =
        D₂.liftKaehlerDifferential.comp e.toLinearMap := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a x =>
        simp only [e,
          KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
          KaehlerDifferential.mapBaseChange_tmul,
          LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.map_smul]
        exact congrArg (a • ·) (LinearMap.congr_fun hbase x)
  apply Derivation.ext
  intro x
  have hmaps : D₁.liftKaehlerDifferential = D₂.liftKaehlerDifferential := by
    apply LinearMap.ext
    intro w
    obtain ⟨z, rfl⟩ := e.surjective w
    exact LinearMap.congr_fun hpull z
  simpa [Derivation.liftKaehlerDifferential_comp_D] using
    LinearMap.congr_fun hmaps (KaehlerDifferential.D k B x)

end

end AlgebraicAnalysis.DifferentialOperators.FormallyEtaleDerivations
