/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import Mathlib.RingTheory.Etale.Field
public import LeanPool.Stafford38.AlgebraicAnalysis.DifferentialOperators.FormallyEtaleDerivations


/-!
# Extending residue-field derivations through a separable extension

Let `k -> E -> K` be a tower of fields and suppose that `K/E` is separable.
Formal etaleness identifies the Kahler differentials of `K/k` with the base
change to `K` of the differentials of `E/k`.  Dualizing gives an exact linear
equivalence

`Der_k(K, K) = Der_k(E, K)`.

Thus every `k`-derivation of the relative coefficient field, after mapping its
values into the boundary residue field, extends uniquely to that residue
field.  This is the derivation-extension part of the higher-dimensional
boundary-chart producer.

This file does not construct a coefficient-field section of a complete DVR,
identify a completion with `K[[t]]`, or extend these derivations continuously
to power series.  Those remain separate inputs to the completed-chart step.
-/

@[expose] public section

namespace Stafford38.Geometry.SeparableResidueDerivationExtension

open TensorProduct
open AlgebraicAnalysis.DifferentialOperators

noncomputable section

universe u

variable (k E K : Type u)
variable [Field k] [Field E] [Field K]
variable [Algebra k E] [Algebra k K] [Algebra E K]
variable [IsScalarTower k E K]
variable [Algebra.IsSeparable E K]

/-- Extend a `k`-derivation `E -> K` uniquely through the separable field
extension `K/E`.  The construction is the dual of the formally-etale base
change equivalence for Kahler differentials. -/
noncomputable def extendDerivation
    (D : Derivation k E K) : Derivation k K K := by
  letI : Algebra.FormallyEtale E K :=
    Algebra.FormallyEtale.of_isSeparable E K
  exact FormallyEtaleDerivations.extendDerivation k E K D

/-- Restricting the extended derivation to `E` recovers the supplied
`E -> K` derivation exactly. -/
@[simp]
theorem extendDerivation_compAlgebraMap
    (D : Derivation k E K) :
    (extendDerivation k E K D).compAlgebraMap E = D := by
  let : Algebra.FormallyEtale E K :=
    Algebra.FormallyEtale.of_isSeparable E K
  exact FormallyEtaleDerivations.extendDerivation_compAlgebraMap
    k E K D

/-- A `k`-derivation of `K` is determined by its restriction to `E` when
`K/E` is separable. -/
theorem derivation_ext_of_compAlgebraMap_eq
    {D₁ D₂ : Derivation k K K}
    (h : D₁.compAlgebraMap E = D₂.compAlgebraMap E) :
    D₁ = D₂ := by
  let : Algebra.FormallyEtale E K :=
    Algebra.FormallyEtale.of_isSeparable E K
  exact FormallyEtaleDerivations.derivation_ext_of_compAlgebraMap_eq
    k E K h

/-- Existence and uniqueness in the direct form used by the boundary tower. -/
theorem existsUnique_derivation_extension
    (D : Derivation k E K) :
    ∃! D' : Derivation k K K, D'.compAlgebraMap E = D := by
  refine ⟨extendDerivation k E K D,
    extendDerivation_compAlgebraMap k E K D, ?_⟩
  intro D' hD'
  apply derivation_ext_of_compAlgebraMap_eq k E K
  rw [hD', extendDerivation_compAlgebraMap]

/-- Restriction of derivations along `E -> K`, as a `K`-linear map. -/
def restrictDerivation :
    Derivation k K K →ₗ[K] Derivation k E K where
  toFun D := D.compAlgebraMap E
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl

/-- Restriction is a linear equivalence for a separable field extension.  In
particular, finite derivation frames can be transported without losing linear
relations. -/
noncomputable def derivationRestrictionEquiv :
    Derivation k K K ≃ₗ[K] Derivation k E K :=
  LinearEquiv.ofBijective (restrictDerivation k E K) ⟨
    (fun _ _ h ↦ derivation_ext_of_compAlgebraMap_eq k E K h),
    (fun D ↦ ⟨extendDerivation k E K D,
      extendDerivation_compAlgebraMap k E K D⟩)⟩

@[simp]
theorem derivationRestrictionEquiv_apply
    (D : Derivation k K K) :
    derivationRestrictionEquiv k E K D = D.compAlgebraMap E :=
  rfl

/-- Specialization to a derivation whose values initially lie in `E`. -/
noncomputable def extendCoefficientDerivation
    (D : Derivation k E E) : Derivation k K K :=
  extendDerivation k E K ((Algebra.linearMap E K).compDer D)

@[simp]
theorem extendCoefficientDerivation_compAlgebraMap
    (D : Derivation k E E) :
    (extendCoefficientDerivation k E K D).compAlgebraMap E =
      (Algebra.linearMap E K).compDer D := by
  exact extendDerivation_compAlgebraMap k E K _


end

end Stafford38.Geometry.SeparableResidueDerivationExtension
