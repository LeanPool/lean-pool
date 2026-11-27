/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.WedgeGeometry
public import LeanPool.VacuumBellSeparation.FreeField.SourceComplementStandardness
public import LeanPool.VacuumBellSeparation.FreeField.PolarUnitary

/-!
# Actual standard one-particle halfspace source spaces

The unbounded time-zero halfspaces are handled by their opposite open
halfspaces. Their real spaces are the literal completed source ranges.
The polar unitary is constructed from proved injectivity and density;
no modular boost or wedge duality premise is used.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory
open scoped InnerProductSpace

/-- Right wedge time zero with membership specified by `{x | ℓ < ⟪e₁, x⟫_ℝ}`. -/
def rightWedgeTimeZero (ℓ : ℝ) : Set (EuclideanSpace ℝ (Fin 3)) :=
  {x | ℓ < ⟪e₁, x⟫_ℝ}

theorem isOpen_leftWedgeTimeZero (ℓ : ℝ) : IsOpen (leftWedgeTimeZero ℓ) :=
  isOpen_lt (by fun_prop) continuous_const

theorem isOpen_rightWedgeTimeZero (ℓ : ℝ) : IsOpen (rightWedgeTimeZero ℓ) :=
  isOpen_lt continuous_const (by fun_prop)

theorem leftWedgeTimeZero_nonempty (ℓ : ℝ) : (leftWedgeTimeZero ℓ).Nonempty := by
  refine ⟨(ℓ - 1) • e₁, ?_⟩
  change ⟪e₁, (ℓ - 1) • e₁⟫_ℝ < ℓ
  rw [real_inner_smul_right, inner_e₁_self, mul_one]
  linarith

theorem rightWedgeTimeZero_nonempty (ℓ : ℝ) : (rightWedgeTimeZero ℓ).Nonempty := by
  refine ⟨(ℓ + 1) • e₁, ?_⟩
  change ℓ < ⟪e₁, (ℓ + 1) • e₁⟫_ℝ
  rw [real_inner_smul_right, inner_e₁_self, mul_one]
  linarith

theorem disjoint_wedgeTimeZero (ℓ : ℝ) : Disjoint (leftWedgeTimeZero ℓ) (rightWedgeTimeZero ℓ) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  change ⟪e₁, x⟫_ℝ < ℓ at hx
  change ℓ < ⟪e₁, x⟫_ℝ at hy
  exact lt_asymm hx hy

variable {m : ℝ} (hm : 0 < m) (ℓ : ℝ)

theorem complexSourceMap_injective_leftWedgeTimeZero :
    Function.Injective (complexSourceMap hm (leftWedgeTimeZero ℓ)) :=
  complexSourceMap_injective_of_open_complement hm (disjoint_wedgeTimeZero ℓ)
    (isOpen_rightWedgeTimeZero ℓ) (rightWedgeTimeZero_nonempty ℓ)

/-- Left wedge source standard subspace. -/
noncomputable def leftWedgeSourceStandardSubspace :
    StandardSubspace (Lp ℂ 2 (oneParticleMeasure m)) :=
  physicalSourceStandardSubspaceOfComplement hm (disjoint_wedgeTimeZero ℓ)
    (isOpen_leftWedgeTimeZero ℓ) (leftWedgeTimeZero_nonempty ℓ)
    (isOpen_rightWedgeTimeZero ℓ) (rightWedgeTimeZero_nonempty ℓ)

/-- Linear isometry equivalence for the left wedge source polar unitary, of type
`ComplexSourceHilbert hm (leftWedgeTimeZero ℓ) ≃ₗᵢ[ℂ] Lp ℂ 2 (oneParticleMeasure m)`. -/
noncomputable def leftWedgeSourcePolarUnitary :
    ComplexSourceHilbert hm (leftWedgeTimeZero ℓ) ≃ₗᵢ[ℂ] Lp ℂ 2 (oneParticleMeasure m) :=
  polarUnitary (complexSourceMap hm (leftWedgeTimeZero ℓ))
    (complexSourceMap_injective_leftWedgeTimeZero hm ℓ)
    (complexSourceMap_denseRange_of_open hm _ (isOpen_leftWedgeTimeZero ℓ)
      (leftWedgeTimeZero_nonempty ℓ))

theorem leftWedgeSourcePolarUnitary_factorization (z : ComplexSourceHilbert hm
  (leftWedgeTimeZero ℓ)) :
    leftWedgeSourcePolarUnitary hm ℓ (CFC.sqrt (sourceGram hm (leftWedgeTimeZero ℓ)) z) =
      complexSourceMap hm (leftWedgeTimeZero ℓ) z :=
  polarUnitary_polarGramRoot (complexSourceMap hm (leftWedgeTimeZero ℓ)) _ _ z

end VacuumBellSeparation
