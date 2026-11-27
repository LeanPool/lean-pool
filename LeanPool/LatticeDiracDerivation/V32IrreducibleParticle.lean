/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

/-
Adapted from gpartin/LeanDiracDerivation at commit e2161e0936f181d4a5a9d49963a666f7cea42502.
Upstream source is dual-licensed under MIT or CC0 1.0; used here under MIT.
-/

module

public import LeanPool.LatticeDiracDerivation.V32CopyClassification

/-!
# V3.2 Stage 6: massive spin-one-half sector

The V3.1 Lorentz certificate already derives the unique nonzero half scale,
the little-group algebra, finite rotations, and the rest Pauli--Lubanski
Casimir.  This stage combines it with the global branch projectors and the
two-copy classification without promoting the result to a physical electron.
-/

@[expose] public section



namespace LeanDirac.V2

noncomputable section

/-- The V3.2 R es tS pi no r2 definition used by this stage. -/
abbrev V32RestSpinor2 := Fin 2 → ℂ

/-- The V3.2 R es tP os it iv eE mb ed definition used by this stage. -/
def v32RestPositiveEmbed (z : V32RestSpinor2) : CubicalCell4
  | 0 => z 0
  | 1 => z 1
  | _ => 0

/-- The V3.2 R es tP os it iv eR ea d definition used by this stage. -/
def v32RestPositiveRead (z : CubicalCell4) : V32RestSpinor2
  | 0 => z 0
  | _ => z 1

/-- The V3.2 R es tS pi n definition used by this stage. -/
def v32RestSpin (axis : Fin 3) (z : V32RestSpinor2) : V32RestSpinor2 :=
  v32RestPositiveRead (standardCubicalSpin axis (v32RestPositiveEmbed z))

/-- The V3.2 S pi n2 Ma tr ix Ac ti on definition used by this stage. -/
def v32Spin2MatrixAction
    (a b c d : ℂ) (z : V32RestSpinor2) : V32RestSpinor2
  | 0 => a * z 0 + b * z 1
  | _ => c * z 0 + d * z 1

/-- The V3.2 S pi n2 Ba si s0 definition used by this stage. -/
def v32Spin2Basis0 : V32RestSpinor2
  | 0 => 1
  | _ => 0

/-- The V3.2 S pi n2 Ba si s1 definition used by this stage. -/
def v32Spin2Basis1 : V32RestSpinor2
  | 0 => 0
  | _ => 1

theorem v32_positive_rest_projector_fixes_spinor
    (mass : ℝ) (hmass : 0 < mass) (z : V32RestSpinor2) :
    v32PositiveProjector mass 0 0 0 mass (v32RestPositiveEmbed z) =
      v32RestPositiveEmbed z := by
  funext component
  fin_cases component <;>
    simp [v32PositiveProjector, v32SpectralProjector,
      v32ContinuumHamiltonian, cubicalStandardHamiltonian,
      cubicalStandardSpatial, cubicalStandardBeta,
      cubicalStandardAlphaX, cubicalStandardAlphaY,
      cubicalStandardAlphaZ, v32RestPositiveEmbed, ne_of_gt hmass] <;> ring

theorem v32_rest_spin_commutant_is_scalar
    (a b c d : ℂ)
    (hcommute : ∀ axis z,
      v32Spin2MatrixAction a b c d (v32RestSpin axis z) =
        v32RestSpin axis (v32Spin2MatrixAction a b c d z)) :
    b = 0 ∧ c = 0 ∧ a = d := by
  have hz1 := congrFun (hcommute (2 : Fin 3) v32Spin2Basis1) 0
  have hx0 := congrFun (hcommute (0 : Fin 3) v32Spin2Basis0) 1
  have hx1 := congrFun (hcommute (0 : Fin 3) v32Spin2Basis1) 0
  norm_num [v32RestSpin, v32RestPositiveRead, v32RestPositiveEmbed,
    v32Spin2MatrixAction,
    v32Spin2Basis0, v32Spin2Basis1, standardCubicalSpin,
    standardCubicalPlaneBivector, standardCubicalGamma,
    cubicalStandardAlphaX, cubicalStandardAlphaY,
    cubicalStandardAlphaZ, native_cubical_spin_scale_eq_half] at hx0 hx1 hz1
  have hII (x : ℂ) : Complex.I * (Complex.I * x) = -x := by
    rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]
  constructor
  · rw [hII b] at hx1
    field_simp at hx1
    exact CharZero.eq_neg_self_iff.mp hx1
  constructor
  · rw [hII c] at hx0
    field_simp at hx0
    exact CharZero.eq_neg_self_iff.mp hx0
  · rw [hII d] at hz1
    field_simp at hz1
    simpa using hz1

/-- The bundled V3.2 I rr ed uc ib le Pa rt ic le Ce rt if ic at e. -/
structure V32IrreducibleParticleCertificate : Prop where
  projectors : V32SpectralProjectorCertificate
  copies : V32CopyClassificationCertificate
  lorentzSpin : LorentzSpinHalfCertificate
  restCasimir : ∀ mass z,
    cubicalPauliLubanskiSquare mass (fun _ => 0) z =
      fun component => -(3 / 4 : ℂ) * mass ^ 2 * z component
  uniqueHalfScale : ∃! scale : ℝ, admissibleCubicalSpinScale scale
  positiveRestProjectorIsTwoState : ∀ mass, 0 < mass → ∀ z,
    v32PositiveProjector mass 0 0 0 mass (v32RestPositiveEmbed z) =
      v32RestPositiveEmbed z
  restLittleGroupCommutantScalar : ∀ a b c d,
    (∀ axis z,
      v32Spin2MatrixAction a b c d (v32RestSpin axis z) =
        v32RestSpin axis (v32Spin2MatrixAction a b c d z)) →
      b = 0 ∧ c = 0 ∧ a = d
  fullTheoryCopyMultiplicity : V32CopyClassificationCertificate

theorem v32_irreducible_particle_sector :
    V32IrreducibleParticleCertificate where
  projectors := v32_spectral_projectors
  copies := v32_copy_classification
  lorentzSpin := lorentz_spin_half_from_native_action
  restCasimir := rest_pauli_lubanski_spin_half
  uniqueHalfScale := exists_unique_admissible_cubical_spin_scale
  positiveRestProjectorIsTwoState := v32_positive_rest_projector_fixes_spinor
  restLittleGroupCommutantScalar := v32_rest_spin_commutant_is_scalar
  fullTheoryCopyMultiplicity := v32_copy_classification


end
end LeanDirac.V2
