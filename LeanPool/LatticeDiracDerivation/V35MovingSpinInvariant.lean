/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

/-
Adapted from gpartin/LeanDiracDerivation at commit 43859849eb6ed37e16c802fbae3fd50dd731665c.
Upstream source is dual-licensed under MIT or CC0 1.0; used here under MIT.
-/

module

public import LeanPool.LatticeDiracDerivation.V35BilinearCliffordClosure
public import LeanPool.LatticeDiracDerivation.V34MomentumHelicity

/-!
# V3.5 Stage 7: moving spin invariant and helicity agreement

V3.2 proved the Pauli--Lubanski value at rest.  This stage evaluates the same
cube-derived operator at arbitrary energy and momentum and identifies the
V3.4 helicity operator with its normalized time component.
-/

@[expose] public section

namespace LeanDirac.V2

noncomputable section

/-- Package Cartesian momentum components as inherited complex momentum data. -/
def v35Momentum3 (px py pz : ℝ) : Fin 3 → ℂ
  | 0 => px
  | 1 => py
  | _ => pz

theorem v35_pauli_lubanski_square_at_momentum
    (energy px py pz : ℝ) (z : CubicalCell4) :
    cubicalPauliLubanskiSquare (energy : ℂ) (v35Momentum3 px py pz) z =
      fun component =>
        -(3 / 4 : ℂ) *
          ((energy : ℂ)^2 - (px : ℂ)^2 - (py : ℂ)^2 - (pz : ℂ)^2) *
            z component := by
  funext component
  fin_cases component <;>
    simp [cubicalPauliLubanskiSquare, cubicalPauliLubanskiTime,
      cubicalPauliLubanskiSpace, cubicalMomentumCrossBoost,
      v35Momentum3, standardCubicalSpin, standardCubicalBoost,
      standardCubicalPlaneBivector, standardCubicalGamma,
      cubicalStandardAlphaX, cubicalStandardAlphaY,
      cubicalStandardAlphaZ] <;>
    ring_nf <;> norm_num [Complex.I_sq] <;> ring

theorem v35_on_shell_pauli_lubanski_spin_half
    (mass energy px py pz : ℝ)
    (hshell : energy ^ 2 = mass ^ 2 + px ^ 2 + py ^ 2 + pz ^ 2)
    (z : CubicalCell4) :
    cubicalPauliLubanskiSquare (energy : ℂ) (v35Momentum3 px py pz) z =
      fun component => -(3 / 4 : ℂ) * (mass : ℂ)^2 * z component := by
  rw [v35_pauli_lubanski_square_at_momentum]
  have hshellC : (energy : ℂ)^2 =
      (mass : ℂ)^2 + (px : ℂ)^2 + (py : ℂ)^2 + (pz : ℂ)^2 := by
    exact_mod_cast hshell
  funext component
  rw [hshellC]
  ring

/-- The V3.4 Pauli readout uses the cube-generator ordering.  For standard
`(px,py,pz)` labels that ordering is `(-pz,-py,px)`; the signs and permutation
are therefore derived from the existing cubical generators, not selected to
change the spectrum. -/
theorem v35_helicity_is_pauli_lubanski_time_at_nonzero_scale
    (radius px py pz : ℝ) (hne : radius ≠ 0)
    (z : CubicalCell4) :
    cubicalPauliLubanskiTime (v35Momentum3 px py pz) z =
      fun component =>
        (radius : ℂ) *
          v34MomentumHelicity radius (-pz) (-py) px z component := by
  funext component
  fin_cases component <;>
    simp [cubicalPauliLubanskiTime, v35Momentum3,
      standardCubicalSpin, standardCubicalPlaneBivector,
      standardCubicalGamma, v34MomentumHelicity,
      v34TwoChannelHelicity, v34UpperChannels, v34LowerChannels,
      positivePauliSpatial, cubicalSpatialLower, cubicalStandardSpatial,
      cubicalUpperEmbedding, cubicalStandardAlphaX,
      cubicalStandardAlphaY, cubicalStandardAlphaZ] <;>
    field_simp [hne]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq]
  all_goals ring

/-- Specialize the nonzero-scale helicity identity to a positive radius whose
square is the momentum norm. -/
theorem v35_helicity_is_normalized_pauli_lubanski_time
    (radius px py pz : ℝ) (hpositive : 0 < radius)
    (_hradius : radius ^ 2 = px ^ 2 + py ^ 2 + pz ^ 2)
    (z : CubicalCell4) :
    cubicalPauliLubanskiTime (v35Momentum3 px py pz) z =
      fun component =>
        (radius : ℂ) *
          v34MomentumHelicity radius (-pz) (-py) px z component := by
  exact v35_helicity_is_pauli_lubanski_time_at_nonzero_scale
    radius px py pz (ne_of_gt hpositive) z

/-- Certificate for the arbitrary-momentum Pauli--Lubanski square, its on-shell
value, and the helicity bridge. -/
structure V35MovingSpinInvariantCertificate : Prop where
  arbitraryMomentum : ∀ (energy px py pz : ℝ) (z : CubicalCell4),
    cubicalPauliLubanskiSquare (energy : ℂ) (v35Momentum3 px py pz) z =
      fun component =>
        -(3 / 4 : ℂ) *
          ((energy : ℂ)^2 - (px : ℂ)^2 - (py : ℂ)^2 - (pz : ℂ)^2) *
            z component
  onShellSpinHalf : ∀ (mass energy px py pz : ℝ),
    energy ^ 2 = mass ^ 2 + px ^ 2 + py ^ 2 + pz ^ 2 → ∀ z,
      cubicalPauliLubanskiSquare (energy : ℂ) (v35Momentum3 px py pz) z =
        fun component => -(3 / 4 : ℂ) * (mass : ℂ)^2 * z component
  helicityAgreement : ∀ (radius px py pz : ℝ),
    0 < radius →
    radius ^ 2 = px ^ 2 + py ^ 2 + pz ^ 2 → ∀ z : CubicalCell4,
      cubicalPauliLubanskiTime (v35Momentum3 px py pz) z =
        fun component =>
          (radius : ℂ) *
            v34MomentumHelicity radius (-pz) (-py) px z component

theorem v35_moving_spin_invariant : V35MovingSpinInvariantCertificate where
  arbitraryMomentum := v35_pauli_lubanski_square_at_momentum
  onShellSpinHalf := v35_on_shell_pauli_lubanski_spin_half
  helicityAgreement := v35_helicity_is_normalized_pauli_lubanski_time

end
end LeanDirac.V2
