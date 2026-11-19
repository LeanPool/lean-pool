/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

/-
Adapted from gpartin/LeanDiracDerivation, file `LeanDirac/Dirac027.lean`, at commit
867004142ada3eec464d5bd3088d7313fdad1613.
Upstream copyright (c) 2026 G. D. Partin, dual-licensed at the recipient's
option under the MIT License or CC0 1.0 (see the upstream `LICENSE`,
`LICENSE-CC0` and `LICENSING.md`); used here under the MIT License.
-/

module

public import LeanPool.LatticeDiracDerivation.Dirac026

/-!
# DIRAC-027: Pauli--Lubanski spin invariant

This stage combines the rotations and boosts proved in DIRAC-026 into the
Pauli--Lubanski four-vector.  Its square is then calculated from the same
operators.  No spin value is inserted into the definition.
-/

@[expose] public section

namespace LeanDirac

noncomputable section
open Complex

/-- The time component `px S₀ + py S₁ + pz S₂` of the Pauli–Lubanski operator, where
`Sᵢ = standardCubeSpin i`. -/
def pauliLubanskiTime
    (px py pz : ℝ) (z : Cell4) : Cell4 :=
  fun component =>
    (px : ℂ) * standardCubeSpin 0 z component +
      (py : ℂ) * standardCubeSpin 1 z component +
      (pz : ℂ) * standardCubeSpin 2 z component

/-- The first spatial component `energy S₀ - py K₂ + pz K₁` of the Pauli–Lubanski operator, where
`Sᵢ = standardCubeSpin i` and `Kᵢ = standardC19BoostGenerator i`. -/
def pauliLubanskiX
    (energy py pz : ℝ) (z : Cell4) : Cell4 :=
  fun component =>
    (energy : ℂ) * standardCubeSpin 0 z component -
      (py : ℂ) * standardC19BoostGenerator 2 z component +
      (pz : ℂ) * standardC19BoostGenerator 1 z component

/-- The second spatial component `energy S₁ - pz K₀ + px K₂` of the Pauli–Lubanski operator,
where `Sᵢ = standardCubeSpin i` and `Kᵢ = standardC19BoostGenerator i`. -/
def pauliLubanskiY
    (energy pz px : ℝ) (z : Cell4) : Cell4 :=
  fun component =>
    (energy : ℂ) * standardCubeSpin 1 z component -
      (pz : ℂ) * standardC19BoostGenerator 0 z component +
      (px : ℂ) * standardC19BoostGenerator 2 z component

/-- The third spatial component `energy S₂ - px K₁ + py K₀` of the Pauli–Lubanski operator, where
`Sᵢ = standardCubeSpin i` and `Kᵢ = standardC19BoostGenerator i`. -/
def pauliLubanskiZ
    (energy px py : ℝ) (z : Cell4) : Cell4 :=
  fun component =>
    (energy : ℂ) * standardCubeSpin 2 z component -
      (px : ℂ) * standardC19BoostGenerator 1 z component +
      (py : ℂ) * standardC19BoostGenerator 0 z component

/-- The Minkowski square `W₀² - W₁² - W₂² - W₃²` of the Pauli–Lubanski operator, with components
`pauliLubanskiTime`, `pauliLubanskiX`, `pauliLubanskiY` and `pauliLubanskiZ`. -/
def pauliLubanskiSquare
    (energy px py pz : ℝ) (z : Cell4) : Cell4 :=
  fun component =>
    pauliLubanskiTime px py pz
        (pauliLubanskiTime px py pz z) component -
      pauliLubanskiX energy py pz
        (pauliLubanskiX energy py pz z) component -
      pauliLubanskiY energy pz px
        (pauliLubanskiY energy pz px z) component -
      pauliLubanskiZ energy px py
        (pauliLubanskiZ energy px py z) component

theorem pauli_lubanski_square_is_spin_half
    (energy px py pz : ℝ) (z : Cell4) :
    pauliLubanskiSquare energy px py pz z =
      fun component =>
        ((-(3 : ℝ) / 4 *
          (energy ^ 2 - px ^ 2 - py ^ 2 - pz ^ 2) : ℝ) : ℂ) *
            z component := by
  have hI4 : I ^ 4 = (1 : ℂ) := by
    rw [show I ^ 4 = (I ^ 2) ^ 2 by ring, Complex.I_sq]
    ring
  funext component
  fin_cases component <;>
    simp [pauliLubanskiSquare, pauliLubanskiTime,
      pauliLubanskiX, pauliLubanskiY, pauliLubanskiZ,
      standardC19BoostGenerator, standardCubeSpin,
      standardCubePlaneBivector, standardCubeGamma,
      standardDiracAlphaX, standardDiracAlphaY,
      standardDiracAlphaZ] <;>
    ring_nf
  all_goals rw [hI4, Complex.I_sq]
  all_goals ring

theorem pauli_lubanski_mass_shell_spin_half
    (mass energy px py pz : ℝ) (z : Cell4)
    (hmassShell : energy ^ 2 - px ^ 2 - py ^ 2 - pz ^ 2 = mass ^ 2) :
    pauliLubanskiSquare energy px py pz z =
      fun component => ((-(3 : ℝ) / 4 * mass ^ 2 : ℝ) : ℂ) *
        z component := by
  rw [pauli_lubanski_square_is_spin_half]
  rw [hmassShell]

theorem pauli_lubanski_native_boost_spin_half
    (rapidity : ℝ) (axis : Fin 3) (z : Cell4) :
    pauliLubanskiSquare
        (nativeBoostEnergy rapidity)
        (c19ContinuumSpeed * nativeBoostMomentum rapidity axis 0)
        (c19ContinuumSpeed * nativeBoostMomentum rapidity axis 1)
        (c19ContinuumSpeed * nativeBoostMomentum rapidity axis 2) z =
      fun component =>
        ((-(3 : ℝ) / 4 * chi0 ^ 2 : ℝ) : ℂ) * z component := by
  rw [pauli_lubanski_square_is_spin_half]
  have hm := native_boost_mass_shell rapidity axis
  have hscaled :
      (c19ContinuumSpeed * nativeBoostMomentum rapidity axis 0) ^ 2 +
          (c19ContinuumSpeed * nativeBoostMomentum rapidity axis 1) ^ 2 +
          (c19ContinuumSpeed * nativeBoostMomentum rapidity axis 2) ^ 2 =
        c19ContinuumSpeed ^ 2 *
          continuumMomentumMagnitudeSq
            (nativeBoostMomentum rapidity axis) := by
    unfold continuumMomentumMagnitudeSq
    simp [Fin.sum_univ_succ]
    ring
  have hbracket :
      nativeBoostEnergy rapidity ^ 2 -
          (c19ContinuumSpeed * nativeBoostMomentum rapidity axis 0) ^ 2 -
          (c19ContinuumSpeed * nativeBoostMomentum rapidity axis 1) ^ 2 -
          (c19ContinuumSpeed * nativeBoostMomentum rapidity axis 2) ^ 2 =
        chi0 ^ 2 := by
    nlinarith [hm, hscaled]
  rw [hbracket]

/-- The statement that `pauliLubanskiSquare` acts as the scalar
`-(3 / 4) * (energy ^ 2 - px ^ 2 - py ^ 2 - pz ^ 2)`, equal to `-(3 / 4) * chi0 ^ 2` on the boosted
energy and momentum. -/
structure Dirac027PauliLubanskiCertificate : Prop where
  previousGate : Dirac026FreeLorentzBoostCertificate
  relativisticSpinInvariant : ∀ energy px py pz z,
    pauliLubanskiSquare energy px py pz z =
      fun component =>
        ((-(3 : ℝ) / 4 *
          (energy ^ 2 - px ^ 2 - py ^ 2 - pz ^ 2) : ℝ) : ℂ) *
            z component
  nativeMassShellValue : ∀ rapidity axis z,
    pauliLubanskiSquare
        (nativeBoostEnergy rapidity)
        (c19ContinuumSpeed * nativeBoostMomentum rapidity axis 0)
        (c19ContinuumSpeed * nativeBoostMomentum rapidity axis 1)
        (c19ContinuumSpeed * nativeBoostMomentum rapidity axis 2) z =
      fun component =>
        ((-(3 : ℝ) / 4 * chi0 ^ 2 : ℝ) : ℂ) * z component

theorem dirac027_pauli_lubanski_spin_half :
    Dirac027PauliLubanskiCertificate where
  previousGate := dirac026_free_lorentz_boost
  relativisticSpinInvariant := pauli_lubanski_square_is_spin_half
  nativeMassShellValue := pauli_lubanski_native_boost_spin_half

end
end LeanDirac
