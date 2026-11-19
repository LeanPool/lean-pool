/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

/-
Adapted from gpartin/LeanDiracDerivation, file `LeanDirac/Dirac026.lean`, at commit
867004142ada3eec464d5bd3088d7313fdad1613.
Upstream copyright (c) 2026 G. D. Partin, dual-licensed at the recipient's
option under the MIT License or CC0 1.0 (see the upstream `LICENSE`,
`LICENSE-CC0` and `LICENSING.md`); used here under the MIT License.
-/

module

public import LeanPool.LatticeDiracDerivation.Dirac025

/-!
# DIRAC-026: free Lorentz boosts from the derived transport algebra

This stage stays inside the free continuum sector.  The boost generator is
not supplied as a new matrix: it is the imaginary half of the same cubical
direction operator whose coefficient was derived as the Hamiltonian momentum
response.  We prove the boost part of the Lorentz Lie algebra, construct its
closed rapidity action, boost both positive-rest spin states, and recover the
energy, momentum, current and invariant rest coefficient selected upstream.

No external field, force, action term, coefficient or boost rule is added to
the native lattice dynamics.
-/

@[expose] public section

namespace LeanDirac

noncomputable section
open Complex

/-- The boost generator along `axis` on four-component vectors, `I / 2` times
`standardCubeGamma axis`. -/
def standardC19BoostGenerator (axis : Fin 3) (z : Cell4) : Cell4 :=
  fun component =>
    (I / 2) * standardCubeGamma axis z component

theorem standard_cube_gamma_square (axis : Fin 3) (z : Cell4) :
    standardCubeGamma axis (standardCubeGamma axis z) = z := by
  funext component
  fin_cases axis <;> fin_cases component <;>
    simp [standardCubeGamma, standardDiracAlphaX,
      standardDiracAlphaY, standardDiracAlphaZ] <;>
    ring_nf <;> rw [Complex.I_sq] <;> ring

theorem standard_cube_gamma_beta_anticommute
    (axis : Fin 3) (z : Cell4) :
    standardCubeGamma axis (standardDiracBeta z) =
      fun component =>
        -standardDiracBeta (standardCubeGamma axis z) component := by
  funext component
  fin_cases axis <;> fin_cases component <;>
    simp [standardCubeGamma, standardDiracBeta,
      standardDiracAlphaX, standardDiracAlphaY,
      standardDiracAlphaZ]

theorem standard_dirac_beta_gamma_anticommute
    (axis : Fin 3) (z : Cell4) :
    standardDiracBeta (standardCubeGamma axis z) =
      fun component =>
        -standardCubeGamma axis (standardDiracBeta z) component := by
  funext component
  fin_cases axis <;> fin_cases component <;>
    simp [standardCubeGamma, standardDiracBeta,
      standardDiracAlphaX, standardDiracAlphaY,
      standardDiracAlphaZ]

theorem standard_cube_gamma_linear_combination
    (axis : Fin 3) (a b : ℂ) (z w : Cell4) :
    standardCubeGamma axis
        (fun component => a * z component + b * w component) =
      fun component =>
        a * standardCubeGamma axis z component +
          b * standardCubeGamma axis w component := by
  funext component
  fin_cases axis <;> fin_cases component <;>
    simp [standardCubeGamma, standardDiracAlphaX,
      standardDiracAlphaY, standardDiracAlphaZ] <;> ring

theorem standard_dirac_beta_linear_combination
    (a b : ℂ) (z w : Cell4) :
    standardDiracBeta
        (fun component => a * z component + b * w component) =
      fun component =>
        a * standardDiracBeta z component +
          b * standardDiracBeta w component := by
  funext component
  fin_cases component <;> simp [standardDiracBeta] <;> ring

theorem boost_commutator_01 (z : Cell4) :
    (fun component =>
      standardC19BoostGenerator 0
          (standardC19BoostGenerator 1 z) component -
        standardC19BoostGenerator 1
          (standardC19BoostGenerator 0 z) component) =
      fun component => -I * standardCubeSpin 2 z component := by
  funext component
  fin_cases component <;>
    simp [standardC19BoostGenerator, standardCubeSpin,
      standardCubePlaneBivector, standardCubeGamma,
      standardDiracAlphaY, standardDiracAlphaZ] <;>
    ring_nf

theorem boost_commutator_12 (z : Cell4) :
    (fun component =>
      standardC19BoostGenerator 1
          (standardC19BoostGenerator 2 z) component -
        standardC19BoostGenerator 2
          (standardC19BoostGenerator 1 z) component) =
      fun component => -I * standardCubeSpin 0 z component := by
  funext component
  fin_cases component <;>
    simp [standardC19BoostGenerator, standardCubeSpin,
      standardCubePlaneBivector, standardCubeGamma,
      standardDiracAlphaX, standardDiracAlphaY] <;>
    ring_nf

theorem boost_commutator_20 (z : Cell4) :
    (fun component =>
      standardC19BoostGenerator 2
          (standardC19BoostGenerator 0 z) component -
        standardC19BoostGenerator 0
          (standardC19BoostGenerator 2 z) component) =
      fun component => -I * standardCubeSpin 1 z component := by
  funext component
  fin_cases component <;>
    simp [standardC19BoostGenerator, standardCubeSpin,
      standardCubePlaneBivector, standardCubeGamma,
      standardDiracAlphaX, standardDiracAlphaZ] <;>
    ring_nf

theorem rotation_boost_commutator_01 (z : Cell4) :
    (fun component =>
      standardCubeSpin 0 (standardC19BoostGenerator 1 z) component -
        standardC19BoostGenerator 1 (standardCubeSpin 0 z) component) =
      fun component => I * standardC19BoostGenerator 2 z component := by
  have hI4 : I ^ 4 = (1 : ℂ) := by
    rw [show I ^ 4 = (I ^ 2) ^ 2 by ring, Complex.I_sq]
    ring
  funext component
  fin_cases component <;>
    simp [standardC19BoostGenerator, standardCubeSpin,
      standardCubePlaneBivector, standardCubeGamma,
      standardDiracAlphaX, standardDiracAlphaY] <;>
    ring_nf
  all_goals rw [hI4, Complex.I_sq]
  all_goals ring

theorem rotation_boost_commutator_12 (z : Cell4) :
    (fun component =>
      standardCubeSpin 1 (standardC19BoostGenerator 2 z) component -
        standardC19BoostGenerator 2 (standardCubeSpin 1 z) component) =
      fun component => I * standardC19BoostGenerator 0 z component := by
  funext component
  fin_cases component <;>
    simp [standardC19BoostGenerator, standardCubeSpin,
      standardCubePlaneBivector, standardCubeGamma,
      standardDiracAlphaX, standardDiracAlphaZ] <;>
    ring_nf

theorem rotation_boost_commutator_20 (z : Cell4) :
    (fun component =>
      standardCubeSpin 2 (standardC19BoostGenerator 0 z) component -
        standardC19BoostGenerator 0 (standardCubeSpin 2 z) component) =
      fun component => I * standardC19BoostGenerator 1 z component := by
  funext component
  fin_cases component <;>
    simp [standardC19BoostGenerator, standardCubeSpin,
      standardCubePlaneBivector, standardCubeGamma,
      standardDiracAlphaY, standardDiracAlphaZ] <;>
    ring_nf

/-- The real number `cosh (rapidity / 2)`, viewed as a complex number. -/
def boostCoshHalf (rapidity : ℝ) : ℂ :=
  ⟨Real.cosh (rapidity / 2), 0⟩

/-- The real number `sinh (rapidity / 2)`, viewed as a complex number. -/
def boostSinhHalf (rapidity : ℝ) : ℂ :=
  ⟨Real.sinh (rapidity / 2), 0⟩

/-- The boost of rapidity `rapidity` along `axis` on four-component vectors:
`z ↦ cosh (rapidity / 2) • z + sinh (rapidity / 2) • standardCubeGamma axis z`. -/
def standardC19RapidityBoost
    (rapidity : ℝ) (axis : Fin 3) (z : Cell4) : Cell4 :=
  fun component =>
    boostCoshHalf rapidity * z component +
      boostSinhHalf rapidity *
        standardCubeGamma axis z component

theorem standard_c19_rapidity_boost_inverse
    (rapidity : ℝ) (axis : Fin 3) (z : Cell4) :
    standardC19RapidityBoost (-rapidity) axis
        (standardC19RapidityBoost rapidity axis z) = z := by
  have hcoshNeg : Real.cosh (-rapidity / 2) =
      Real.cosh (rapidity / 2) := by
    rw [show -rapidity / 2 = -(rapidity / 2) by ring,
      Real.cosh_neg]
  have hsinhNeg : Real.sinh (-rapidity / 2) =
      -Real.sinh (rapidity / 2) := by
    rw [show -rapidity / 2 = -(rapidity / 2) by ring,
      Real.sinh_neg]
  have hhyper := Real.cosh_sq_sub_sinh_sq (rapidity / 2)
  have hhalf : rapidity * (1 / 2 : ℝ) = rapidity / 2 := by
    ring
  have hcoshHalf : Real.cosh (rapidity * (1 / 2 : ℝ)) =
      Real.cosh (rapidity / 2) := congrArg Real.cosh hhalf
  have hsinhHalf : Real.sinh (rapidity * (1 / 2 : ℝ)) =
      Real.sinh (rapidity / 2) := congrArg Real.sinh hhalf
  unfold standardC19RapidityBoost
  rw [standard_cube_gamma_linear_combination]
  rw [standard_cube_gamma_square]
  funext component
  unfold boostCoshHalf boostSinhHalf
  simp only [hcoshNeg, hsinhNeg]
  apply Complex.ext
  · simp [Complex.mul_re, Complex.mul_im]
    ring_nf
    rw [hcoshHalf, hsinhHalf]
    linear_combination (z component).re * hhyper
  · simp [Complex.mul_re, Complex.mul_im]
    ring_nf
    rw [hcoshHalf, hsinhHalf]
    linear_combination (z component).im * hhyper

/-- The lattice momentum with component `chi0 * sinh rapidity / c19ContinuumSpeed` along `axis`
and zero along the other two axes. -/
def nativeBoostMomentum
    (rapidity : ℝ) (axis : Fin 3) : LatticeMomentum :=
  fun component =>
    if component = axis then
      chi0 * Real.sinh rapidity / c19ContinuumSpeed
    else 0

/-- The energy `chi0 * cosh rapidity`. -/
def nativeBoostEnergy (rapidity : ℝ) : ℝ :=
  chi0 * Real.cosh rapidity

theorem standard_c19_hamiltonian_on_native_boost_momentum
    (rapidity : ℝ) (axis : Fin 3) (z : Cell4) :
    standardC19Hamiltonian (chi0 : ℂ)
        (nativeBoostMomentum rapidity axis) z =
      fun component =>
        (chi0 : ℂ) * standardDiracBeta z component +
          ((chi0 * Real.sinh rapidity : ℝ) : ℂ) *
            standardCubeGamma axis z component := by
  have hspeed : c19ContinuumSpeed ≠ 0 := by
    unfold c19ContinuumSpeed
    positivity
  funext component
  fin_cases axis <;> fin_cases component <;>
    simp [standardC19Hamiltonian, nativeBoostMomentum,
      standardDiracHamiltonian, standardDiracSpatial,
      standardDiracBeta, standardDiracAlphaX,
      standardDiracAlphaY, standardDiracAlphaZ,
      standardCubeGamma] <;>
    field_simp [hspeed] <;> ring_nf <;> simp

/-- The standard basis vector `cell4Basis0` for `spin = 0` and `cell4Basis1` for `spin = 1`; both
are fixed by `standardDiracBeta`. -/
def positiveRestSpinState (spin : Fin 2) : Cell4 :=
  if spin = 0 then cell4Basis0 else cell4Basis1

theorem positive_rest_spin_state_beta
    (spin : Fin 2) :
    standardDiracBeta (positiveRestSpinState spin) =
      positiveRestSpinState spin := by
  fin_cases spin <;>
    funext component <;> fin_cases component <;>
    simp [positiveRestSpinState, cell4Basis0, cell4Basis1,
      standardDiracBeta]

theorem positive_rest_spin_state_density (spin : Fin 2) :
    cell4Density (positiveRestSpinState spin) = 1 := by
  fin_cases spin <;>
    simp [positiveRestSpinState, cell4Basis0, cell4Basis1,
      cell4Density, Complex.normSq, Fin.sum_univ_succ]

theorem boosted_positive_rest_is_energy_eigenstate
    (rapidity : ℝ) (axis : Fin 3) (spin : Fin 2) :
    standardC19Hamiltonian (chi0 : ℂ)
        (nativeBoostMomentum rapidity axis)
        (standardC19RapidityBoost rapidity axis
          (positiveRestSpinState spin)) =
      fun component =>
        (nativeBoostEnergy rapidity : ℂ) *
          standardC19RapidityBoost rapidity axis
            (positiveRestSpinState spin) component := by
  have hc : Real.cosh rapidity =
      Real.cosh (rapidity / 2) ^ 2 +
        Real.sinh (rapidity / 2) ^ 2 := by
    convert Real.cosh_two_mul (rapidity / 2) using 1
    all_goals ring_nf
  have hs : Real.sinh rapidity =
      2 * Real.sinh (rapidity / 2) *
        Real.cosh (rapidity / 2) := by
    convert Real.sinh_two_mul (rapidity / 2) using 1
    all_goals ring_nf
  have hh := Real.cosh_sq_sub_sinh_sq (rapidity / 2)
  have hhalf : rapidity * (1 / 2 : ℝ) = rapidity / 2 := by
    ring
  have hcoshHalf : Real.cosh (rapidity * (1 / 2 : ℝ)) =
      Real.cosh (rapidity / 2) := congrArg Real.cosh hhalf
  have hsinhHalf : Real.sinh (rapidity * (1 / 2 : ℝ)) =
      Real.sinh (rapidity / 2) := congrArg Real.sinh hhalf
  have hfirst :
      Real.cosh (rapidity / 2) +
          Real.sinh rapidity * Real.sinh (rapidity / 2) =
        Real.cosh rapidity * Real.cosh (rapidity / 2) := by
    rw [hc, hs]
    linear_combination -(Real.cosh (rapidity / 2)) * hh
  have hsecond :
      -Real.sinh (rapidity / 2) +
          Real.sinh rapidity * Real.cosh (rapidity / 2) =
        Real.cosh rapidity * Real.sinh (rapidity / 2) := by
    rw [hc, hs]
    linear_combination (Real.sinh (rapidity / 2)) * hh
  have hfirstC :
      ((Real.cosh (rapidity / 2) +
          Real.sinh rapidity * Real.sinh (rapidity / 2) : ℝ) : ℂ) =
        ((Real.cosh rapidity * Real.cosh (rapidity / 2) : ℝ) : ℂ) := by
    exact_mod_cast hfirst
  have hsecondC :
      ((-Real.sinh (rapidity / 2) +
          Real.sinh rapidity * Real.cosh (rapidity / 2) : ℝ) : ℂ) =
        ((Real.cosh rapidity * Real.sinh (rapidity / 2) : ℝ) : ℂ) := by
    exact_mod_cast hsecond
  have hfirstMulC :
      ((Real.cosh (rapidity * (1 / 2 : ℝ)) +
          Real.sinh rapidity * Real.sinh (rapidity * (1 / 2 : ℝ)) : ℝ) : ℂ) =
        ((Real.cosh rapidity * Real.cosh (rapidity * (1 / 2 : ℝ)) : ℝ) : ℂ) := by
    rw [hcoshHalf, hsinhHalf]
    exact hfirstC
  have hsecondMulC :
      ((-Real.sinh (rapidity * (1 / 2 : ℝ)) +
          Real.sinh rapidity * Real.cosh (rapidity * (1 / 2 : ℝ)) : ℝ) : ℂ) =
        ((Real.cosh rapidity * Real.sinh (rapidity * (1 / 2 : ℝ)) : ℝ) : ℂ) := by
    rw [hcoshHalf, hsinhHalf]
    exact hsecondC
  rw [standard_c19_hamiltonian_on_native_boost_momentum]
  unfold standardC19RapidityBoost nativeBoostEnergy
  rw [standard_dirac_beta_linear_combination,
    standard_cube_gamma_linear_combination]
  rw [positive_rest_spin_state_beta spin,
    standard_dirac_beta_gamma_anticommute,
    positive_rest_spin_state_beta spin,
    standard_cube_gamma_square]
  funext component
  unfold boostCoshHalf boostSinhHalf
  change
    (chi0 : ℂ) *
          (((Real.cosh (rapidity / 2) : ℝ) : ℂ) *
              positiveRestSpinState spin component +
            ((Real.sinh (rapidity / 2) : ℝ) : ℂ) *
              -standardCubeGamma axis
                (positiveRestSpinState spin) component) +
        ((chi0 * Real.sinh rapidity : ℝ) : ℂ) *
          (((Real.cosh (rapidity / 2) : ℝ) : ℂ) *
              standardCubeGamma axis
                (positiveRestSpinState spin) component +
            ((Real.sinh (rapidity / 2) : ℝ) : ℂ) *
              positiveRestSpinState spin component) =
      ((chi0 * Real.cosh rapidity : ℝ) : ℂ) *
        (((Real.cosh (rapidity / 2) : ℝ) : ℂ) *
            positiveRestSpinState spin component +
          ((Real.sinh (rapidity / 2) : ℝ) : ℂ) *
            standardCubeGamma axis
              (positiveRestSpinState spin) component)
  calc
    _ = (chi0 : ℂ) *
          (((Real.cosh (rapidity * (1 / 2 : ℝ)) +
              Real.sinh rapidity *
                Real.sinh (rapidity * (1 / 2 : ℝ)) : ℝ) : ℂ)) *
            positiveRestSpinState spin component +
        (chi0 : ℂ) *
          (((-Real.sinh (rapidity * (1 / 2 : ℝ)) +
              Real.sinh rapidity *
                Real.cosh (rapidity * (1 / 2 : ℝ)) : ℝ) : ℂ)) *
            standardCubeGamma axis
              (positiveRestSpinState spin) component := by
          push_cast
          ring_nf
    _ = _ := by
      rw [hfirstMulC, hsecondMulC]
      push_cast
      ring_nf

theorem native_boost_mass_shell (rapidity : ℝ) (axis : Fin 3) :
    nativeBoostEnergy rapidity ^ 2 -
        c19ContinuumSpeed ^ 2 *
          continuumMomentumMagnitudeSq
            (nativeBoostMomentum rapidity axis) =
      chi0 ^ 2 := by
  have hspeed : c19ContinuumSpeed ≠ 0 := by
    unfold c19ContinuumSpeed
    positivity
  have hhyper := Real.cosh_sq_sub_sinh_sq rapidity
  fin_cases axis <;>
    simp [nativeBoostEnergy, nativeBoostMomentum,
      continuumMomentumMagnitudeSq] <;>
    field_simp [hspeed] <;>
    norm_num [chi0] at hhyper ⊢

theorem boosted_positive_rest_density
    (rapidity : ℝ) (axis : Fin 3) (spin : Fin 2) :
    cell4Density
        (standardC19RapidityBoost rapidity axis
          (positiveRestSpinState spin)) =
      Real.cosh rapidity := by
  have hc : Real.cosh rapidity =
      Real.cosh (rapidity / 2) ^ 2 +
        Real.sinh (rapidity / 2) ^ 2 := by
    convert Real.cosh_two_mul (rapidity / 2) using 1
    all_goals ring_nf
  fin_cases axis <;> fin_cases spin <;>
    simp [cell4Density, standardC19RapidityBoost,
      positiveRestSpinState, cell4Basis0, cell4Basis1,
      boostCoshHalf, boostSinhHalf,
      standardCubeGamma, standardDiracAlphaX,
      standardDiracAlphaY, standardDiracAlphaZ,
      Complex.normSq, Fin.sum_univ_succ,
      Complex.mul_re, Complex.mul_im] <;>
    nlinarith

theorem boosted_positive_rest_current
    (rapidity : ℝ) (axis : Fin 3) (spin : Fin 2) :
    standardC19DiracCurrent axis
        (standardC19RapidityBoost rapidity axis
          (positiveRestSpinState spin)) =
      c19ContinuumSpeed * Real.sinh rapidity := by
  have hs : Real.sinh rapidity =
      2 * Real.sinh (rapidity / 2) *
        Real.cosh (rapidity / 2) := by
    convert Real.sinh_two_mul (rapidity / 2) using 1
    all_goals ring_nf
  fin_cases axis <;> fin_cases spin <;>
    simp [standardC19DiracCurrent, cell4RealPair,
      scalarRealPair, standardC19VelocityOperator,
      standardC19RapidityBoost, positiveRestSpinState,
      boostCoshHalf, boostSinhHalf,
      cell4Basis0, cell4Basis1, standardCubeGamma,
      standardDiracAlphaX, standardDiracAlphaY,
      standardDiracAlphaZ, Fin.sum_univ_succ,
      Complex.mul_re, Complex.mul_im] <;>
    ring_nf
  all_goals
    rw [show rapidity * (1 / 2 : ℝ) = rapidity / 2 by ring]
    rw [hs]
    ring

/-- The collected results on boosts: the commutation relations of the boost generators with each
other and with `standardCubeSpin`, invertibility of `standardC19RapidityBoost`, and the boosted
rest states being eigenvectors of `standardC19Hamiltonian` with eigenvalue
`chi0 * cosh rapidity`. -/
structure Dirac026FreeLorentzBoostCertificate : Prop where
  previousGate : Dirac025VelocityClockCertificate
  boostBoostCommutator :
    (∀ z, (fun component =>
      standardC19BoostGenerator 0
          (standardC19BoostGenerator 1 z) component -
        standardC19BoostGenerator 1
          (standardC19BoostGenerator 0 z) component) =
      fun component => -I * standardCubeSpin 2 z component) ∧
    (∀ z, (fun component =>
      standardC19BoostGenerator 1
          (standardC19BoostGenerator 2 z) component -
        standardC19BoostGenerator 2
          (standardC19BoostGenerator 1 z) component) =
      fun component => -I * standardCubeSpin 0 z component) ∧
    (∀ z, (fun component =>
      standardC19BoostGenerator 2
          (standardC19BoostGenerator 0 z) component -
        standardC19BoostGenerator 0
          (standardC19BoostGenerator 2 z) component) =
      fun component => -I * standardCubeSpin 1 z component)
  rotationBoostCommutator :
    (∀ z, (fun component =>
      standardCubeSpin 0 (standardC19BoostGenerator 1 z) component -
        standardC19BoostGenerator 1 (standardCubeSpin 0 z) component) =
      fun component => I * standardC19BoostGenerator 2 z component) ∧
    (∀ z, (fun component =>
      standardCubeSpin 1 (standardC19BoostGenerator 2 z) component -
        standardC19BoostGenerator 2 (standardCubeSpin 1 z) component) =
      fun component => I * standardC19BoostGenerator 0 z component) ∧
    (∀ z, (fun component =>
      standardCubeSpin 2 (standardC19BoostGenerator 0 z) component -
        standardC19BoostGenerator 0 (standardCubeSpin 2 z) component) =
      fun component => I * standardC19BoostGenerator 1 z component)
  rapidityBoostIsInvertible : ∀ rapidity axis z,
    standardC19RapidityBoost (-rapidity) axis
        (standardC19RapidityBoost rapidity axis z) = z
  boostedRestStatesSolveDirac : ∀ rapidity axis spin,
    standardC19Hamiltonian (chi0 : ℂ)
        (nativeBoostMomentum rapidity axis)
        (standardC19RapidityBoost rapidity axis
          (positiveRestSpinState spin)) =
      fun component =>
        (nativeBoostEnergy rapidity : ℂ) *
          standardC19RapidityBoost rapidity axis
            (positiveRestSpinState spin) component
  invariantRestCoefficient : ∀ rapidity axis,
    nativeBoostEnergy rapidity ^ 2 -
        c19ContinuumSpeed ^ 2 *
          continuumMomentumMagnitudeSq
            (nativeBoostMomentum rapidity axis) = chi0 ^ 2
  boostedDensityAndCurrent : ∀ rapidity axis spin,
    cell4Density
        (standardC19RapidityBoost rapidity axis
          (positiveRestSpinState spin)) = Real.cosh rapidity ∧
    standardC19DiracCurrent axis
        (standardC19RapidityBoost rapidity axis
          (positiveRestSpinState spin)) =
      c19ContinuumSpeed * Real.sinh rapidity

theorem dirac026_free_lorentz_boost :
    Dirac026FreeLorentzBoostCertificate where
  previousGate := dirac025_velocity_variance_clock_identity
  boostBoostCommutator :=
    ⟨boost_commutator_01, boost_commutator_12, boost_commutator_20⟩
  rotationBoostCommutator :=
    ⟨rotation_boost_commutator_01,
      rotation_boost_commutator_12,
      rotation_boost_commutator_20⟩
  rapidityBoostIsInvertible := standard_c19_rapidity_boost_inverse
  boostedRestStatesSolveDirac := boosted_positive_rest_is_energy_eigenstate
  invariantRestCoefficient := native_boost_mass_shell
  boostedDensityAndCurrent := fun rapidity axis spin =>
    ⟨boosted_positive_rest_density rapidity axis spin,
      boosted_positive_rest_current rapidity axis spin⟩

end
end LeanDirac
