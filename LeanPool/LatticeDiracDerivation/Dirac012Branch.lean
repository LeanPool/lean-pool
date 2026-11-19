/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

/-
Adapted from gpartin/LeanDiracDerivation, file `LeanDirac/Dirac012Branch.lean`, at commit
867004142ada3eec464d5bd3088d7313fdad1613.
Upstream copyright (c) 2026 G. D. Partin, dual-licensed at the recipient's
option under the MIT License or CC0 1.0 (see the upstream `LICENSE`,
`LICENSE-CC0` and `LICENSING.md`); used here under the MIT License.
-/

module

public import LeanPool.LatticeDiracDerivation.Dirac012

/-!
# DIRAC-012 centered-recurrence branch bridge

This module closes the second gap identified by independent review.  The old
DIRAC-012 bound inserted a continuum exponential mode into the centered
recurrence.  Here the one-step first-order branch is instead derived from the
characteristic equation of that recurrence itself.

For the continuum C19 quadratic symbol, the branch solves the centered
recurrence exactly.  Replacing the continuum symbol by the exact native C19
symbol leaves exactly the already-derived spatial remainder.  The branch
generator then approaches the same four-component Dirac Hamiltonian, with its
two timestep coefficients displayed explicitly.
-/

@[expose] public section

namespace LeanDirac

noncomputable section
open Complex Filter Topology

def continuumModeSquare (momentum : LatticeMomentum) : ℝ :=
  chi0 ^ 2 + c19QuadraticSymbol momentum

def continuumModeFrequency (momentum : LatticeMomentum) : ℝ :=
  Real.sqrt (continuumModeSquare momentum)

theorem continuum_mode_square_positive (momentum : LatticeMomentum) :
    0 < continuumModeSquare momentum := by
  unfold continuumModeSquare c19QuadraticSymbol chi0
  positivity

theorem continuum_mode_frequency_positive (momentum : LatticeMomentum) :
    0 < continuumModeFrequency momentum := by
  exact Real.sqrt_pos.2 (continuum_mode_square_positive momentum)

theorem continuum_mode_frequency_square (momentum : LatticeMomentum) :
    continuumModeFrequency momentum ^ 2 = continuumModeSquare momentum := by
  exact Real.sq_sqrt (le_of_lt (continuum_mode_square_positive momentum))

def recurrenceBranchCos (dt frequency : ℝ) : ℝ :=
  1 - (dt * frequency) ^ 2 / 2

def recurrenceBranchRadical (dt frequency : ℝ) : ℝ :=
  Real.sqrt (1 - (dt * frequency) ^ 2 / 4)

def recurrenceBranchSin (dt frequency : ℝ) : ℝ :=
  dt * frequency * recurrenceBranchRadical dt frequency

theorem recurrence_branch_radical_square
    (dt frequency : ℝ) (hstable : (dt * frequency) ^ 2 ≤ 4) :
    recurrenceBranchRadical dt frequency ^ 2 =
      1 - (dt * frequency) ^ 2 / 4 := by
  unfold recurrenceBranchRadical
  rw [Real.sq_sqrt]
  nlinarith

theorem recurrence_branch_circle
    (dt frequency : ℝ) (hstable : (dt * frequency) ^ 2 ≤ 4) :
    recurrenceBranchCos dt frequency ^ 2 +
        recurrenceBranchSin dt frequency ^ 2 = 1 := by
  rw [show recurrenceBranchSin dt frequency ^ 2 =
      (dt * frequency) ^ 2 * recurrenceBranchRadical dt frequency ^ 2 by
        unfold recurrenceBranchSin
        ring]
  rw [recurrence_branch_radical_square dt frequency hstable]
  unfold recurrenceBranchCos
  ring

def cell4LinearCombination
    (a b : ℂ) (z w : Cell4) : Cell4 :=
  fun component => a * z component + b * w component

theorem standard_c19_hamiltonian_linear_combination
    (mass : ℂ) (momentum : LatticeMomentum)
    (a b : ℂ) (z w : Cell4) :
    standardC19Hamiltonian mass momentum
        (cell4LinearCombination a b z w) =
      cell4LinearCombination a b
        (standardC19Hamiltonian mass momentum z)
        (standardC19Hamiltonian mass momentum w) := by
  funext component
  fin_cases component <;>
    simp [standardC19Hamiltonian, standardDiracHamiltonian,
      standardDiracSpatial, standardDiracBeta, standardDiracAlphaX,
      standardDiracAlphaY, standardDiracAlphaZ,
      cell4LinearCombination] <;> ring

def recurrenceDiracBranchStep
    (dt : ℝ) (momentum : LatticeMomentum) (z : Cell4) : Cell4 :=
  let frequency := continuumModeFrequency momentum
  let cosine := recurrenceBranchCos dt frequency
  let sine := recurrenceBranchSin dt frequency
  cell4LinearCombination (cosine : ℂ)
    (-Complex.I * (sine / frequency : ℝ)) z
    (standardC19Hamiltonian (chi0 : ℂ) momentum z)

theorem standard_c19_hamiltonian_square_is_frequency_square
    (momentum : LatticeMomentum) (z : Cell4) :
    standardC19Hamiltonian (chi0 : ℂ) momentum
        (standardC19Hamiltonian (chi0 : ℂ) momentum z) =
      fun component =>
        (continuumModeFrequency momentum ^ 2 : ℝ) * z component := by
  rw [standard_c19_hamiltonian_square_is_continuum_dispersion]
  funext component
  rw [continuum_mode_frequency_square]
  rfl

theorem recurrence_dirac_branch_solves_continuum_centered_recurrence
    (dt : ℝ) (momentum : LatticeMomentum) (z : Cell4)
    (hstable : (dt * continuumModeFrequency momentum) ^ 2 ≤ 4) :
    recurrenceDiracBranchStep dt momentum
        (recurrenceDiracBranchStep dt momentum z) =
      fun component =>
        2 * recurrenceDiracBranchStep dt momentum z component - z component -
          ((dt ^ 2 * continuumModeSquare momentum : ℝ) : ℂ) *
            recurrenceDiracBranchStep dt momentum z component := by
  let frequency := continuumModeFrequency momentum
  let cosine := recurrenceBranchCos dt frequency
  let sine := recurrenceBranchSin dt frequency
  let hamiltonian := standardC19Hamiltonian (chi0 : ℂ) momentum
  have hfrequency : frequency ≠ 0 :=
    ne_of_gt (continuum_mode_frequency_positive momentum)
  have hcircle : cosine ^ 2 + sine ^ 2 = 1 := by
    exact recurrence_branch_circle dt frequency hstable
  have hsquare : hamiltonian (hamiltonian z) =
      fun component => (frequency ^ 2 : ℝ) * z component := by
    exact standard_c19_hamiltonian_square_is_frequency_square momentum z
  have hlinear := standard_c19_hamiltonian_linear_combination
    (chi0 : ℂ) momentum (cosine : ℂ)
      (-Complex.I * (sine / frequency : ℝ)) z (hamiltonian z)
  have htwice : recurrenceDiracBranchStep dt momentum
        (recurrenceDiracBranchStep dt momentum z) =
      fun component =>
        ((cosine ^ 2 - sine ^ 2 : ℝ) : ℂ) * z component -
          2 * Complex.I * ((cosine * sine / frequency : ℝ) : ℂ) *
            hamiltonian z component := by
    change cell4LinearCombination (cosine : ℂ)
        (-Complex.I * (sine / frequency : ℝ))
        (cell4LinearCombination (cosine : ℂ)
          (-Complex.I * (sine / frequency : ℝ)) z (hamiltonian z))
        (hamiltonian
          (cell4LinearCombination (cosine : ℂ)
            (-Complex.I * (sine / frequency : ℝ)) z
            (hamiltonian z))) = _
    dsimp only [hamiltonian] at hlinear hsquare ⊢
    rw [hlinear, hsquare]
    funext component
    simp only [cell4LinearCombination]
    push_cast
    field_simp [hfrequency]
    ring_nf
    rw [Complex.I_sq]
    ring
  have hposition : cosine ^ 2 - sine ^ 2 =
      2 * cosine - 1 - dt ^ 2 * frequency ^ 2 * cosine := by
    have hsine : sine ^ 2 = 1 - cosine ^ 2 := by nlinarith [hcircle]
    rw [hsine]
    dsimp only [cosine]
    unfold recurrenceBranchCos
    ring
  have hvelocity : -2 * cosine * (sine / frequency) =
      -2 * (sine / frequency) +
        dt ^ 2 * frequency ^ 2 * (sine / frequency) := by
    dsimp only [cosine]
    unfold recurrenceBranchCos
    field_simp [hfrequency]
    ring
  have hfrequencySquare : frequency ^ 2 = continuumModeSquare momentum :=
    continuum_mode_frequency_square momentum
  rw [htwice]
  change (fun component =>
      ((cosine ^ 2 - sine ^ 2 : ℝ) : ℂ) * z component -
        2 * Complex.I * ((cosine * sine / frequency : ℝ) : ℂ) *
          hamiltonian z component) = _
  funext component
  simp only [recurrenceDiracBranchStep, cell4LinearCombination]
  dsimp only [frequency, cosine, sine, hamiltonian] at hposition hvelocity
  dsimp only [frequency, cosine, sine, hamiltonian]
  push_cast
  have hpositionC :
      (recurrenceBranchCos dt (continuumModeFrequency momentum) : ℂ) ^ 2 -
          (recurrenceBranchSin dt (continuumModeFrequency momentum) : ℂ) ^ 2 =
        2 * (recurrenceBranchCos dt (continuumModeFrequency momentum) : ℂ) - 1 -
          (dt : ℂ) ^ 2 *
            (continuumModeFrequency momentum : ℂ) ^ 2 *
            (recurrenceBranchCos dt (continuumModeFrequency momentum) : ℂ) := by
    exact_mod_cast hposition
  have hvelocityC :
      -2 * (recurrenceBranchCos dt (continuumModeFrequency momentum) : ℂ) *
          ((recurrenceBranchSin dt (continuumModeFrequency momentum) : ℂ) /
            (continuumModeFrequency momentum : ℂ)) =
        -2 * ((recurrenceBranchSin dt (continuumModeFrequency momentum) : ℂ) /
            (continuumModeFrequency momentum : ℂ)) +
          (dt : ℂ) ^ 2 * (continuumModeFrequency momentum : ℂ) ^ 2 *
            ((recurrenceBranchSin dt (continuumModeFrequency momentum) : ℂ) /
              (continuumModeFrequency momentum : ℂ)) := by
    exact_mod_cast hvelocity
  have hfrequencySquareC :
      (continuumModeFrequency momentum : ℂ) ^ 2 =
        (continuumModeSquare momentum : ℂ) := by
    exact_mod_cast hfrequencySquare
  rw [← hfrequencySquareC]
  linear_combination
    (z component) * hpositionC +
      (Complex.I * standardC19Hamiltonian (chi0 : ℂ) momentum z component) *
        hvelocityC

def nativeBranchRecurrenceDefect
    (dt : ℝ) (momentum : LatticeMomentum) (z : Cell4) : Cell4 :=
  fun component =>
    recurrenceDiracBranchStep dt momentum
        (recurrenceDiracBranchStep dt momentum z) component -
      2 * recurrenceDiracBranchStep dt momentum z component + z component +
      ((dt ^ 2 * nativePsiTangentSymbol momentum : ℝ) : ℂ) *
        recurrenceDiracBranchStep dt momentum z component

/-!
This is the native recurrence-to-Dirac evolution identity.  The time-discrete
branch was obtained from the recurrence, so no temporal trial-mode error is
inserted.  Its complete defect in the exact C19 recurrence is precisely the
finite-spacing C19 remainder.
-/
theorem native_branch_defect_is_spatial_remainder
    (dt : ℝ) (momentum : LatticeMomentum) (z : Cell4)
    (hstable : (dt * continuumModeFrequency momentum) ^ 2 ≤ 4) :
    nativeBranchRecurrenceDefect dt momentum z =
      fun component =>
        ((dt ^ 2 * c19SpatialRemainder momentum : ℝ) : ℂ) *
          recurrenceDiracBranchStep dt momentum z component := by
  have hrecurrence :=
    recurrence_dirac_branch_solves_continuum_centered_recurrence
      dt momentum z hstable
  funext component
  have hc := congrFun hrecurrence component
  unfold nativeBranchRecurrenceDefect
  rw [hc]
  rw [native_psi_tangent_symbol_is_exact_scalar_coefficient]
  unfold continuumModeSquare
  push_cast
  ring

def recurrenceBranchGeneratorDefect
    (dt : ℝ) (momentum : LatticeMomentum) (z : Cell4) : Cell4 :=
  fun component =>
    (recurrenceDiracBranchStep dt momentum z component - z component) /
        (dt : ℂ) +
      Complex.I * standardC19Hamiltonian (chi0 : ℂ) momentum z component

theorem recurrence_branch_generator_defect_exact
    (dt : ℝ) (momentum : LatticeMomentum) (z : Cell4)
    (hdt : dt ≠ 0) :
    recurrenceBranchGeneratorDefect dt momentum z =
      fun component =>
        (-(dt * continuumModeFrequency momentum ^ 2) / 2 : ℝ) *
            z component +
          Complex.I *
            (1 - recurrenceBranchRadical dt
              (continuumModeFrequency momentum) : ℝ) *
            standardC19Hamiltonian (chi0 : ℂ) momentum z component := by
  have hfrequency : continuumModeFrequency momentum ≠ 0 :=
    ne_of_gt (continuum_mode_frequency_positive momentum)
  funext component
  unfold recurrenceBranchGeneratorDefect recurrenceDiracBranchStep
    recurrenceBranchCos recurrenceBranchSin cell4LinearCombination
  push_cast
  field_simp [hdt, hfrequency]
  ring

theorem recurrence_branch_radical_tends_to_one (frequency : ℝ) :
    Tendsto (fun dt : ℝ => recurrenceBranchRadical dt frequency)
      (nhds 0) (nhds 1) := by
  have h : ContinuousAt
      (fun dt : ℝ => recurrenceBranchRadical dt frequency) 0 := by
    unfold recurrenceBranchRadical
    fun_prop
  change Tendsto (fun dt : ℝ => recurrenceBranchRadical dt frequency)
    (nhds 0) (nhds (recurrenceBranchRadical 0 frequency)) at h
  simpa [recurrenceBranchRadical] using h

theorem recurrence_branch_generator_coefficients_vanish
    (frequency : ℝ) :
    Tendsto
      (fun dt : ℝ =>
        (-(dt * frequency ^ 2) / 2,
          1 - recurrenceBranchRadical dt frequency))
      (nhds 0) (nhds (0, 0)) := by
  have hfirstContinuous : ContinuousAt
      (fun dt : ℝ => -(dt * frequency ^ 2) / 2) 0 := by fun_prop
  have hfirst : Tendsto (fun dt : ℝ => -(dt * frequency ^ 2) / 2)
      (nhds 0) (nhds 0) := by
    change Tendsto (fun dt : ℝ => -(dt * frequency ^ 2) / 2)
      (nhds 0) (nhds (-(0 * frequency ^ 2) / 2)) at hfirstContinuous
    simpa using hfirstContinuous
  have hsecond : Tendsto
      (fun dt : ℝ => 1 - recurrenceBranchRadical dt frequency)
      (nhds 0) (nhds 0) := by
    have hsecondContinuous : ContinuousAt
        (fun dt : ℝ => 1 - recurrenceBranchRadical dt frequency) 0 := by
      unfold recurrenceBranchRadical
      fun_prop
    change Tendsto
      (fun dt : ℝ => 1 - recurrenceBranchRadical dt frequency)
      (nhds 0) (nhds (1 - recurrenceBranchRadical 0 frequency))
      at hsecondContinuous
    simpa [recurrenceBranchRadical] using hsecondContinuous
  exact hfirst.prodMk_nhds hsecond

/-!
The coefficient limit above is useful bookkeeping, but the publication claim
needs the operator statement itself: on the nonzero-timestep domain where the
difference quotient is defined, the recurrence-derived four-component branch
has the Dirac Hamiltonian as its infinitesimal generator.
-/
theorem recurrence_branch_generator_defect_tends_to_zero
    (momentum : LatticeMomentum) (z : Cell4) (component : Fin 4) :
    Tendsto
      (fun dt : ℝ =>
        recurrenceBranchGeneratorDefect dt momentum z component)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
  let extension : ℝ → ℂ := fun dt =>
    ((-(dt * continuumModeFrequency momentum ^ 2) / 2 : ℝ) : ℂ) *
        z component +
      Complex.I *
        ((1 - recurrenceBranchRadical dt
          (continuumModeFrequency momentum) : ℝ) : ℂ) *
        standardC19Hamiltonian (chi0 : ℂ) momentum z component
  have hcontinuous : ContinuousAt extension 0 := by
    dsimp only [extension]
    unfold recurrenceBranchRadical
    fun_prop
  have hlimit : Tendsto extension (nhds 0) (nhds 0) := by
    have h := hcontinuous.tendsto
    change Tendsto extension (nhds 0) (nhds (extension 0)) at h
    simpa [extension, recurrenceBranchRadical] using h
  have hwithin :
      Tendsto extension (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) :=
    hlimit.mono_left inf_le_left
  apply hwithin.congr'
  filter_upwards [self_mem_nhdsWithin] with dt hdt
  have hne : dt ≠ 0 := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hdt
  have hexact := congrFun
    (recurrence_branch_generator_defect_exact dt momentum z hne) component
  simpa only [extension] using hexact.symm

structure Dirac012RecurrenceBranchCertificate : Prop where
  frequencyPositive : ∀ momentum, 0 < continuumModeFrequency momentum
  frequencySquare : ∀ momentum,
    continuumModeFrequency momentum ^ 2 = continuumModeSquare momentum
  exactContinuumBranch : ∀ dt momentum z,
    (dt * continuumModeFrequency momentum) ^ 2 ≤ 4 →
    recurrenceDiracBranchStep dt momentum
        (recurrenceDiracBranchStep dt momentum z) =
      fun component =>
        2 * recurrenceDiracBranchStep dt momentum z component - z component -
          ((dt ^ 2 * continuumModeSquare momentum : ℝ) : ℂ) *
            recurrenceDiracBranchStep dt momentum z component
  nativeDefect : ∀ dt momentum z,
    (dt * continuumModeFrequency momentum) ^ 2 ≤ 4 →
    nativeBranchRecurrenceDefect dt momentum z =
      fun component =>
        ((dt ^ 2 * c19SpatialRemainder momentum : ℝ) : ℂ) *
          recurrenceDiracBranchStep dt momentum z component
  generatorDefect : ∀ dt momentum z, dt ≠ 0 →
    recurrenceBranchGeneratorDefect dt momentum z =
      fun component =>
        (-(dt * continuumModeFrequency momentum ^ 2) / 2 : ℝ) *
            z component +
          Complex.I *
            (1 - recurrenceBranchRadical dt
              (continuumModeFrequency momentum) : ℝ) *
            standardC19Hamiltonian (chi0 : ℂ) momentum z component
  generatorCoefficientsVanish : ∀ frequency,
    Tendsto
      (fun dt : ℝ =>
        (-(dt * frequency ^ 2) / 2,
          1 - recurrenceBranchRadical dt frequency))
      (nhds 0) (nhds (0, 0))
  generatorTendsToDirac : ∀ momentum z component,
    Tendsto
      (fun dt : ℝ =>
        recurrenceBranchGeneratorDefect dt momentum z component)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0)

theorem dirac012_native_recurrence_branch :
    Dirac012RecurrenceBranchCertificate where
  frequencyPositive := continuum_mode_frequency_positive
  frequencySquare := continuum_mode_frequency_square
  exactContinuumBranch :=
    recurrence_dirac_branch_solves_continuum_centered_recurrence
  nativeDefect := native_branch_defect_is_spatial_remainder
  generatorDefect := recurrence_branch_generator_defect_exact
  generatorCoefficientsVanish :=
    recurrence_branch_generator_coefficients_vanish
  generatorTendsToDirac :=
    recurrence_branch_generator_defect_tends_to_zero

/-! The repaired DIRAC-012 gate retains the independently useful scalar-mode
bound from the original gate, but no longer asks that bound to establish the
first-order evolution.  The second field is the native-recurrence bridge that
does that work. -/
structure Dirac012CompleteCertificate : Prop where
  scalarModeControl : Dirac012Certificate
  recurrenceBranch : Dirac012RecurrenceBranchCertificate

theorem dirac012_complete_centered_recurrence_evolution :
    Dirac012CompleteCertificate where
  scalarModeControl := dirac012_controlled_continuum_evolution
  recurrenceBranch := dirac012_native_recurrence_branch

end
end LeanDirac
