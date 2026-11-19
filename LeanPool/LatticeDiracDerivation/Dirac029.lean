/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

/-
Adapted from gpartin/LeanDiracDerivation, file `LeanDirac/Dirac029.lean`, at commit
867004142ada3eec464d5bd3088d7313fdad1613.
Upstream copyright (c) 2026 G. D. Partin, dual-licensed at the recipient's
option under the MIT License or CC0 1.0 (see the upstream `LICENSE`,
`LICENSE-CC0` and `LICENSING.md`); used here under the MIT License.
-/

module

public import LeanPool.LatticeDiracDerivation.Dirac028

/-!
# DIRAC-029: free charge-conjugation / antiparticle structure

The anti-linear map in this file is assembled from the mass grading,
the y-transport generator and complex conjugation already present in the
derived four-component sector.  We prove its involution, density preservation
and exact intertwining of the positive- and negative-frequency free
Hamiltonians.  Electric charge and an interacting positron remain outside
this free theorem.
-/

@[expose] public section

namespace LeanDirac

noncomputable section
open Complex

def cell4Conjugate (z : Cell4) : Cell4 :=
  fun component => starRingEnd ℂ (z component)

def standardChargeConjugation (z : Cell4) : Cell4 :=
  fun component =>
    I * standardDiracBeta
      (standardDiracAlphaY (cell4Conjugate z)) component

def negateLatticeMomentum (momentum : LatticeMomentum) : LatticeMomentum :=
  fun axis => -momentum axis

theorem standard_charge_conjugation_involution (z : Cell4) :
    standardChargeConjugation (standardChargeConjugation z) = z := by
  have hI4 : I ^ 4 = (1 : ℂ) := by
    rw [show I ^ 4 = (I ^ 2) ^ 2 by ring, Complex.I_sq]
    ring
  funext component
  fin_cases component <;>
    simp [standardChargeConjugation, cell4Conjugate,
      standardDiracBeta, standardDiracAlphaY] <;>
    ring_nf
  all_goals rw [hI4]
  all_goals ring

theorem standard_charge_conjugation_antilinear
    (a b : ℂ) (z w : Cell4) :
    standardChargeConjugation
        (fun component => a * z component + b * w component) =
      fun component =>
        starRingEnd ℂ a * standardChargeConjugation z component +
          starRingEnd ℂ b * standardChargeConjugation w component := by
  funext component
  fin_cases component <;>
    simp [standardChargeConjugation, cell4Conjugate,
      standardDiracBeta, standardDiracAlphaY] <;>
    ring

theorem standard_charge_conjugation_preserves_density (z : Cell4) :
    cell4Density (standardChargeConjugation z) = cell4Density z := by
  simp [cell4Density, standardChargeConjugation, cell4Conjugate,
    standardDiracBeta, standardDiracAlphaY, Fin.sum_univ_succ,
    Complex.normSq, Complex.mul_re, Complex.mul_im]
  ring

theorem standard_charge_conjugation_dirac_hamiltonian
    (mass px py pz : ℝ) (z : Cell4) :
    standardDiracHamiltonian (mass : ℂ)
        (-px : ℂ) (-py : ℂ) (-pz : ℂ)
        (standardChargeConjugation z) =
      fun component =>
        -standardChargeConjugation
          (standardDiracHamiltonian (mass : ℂ)
            (px : ℂ) (py : ℂ) (pz : ℂ) z) component := by
  funext component
  fin_cases component <;>
    simp [standardDiracHamiltonian, standardDiracSpatial,
      standardChargeConjugation, cell4Conjugate,
      standardDiracBeta, standardDiracAlphaX,
      standardDiracAlphaY, standardDiracAlphaZ] <;>
    ring_nf

theorem standard_charge_conjugation_c19_hamiltonian
    (mass : ℝ) (momentum : LatticeMomentum) (z : Cell4) :
    standardC19Hamiltonian (mass : ℂ)
        (negateLatticeMomentum momentum)
        (standardChargeConjugation z) =
      fun component =>
        -standardChargeConjugation
          (standardC19Hamiltonian (mass : ℂ) momentum z) component := by
  unfold standardC19Hamiltonian negateLatticeMomentum
  simpa using standard_charge_conjugation_dirac_hamiltonian mass
    (-c19ContinuumSpeed * momentum 2)
    (-c19ContinuumSpeed * momentum 1)
    (c19ContinuumSpeed * momentum 0) z

theorem charge_conjugate_of_positive_frequency_is_negative
    (mass energy : ℝ) (momentum : LatticeMomentum) (z : Cell4)
    (hpositive : standardC19Hamiltonian (mass : ℂ) momentum z =
      fun component => (energy : ℂ) * z component) :
    standardC19Hamiltonian (mass : ℂ)
        (negateLatticeMomentum momentum)
        (standardChargeConjugation z) =
      fun component => (-energy : ℂ) *
        standardChargeConjugation z component := by
  rw [standard_charge_conjugation_c19_hamiltonian, hpositive]
  funext component
  fin_cases component <;>
    simp [standardChargeConjugation, cell4Conjugate,
      standardDiracBeta, standardDiracAlphaY] <;>
    ring

theorem charge_conjugate_minus_copy_remains_a_minus_copy (z : Cell4) :
    cubeFlavor (cubeEmbedMinus (standardChargeConjugation z)) =
      fun corner => -cubeEmbedMinus (standardChargeConjugation z) corner :=
  cube_embed_minus_has_negative_flavor (standardChargeConjugation z)

theorem charge_conjugate_plus_copy_remains_a_plus_copy (z : Cell4) :
    cubeFlavor (cubeEmbedPlus (standardChargeConjugation z)) =
      cubeEmbedPlus (standardChargeConjugation z) :=
  cube_embed_plus_has_positive_flavor (standardChargeConjugation z)

structure Dirac029ChargeConjugationCertificate : Prop where
  previousGate : Dirac028WignerThomasCertificate
  involution : ∀ z, standardChargeConjugation
    (standardChargeConjugation z) = z
  preservesDensity : ∀ z,
    cell4Density (standardChargeConjugation z) = cell4Density z
  interchangesFrequencyBranches :
    ∀ (mass energy : ℝ) (momentum : LatticeMomentum) (z : Cell4),
    standardC19Hamiltonian (mass : ℂ) momentum z =
        (fun component => (energy : ℂ) * z component) →
      standardC19Hamiltonian (mass : ℂ)
          (negateLatticeMomentum momentum)
          (standardChargeConjugation z) =
        fun component => (-energy : ℂ) *
          standardChargeConjugation z component
  bothCubeCopiesCarryTheMap : ∀ z,
    cubeFlavor (cubeEmbedMinus (standardChargeConjugation z)) =
        (fun corner => -cubeEmbedMinus
          (standardChargeConjugation z) corner) ∧
      cubeFlavor (cubeEmbedPlus (standardChargeConjugation z)) =
        cubeEmbedPlus (standardChargeConjugation z)

theorem dirac029_free_charge_conjugation :
    Dirac029ChargeConjugationCertificate where
  previousGate := dirac028_wigner_thomas_half_factor
  involution := standard_charge_conjugation_involution
  preservesDensity := standard_charge_conjugation_preserves_density
  interchangesFrequencyBranches :=
    charge_conjugate_of_positive_frequency_is_negative
  bothCubeCopiesCarryTheMap := fun z =>
    ⟨charge_conjugate_minus_copy_remains_a_minus_copy z,
      charge_conjugate_plus_copy_remains_a_plus_copy z⟩

end
end LeanDirac
