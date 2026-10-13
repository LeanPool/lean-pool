/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.LawCarrier
public import LeanPool.HighContrastHomogenization.Support.Book.Ch04.Theorems.WidetildeTheta
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.MultiscaleEllipticity.Representatives
public import LeanPool.HighContrastHomogenization.Support.Deterministic.CoarsePoincare.Setup.UniformBounds

/-!
# P4Bounds

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Samplewise coarse-ellipticity bounds for the genuine cutoff

The actual cutoff has deterministic lower coercivity `nu`, but its upper
ellipticity is a local random envelope.  This module records the exact bridge
from that envelope to CoarseGraining's Chapter 4 upper coarse observable.  It
does not replace the random upper envelope by `nu` or assert `(P4)` prematurely.
-/

namespace Algsuperdiff.Section3.Cutoff

open Filter MeasureTheory Set
open HCPolySupport HCPolySupport.Book
open scoped BigOperators

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
/-- The Chapter 4 field is locally a.e.-elliptic on every genuine cutoff
sample, with the cube-wise sample-dependent upper envelope from
`CoefficientFamily`. -/
theorem coefficientCutoff_aelocallyUniformlyElliptic (M : ABKModel d) (m : ℤ)
    (omega : CutoffSample d) :
    Ch04.AELocallyUniformlyEllipticField (coefficientCutoff M.nu m omega) :=
  coefficientCutoff_aeLocallyUniformlyEllipticField M m omega

omit [NeZero d] in
/-- The canonical CoarseGraining coefficient family and the literal cutoff family
have the same representatives on every cube. -/
theorem coefficientCutoff_canonicalFamily_aeeq (M : ABKModel d) (m : ℤ)
    (omega : CutoffSample d) :
    Ch02.TriadicCoeffFamily.AEEq
      (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField
        (coefficientCutoff M.nu m omega)
        (coefficientCutoff_aelocallyUniformlyElliptic M m omega))
      (coefficientCutoffTriadicCoeffFamily M m omega) := by
  intro Q
  change coefficientCutoff M.nu m omega =ᵐ[volumeMeasureOn (Ch02.cubeDomain Q : Set (Vec d))]
    coefficientCutoff M.nu m omega
  exact Filter.EventuallyEq.rfl

/-- A descendant upper-block maximum is controlled by the upper ellipticity
envelope of its root cube.  The envelope is the genuine random one. -/
theorem maxDescendantBMatrixNormAtScale_le_cutoffEnvelope
    (M : ABKModel d) (m : ℤ) (omega : CutoffSample d)
    (Q : TriadicCube d) (n : ℕ) :
    Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ))
      (coefficientCutoffTriadicCoeffFamily M m omega) ≤
      4 * (d : ℝ) * M.nu⁻¹ *
        (coefficientCutoffCubeEllipticityUpper M m omega Q) ^ 2 := by
  let F : Ch02.TriadicCoeffFamily d := coefficientCutoffTriadicCoeffFamily M m omega
  let A : CoeffField d := Internal.Ch02.BookCh02.pointwiseCoeffField
    (Ch02.cubeDomain Q) (F.coeffOn Q)
  have hk : Q.scale - (n : ℤ) ≤ Q.scale := by
    exact sub_le_self _ (by exact_mod_cast Nat.zero_le n)
  have hEll : IsEllipticFieldOn M.nu
      (coefficientCutoffCubeEllipticityUpper M m omega Q) (openCubeSet Q) A := by
    simpa [A, F, coefficientCutoffTriadicCoeffFamily, coefficientCutoffCoeffOn] using
      Internal.Ch02.BookCh02.pointwiseCoeffField_isEllipticFieldOn
        (Ch02.cubeDomain Q) (F.coeffOn Q)
  have hData : OpenCubeDescendantDeterministicCoarseData Q A := by
    simpa [A] using Ch02.pointwiseCoeffField_openCube_descendant_data Q (F.coeffOn Q)
  calc
    Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) F ≤
      HCPolySupport.maxDescendantBBlockNormAtScale Q (Q.scale - (n : ℤ)) A := by
        exact Ch02.maxDescendantBMatrixNormAtScale_le_maxDescendantBBlockNormAtScale F Q hk
    _ ≤ 4 * (d : ℝ) * M.nu⁻¹ *
        (coefficientCutoffCubeEllipticityUpper M m omega Q) ^ 2 := by
      simpa [A] using
        HCPolySupport.maxDescendantBBlockNorm_le_uniform_of_ellipticField_openCubeSet
          Q A hEll hData n

/-- The ambient Chapter 4 descendant observable agrees with the literal
cutoff family, and hence inherits the same root-cube envelope bound. -/
theorem maxDescendantBMatrixNormCoeffFieldAtScale_le_cutoffEnvelope
    (M : ABKModel d) (m : ℤ) (omega : CutoffSample d)
    (Q : TriadicCube d) (n : ℕ) :
    Ch04.maxDescendantBMatrixNormCoeffFieldAtScale
      Q (Q.scale - (n : ℤ)) (coefficientCutoff M.nu m omega) ≤
      4 * (d : ℝ) * M.nu⁻¹ *
        (coefficientCutoffCubeEllipticityUpper M m omega Q) ^ 2 := by
  let hlocal : Ch04.AELocallyUniformlyEllipticField
      (coefficientCutoff M.nu m omega) := coefficientCutoff_aelocallyUniformlyElliptic M m omega
  let F : Ch02.TriadicCoeffFamily d := coefficientCutoffTriadicCoeffFamily M m omega
  have hAEEq :
      (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField
        (coefficientCutoff M.nu m omega) hlocal).AEEq F := by
    simpa [F, hlocal] using coefficientCutoff_canonicalFamily_aeeq M m omega
  have hEq :
      Ch04.maxDescendantBMatrixNormCoeffFieldAtScale
          Q (Q.scale - (n : ℤ)) (coefficientCutoff M.nu m omega) =
        Ch02.maxDescendantBMatrixNormAtScale Q (Q.scale - (n : ℤ)) F := by
    simp [Ch04.maxDescendantBMatrixNormCoeffFieldAtScale, hlocal, F,
      Ch02.maxDescendantBMatrixNormAtScale_eq_ofAEEq hAEEq]
  rw [hEq]
  exact maxDescendantBMatrixNormAtScale_le_cutoffEnvelope M m omega Q n

/-- The lower inverse descendant maximum uses only the literal coercivity
`nu`; the sample-dependent upper envelope plays no role in this bound. -/
theorem maxDescendantSigmaStarInvMatrixNormAtScale_le_cutoffCoercivity
    (M : ABKModel d) (m : ℤ) (omega : CutoffSample d)
    (Q : TriadicCube d) (n : ℕ) :
    Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ))
      (coefficientCutoffTriadicCoeffFamily M m omega) ≤
      4 * (d : ℝ) * M.nu⁻¹ := by
  let F : Ch02.TriadicCoeffFamily d := coefficientCutoffTriadicCoeffFamily M m omega
  let A : CoeffField d := Internal.Ch02.BookCh02.pointwiseCoeffField
    (Ch02.cubeDomain Q) (F.coeffOn Q)
  have hk : Q.scale - (n : ℤ) ≤ Q.scale := by
    exact sub_le_self _ (by exact_mod_cast Nat.zero_le n)
  have hEll : IsEllipticFieldOn M.nu
      (coefficientCutoffCubeEllipticityUpper M m omega Q) (openCubeSet Q) A := by
    simpa [A, F, coefficientCutoffTriadicCoeffFamily, coefficientCutoffCoeffOn] using
      Internal.Ch02.BookCh02.pointwiseCoeffField_isEllipticFieldOn
        (Ch02.cubeDomain Q) (F.coeffOn Q)
  have hData : OpenCubeDescendantDeterministicCoarseData Q A := by
    simpa [A] using Ch02.pointwiseCoeffField_openCube_descendant_data Q (F.coeffOn Q)
  calc
    Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) F ≤
      HCPolySupport.maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (n : ℤ)) A := by
        exact
          Ch02.maxDescendantSigmaStarInvMatrixNormAtScale_le_maxDescendantSigmaStarInvNormAtScale
          F Q hk
    _ ≤ 4 * (d : ℝ) * M.nu⁻¹ := by
      simpa [A] using
        HCPolySupport.maxDescendantSigmaStarInvNorm_le_uniform_of_ellipticField_openCubeSet
          Q A hEll hData n

/-- Ambient Chapter 4 form of the deterministic lower inverse descendant
bound. -/
theorem maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale_le_cutoffCoercivity
    (M : ABKModel d) (m : ℤ) (omega : CutoffSample d)
    (Q : TriadicCube d) (n : ℕ) :
    Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale
      Q (Q.scale - (n : ℤ)) (coefficientCutoff M.nu m omega) ≤
      4 * (d : ℝ) * M.nu⁻¹ := by
  let hlocal : Ch04.AELocallyUniformlyEllipticField
      (coefficientCutoff M.nu m omega) := coefficientCutoff_aelocallyUniformlyElliptic M m omega
  let F : Ch02.TriadicCoeffFamily d := coefficientCutoffTriadicCoeffFamily M m omega
  have hAEEq :
      (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField
        (coefficientCutoff M.nu m omega) hlocal).AEEq F := by
    simpa [F, hlocal] using coefficientCutoff_canonicalFamily_aeeq M m omega
  have hEq :
      Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale
          Q (Q.scale - (n : ℤ)) (coefficientCutoff M.nu m omega) =
        Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) F := by
    simp [Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale, hlocal, F,
      Ch02.maxDescendantSigmaStarInvMatrixNormAtScale_eq_ofAEEq hAEEq]
  rw [hEq]
  exact maxDescendantSigmaStarInvMatrixNormAtScale_le_cutoffCoercivity M m omega Q n

private theorem tsum_geometricWeight_one_mul_le_const
    {H : ℕ → ℝ} {s C : ℝ} (hs : 0 < s)
    (hH_nonneg : ∀ n : ℕ, 0 ≤ H n)
    (hH_le : ∀ n : ℕ, H n ≤ C) :
    (∑' n : ℕ, Ch02.geometricWeight s 1 n * H n) ≤ C := by
  have hs1 : 0 < s * (1 : ℝ) := by simpa using hs
  have hsumH : Summable (fun n : ℕ => Ch02.geometricWeight s 1 n * H n) :=
    HCPolySupport.summable_geometricWeight_mul_of_nonneg_of_le
      (s := s) (q := 1) (C := C) hs1 hH_nonneg hH_le
  have hsumC : Summable (fun n : ℕ => Ch02.geometricWeight s 1 n * C) :=
    (HCPolySupport.summable_geometricWeight (s := s) (q := 1) hs1).mul_right C
  have hterm : ∀ n : ℕ, Ch02.geometricWeight s 1 n * H n ≤
      Ch02.geometricWeight s 1 n * C := by
    intro n
    exact mul_le_mul_of_nonneg_left (hH_le n)
      (HCPolySupport.geometricWeight_nonneg n hs1.le)
  calc
    (∑' n : ℕ, Ch02.geometricWeight s 1 n * H n) ≤
        ∑' n : ℕ, Ch02.geometricWeight s 1 n * C :=
      Summable.tsum_le_tsum hterm hsumH hsumC
    _ = C := by
      rw [tsum_mul_right]
      have hweight : (∑' n : ℕ, Ch02.geometricWeight s 1 n) = 1 := by
        simpa [Ch02.geometricWeight_eq_old] using
          (HCPolySupport.tsum_geometricWeight_eq_one hs1)
      rw [hweight, one_mul]

/-- Exact samplewise upper bound for CoarseGraining's `Λ_{s,1}` observable.  This
is the bridge that permits the `Γ₂` moments of the local cutoff control to feed
the upper `(P4)` moment; it retains the random local upper constant. -/
theorem LambdaSqCoeffField_le_cutoffEnvelope
    (M : ABKModel d) (m : ℤ) (omega : CutoffSample d)
    (Q : TriadicCube d) {s : ℝ} (hs : 0 < s) :
    Ch04.LambdaSqCoeffField Q s (.finite 1) (coefficientCutoff M.nu m omega) ≤
      4 * (d : ℝ) * M.nu⁻¹ *
        (coefficientCutoffCubeEllipticityUpper M m omega Q) ^ 2 := by
  let C : ℝ := 4 * (d : ℝ) * M.nu⁻¹ *
    (coefficientCutoffCubeEllipticityUpper M m omega Q) ^ 2
  have hnonneg : ∀ n : ℕ, 0 ≤
      Ch04.maxDescendantBMatrixNormCoeffFieldAtScale
        Q (Q.scale - (n : ℤ)) (coefficientCutoff M.nu m omega) := by
    intro n
    let hlocal : Ch04.AELocallyUniformlyEllipticField
        (coefficientCutoff M.nu m omega) := coefficientCutoff_aelocallyUniformlyElliptic M m omega
    let F : Ch02.TriadicCoeffFamily d := coefficientCutoffTriadicCoeffFamily M m omega
    have hAEEq :
        (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField
          (coefficientCutoff M.nu m omega) hlocal).AEEq F := by
      simpa [F, hlocal] using coefficientCutoff_canonicalFamily_aeeq M m omega
    rw [Ch04.maxDescendantBMatrixNormCoeffFieldAtScale, dite_eq_left hlocal]
    rw [Ch02.maxDescendantBMatrixNormAtScale_eq_ofAEEq hAEEq]
    exact Ch02.maxDescendantBMatrixNormAtScale_nonneg Q
      (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) F
  have hbound : ∀ n : ℕ,
      Ch04.maxDescendantBMatrixNormCoeffFieldAtScale
        Q (Q.scale - (n : ℤ)) (coefficientCutoff M.nu m omega) ≤ C := by
    intro n
    exact maxDescendantBMatrixNormCoeffFieldAtScale_le_cutoffEnvelope M m omega Q n
  calc
    Ch04.LambdaSqCoeffField Q s (.finite 1) (coefficientCutoff M.nu m omega) ≤
      ∑' n : ℕ, Ch02.geometricWeight s 1 n *
        Ch04.maxDescendantBMatrixNormCoeffFieldAtScale
          Q (Q.scale - (n : ℤ)) (coefficientCutoff M.nu m omega) :=
      Ch04.LambdaSqCoeffField_finite_one_le_tsum_weighted_maxDescendantBMatrixNormAtScale
        Q (coefficientCutoff M.nu m omega) hs
    _ ≤ C := tsum_geometricWeight_one_mul_le_const hs hnonneg hbound

/-- Exact samplewise lower `(P4)` bound: the inverse lower coarse observable is
uniformly controlled by the molecular coercivity `nu`. -/
theorem lambdaSqCoeffField_inv_le_cutoffCoercivity
    (M : ABKModel d) (m : ℤ) (omega : CutoffSample d)
    (Q : TriadicCube d) {s : ℝ} (hs : 0 < s) :
    (Ch04.lambdaSqCoeffField Q s (.finite 1) (coefficientCutoff M.nu m omega))⁻¹ ≤
      4 * (d : ℝ) * M.nu⁻¹ := by
  let C : ℝ := 4 * (d : ℝ) * M.nu⁻¹
  have hnonneg : ∀ n : ℕ, 0 ≤
      Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale
        Q (Q.scale - (n : ℤ)) (coefficientCutoff M.nu m omega) := by
    intro n
    let hlocal : Ch04.AELocallyUniformlyEllipticField
        (coefficientCutoff M.nu m omega) := coefficientCutoff_aelocallyUniformlyElliptic M m omega
    let F : Ch02.TriadicCoeffFamily d := coefficientCutoffTriadicCoeffFamily M m omega
    have hAEEq :
        (Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField
          (coefficientCutoff M.nu m omega) hlocal).AEEq F := by
      simpa [F, hlocal] using coefficientCutoff_canonicalFamily_aeeq M m omega
    rw [Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale, dite_eq_left hlocal]
    rw [Ch02.maxDescendantSigmaStarInvMatrixNormAtScale_eq_ofAEEq hAEEq]
    exact Ch02.maxDescendantSigmaStarInvMatrixNormAtScale_nonneg Q
      (sub_le_self _ (by exact_mod_cast Nat.zero_le n)) F
  have hbound : ∀ n : ℕ,
      Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale
        Q (Q.scale - (n : ℤ)) (coefficientCutoff M.nu m omega) ≤ C := by
    intro n
    exact maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale_le_cutoffCoercivity
      M m omega Q n
  calc
    (Ch04.lambdaSqCoeffField Q s (.finite 1) (coefficientCutoff M.nu m omega))⁻¹ ≤
      ∑' n : ℕ, Ch02.geometricWeight s 1 n *
        Ch04.maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale
          Q (Q.scale - (n : ℤ)) (coefficientCutoff M.nu m omega) :=
      Ch04.lambdaSqCoeffField_finite_one_inv_le_tsum_weighted_maxDescendantSigmaStarInvMatrixNormAtScale
        Q (coefficientCutoff M.nu m omega) hs
    _ ≤ C := tsum_geometricWeight_one_mul_le_const hs hnonneg hbound

end

end Algsuperdiff.Section3.Cutoff
