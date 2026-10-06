/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.C1FiniteFixedBaseDecay
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.C1CanonicalPmProvider

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Corrector.C1CanonicalProjectionExactness

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Exactness of the canonical finite-corrector projection

The coefficient-weighted least-squares selector minimizes the same local
quadratic form that defines the finite affine excess.  When its harmonic
target is the restriction of a cube solution, it therefore realizes that
excess exactly.
-/

namespace HCPolySupport
namespace HighContrast
namespace Root

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- Squaring a finite-affine residual norm gives its real normalized
coefficient energy. -/
theorem residualWeightedNorm_sq_eq_ofReal_energy
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    {q m : ℕ} (hqm : q ≤ m)
    (u : Book.Ch03.CubeSolution (originCube d (m : ℤ)) a) (b : Vec d) :
    weightedGradNorm
        (a.coeffOn (originCube d (q : ℤ))).toCoeffField
        (openCubeSet (originCube d (q : ℤ)))
        (fun x ↦ u.toH1.grad x -
          (finiteAffineSolution a (m : ℤ) b).toH1.grad x) ^ 2 =
      ENNReal.ofReal (normalizedLocalSymmetricEnergy
        (Book.Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet
          (originCube d (q : ℤ)) a)
        ((finiteAffineGradientResidual a
          (show (q : ℤ) ≤ (m : ℤ) by exact_mod_cast hqm) u b).toH1.gradToHilbertVectorL2)) := by
  let r := finiteAffineGradientResidual a
    (show (q : ℤ) ≤ (m : ℤ) by exact_mod_cast hqm) u b
  let hEll := Book.Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet
    (originCube d (q : ℤ)) a
  have hraw := ofReal_normalizedLocalSymmetricEnergy_eq_weightedGradNorm_sq
    hEll r.toH1.grad_memVectorL2
  rw [weightedGradNorm_congr_coeff_ae_on _
    (Book.Ch03.publicCoeffField_ae_eq_openCubeSet
      (originCube d (q : ℤ)) a).symm]
  rw [← finiteAffineGradientResidual_grad a
    (show (q : ℤ) ≤ (m : ℤ) by exact_mod_cast hqm) u b]
  exact hraw.symm

/-- If the harmonic target map agrees with the restriction of a cube
solution, the canonical weighted projection realizes its finite affine
gradient excess. -/
theorem finiteCorrectorWeightedProjection_spec_of_target
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (hCauchy : FiniteAffineCorrectionLocalCauchy a)
    {q m : ℕ} (hqm : q ≤ m)
    (hT : Function.Injective (finiteTrialHarmonicGradientLinearMap a hqm))
    (e : Vec d)
    (u : Book.Ch03.CubeSolution (originCube d (m : ℤ)) a)
    (hJ : ((jointTargetHarmonicGradientLinearMap a hCauchy q) e :
        LocalGradientL2 d q) =
      (finiteCubeSolutionRestriction a
        (show (q : ℤ) ≤ (m : ℤ) by exact_mod_cast hqm) u).toH1.gradToHilbertVectorL2) :
    weightedGradNorm
        (a.coeffOn (originCube d (q : ℤ))).toCoeffField
        (openCubeSet (originCube d (q : ℤ)))
        (fun x ↦ u.toH1.grad x -
          (finiteAffineSolution a (m : ℤ)
            (finiteCorrectorWeightedProjection a hCauchy hqm hT e)).toH1.grad x) =
      finiteAffineGradientExcess a (q : ℤ) (m : ℤ) u := by
  let P := finiteCorrectorWeightedProjection a hCauchy hqm hT
  let T := finiteTrialHarmonicGradientLinearMap a hqm
  let J := jointTargetHarmonicGradientLinearMap a hCauchy q
  let B := AHarmonicGradientHilbert.symmCoeffBilin
    (PotentialSolenoidalL2Data.ofSubmoduleClosures (localGradientCube d q))
    (Book.Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet
      (originCube d (q : ℤ)) a)
  have hproj := finiteCorrectorWeightedProjection_minimizes
    a hCauchy hqm hT e
  have hbest : ∀ b : Vec d,
      weightedGradNorm
          (a.coeffOn (originCube d (q : ℤ))).toCoeffField
          (openCubeSet (originCube d (q : ℤ)))
          (fun x ↦ u.toH1.grad x -
            (finiteAffineSolution a (m : ℤ) (P e)).toH1.grad x) ≤
        weightedGradNorm
          (a.coeffOn (originCube d (q : ℤ))).toCoeffField
          (openCubeSet (originCube d (q : ℤ)))
          (fun x ↦ u.toH1.grad x -
            (finiteAffineSolution a (m : ℤ) b).toH1.grad x) := by
    intro b
    have hquad := hproj b
    dsimp only at hquad
    have hbilin : B (J e - T (P e)) (J e - T (P e)) ≤
        B (J e - T b) (J e - T b) := by
      unfold quadraticEnergy at hquad
      dsimp only [B, J, T, P]
      linarith only [hquad]
    let hEll := Book.Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet
      (originCube d (q : ℤ)) a
    have henergy : normalizedLocalSymmetricEnergy hEll
          ((J e - T (P e) : _ ) : LocalGradientL2 d q) ≤
        normalizedLocalSymmetricEnergy hEll
          ((J e - T b : _) : LocalGradientL2 d q) := by
      unfold normalizedLocalSymmetricEnergy
      exact mul_le_mul_of_nonneg_left hbilin
        (inv_nonneg.mpr ENNReal.toReal_nonneg)
    have hresP := finiteTrialGradientResidual_eq a hqm u (P e)
    have hresb := finiteTrialGradientResidual_eq a hqm u b
    have hJP : ((J e - T (P e) : _) : LocalGradientL2 d q) =
        (finiteAffineGradientResidual a
          (show (q : ℤ) ≤ (m : ℤ) by exact_mod_cast hqm) u
          (P e)).toH1.gradToHilbertVectorL2 := by
      change ((J e : _) : LocalGradientL2 d q) -
          ((T (P e) : _) : LocalGradientL2 d q) = _
      rw [hJ]
      exact hresP
    have hJb : ((J e - T b : _) : LocalGradientL2 d q) =
        (finiteAffineGradientResidual a
          (show (q : ℤ) ≤ (m : ℤ) by exact_mod_cast hqm) u b).toH1.gradToHilbertVectorL2 := by
      change ((J e : _) : LocalGradientL2 d q) -
          ((T b : _) : LocalGradientL2 d q) = _
      rw [hJ]
      exact hresb
    rw [hJP, hJb] at henergy
    have hsquares : weightedGradNorm
          (a.coeffOn (originCube d (q : ℤ))).toCoeffField
          (openCubeSet (originCube d (q : ℤ)))
          (fun x ↦ u.toH1.grad x -
            (finiteAffineSolution a (m : ℤ) (P e)).toH1.grad x) ^ 2 ≤
        weightedGradNorm
          (a.coeffOn (originCube d (q : ℤ))).toCoeffField
          (openCubeSet (originCube d (q : ℤ)))
          (fun x ↦ u.toH1.grad x -
            (finiteAffineSolution a (m : ℤ) b).toH1.grad x) ^ 2 := by
      rw [residualWeightedNorm_sq_eq_ofReal_energy a hqm u (P e),
        residualWeightedNorm_sq_eq_ofReal_energy a hqm u b]
      exact ENNReal.ofReal_le_ofReal henergy
    exact (ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 2)).mp (by
      simpa only [ENNReal.rpow_two] using hsquares)
  apply le_antisymm
  · change _ ≤ ⨅ b : Vec d, weightedGradNorm _ _ _
    exact le_iInf hbest
  · exact finiteAffineGradientExcess_le a (q : ℤ) (m : ℤ) u (P e)

/-- Under the same target identification, the canonical projection is the
proof-irrelevant exact affine-excess minimizer. -/
theorem finiteCorrectorWeightedProjection_eq_exactMinimizer_of_target
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (hCauchy : FiniteAffineCorrectionLocalCauchy a)
    {q m : ℕ} (hqm : q ≤ m)
    (hT : Function.Injective (finiteTrialHarmonicGradientLinearMap a hqm))
    (e : Vec d)
    (u : Book.Ch03.CubeSolution (originCube d (m : ℤ)) a)
    (hJ : ((jointTargetHarmonicGradientLinearMap a hCauchy q) e :
        LocalGradientL2 d q) =
      (finiteCubeSolutionRestriction a
        (show (q : ℤ) ≤ (m : ℤ) by exact_mod_cast hqm) u).toH1.gradToHilbertVectorL2) :
    finiteCorrectorWeightedProjection a hCauchy hqm hT e =
      finiteAffineExactMinimizer a
        (show (q : ℤ) ≤ (m : ℤ) by exact_mod_cast hqm) u := by
  let P := finiteCorrectorWeightedProjection a hCauchy hqm hT
  let bExact := finiteAffineExactMinimizer a
    (show (q : ℤ) ≤ (m : ℤ) by exact_mod_cast hqm) u
  have hP := finiteCorrectorWeightedProjection_spec_of_target
    a hCauchy hqm hT e u hJ
  have hE := finiteAffineExactMinimizer_spec a
    (show (q : ℤ) ≤ (m : ℤ) by exact_mod_cast hqm) u
  have hnorm : weightedGradNorm
        (a.coeffOn (originCube d (q : ℤ))).toCoeffField
        (openCubeSet (originCube d (q : ℤ)))
        (fun x ↦ u.toH1.grad x -
          (finiteAffineSolution a (m : ℤ) (P e)).toH1.grad x) =
      weightedGradNorm
        (a.coeffOn (originCube d (q : ℤ))).toCoeffField
        (openCubeSet (originCube d (q : ℤ)))
        (fun x ↦ u.toH1.grad x -
          (finiteAffineSolution a (m : ℤ) bExact).toH1.grad x) := by
    rw [hP, hE]
  have hsquares := congrArg (fun z : ℝ≥0∞ ↦ z ^ 2) hnorm
  change weightedGradNorm
        (a.coeffOn (originCube d (q : ℤ))).toCoeffField
        (openCubeSet (originCube d (q : ℤ)))
        (fun x ↦ u.toH1.grad x -
          (finiteAffineSolution a (m : ℤ) (P e)).toH1.grad x) ^ 2 =
      weightedGradNorm
        (a.coeffOn (originCube d (q : ℤ))).toCoeffField
        (openCubeSet (originCube d (q : ℤ)))
        (fun x ↦ u.toH1.grad x -
          (finiteAffineSolution a (m : ℤ) bExact).toH1.grad x) ^ 2 at hsquares
  rw [residualWeightedNorm_sq_eq_ofReal_energy a hqm u (P e),
    residualWeightedNorm_sq_eq_ofReal_energy a hqm u bExact] at hsquares
  let hEll := Book.Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet
    (originCube d (q : ℤ)) a
  have henergy : normalizedLocalSymmetricEnergy hEll
        (finiteAffineGradientResidual a
          (show (q : ℤ) ≤ (m : ℤ) by exact_mod_cast hqm) u
          (P e)).toH1.gradToHilbertVectorL2 =
      normalizedLocalSymmetricEnergy hEll
        (finiteAffineGradientResidual a
          (show (q : ℤ) ≤ (m : ℤ) by exact_mod_cast hqm) u
          bExact).toH1.gradToHilbertVectorL2 := by
    exact (ENNReal.ofReal_eq_ofReal_iff
      (normalizedLocalSymmetricEnergy_nonneg hEll _)
      (normalizedLocalSymmetricEnergy_nonneg hEll _)).mp hsquares
  let T := finiteTrialHarmonicGradientLinearMap a hqm
  let H := AHarmonicGradientHilbert.Space
    (PotentialSolenoidalL2Data.ofSubmoduleClosures (localGradientCube d q))
    (Book.Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet
      (originCube d (q : ℤ)) a)
  let hclosed : IsClosed (LinearMap.range T : Set H) := by
    let _ : FiniteDimensional ℝ (LinearMap.range T) := T.finiteDimensional_range
    exact (LinearMap.range T).closed_of_finiteDimensional
  let B := AHarmonicGradientHilbert.symmCoeffBilin
    (PotentialSolenoidalL2Data.ofSubmoduleClosures (localGradientCube d q)) hEll
  let hB := AHarmonicGradientHilbert.isCoercive_symmCoeffBilin
    (M := PotentialSolenoidalL2Data.ofSubmoduleClosures (localGradientCube d q))
    (Book.Ch02.openCubeSet_nonempty (originCube d (q : ℤ))) hEll
  let J := LinearMap.toContinuousLinearMap
    (jointTargetHarmonicGradientLinearMap a hCauchy q)
  have hresP : ((J e - T (P e) : H) : LocalGradientL2 d q) =
      (finiteAffineGradientResidual a
        (show (q : ℤ) ≤ (m : ℤ) by exact_mod_cast hqm) u
        (P e)).toH1.gradToHilbertVectorL2 := by
    change ((jointTargetHarmonicGradientLinearMap a hCauchy q e : _) :
        LocalGradientL2 d q) - ((T (P e) : H) : LocalGradientL2 d q) = _
    rw [hJ]
    exact finiteTrialGradientResidual_eq a hqm u (P e)
  have hresE : ((J e - T bExact : H) : LocalGradientL2 d q) =
      (finiteAffineGradientResidual a
        (show (q : ℤ) ≤ (m : ℤ) by exact_mod_cast hqm) u
        bExact).toH1.gradToHilbertVectorL2 := by
    change ((jointTargetHarmonicGradientLinearMap a hCauchy q e : _) :
        LocalGradientL2 d q) - ((T bExact : H) : LocalGradientL2 d q) = _
    rw [hJ]
    exact finiteTrialGradientResidual_eq a hqm u bExact
  have hvol : 0 < (volume (openCubeSet (originCube d (q : ℤ)))).toReal :=
    volume_openCubeSet_originCube_toReal_pos (d := d) (q : ℤ)
  have hbilin : B (J e - T bExact) (J e - T bExact) ≤
      B (J e - T (P e)) (J e - T (P e)) := by
    have henergy' := henergy.symm.le
    rw [← hresE, ← hresP] at henergy'
    unfold normalizedLocalSymmetricEnergy at henergy'
    dsimp only [B]
    have hinv : 0 < (volume (openCubeSet (originCube d (q : ℤ)))).toReal⁻¹ :=
      inv_pos.mpr hvol
    have hzb := AHarmonicGradientHilbert.symmCoeffBilin_apply
      (M := PotentialSolenoidalL2Data.ofSubmoduleClosures (localGradientCube d q))
      (hEll := hEll) (J e - T bExact) (J e - T bExact)
    have hzp := AHarmonicGradientHilbert.symmCoeffBilin_apply
      (M := PotentialSolenoidalL2Data.ofSubmoduleClosures (localGradientCube d q))
      (hEll := hEll) (J e - T (P e)) (J e - T (P e))
    rw [hzb, hzp]
    exact le_of_mul_le_mul_left henergy' hinv
  have hquad : quadraticEnergy B (J e - T bExact) ≤
      quadraticEnergy B (J e - T (P e)) := by
    unfold quadraticEnergy
    exact mul_le_mul_of_nonneg_left hbilin (by norm_num)
  have heq := eq_weightedLeastSquaresSlopeMap_of_quadraticEnergy_le
    T hT hclosed hB
    (fun x y ↦ AHarmonicGradientHilbert.symmCoeffBilin_symm x y)
    J e bExact hquad
  change P e = bExact
  symm
  simpa only [P, finiteCorrectorWeightedProjection, T, H, hclosed, B, hB, J]
    using heq

end

end Root
end HighContrast
end HCPolySupport
