/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Analytic.AffineFractionalNorm
public import LeanPool.HighContrastHomogenization.Analytic.AffineH10
public import LeanPool.HighContrastHomogenization.Provider.Regularity.AffineGradientQuotientInverse
public import LeanPool.HighContrastHomogenization.Provider.Regularity.AffinePullbackCoeffSpaceEquiv
public import LeanPool.HighContrastHomogenization.Provider.Regularity.RoundedReferenceConstantMatrix
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CubeVolume
public import LeanPool.HighContrastHomogenization.Support.Deterministic.ConstantCoefficientDirichletBesov.CenteredCubeHsRegularity

/-!
# High-contrast homogenization: Provider.Regularity.RoundedPhysicalDirichletAffineResponse

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Quotient-first physical rounded Dirichlet response

The rounded reference-cube response is pushed to the physical adapted cube by
the inverse rounded map.  The weak right-hand side and the constant reference
coefficient are transported together, while the gradient is identified on the
Hilbert `L²` quotient before any representative is used downstream.  The
Euclidean fractional distortion is recorded in one named affine factor.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory Set
open scoped ENNReal Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ} {m : ℤ}

/-- The physical adapted cube selected by the source's rounded map. -/
@[expose]
def roundedPhysicalCube (abar : Mat d) (m : ℤ) : Set (Vec d) :=
  matImage (baseRoundedGrid (symmPart abar))
    (openCubeSet (originCube d m))

/-- The scalar-normalized physical symmetric reference whose rounded
pullback is `roundedReferenceMatrix`. -/
@[expose]
def roundedPhysicalReferenceMatrix (abar : Mat d) : Mat d :=
  specBound ((symmPart abar)⁻¹) • symmPart abar

/-- Contravariant transport of a reference-cube divergence datum to the
physical rounded cube. -/
@[expose]
def roundedPhysicalDirichletDatum (abar : Mat d)
    (h : CenteredCubeEuclideanL2Field d m) : Vec d → Vec d :=
  fun x ↦ matVecMul (baseRoundedGrid (symmPart abar))
    (h (matVecMul (baseRoundedGrid (symmPart abar))⁻¹ x))

/-- The single Euclidean fractional loss for pushing a gradient from the
reference cube to the physical rounded cube.  It contains both the domain
distortion and the inverse-transpose value action. -/
@[expose]
def roundedPhysicalGradientHsLoss (abar : Mat d) (s : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal
      (hsAffineFactor (baseRoundedGrid (symmPart abar)) s
        ‖(baseRoundedGrid (symmPart abar))⁻¹‖) *
    ENNReal.ofReal (‖(baseRoundedGrid (symmPart abar))⁻¹‖ ^ 2)

private theorem isZeroTraceDirichletRhsWeakSolution_affinePullback
    {L : Mat d} (hL : IsUnit L.det) {U : Set (Vec d)}
    (hU : MeasurableSet U) (a : CoeffField d) (g : Vec d → Vec d)
    (u : H10Function U)
    (uL : H10Function (matImage L⁻¹ U))
    (huLgrad : uL.toH1Function.grad =
      fun y ↦ matVecMul (matTranspose L)
        (u.toH1Function.grad (matVecMul L y)))
    (hu : IsZeroTraceDirichletRhsWeakSolution a U u g) :
    IsZeroTraceDirichletRhsWeakSolution (affineCoefficient L hL a)
      (matImage L⁻¹ U) uL
      (fun y ↦ matVecMul L⁻¹ (g (matVecMul L y))) := by
  intro phi
  let V : Set (Vec d) := matImage L⁻¹ U
  have hV : MeasurableSet V := measurableSet_affinePullback hL hU
  have hLV : matImage L V = U := by
    simpa only [V] using matImage_matImage_inv hL U
  have hpsiPullback := exists_h10Function_affinePullback
    (Matrix.isUnit_nonsing_inv_det L hL) hV phi
  rw [Matrix.nonsing_inv_nonsing_inv L hL, hLV] at hpsiPullback
  obtain ⟨psi, _hpsiFun, hpsiGrad⟩ := hpsiPullback
  let lhsSource : Vec d → ℝ := fun x ↦
    vecDot (matVecMul (a x) (u.toH1Function.grad x))
      (psi.toH1Function.grad x)
  let rhsSource : Vec d → ℝ := fun x ↦
    vecDot (g x) (psi.toH1Function.grad x)
  let lhsTarget : Vec d → ℝ := fun y ↦
    vecDot
      (matVecMul (affineCoefficient L hL a y)
        (uL.toH1Function.grad y))
      (phi.toH1Function.grad y)
  let rhsTarget : Vec d → ℝ := fun y ↦
    vecDot (matVecMul L⁻¹ (g (matVecMul L y)))
      (phi.toH1Function.grad y)
  have hpsiAt (y : Vec d) :
      psi.toH1Function.grad (matVecMul L y) =
        matVecMul (matTranspose L⁻¹) (phi.toH1Function.grad y) := by
    rw [hpsiGrad]
    simp only [matVecMul_mul, Matrix.nonsing_inv_mul L hL, matVecMul_one]
  have hlhsPointwise (y : Vec d) :
      lhsTarget y = lhsSource (matVecMul L y) := by
    dsimp only [lhsTarget, lhsSource]
    rw [huLgrad, affineCoefficient_flux hL, hpsiAt]
    exact (vecDot_matVecMul_transpose
      (matVecMul (a (matVecMul L y))
        (u.toH1Function.grad (matVecMul L y)))
      (phi.toH1Function.grad y) L⁻¹).symm
  have hrhsPointwise (y : Vec d) :
      rhsTarget y = rhsSource (matVecMul L y) := by
    dsimp only [rhsTarget, rhsSource]
    rw [hpsiAt]
    exact (vecDot_matVecMul_transpose (g (matVecMul L y))
      (phi.toH1Function.grad y) L⁻¹).symm
  have hlhsChange :
      ∫ x in U, lhsSource x ∂volume =
        |L.det| * ∫ y in V, lhsTarget y ∂volume := by
    have hchange := setIntegral_matImage hL hV lhsSource
    rw [hLV] at hchange
    calc
      ∫ x in U, lhsSource x ∂volume =
          |L.det| * ∫ y in V, lhsSource (matVecMul L y) ∂volume := by
        simpa only [smul_eq_mul] using hchange
      _ = |L.det| * ∫ y in V, lhsTarget y ∂volume := by
        congr 1
        exact integral_congr_ae
          (_root_.Filter.Eventually.of_forall fun y ↦ (hlhsPointwise y).symm)
  have hrhsChange :
      ∫ x in U, rhsSource x ∂volume =
        |L.det| * ∫ y in V, rhsTarget y ∂volume := by
    have hchange := setIntegral_matImage hL hV rhsSource
    rw [hLV] at hchange
    calc
      ∫ x in U, rhsSource x ∂volume =
          |L.det| * ∫ y in V, rhsSource (matVecMul L y) ∂volume := by
        simpa only [smul_eq_mul] using hchange
      _ = |L.det| * ∫ y in V, rhsTarget y ∂volume := by
        congr 1
        exact integral_congr_ae
          (_root_.Filter.Eventually.of_forall fun y ↦ (hrhsPointwise y).symm)
  have hsource :
      ∫ x in U, lhsSource x ∂volume =
        ∫ x in U, rhsSource x ∂volume := by
    simpa only [lhsSource, rhsSource] using hu psi
  change (∫ y in V, lhsTarget y ∂volume) =
    ∫ y in V, rhsTarget y ∂volume
  apply mul_left_cancel₀ (abs_ne_zero.mpr hL.ne_zero)
  rw [← hlhsChange, ← hrhsChange]
  exact hsource

/-- A normalized rounded-reference response has one physical adapted-cube
representative.  Its weak equation is the inverse affine image of the
reference equation, its gradient is identified on the quotient carrier, and
its physical fractional norm pays exactly the named affine loss once. -/
theorem exists_roundedPhysicalDirichletAffineResponse [NeZero d]
    (abar : Mat d) (hS : (symmPart abar).PosDef)
    (h : CenteredCubeEuclideanL2Field d m)
    (w : H10Function (openCubeSet (originCube d m)))
    (hw : IsZeroTraceDirichletRhsWeakSolution
      (constantCoeffField (roundedReferenceMatrix abar hS))
      (openCubeSet (originCube d m)) w (fun y ↦ -h y)) :
    ∃ wPhysical : H10Function (roundedPhysicalCube abar m),
      wPhysical.toH1Function.toFun =
        (fun x ↦ w.toH1Function.toFun
          (matVecMul (baseRoundedGrid (symmPart abar))⁻¹ x)) ∧
      wPhysical.toH1Function.grad =
        (fun x ↦ matVecMul (baseRoundedGrid (symmPart abar))⁻¹
          (w.toH1Function.grad
            (matVecMul (baseRoundedGrid (symmPart abar))⁻¹ x))) ∧
      IsZeroTraceDirichletRhsWeakSolution
        (constantCoeffField (roundedPhysicalReferenceMatrix abar))
        (roundedPhysicalCube abar m) wPhysical
        (fun x ↦ -roundedPhysicalDirichletDatum abar h x) ∧
      wPhysical.toH1Function.gradToHilbertVectorL2 =
        affineGradientQuotientPushforward
          (isUnit_det_baseRoundedGrid hS)
          (measurableSet_matImage (isUnit_det_baseRoundedGrid hS)
            (measurableSet_openCubeSet (originCube d m)))
          (matImage_inv_matImage (isUnit_det_baseRoundedGrid hS)
            (openCubeSet (originCube d m))).symm
          (baseRoundedGrid (symmPart abar))⁻¹
          w.toH1Function.gradToHilbertVectorL2 ∧
      ∀ s : FractionalOrder,
        hsNormSq (roundedPhysicalCube abar m) s.1
            wPhysical.toH1Function.grad ≤
          roundedPhysicalGradientHsLoss abar s.1 *
            hsNormSq (openCubeSet (originCube d m)) s.1
              w.toH1Function.grad := by
  let q : Mat d := baseRoundedGrid (symmPart abar)
  let U : Set (Vec d) := openCubeSet (originCube d m)
  let V : Set (Vec d) := roundedPhysicalCube abar m
  have hq : IsUnit q.det := by
    simpa only [q] using isUnit_det_baseRoundedGrid hS
  have hqInv : IsUnit (q⁻¹).det := Matrix.isUnit_nonsing_inv_det q hq
  have hqSymm : matTranspose q = q := by
    simpa only [q] using matTranspose_baseRoundedGrid hS
  have hqInvSymm : matTranspose q⁻¹ = q⁻¹ := by
    rw [matTranspose, Matrix.transpose_nonsing_inv]
    exact congrArg (fun A : Mat d ↦ A⁻¹)
      (by simpa only [matTranspose] using hqSymm)
  have hU : MeasurableSet U := by
    simpa only [U] using measurableSet_openCubeSet (originCube d m)
  have hV : V = matImage q U := by
    rfl
  have hUV : MeasurableSet V := hV ▸ measurableSet_matImage hq hU
  have hVinv : U = matImage q⁻¹ V := hV ▸ (matImage_inv_matImage hq U).symm
  have hwPhysicalBundle :
      ∃ wPhysical : H10Function (matImage (q⁻¹)⁻¹ U),
        wPhysical.toH1Function.toFun =
          (fun x ↦ w.toH1Function.toFun (matVecMul q⁻¹ x)) ∧
        wPhysical.toH1Function.grad =
          (fun x ↦ matVecMul (matTranspose q⁻¹)
            (w.toH1Function.grad (matVecMul q⁻¹ x))) ∧
        IsZeroTraceDirichletRhsWeakSolution
          (affineCoefficient q⁻¹ hqInv
            (constantCoeffField (roundedReferenceMatrix abar hS)))
          (matImage (q⁻¹)⁻¹ U) wPhysical
          (fun x ↦ matVecMul (q⁻¹)⁻¹ (-h (matVecMul q⁻¹ x))) := by
    obtain ⟨wPhysical, hwPhysicalFun, hwPhysicalGrad⟩ :=
      exists_h10Function_affinePullback hqInv hU w
    refine ⟨wPhysical, hwPhysicalFun, hwPhysicalGrad, ?_⟩
    exact isZeroTraceDirichletRhsWeakSolution_affinePullback
      hqInv hU (constantCoeffField (roundedReferenceMatrix abar hS))
      (fun y ↦ -h y) w wPhysical hwPhysicalGrad hw
  rw [Matrix.nonsing_inv_nonsing_inv q hq, ← hV] at hwPhysicalBundle
  obtain ⟨wPhysical, hwPhysicalFun, hwPhysicalGrad, hweakAffine⟩ :=
    hwPhysicalBundle
  have hwPhysicalGrad' : wPhysical.toH1Function.grad =
      fun x ↦ matVecMul q⁻¹
        (w.toH1Function.grad (matVecMul q⁻¹ x)) := by
    simpa only [hqInvSymm] using hwPhysicalGrad
  have hcoeff : affineCoefficient q⁻¹ hqInv
      (constantCoeffField (roundedReferenceMatrix abar hS)) =
        constantCoeffField (roundedPhysicalReferenceMatrix abar) := by
    have href : constantCoeffField (roundedReferenceMatrix abar hS) =
        roundedSymmetricReferenceCoefficient abar hS := by
      simpa only [roundedReferenceConstantCoeffMatrix_matrix] using
        constantCoeffField_roundedReferenceConstantCoeffMatrix abar hS
    rw [href]
    change affineCoefficient q⁻¹ hqInv
        (affineCoefficient q hq
          (fun _ ↦ roundedPhysicalReferenceMatrix abar)) = _
    funext x
    exact affineCoefficient_inv_affineCoefficient q hq
      (fun _ ↦ roundedPhysicalReferenceMatrix abar) x
  have hweakPhysical : IsZeroTraceDirichletRhsWeakSolution
      (constantCoeffField (roundedPhysicalReferenceMatrix abar)) V
      wPhysical (fun x ↦ -roundedPhysicalDirichletDatum abar h x) := by
    rw [← hcoeff]
    simpa only [roundedPhysicalDirichletDatum, q, matVecMul_neg] using
      hweakAffine
  have hquotient' : wPhysical.toH1Function.gradToHilbertVectorL2 =
      affineGradientQuotientPushforward hq hUV hVinv q⁻¹
        w.toH1Function.gradToHilbertVectorL2 := by
    apply Lp.ext
    have hsourceRaw := ae_affinePullback hqInv hU
      w.toH1Function.coeFn_gradToHilbertVectorL2
    have hsource : ∀ᵐ x ∂volumeMeasureOn V,
        w.toH1Function.gradToHilbertVectorL2 (matVecMul q⁻¹ x) =
          hilbertifyVecField w.toH1Function.grad (matVecMul q⁻¹ x) := by
      simpa only [Matrix.nonsing_inv_nonsing_inv q hq, ← hV] using hsourceRaw
    filter_upwards [wPhysical.toH1Function.coeFn_gradToHilbertVectorL2,
      coeFn_affineGradientQuotientPushforward hq hUV hVinv q⁻¹
        w.toH1Function.gradToHilbertVectorL2,
      hsource] with x hphysical hquot hsrc
    rw [hphysical, hwPhysicalGrad', hquot, hsrc]
    rfl
  have hquotient : wPhysical.toH1Function.gradToHilbertVectorL2 =
      affineGradientQuotientPushforward hq
        (measurableSet_matImage hq hU)
        (matImage_inv_matImage hq U).symm q⁻¹
        w.toH1Function.gradToHilbertVectorL2 :=
    hquotient'
  have hHs (s : FractionalOrder) :
      hsNormSq V s.1 wPhysical.toH1Function.grad ≤
        roundedPhysicalGradientHsLoss abar s.1 *
          hsNormSq U s.1 w.toH1Function.grad := by
    have hsNonneg : 0 ≤ (d : ℝ) + 2 * s.1 :=
      add_nonneg (Nat.cast_nonneg d)
        (mul_nonneg (by norm_num) (FractionalOrder.pos s).le)
    have hdomain := hsNormSq_matImage_le_opNorm hq hU
      (volume_openCubeSet_ne_zero (originCube d m)) hsNonneg
      wPhysical.toH1Function.grad
    rw [← hV] at hdomain
    have hcomposed :
        (fun y ↦ wPhysical.toH1Function.grad (matVecMul q y)) =
          fun y ↦ matVecMul q⁻¹ (w.toH1Function.grad y) := by
      funext y
      rw [hwPhysicalGrad']
      simp only [matVecMul_mul, Matrix.nonsing_inv_mul q hq, matVecMul_one]
    rw [hcomposed] at hdomain
    have hvalue := hsNormSq_matVecMul_le q⁻¹ U s.1
      w.toH1Function.grad
    calc
      hsNormSq V s.1 wPhysical.toH1Function.grad ≤
          ENNReal.ofReal (hsAffineFactor q s.1 ‖q⁻¹‖) *
            hsNormSq U s.1
              (fun y ↦ matVecMul q⁻¹ (w.toH1Function.grad y)) := hdomain
      _ ≤ ENNReal.ofReal (hsAffineFactor q s.1 ‖q⁻¹‖) *
          (ENNReal.ofReal (‖q⁻¹‖ ^ 2) *
            hsNormSq U s.1 w.toH1Function.grad) := by
        exact mul_le_mul_right hvalue _
      _ = roundedPhysicalGradientHsLoss abar s.1 *
          hsNormSq U s.1 w.toH1Function.grad := by
        simp only [roundedPhysicalGradientHsLoss, q]
        ac_rfl
  refine ⟨wPhysical, ?_, hwPhysicalGrad', hweakPhysical, ?_, ?_⟩
  · simpa only [q] using hwPhysicalFun
  · simpa only [q, U, V, hV] using hquotient
  · intro s
    simpa only [U, V] using hHs s

end

end HighContrast
end HCPolySupport
