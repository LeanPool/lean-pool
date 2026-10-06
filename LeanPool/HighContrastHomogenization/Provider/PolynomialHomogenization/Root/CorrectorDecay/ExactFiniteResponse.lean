/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorDecay.IdentityAffineReplacement
public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteCorrector

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.CorrectorDecay.ExactFiniteResponse

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

private theorem normalizedDual_eq_of_ae_eq_on_cubeSet
    {d : ℕ} {Q : TriadicCube d} {F G : Vec d → Vec d} (s : ℝ)
    (hFG : F =ᵐ[volumeMeasureOn (cubeSet Q)] G) :
    cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q s F =
      cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q s G := by
  unfold cubeScaleNormalizedDualNegativeBesovVectorNormTwo
  congr 1
  apply Finset.sum_congr rfl
  intro i _hi
  exact Book.Ch03.cubeBesovDualFullNorm_eq_of_ae_eq_on_cubeSet
    s (2 : ℝ≥0∞) (2 : ℝ≥0∞) (hFG.fun_comp fun z ↦ z i)

private theorem cubeLpNorm_eq_of_ae_eq_on_parent_cube
    {d : ℕ} {Q R : TriadicCube d} {j : ℕ} {f h : Vec d → ℝ}
    (hR : R ∈ descendantsAtDepth Q j)
    (hfh : f =ᵐ[volumeMeasureOn (cubeSet Q)] h) :
    cubeLpNorm R (2 : ℝ≥0∞) f = cubeLpNorm R (2 : ℝ≥0∞) h := by
  have hvol : f =ᵐ[MeasureTheory.volume.restrict (cubeSet R)] h :=
    MeasureTheory.ae_restrict_of_ae_restrict_of_subset
      (cubeSet_subset_of_mem_descendantsAtDepth hR)
      (by simpa only [volumeMeasureOn] using! hfh)
  have hnorm : f =ᵐ[normalizedCubeMeasure R] h := by
    show ∀ᵐ x ∂normalizedCubeMeasure R, f x = h x
    simpa only [normalizedCubeMeasure, cubeMeasure] using
      MeasureTheory.Measure.ae_smul_measure hvol
        (ENNReal.ofReal ((cubeVolume R)⁻¹))
  unfold cubeLpNorm
  rw [MeasureTheory.eLpNorm_congr_ae hnorm]

/-- At exact identity reference, the two actual finite affine response rows
are controlled at the same printed order as the scalar identity weak error. -/
theorem exists_identityFiniteResponseConstant
    (d : ℕ) [NeZero d] (g : ℝ) (hg : g ∈ Set.Ico (0 : ℝ) 1) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (a : Book.Ch03.CoeffFamily d) (m : ℤ) (e : Vec d),
        scalarIdentityWeakError a (printCertificateOrder g) m ≤ 1 →
        let u := (finiteAffineSolution a m e).toH1
        let E := scalarIdentityWeakError a (printCertificateOrder g) m
        cubeScaleNormalizedDualNegativeBesovVectorNormTwo
            (originCube d m) (printCertificateOrder g)
            (fun x ↦ u.grad x - e) ≤ C * E * euclideanNorm e ∧
        cubeScaleNormalizedDualNegativeBesovVectorNormTwo
            (originCube d m) (printCertificateOrder g)
            (fun x ↦
              matVecMul (Book.Ch03.publicCoeffField (originCube d m) a x)
                  (u.grad x) - e) ≤ C * E * euclideanNorm e ∧
        cubeBesovScaleWeight (1 : ℝ) (originCube d m) *
            cubeLpNorm (originCube d (m - 1)) (2 : ℝ≥0∞)
              (finiteAffineCorrection a m e).toH1Function.toFun ≤
          C * E * euclideanNorm e := by
  obtain ⟨Cid, hidentity⟩ :=
    exists_printOrderIdentityCubeDualRegularityWithConstant d g hg
  obtain ⟨Ccomp, hCcomp, hcomp⟩ :=
    exists_identityHarmonicComparisonConstant d g Cid hg hidentity
  let s : ℝ := printCertificateOrder g
  have hs : 0 < s := by simpa only [s] using (printOrder_margins hg).1
  have hsOne : s < 1 :=
    (printOrder_margins hg).2.1.trans (by norm_num)
  obtain ⟨Cenergy, hCenergy, henergy⟩ :=
    exists_finiteAffineSolutionEnergyEstimateConstant d s hs hsOne
  let C : ℝ := Ccomp * (2 * Cenergy)
  have hC : 0 ≤ C := mul_nonneg hCcomp (by positivity)
  refine ⟨C, hC, ?_⟩
  intro a m e herror
  let Q := originCube d m
  let u := (finiteAffineSolution a m e).toH1
  let hu := isWeakSolutionOn_finiteAffineSolution a m e
  let W := identityHarmonicReplacementDatum a m u hu
  let E := scalarIdentityWeakError a s m
  let A := Book.Ch03.h1EnergyNormOnCube Q a u
  have hraw := hcomp a m u hu
  have hAraw : A ≤ Cenergy * (1 + E) * euclideanNorm e := by
    simpa only [A, Q, u, E, s] using henergy a m e
  have hE : 0 ≤ E := scalarIdentityWeakError_nonneg a s m
  have hEone : E ≤ 1 := by simpa only [E, s] using herror
  have hA : A ≤ (2 * Cenergy) * euclideanNorm e := by
    calc
      A ≤ Cenergy * (1 + E) * euclideanNorm e := hAraw
      _ ≤ Cenergy * 2 * euclideanNorm e := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by linarith only [hEone]) hCenergy.le)
          (euclideanNorm_nonneg e)
      _ = (2 * Cenergy) * euclideanNorm e := by ring
  have hW : W.v.grad =ᵐ[volumeMeasureOn (cubeSet Q)] fun _ ↦ e := by
    simpa only [Q, u, hu, W] using
      identityHarmonicReplacementDatum_affine_grad_ae a m e
  have hWvalue : W.v.toFun =ᵐ[volumeMeasureOn (cubeSet Q)]
      (finiteAffineBoundaryH1 m e).toFun := by
    simpa only [Q, u, hu, W] using
      identityHarmonicReplacementDatum_affine_toFun_ae a m e
  have hgradAE : (fun x ↦ u.grad x - W.v.grad x)
      =ᵐ[volumeMeasureOn (cubeSet Q)] fun x ↦ u.grad x - e := by
    filter_upwards [hW] with x hx
    rw [hx]
  have hfluxAE :
      Book.Ch03.homogenizationComparisonFluxField Q a
          (identityConstantCoeffMatrix d) u W.v
        =ᵐ[volumeMeasureOn (cubeSet Q)] fun x ↦
          matVecMul (Book.Ch03.publicCoeffField Q a x) (u.grad x) - e := by
    have hbase :=
      Book.Ch03.homogenizationComparisonFluxField_ae_eq_fluxComparison_publicCoeffField_cubeSet
        (Q := Q) (a := a) (a0 := identityConstantCoeffMatrix d) u W.v
    filter_upwards [hbase, hW] with x hx hWx
    rw [hx]
    unfold fluxComparison
    rw [identityConstantCoeffMatrix_matrix, hWx,
      HCPolySupport.matVecMul_one]
  have hgrad := hraw.1
  have hflux := hraw.2.1
  have hvalue := hraw.2.2
  rw [normalizedDual_eq_of_ae_eq_on_cubeSet s hgradAE] at hgrad
  rw [normalizedDual_eq_of_ae_eq_on_cubeSet s hfluxAE] at hflux
  have hcorrectionAE : (fun x ↦ u.toFun x - W.v.toFun x)
      =ᵐ[volumeMeasureOn (cubeSet Q)]
        (finiteAffineCorrection a m e).toH1Function.toFun := by
    filter_upwards [hWvalue] with x hx
    rw [hx]
    simp only [u, finiteAffineSolution_toH1, H1Function.add_toFun]
    ring
  have hdesc : originCube d (m - 1) ∈ descendantsAtDepth Q 1 := by
    simpa only [Q, centralDescendant_originCube_eq_originCube_sub, Nat.cast_one] using
      CubeCalderonZygmund.centralDescendant_mem_descendantsAtDepth Q 1
  rw [cubeLpNorm_eq_of_ae_eq_on_parent_cube hdesc hcorrectionAE] at hvalue
  have hscale : Ccomp * E * A ≤ C * E * euclideanNorm e := by
    calc
      Ccomp * E * A ≤ Ccomp * E * ((2 * Cenergy) * euclideanNorm e) :=
        mul_le_mul_of_nonneg_left hA (mul_nonneg hCcomp hE)
      _ = C * E * euclideanNorm e := by
        dsimp only [C]
        ring
  exact ⟨hgrad.trans hscale, hflux.trans hscale, hvalue.trans hscale⟩

end

end HighContrast
end HCPolySupport
