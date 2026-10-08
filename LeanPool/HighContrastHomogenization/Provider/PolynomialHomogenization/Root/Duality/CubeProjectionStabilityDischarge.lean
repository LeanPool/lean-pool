/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Duality.CubeHodgeByDuality
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.CubeFractionalNormBridge
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CubeVolume
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Fractional.CenteredCubeFractionalCZFullNorm
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.ABK26.FluxComparisonBridges
public import LeanPool.HighContrastHomogenization.Support.Deterministic.ConstantCoefficientDirichletBesov.PublicTheorems

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Duality.CubeProjectionStabilityDischarge

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Discharging the cube projection stability

The positive-direction input of the cube Hodge estimate is proved from material:

* existence of the zero-trace identity-coefficient solution of
  `div (∇v − psi) = 0` on the open cube
  (`exists_isZeroTraceDirichletRhsWeakSolution_of_potentialZeroTraceClosureRealization`
  through the convex-domain closure realization);
* the fractional Calderón--Zygmund estimate for that solution on an origin cube
  (`centeredCubeH10ScalarDivergence_fractional_cz_full`);
* the two norm bridges `cubeEuclideanWspFullENorm_two_sq_eq_hsNormSq` and the
  packaging of a finite-fractional field as a cube `Wsp ∩ L²` field.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- A local vector test has finite normalized `H^s` norm on an open cube. -/
private theorem hsNormSq_openCubeSet_ne_top (Q : TriadicCube d)
    {s : ℝ} (hs : 0 < s) (hsHalf : s < 1 / 2) {G : Vec d → Vec d}
    (hG : IsLocalVecTest (openCubeSet Q) G) :
    hsNormSq (openCubeSet Q) s G ≠ ⊤ := by
  have hs0 : 0 ≤ (d : ℝ) + 2 * s := by positivity
  have hs1 : s < 1 := hsHalf.trans (by norm_num)
  have hVtop : volume (openCubeSet Q) ≠ ⊤ := (volume_openCubeSet_lt_top Q).ne
  have hV0 : volume (openCubeSet Q) ≠ 0 := volume_openCubeSet_ne_zero Q
  have hweight : volume (openCubeSet Q) ^ (-(2 * s) / (d : ℝ)) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_ne_zero hV0 hVtop
  have hL2 : eVolumeAverage (openCubeSet Q)
      (fun x => ENNReal.ofReal (vecNormSq (G x))) ≠ ⊤ :=
    ne_of_lt (eVolumeAverage_lt_top hV0
      (lintegral_vecNormSq_ne_top (isBoundedDomain_openCubeSet Q)
        hG.contDiff.continuous hG.hasCompactSupport))
  have hFractional : fracSeminormSq (openCubeSet Q) s G ≠ ⊤ := by
    refine ne_of_lt (eVolumeAverage_lt_top hV0 ?_)
    exact lintegral_fracSeminorm_ne_top (measurableSet_openCubeSet Q)
      (isBoundedDomain_openCubeSet Q) hs0 hs1 hG.contDiff hG.hasCompactSupport
  simp only [hsNormSq]
  exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top hweight hL2, hFractional⟩

/-- Packaging of a measurable field of finite normalized `H^s` norm as a cube
`Wsp ∩ L²` field.  (The construction of the same content is private at
its file; it is reproved here rather than imported.) -/
@[expose]
public noncomputable def wspL2FieldOfHsNormSq (Q : TriadicCube d)
    {s : ℝ} (hs : 0 < s) (hsHalf : s < 1 / 2) (G : Vec d → Vec d)
    (hGmeas : AEStronglyMeasurable G (volume.restrict (openCubeSet Q)))
    (hGfinite : hsNormSq (openCubeSet Q) s G ≠ ⊤) :
    CubeEuclideanWspL2Field Q
      (⟨s, hs, hsHalf.trans (by norm_num)⟩ : FractionalOrder)
      FiniteLpExponent.two := by
  let sF : FractionalOrder := ⟨s, hs, hsHalf.trans (by norm_num)⟩
  have hV0 : volume (openCubeSet Q) ≠ 0 := volume_openCubeSet_ne_zero Q
  have hweight0 : volume (openCubeSet Q) ^ (-(2 * s) / (d : ℝ)) ≠ 0 :=
    ne_of_gt (ENNReal.rpow_pos (lt_of_le_of_ne zero_le (Ne.symm hV0))
      (volume_openCubeSet_lt_top Q).ne)
  have hparts :
      volume (openCubeSet Q) ^ (-(2 * s) / (d : ℝ)) *
          eVolumeAverage (openCubeSet Q)
            (fun x => ENNReal.ofReal (vecNormSq (G x))) ≠ ⊤ ∧
        fracSeminormSq (openCubeSet Q) s G ≠ ⊤ :=
    ENNReal.add_ne_top.mp (by simpa only [hsNormSq] using hGfinite)
  have haverageTop :
      eVolumeAverage (openCubeSet Q)
          (fun x => ENNReal.ofReal (vecNormSq (G x))) ≠ ⊤ := by
    intro havg
    apply hparts.1
    rw [havg, ENNReal.mul_top hweight0]
  have hGnormMeas : AEStronglyMeasurable G (normalizedCubeMeasure Q) := by
    unfold normalizedCubeMeasure cubeMeasure
    rw [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
    exact AEStronglyMeasurable.mono_ac Measure.smul_absolutelyContinuous hGmeas
  have hGhilbertMeas : AEStronglyMeasurable
      (fun x => HilbertVec.ofVec (G x)) (normalizedCubeMeasure Q) :=
    (HilbertVec.ofVecL d).continuous.comp_aestronglyMeasurable hGnormMeas
  have hL2sq :
      (eLpNorm (fun x => HilbertVec.ofVec (G x)) 2
          (normalizedCubeMeasure Q)) ^ (2 : ℕ) =
        eVolumeAverage (openCubeSet Q)
          (fun x => ENNReal.ofReal (vecNormSq (G x))) := by
    simpa only [BoundedMeasurableDomain.normalizedEuclideanLpENorm,
      BoundedMeasurableDomain.normalizedLpENorm,
      cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure,
      euclideanNorm_eq_norm_ofVec, eLpNorm_norm _ hGhilbertMeas] using
        normalizedEuclideanLpENorm_two_sq_eq_eVolumeAverage Q G
          (by simpa only [euclideanNorm_eq_norm_ofVec] using hGhilbertMeas.norm)
  have hL2top : eLpNorm (fun x => HilbertVec.ofVec (G x)) 2
      (normalizedCubeMeasure Q) ≠ ⊤ := by
    intro htop
    apply haverageTop
    rw [← hL2sq, htop]
    norm_num
  have hGmemL2 : MemLp (fun x => HilbertVec.ofVec (G x)) 2
      (normalizedCubeMeasure Q) :=
    lt_top_iff_ne_top.mpr hL2top
  have hsemisq :
      (cubeEuclideanWspESeminorm Q sF FiniteLpExponent.two G) ^ (2 : ℕ) =
        fracSeminormSq (openCubeSet Q) s G := by
    simpa only [sF] using
      cubeEuclideanWspESeminorm_two_sq_eq_fracSeminormSq Q sF G hGmeas
  have hsemitop : cubeEuclideanWspESeminorm Q sF FiniteLpExponent.two G ≠ ⊤ := by
    intro htop
    apply hparts.2
    rw [← hsemisq, htop]
    norm_num
  exact
    { toField := G
      euclideanMemLp := hGmemL2
      euclideanMemWsp := memCubeEuclideanWsp_of_memLp_of_eSeminorm_lt_top
        hGmemL2 (lt_top_iff_ne_top.mpr hsemitop)
      euclideanMemL2 := hGmemL2 }

@[simp] private theorem wspL2FieldOfHsNormSq_toField
    (Q : TriadicCube d) {s : ℝ} (hs : 0 < s) (hsHalf : s < 1 / 2)
    (G : Vec d → Vec d)
    (hGmeas : AEStronglyMeasurable G (volume.restrict (openCubeSet Q)))
    (hGfinite : hsNormSq (openCubeSet Q) s G ≠ ⊤) :
    (wspL2FieldOfHsNormSq Q hs hsHalf G hGmeas hGfinite).toField = G := rfl

/-- **The cube projection stability is proved.**  Every admissible test on an
origin cube splits into a zero-trace potential part and a solenoidal remainder,
with the potential part `H^s`-bounded by the test, at a constant fixed before
the scale, the order and the test. -/
theorem exists_cubeGradientProjectionHsStability_originCube (d : ℕ) [NeZero d] :
    ∃ Cproj : ℝ, 0 ≤ Cproj ∧
      ∀ (m : ℤ) {s : ℝ}, 0 < s → s < 1 / 2 →
        CubeGradientProjectionHsStability d (originCube d m) s Cproj := by
  classical
  obtain ⟨C, hCtop, hCZ⟩ :=
    centeredCubeH10ScalarDivergence_fractional_cz_full d FiniteLpExponent.two
  refine ⟨C.toReal, ENNReal.toReal_nonneg, ?_⟩
  intro m s hs hsHalf
  refine ⟨ENNReal.toReal_nonneg, ?_⟩
  intro psi htest
  have hUopen : IsOpenBoundedConvexDomain (openCubeSet (originCube d m)) :=
    isOpenBoundedConvexDomain_openCubeSet (originCube d m)
  have hfin : MeasureTheory.IsFiniteMeasure
      (volumeMeasureOn (openCubeSet (originCube d m))) :=
    hUopen.isFiniteMeasure_restrict_volume
  have hpsiMeas : AEStronglyMeasurable psi
      (volume.restrict (openCubeSet (originCube d m))) :=
    htest.contDiff.continuous.aestronglyMeasurable
  have hpsiFinite : hsNormSq (openCubeSet (originCube d m)) s psi ≠ ⊤ :=
    hsNormSq_openCubeSet_ne_top (originCube d m) hs hsHalf htest
  have hpsiL2 : MemVectorL2 (openCubeSet (originCube d m)) psi :=
    (htest.contDiff.continuous.memLp_of_hasCompactSupport
      htest.hasCompactSupport).restrict _
  have hRealize :=
    PotentialSolenoidalL2Data.hasPotentialZeroTraceClosureRealization_of_convexDomain
      hUopen
  have hEll : IsEllipticFieldOn 1 1 (openCubeSet (originCube d m))
      (identityCoeffField d) :=
    isEllipticFieldOn_identityCoeffField
      (measurableSet_openCubeSet (originCube d m))
  obtain ⟨v, hv⟩ :=
    exists_isZeroTraceDirichletRhsWeakSolution_of_potentialZeroTraceClosureRealization
      (a := identityCoeffField d) (g := psi) hpsiL2 hRealize
      (openCubeSet_nonempty_internal (originCube d m)) hEll
  -- the weak equation with the identity coefficient removed
  have hvEq : ∀ phi : H10Function (openCubeSet (originCube d m)),
      ∫ x in openCubeSet (originCube d m),
          vecDot (v.toH1Function.grad x) (phi.toH1Function.grad x) ∂volume =
        ∫ x in openCubeSet (originCube d m),
          vecDot (psi x) (phi.toH1Function.grad x) ∂volume := by
    intro phi
    have h0 := hv phi
    have hleft : ∫ x in openCubeSet (originCube d m),
        vecDot (matVecMul (identityCoeffField d x) (v.toH1Function.grad x))
          (phi.toH1Function.grad x) ∂volume =
        ∫ x in openCubeSet (originCube d m),
          vecDot (v.toH1Function.grad x) (phi.toH1Function.grad x) ∂volume := by
      refine setIntegral_congr_fun (measurableSet_openCubeSet _) ?_
      intro x _hx
      simp only [matVecMul_identityCoeffField]
    rw [hleft] at h0
    exact h0
  refine ⟨v.toH1Function.grad, v.isPotentialZeroTraceOn, ?_, ?_⟩
  · -- the remainder is solenoidal
    intro phi
    have hInt1 : IntegrableOn
        (fun x => vecDot (psi x) (phi.toH1Function.grad x))
        (openCubeSet (originCube d m)) volume :=
      integrableOn_vecDot_of_memVectorL2 hpsiL2
        phi.toH1Function.grad_memVectorL2
    have hInt2 : IntegrableOn
        (fun x => vecDot (v.toH1Function.grad x) (phi.toH1Function.grad x))
        (openCubeSet (originCube d m)) volume :=
      integrableOn_vecDot_of_memVectorL2 v.toH1Function.grad_memVectorL2
        phi.toH1Function.grad_memVectorL2
    have hsplit :
        (fun x => vecDot (psi x - v.toH1Function.grad x)
            (phi.toH1Function.grad x)) =
          fun x => vecDot (psi x) (phi.toH1Function.grad x) -
            vecDot (v.toH1Function.grad x) (phi.toH1Function.grad x) := by
      funext x
      rw [sub_eq_add_neg, vecDot_add_left, vecDot_neg_left, ← sub_eq_add_neg]
    rw [hsplit, integral_sub hInt1 hInt2, hvEq phi, sub_self]
  · -- the fractional Calderón--Zygmund bound
    have hnegMeas : AEStronglyMeasurable (fun x => -psi x)
        (volume.restrict (openCubeSet (originCube d m))) := hpsiMeas.neg
    have hnegFinite : hsNormSq (openCubeSet (originCube d m)) s
        (fun x => -psi x) ≠ ⊤ := by
      rw [show (fun x => -psi x) = -psi from rfl, hsNormSq_neg]
      exact hpsiFinite
    set negField := wspL2FieldOfHsNormSq (originCube d m) hs hsHalf
      (fun x => -psi x) hnegMeas hnegFinite with hnegField
    have hdiv : CubeDirichletDivergenceProblem (originCube d m) v
        (fun x => -psi x) := by
      intro phi
      rw [hvEq phi]
      rw [show ∫ x in openCubeSet (originCube d m),
          vecDot (-psi x) (phi.toH1Function.grad x) ∂volume =
          -∫ x in openCubeSet (originCube d m),
            vecDot (psi x) (phi.toH1Function.grad x) ∂volume from ?_]
      · rw [neg_neg]
      · rw [← integral_neg]
        refine integral_congr_ae ?_
        filter_upwards with x
        exact vecDot_neg_left (psi x) (phi.toH1Function.grad x)
    have hsolCZ : IsCenteredCubeH10ScalarDivergenceSolution m 1 v
        negField.toLpTwo :=
      Book.Ch03.ABK26.cubeDirichletDivergenceProblem_to_centeredCubeH10ScalarDivergenceSolution
        (p := FiniteLpExponent.two) m negField.euclideanMemL2 hdiv
    have hbound := hCZ m 1
      (⟨s, hs, hsHalf.trans (by norm_num)⟩ : FractionalOrder) negField v
      one_pos hsolCZ
    rw [ENNReal.ofReal_one, inv_one, mul_one] at hbound
    have hvgradMeas : AEStronglyMeasurable v.toH1Function.grad
        (volume.restrict (openCubeSet (originCube d m))) :=
      v.toH1Function.grad_memVectorL2.aestronglyMeasurable
    have hsq := ENNReal.rpow_le_rpow hbound (by norm_num : (0 : ℝ) ≤ 2)
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2),
      cubeEuclideanWspFullENorm_two_sq_eq_hsNormSq (originCube d m)
        (⟨s, hs, hsHalf.trans (by norm_num)⟩ : FractionalOrder)
        v.toH1Function.grad hvgradMeas,
      cubeEuclideanWspFullENorm_two_sq_eq_hsNormSq (originCube d m)
        (⟨s, hs, hsHalf.trans (by norm_num)⟩ : FractionalOrder)
        negField.toField (by
          rw [hnegField, wspL2FieldOfHsNormSq_toField]
          exact hnegMeas)] at hsq
    have hnegEq : hsNormSq (openCubeSet (originCube d m)) s negField.toField =
        hsNormSq (openCubeSet (originCube d m)) s psi := by
      rw [hnegField, wspL2FieldOfHsNormSq_toField,
        show (fun x => -psi x) = -psi from rfl, hsNormSq_neg]
    have hC2 : C ^ (2 : ℝ) = ENNReal.ofReal (C.toReal ^ 2) := by
      rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg 2,
        ENNReal.ofReal_toReal hCtop.ne, ← ENNReal.rpow_natCast C 2]
      norm_num
    rw [hnegEq, hC2] at hsq
    exact hsq

end

end RowSupply
end HighContrast
end HCPolySupport
