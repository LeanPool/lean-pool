/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Analytic.LocalEllipticity
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorGlobalH1sLoc
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorIntrinsicSlope

/-!
# High-contrast homogenization: Provider.Regularity.CorrectorGlobalAffineH1sLoc

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Local Sobolev membership of affine-plus-corrector representatives

The global shell representatives agree on every exhaustion cube with the
canonical local carrier. Adding the prescribed affine function and an
arbitrary constant therefore preserves the ballwise `H¹_s` construction.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory Set _root_.Filter

noncomputable section

/-- The affine-plus-global-corrector pair, with an arbitrary additive
constant, belongs to `H¹_{s,loc}`. -/
theorem NormalizedLocalH1Carrier.memH1sLoc_affineAdd_globalRepresentatives
    {d : ℕ} (z : NormalizedLocalH1Carrier d)
    {b : CoeffField d} (hb : IsAELocallyUniformlyElliptic b)
    (e : Vec d) (c : ℝ) :
    MemH1sLoc b
      (fun x => vecDot e x + z.globalValueRepresentative x + c)
      (fun x => e + z.globalGradientRepresentative x) := by
  constructor
  · constructor
    · have haffine : Continuous (fun x : Vec d => vecDot e x) := by
        simp only [vecDot]
        exact continuous_finsetSum _ fun i _ =>
          continuous_const.mul (continuous_apply i)
      exact (haffine.aestronglyMeasurable.add
        z.stronglyMeasurable_globalValueRepresentative.aestronglyMeasurable).add
          aestronglyMeasurable_const
    · intro i
      exact aestronglyMeasurable_const.add
        ((continuous_apply i).comp_aestronglyMeasurable
          z.stronglyMeasurable_globalGradientRepresentative.aestronglyMeasurable)
  · intro R hR
    obtain ⟨n, hclosed⟩ := exists_closedBall_zero_subset_localGradientCube hR
    have hball : euclideanBall d R ⊆ localGradientCube d n := by
      intro x hx
      exact hclosed (Metric.ball_subset_closedBall
        (euclideanBallAt_subset_metricBall (0 : Vec d) hR hx))
    have hμ : volume.restrict (euclideanBall d R) ≤
        volume.restrict (localGradientCube d n) :=
      Measure.restrict_mono_set volume hball
    let u : H1Function (localGradientCube d n) :=
      (affinePlusLocalCarrierH1 e z n).addConst c
    have hboundaryValue :
        (show H1Function (localGradientCube d n) from by
          simpa only [localGradientCube, Book.Ch02.cubeDomain_coe] using
            finiteAffineBoundaryH1 (n : ℤ) e).toFun =
          fun x => vecDot e x := by
      simpa only using! finiteAffineBoundaryH1_toFun (m := (n : ℤ)) e
    have hboundaryGrad :
        (show H1Function (localGradientCube d n) from by
          simpa only [localGradientCube, Book.Ch02.cubeDomain_coe] using
            finiteAffineBoundaryH1 (n : ℤ) e).grad =
          fun _ => e := by
      simpa only using! finiteAffineBoundaryH1_grad (m := (n : ℤ)) e
    have hvalueAE :
        (fun x => vecDot e x + z.globalValueRepresentative x + c)
          =ᵐ[volume.restrict (euclideanBall d R)] u.toFun := by
      have hae := (z.globalValueRepresentative_ae_eq_localH1Function n).filter_mono
        (ae_mono hμ)
      filter_upwards [hae] with x hx
      simp only [u, H1Function.addConst_apply, affinePlusLocalCarrierH1,
        H1Function.add_toFun, hboundaryValue, hx]
    have hgradientAE :
        (fun x => e + z.globalGradientRepresentative x)
          =ᵐ[volume.restrict (euclideanBall d R)] u.grad := by
      have hae :=
        (z.globalGradientRepresentative_ae_eq_localH1Gradient n).filter_mono
          (ae_mono hμ)
      filter_upwards [hae] with x hx
      simp only [u, H1Function.grad_addConst, affinePlusLocalCarrierH1,
        H1Function.add_grad, hboundaryGrad, hx]
    constructor
    · intro i φ hφsmooth hφcompact hφsub
      have hlocal := (u.hasWeakGradient.restrict
        (isOpen_euclideanBall d R) hball) i φ hφsmooth hφcompact hφsub
      calc
        ∫ x in euclideanBall d R,
            (vecDot e x + z.globalValueRepresentative x + c) *
              (fderiv ℝ φ x) (basisVec i) ∂volume =
            ∫ x in euclideanBall d R,
              u.toFun x * (fderiv ℝ φ x) (basisVec i) ∂volume := by
                exact integral_congr_ae
                  (hvalueAE.mono fun x hx => by simp only [hx])
        _ = -(∫ x in euclideanBall d R, u.grad x i * φ x ∂volume) := hlocal
        _ = -(∫ x in euclideanBall d R,
              (e + z.globalGradientRepresentative x) i * φ x ∂volume) := by
                congr 1
                exact integral_congr_ae
                  (hgradientAE.mono fun x hx => by simp only [hx])
    · have hU : IsOpenBoundedConvexDomain (localGradientCube d n) := by
        simpa only [localGradientCube] using
          isOpenBoundedConvexDomain_openCubeSet (originCube d (n : ℤ))
      obtain ⟨w, hwSmooth, hwCube⟩ :=
        exists_contDiff_tendsto_h1NormSqOnUnweighted_sub hU u hclosed hR
      refine ⟨w, hwSmooth, ?_⟩
      obtain ⟨lam, Lam, hlam, -, hell⟩ :=
        hb.exists_ae_isEllipticMatrix_euclideanBall hR
      apply (tendsto_h1sNormSqOn_sub_zero_iff_restrict (Lam := Lam)
        hlam hell _ _ w).mpr
      have hwBall : Tendsto
          (fun k => h1NormSqOnUnweighted (euclideanBall d R)
            (fun x => w k x - u.toFun x)
            (fun x => smoothGrad (w k) x - u.grad x)) atTop (nhds 0) :=
        tendsto_zero_of_le_of_tendsto_zero
          (fun k => h1NormSqOnUnweighted_mono hball _ _) hwCube
      refine hwBall.congr' (Eventually.of_forall fun k => ?_)
      exact (h1NormSqOnUnweighted_congr_ae
        (hvalueAE.mono fun x hx => by simp only [hx])
        (hgradientAE.mono fun x hx => by simp only [hx])).symm

end

end HighContrast
end HCPolySupport
