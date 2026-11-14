/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Freezing.BoundaryFreezingRadius
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Freezing.BoundaryReflectionChain
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Freezing.SkewConst
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Ported.LocalRepresentativeGlue
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Ported.ScalarForcing
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Ported.ZerothOrderSchauderBall
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.BoxGeometry
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.BoundaryCoveringTrace

/-!
# BoundaryLocalRepresentative

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# A continuous representative near a point of the closed cube

Freezing the skew part at a point of the closed cube and normalizing by the
scalar symmetric part makes the coefficient uniformly close to the identity on
a small ball.  On that scale the ball meets only the faces through the centre,
so the solution unfolds oddly into a small-contrast solution on the whole ball.
The scale-free interior estimate then produces a representative continuous on
the half ball, odd under every unfolded reflection, hence vanishing on the part
of the cube boundary that the ball meets.
-/

namespace Algsuperdiff.StochasticProcess.Common.Regularity.Freezing

open MeasureTheory HCPolySupport Filter
open Algsuperdiff.Section4.Provider.ExcessDecay
open Algsuperdiff.StochasticProcess.Common.Regularity
open Algsuperdiff.StochasticProcess.Common.Regularity.Ported

noncomputable section

variable {d : ℕ}

/-- Scaling the coefficient scales the scalar source. -/
theorem isMatrixDivFormWeakSolutionZerothOrderOn_smul_coeff
    {W : Set (Vec d)} {c : ℝ} {a : CoeffField d}
    {u : H1Function W} {g : Vec d → ℝ}
    (hu : IsMatrixDivFormWeakSolutionZerothOrderOn a W u g 0) :
    IsMatrixDivFormWeakSolutionZerothOrderOn
      (fun x => c • a x) W u (fun x => c * g x) 0 := by
  intro phi
  have h := hu phi
  have hleft :
      (∫ x in W, vecDot (matVecMul (c • a x) (u.grad x))
          (phi.toH1Function.grad x) ∂volume) =
        c * ∫ x in W, vecDot (matVecMul (a x) (u.grad x))
          (phi.toH1Function.grad x) ∂volume := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp [smul_matVecMul, vecDot_smul_left]
  have hright :
      (∫ x in W, (c * g x) * phi.toH1Function.toFun x ∂volume) =
        c * ∫ x in W, g x * phi.toH1Function.toFun x ∂volume := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    ring
  rw [hleft, hright]
  simp only [Pi.zero_apply, vecDot_zero_left, integral_zero, sub_zero] at h ⊢
  exact congrArg (c * ·) h

/-- **A continuous representative on a ball about a point of the closed
cube.**  The coefficient is continuous with symmetric part `nu • 1` and skew
part of arbitrary size; no contrast hypothesis appears. -/
theorem exists_boundary_local_representative [NeZero d] (hd : 2 ≤ d)
    (z : Vec d) {L : ℝ} (hL : 0 < L)
    {nu : ℝ} (hnu : 0 < nu) {a : CoeffField d} (hameas : Measurable a)
    (hsymm : ∀ y, symmPart (a y) = nu • (1 : Mat d))
    (hcont : ContinuousOn (fun y => a y - nu • (1 : Mat d))
      {x | MemAxisCubeClosure z L x})
    {u : H10Function (axisCube z L)} {g : Vec d → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hg : MemScalarLInfOn (axisCube z L) g)
    (hgM : ∀ᵐ y ∂volume.restrict (axisCube z L), |g y| ≤ M)
    (hu : IsMatrixDivFormWeakSolutionZerothOrderOn a (axisCube z L)
      u.toH1Function g 0)
    {x₀ : Vec d} (hx₀ : MemAxisCubeClosure z L x₀) :
    ∃ rho > 0, ∃ V : Vec d → ℝ,
      ContinuousOn V (euclideanBall x₀ rho) ∧
      V =ᵐ[volume.restrict (euclideanBall x₀ rho ∩ axisCube z L)]
        u.toH1Function.toFun ∧
      ∀ y ∈ euclideanBall x₀ rho, MemAxisCubeClosure z L y →
        y ∉ axisCube z L → V y = 0 := by
  classical
  set delta : ℝ := smallContrastThreshold d (1 / 2 : ℝ) with hdeltadef
  have hdeltapos : 0 < delta := by
    rw [hdeltadef, smallContrastThreshold]
    positivity
  have hdelta0 : (0 : ℝ) ≤ delta := hdeltapos.le
  obtain ⟨R, hR, hclear, hbound⟩ :=
    exists_boundary_freezing_radius z hL hnu hcont hx₀ hdeltapos
  set S : Finset (Fin d) := axisCubeFaceSet z L x₀ with hSdef
  set sig : Fin d → ℝ := axisCubeFaceOrientation z x₀ with hsigdef
  have hsigma : ∀ i ∈ S, |sig i| = 1 := fun i _ => abs_axisCubeFaceOrientation z x₀ i
  set W : Set (Vec d) := ballSector x₀ R S sig with hWdef
  have hWeq : euclideanBall x₀ R ∩ axisCube z L = W :=
    euclideanBall_inter_axisCube_eq_ballSector z hL hR x₀ hclear
  have hWopen : IsOpen W := isOpen_partialReflectedBallSector x₀ R S sig ∅
  have hWQ : W ⊆ axisCube z L := by
    intro y hy
    have hmem : y ∈ euclideanBall x₀ R ∩ axisCube z L := hWeq.symm ▸ hy
    exact hmem.2
  have hWB : W ⊆ euclideanBall x₀ R := by
    intro y hy
    have hmem : y ∈ euclideanBall x₀ R ∩ axisCube z L := hWeq.symm ▸ hy
    exact hmem.1
  have hWfinite : IsFiniteMeasure (volume.restrict W) :=
    (isOpenBoundedConvexDomain_partialReflectedBallSector x₀ hR S sig
      ∅).isFiniteMeasure_restrict_volume
  -- the frozen normalized coefficient and its data
  set aF : CoeffField d := normalizedFrozenCoeff nu a x₀ with haFdef
  have haFmeas : Measurable aF := measurable_normalizedFrozenCoeff hameas x₀
  have hboundW : ∀ y ∈ W, ‖HilbertVec.applyMat (aF y - (1 : Mat d))‖ ≤ delta := by
    intro y hy
    exact hbound y (hWB hy) (axisCube_subset_closureSet z L (hWQ hy))
  have hcontrastW : CoefficientIdentityDistanceLE W aF delta := by
    filter_upwards [ae_restrict_mem hWopen.measurableSet] with y hy
    exact hboundW y hy
  set uW : H1Function W := u.toH1Function.restrict hWopen hWQ with huWdef
  have hbase : IsMatrixDivFormWeakSolutionZerothOrderOn a W uW g 0 :=
    isMatrixDivFormWeakSolutionZerothOrderOn_restrict (isOpen_axisCube z L)
      hWopen hWQ hu
  have hk : matTranspose (a x₀ - nu • (1 : Mat d)) = -(a x₀ - nu • (1 : Mat d)) :=
    sub_scalar_one_isSkew_of_symmPart_eq (hsymm x₀)
  have hfrozen : IsMatrixDivFormWeakSolutionZerothOrderOn
      (fun x => a x - (a x₀ - nu • (1 : Mat d))) W uW g 0 :=
    (isMatrixDivFormWeakSolutionZerothOrderOn_sub_skew_const_iff hk).2 hbase
  have hnormalized : IsMatrixDivFormWeakSolutionZerothOrderOn aF W uW
      (fun x => nu⁻¹ * g x) 0 :=
    isMatrixDivFormWeakSolutionZerothOrderOn_smul_coeff hfrozen
  have hztW : LocalizedZeroTraceFunctionOn W (euclideanBall x₀ R)
      u.toH1Function.toFun := by
    refine localizedZeroTraceFunctionOn_of_memH10_of_inter_subset hWopen hWQ ?_ u
    intro y hy
    rw [← hWeq]
    exact ⟨hy.1, hy.2⟩
  have hgW : MemLp g 2 (volume.restrict W) :=
    memScalarL2_of_memScalarLInfOn_of_subset hWQ hg
  have hgFW : MemLp (fun x => nu⁻¹ * g x) 2 (volume.restrict W) := hgW.const_mul _
  have hgFM : ∀ᵐ y ∂volume.restrict W, |nu⁻¹ * g y| ≤ nu⁻¹ * M := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hWQ hgM] with y hy
    rw [abs_mul, abs_of_pos (inv_pos.2 hnu)]
    exact mul_le_mul_of_nonneg_left hy (inv_pos.2 hnu).le
  have hMF : (0 : ℝ) ≤ nu⁻¹ * M := mul_nonneg (inv_pos.2 hnu).le hM
  have hEllW : IsEllipticFieldOn 1 ((1 + delta) ^ 2) W aF :=
    isEllipticFieldOn_normalizedFrozenCoeff hWopen.measurableSet hnu hsymm hcont
      (hWQ.trans (axisCube_subset_closureSet z L)) x₀ hdelta0 hboundW
  have hfluxW : ∀ j : Fin d,
      MemLp (fun y => matVecMul (aF y) (uW.grad y) j) 2 (volume.restrict W) := by
    have hvec : MemVectorL2 W (fun y => matVecMul (aF y) (uW.grad y)) :=
      memVectorL2_matVecMul_of_isEllipticFieldOn hEllW uW.grad_memVectorL2
    exact fun j => memLp_pi_iff.1 hvec j
  -- unfold oddly to the whole ball
  obtain ⟨w, b, h, hbmeas, hbcontrast, hhLinf, hweq, hwpin, hwodd⟩ :=
    exists_oddReflection_weakSolution_ball hR hsigma hMF haFmeas hcontrastW uW
      hztW hgFW hgFM hfluxW hnormalized
  obtain ⟨V, hVcont, hVae, -⟩ :=
    schauder_holder_euclideanBall_zerothOrder x₀ hR hd
      (by norm_num : (1 / 2 : ℝ) ∈ Set.Ico (1 / 2 : ℝ) 1) hdelta0 le_rfl hbmeas
      hbcontrast hweq hhLinf
  -- oddness of the continuous representative
  have hglobalAE : ∀ᵐ y ∂(volume : Measure (Vec d)),
      y ∈ euclideanBall x₀ R → V y = w.toFun y :=
    (ae_restrict_iff' (isOpen_euclideanBall x₀ R).measurableSet).1 hVae
  have hhalfSub : euclideanBall x₀ (R / 2) ⊆ euclideanBall x₀ R :=
    euclideanBall_subset_euclideanBall (by positivity) (by linarith only [hR])
  have hoddV : ∀ j ∈ S, ∀ y ∈ euclideanBall x₀ (R / 2),
      V (coordFaceReflection (x₀ j) j y) = -V y := by
    intro j hj
    have hballSymm := mem_euclideanBall_coordFaceReflection_center_iff x₀ (R / 2) j
    have hmaps : Set.MapsTo (coordFaceReflection (x₀ j) j)
        (euclideanBall x₀ (R / 2)) (euclideanBall x₀ (R / 2)) := by
      intro y hy
      exact (hballSymm y).2 hy
    have hcont2 : ContinuousOn (fun y => -V (coordFaceReflection (x₀ j) j y))
        (euclideanBall x₀ (R / 2)) :=
      (hVcont.comp (continuous_coordFaceReflection (x₀ j) j).continuousOn hmaps).neg
    have hreflAE : ∀ᵐ y ∂(volume : Measure (Vec d)),
        coordFaceReflection (x₀ j) j y ∈ euclideanBall x₀ R →
          V (coordFaceReflection (x₀ j) j y) =
            w.toFun (coordFaceReflection (x₀ j) j y) :=
      (measurePreserving_coordFaceReflection (x₀ j) j).quasiMeasurePreserving.ae
        hglobalAE
    have hae : (fun y => V (coordFaceReflection (x₀ j) j y))
        =ᵐ[volume.restrict (euclideanBall x₀ (R / 2))] fun y => -V y := by
      filter_upwards [ae_restrict_mem (isOpen_euclideanBall x₀ (R / 2)).measurableSet,
        ae_restrict_of_ae hglobalAE, ae_restrict_of_ae hreflAE]
        with y hy hyval hyrefl
      have hyR : y ∈ euclideanBall x₀ R := hhalfSub hy
      have hryhalf : coordFaceReflection (x₀ j) j y ∈ euclideanBall x₀ (R / 2) :=
        hmaps hy
      rw [hyrefl (hhalfSub hryhalf), hwodd j hj y, hyval hyR]
    have heqOn := eqOn_of_continuousOn_of_ae_eq (isOpen_euclideanBall x₀ (R / 2))
      (hVcont.comp (continuous_coordFaceReflection (x₀ j) j).continuousOn hmaps)
      (hVcont.neg) hae
    intro y hy
    exact heqOn hy
  refine ⟨R / 2, by positivity, V, hVcont.mono le_rfl, ?_, ?_⟩
  · have hsub : euclideanBall x₀ (R / 2) ∩ axisCube z L ⊆ W := by
      intro y hy
      rw [← hWeq]
      exact ⟨hhalfSub hy.1, hy.2⟩
    have hsubR : euclideanBall x₀ (R / 2) ∩ axisCube z L ⊆ euclideanBall x₀ R :=
      fun y hy => hhalfSub hy.1
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsubR hVae,
      ae_restrict_mem ((isOpen_euclideanBall x₀ (R / 2)).measurableSet.inter
        (isOpen_axisCube z L).measurableSet)] with y hy hymem
    rw [hy]
    exact hwpin y (hsub hymem)
  · intro y hy hyC hyQ
    have hex : ∃ i : Fin d, y i = z i ∨ y i = z i + L := by
      by_contra hcon
      push Not at hcon
      refine hyQ (mem_axisCube_iff.2 fun i => ⟨?_, ?_⟩)
      · exact lt_of_le_of_ne (hyC i).1 (Ne.symm (hcon i).1)
      · exact lt_of_le_of_ne (hyC i).2 (hcon i).2
    obtain ⟨i, hi⟩ := hex
    have hcoord : |y i - x₀ i| < R / 2 := by
      have hball := HCPolySupport.euclideanBall_subset_metricBall (by positivity) hy
      have hpi : dist (y i) (x₀ i) ≤ dist y x₀ := dist_le_pi_dist y x₀ i
      have hlt : dist y x₀ < R / 2 := hball
      rw [Real.dist_eq] at hpi
      linarith only [hpi, hlt]
    have hxi : y i = x₀ i := by
      rcases hi with hlow | hhigh
      · by_cases hxlow : x₀ i = z i
        · rw [hlow, hxlow]
        · have hcl := hclear.1 i hxlow
          rw [hlow] at hcoord
          rw [abs_lt] at hcoord
          linarith only [hcl, hcoord.1, hR]
      · by_cases hxhigh : x₀ i = z i + L
        · rw [hhigh, hxhigh]
        · have hcl := hclear.2 i hxhigh
          rw [hhigh] at hcoord
          rw [abs_lt] at hcoord
          linarith only [hcl, hcoord.2, hR]
    have hiS : i ∈ S := by
      rw [hSdef, mem_axisCubeFaceSet_iff, ← hxi]
      exact hi
    have hfix : coordFaceReflection (x₀ i) i y = y :=
      coordFaceReflection_eq_self hxi
    have hodd := hoddV i hiS y hy
    rw [hfix] at hodd
    linarith only [hodd]

end

end Algsuperdiff.StochasticProcess.Common.Regularity.Freezing
