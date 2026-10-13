/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.Decay.LocalizedInteriorMass
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.Decay.LocalizedTailFreezing

/-!
# LocalizedInteriorPointwise

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Frozen pointwise decay for bounded interior solutions

The weighted half reads the skew constants only on `tsupport eta`.  The
pointwise half freezes the coefficient on a separate small ball about the
evaluation point.
-/

noncomputable section

namespace DivergenceFormProcess.Decay

open HCPolySupport MeasureTheory
open DivergenceFormProcess.Form
open Algsuperdiff.StochasticProcess.Common.Regularity.Ported
open Algsuperdiff.StochasticProcess.Common.Regularity.Freezing
open scoped ENNReal

variable {d : ℕ}

/-- Explicit constant in the localized interior pointwise estimate. -/
def localizedInteriorDecayConstant (d : ℕ) (nu mass Ks Kl M Ceta volLayer alpha E r₀ : ℝ) : ℝ :=
  let L := localizedInteriorUpper nu mass Ks Kl
  M * Real.sqrt (8 * L ^ 2 / (nu * mass) * Ceta * volLayer) /
        Real.sqrt ((volume (smallContrastUnitBall d)).toReal) /
        Real.sqrt ((r₀ / 2) ^ d) +
      smallContrastZerothSchauderConstant d *
          (r₀ ^ (1 - alpha - (d : ℝ) / 2) * E +
            r₀ ^ (2 - alpha) * (mass * M / nu)) *
        (r₀ / 2) ^ alpha

private theorem isScalarForcedWeakSolution_const_smul_interior
    {W : Set (Vec d)} {c : ℝ} {a : CoeffField d}
    {u : H1Function W} {g : Vec d → ℝ}
    (hu : IsScalarForcedWeakSolution a W g u) :
    IsScalarForcedWeakSolution (fun x => c • a x) W (fun x => c * g x) u := by
  refine ⟨?_, fun phi => ?_⟩
  · simpa only [Pi.smul_apply, smul_eq_mul] using! hu.1.const_smul c
  · have h := hu.2 phi
    have hleft :
        (∫ x in W, vecDot (matVecMul (c • a x) (u.grad x))
            (phi.toH1Function.grad x) ∂volume) =
          c * ∫ x in W, vecDot (matVecMul (a x) (u.grad x))
            (phi.toH1Function.grad x) ∂volume := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      simp only [smul_matVecMul, vecDot_smul_left]
    have hright :
        (∫ x in W, (c * g x) * phi.toH1Function.toFun x ∂volume) =
          c * ∫ x in W, g x * phi.toH1Function.toFun x ∂volume := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      ring
    rw [hleft, hright, h]

private theorem isScalarForcedWeakSolution_restrict_interior
    {W V : Set (Vec d)} (hW : IsOpen W) (hV : IsOpen V) (hVW : V ⊆ W)
    {a : CoeffField d} {u : H1Function W} {g : Vec d → ℝ}
    (hu : IsScalarForcedWeakSolution a W g u) :
    IsScalarForcedWeakSolution a V g (u.restrict hV hVW) := by
  refine ⟨hu.1.mono_measure (Measure.restrict_mono hVW le_rfl), fun phi => ?_⟩
  have h := zerothOrderOn_restrict_of_isScalarForcedWeakSolution hW hV hVW hu phi
  simpa only [Pi.zero_apply, vecDot_zero_left, integral_zero, sub_zero] using h

private theorem localizedInteriorPointwise_comparisonBounds1 :
    ∀ {d : ℕ} {Om : Set (Vec d)} (hOm : IsOpenBoundedConvexDomain Om) {u : H1Function Om} {eta psi
      : Vec d → ℝ}
      {nu Ks Kl mass M Ceta volLayer tA : ℝ} (_ : (0 : ℝ) < nu) (_ : (0 : ℝ) < mass) (_ : (0 : ℝ)
        ≤ M)
      (_ : ∀ᵐ (y : Vec d) ∂volumeMeasureOn Om, |u.toFun y| ≤ M) (_ : (0 : ℝ) ≤ Ceta)
      (_ : ∀ y ∈ Om, (vecNormSq fun (i : Fin d) => (fderiv ℝ eta y : (a : Vec d) → ℝ) (basisVec
        i)) ≤ Ceta)
      (_ : ∀ y ∈ Om, fderiv ℝ eta y ≠ (0 : Vec d →L[ℝ] ℝ) → psi y ≤ tA)
      (_ :
        ((volume : (a : Set (Vec d)) → ℝ≥0∞) {y : Vec d | y ∈ Om ∧ fderiv ℝ eta y ≠ (0 : Vec d →L[ℝ]
          ℝ)}).toReal ≤
          volLayer),
      let Lloc : ℝ := localizedInteriorUpper nu mass Ks Kl;
      ∀ (_ : Lloc = localizedInteriorUpper nu mass Ks Kl),
        let kappa : ℝ := agmonRate nu Lloc mass;
        ∀ (_ : (0 : ℝ) < Lloc) (_ : (0 : ℝ) ≤ kappa)
          (_ :
            mass / (2 : ℝ) *
                ∫ (y : Vec d) in Om, u.toFun y ^ (2 : ℕ) * (eta y ^ (2 : ℕ) * Real.exp (kappa *
                  psi y) ^ (2 : ℕ)) ≤
              (4 : ℝ) * localizedInteriorUpper nu mass Ks Kl ^ (2 : ℕ) / nu *
                ∫ (y : Vec d) in Om,
                  u.toFun y ^ (2 : ℕ) *
                    (Real.exp (kappa * psi y) ^ (2 : ℕ) *
                      vecNormSq fun (i : Fin d) => (fderiv ℝ eta y : (a : Vec d) → ℝ) (basisVec
                        i))),
          let _ : IsFiniteMeasure (volumeMeasureOn Om) :=
            IsBoundedDomain.isFiniteMeasure_restrict_volume
              (IsOpenBoundedConvexDomain.isBoundedDomain hOm);
          ∀ (_ : MeasurableSet {y : Vec d | y ∈ Om ∧ fderiv ℝ eta y ≠ (0 : Vec d →L[ℝ] ℝ)})
            (_ :
              MemLp
                (fun (y : Vec d) =>
                  Real.exp (kappa * psi y) ^ (2 : ℕ) *
                    vecNormSq fun (i : Fin d) => (fderiv ℝ eta y : (a : Vec d) → ℝ) (basisVec i))
                ∞ (volumeMeasureOn Om)),
            ∫ (y : Vec d) in Om, u.toFun y ^ (2 : ℕ) * (eta y ^ (2 : ℕ) * Real.exp (kappa * psi y)
              ^ (2 : ℕ)) ≤
              (8 : ℝ) * Lloc ^ (2 : ℕ) / (nu * mass) * Ceta * volLayer * M ^ (2 : ℕ) * Real.exp
                ((2 : ℝ) * (kappa * tA)) := by
  intro d Om hOm u eta psi nu _ _ mass M Ceta volLayer tA _ _ hM hMbound hCeta hetaGrad hlayer
    hvolLayer Lloc hLloc_def kappa _ hkappa0 hagmon this hlayerMeas hlayerTop
  have hlayerInt := integrable_sq_mul_memLpTop (u := u) hlayerTop
  have hlayerBound : (∫ y in Om, u.toFun y ^ 2 *
      (Real.exp (kappa * psi y) ^ 2 *
        vecNormSq (fun i => (fderiv ℝ eta y) (basisVec i))) ∂volume) ≤
      M ^ 2 * Ceta * Real.exp (2 * (kappa * tA)) * volLayer := by
    have hconst : Integrable
        ({y ∈ Om | fderiv ℝ eta y ≠ 0}.indicator
          (fun _ : Vec d => M ^ 2 * Ceta * Real.exp (2 * (kappa * tA))))
        (volumeMeasureOn Om) := (integrable_const _).indicator hlayerMeas
    have hmem : ∀ᵐ y ∂volumeMeasureOn Om, y ∈ Om :=
      (ae_restrict_iff' hOm.isOpen.measurableSet).2
        (Filter.Eventually.of_forall fun _ hy => hy)
    have hmono : (∫ y, u.toFun y ^ 2 *
        (Real.exp (kappa * psi y) ^ 2 *
          vecNormSq (fun i => (fderiv ℝ eta y) (basisVec i)))
          ∂volumeMeasureOn Om) ≤
        ∫ y, {y ∈ Om | fderiv ℝ eta y ≠ 0}.indicator
          (fun _ : Vec d => M ^ 2 * Ceta * Real.exp (2 * (kappa * tA))) y
          ∂volumeMeasureOn Om := by
      refine integral_mono_ae hlayerInt hconst ?_
      filter_upwards [hMbound, hmem] with y hu hyOm
      by_cases hzero : fderiv ℝ eta y = 0
      · rw [Set.indicator_of_notMem (show y ∉
            {z ∈ Om | fderiv ℝ eta z ≠ 0} from fun hy => hy.2 hzero)]
        have hgrad0 : (fun i => (fderiv ℝ eta y) (basisVec i)) =
            fun _ : Fin d => (0 : ℝ) := by
          funext i
          rw [hzero]
          exact zero_apply (basisVec i)
        rw [hgrad0]
        simp only [vecNormSq, vecDot, mul_zero, Finset.sum_const_zero]
        exact le_rfl
      · rw [Set.indicator_of_mem
          (show y ∈ {z ∈ Om | fderiv ℝ eta z ≠ 0} from ⟨hyOm, hzero⟩)]
        have hu2 : u.toFun y ^ 2 ≤ M ^ 2 := by
          have habs := abs_le_abs_of_nonneg (abs_nonneg (u.toFun y)) hu
          nlinarith only [hu, habs, abs_nonneg (u.toFun y),
            sq_abs (u.toFun y), hM]
        have hexp : Real.exp (kappa * psi y) ^ 2 ≤
            Real.exp (2 * (kappa * tA)) := by
          rw [show Real.exp (kappa * psi y) ^ 2 =
            Real.exp (2 * (kappa * psi y)) by rw [sq, ← Real.exp_add]; congr 1; ring]
          exact Real.exp_le_exp.2 (by
            have := mul_le_mul_of_nonneg_left (hlayer y hyOm hzero) hkappa0
            linarith only [this])
        have hgrad := hetaGrad y hyOm
        have hgnn : (0 : ℝ) ≤
            vecNormSq (fun i => (fderiv ℝ eta y) (basisVec i)) :=
          vecNormSq_nonneg _
        have hexpnn : (0 : ℝ) < Real.exp (kappa * psi y) ^ 2 := by positivity
        calc
          u.toFun y ^ 2 * (Real.exp (kappa * psi y) ^ 2 *
              vecNormSq (fun i => (fderiv ℝ eta y) (basisVec i))) ≤
              M ^ 2 * (Real.exp (2 * (kappa * tA)) * Ceta) := by
            have h1 : Real.exp (kappa * psi y) ^ 2 *
                vecNormSq (fun i => (fderiv ℝ eta y) (basisVec i)) ≤
                Real.exp (2 * (kappa * tA)) * Ceta :=
              mul_le_mul hexp hgrad hgnn (Real.exp_pos _).le
            exact mul_le_mul hu2 h1 (mul_nonneg hexpnn.le hgnn) (sq_nonneg M)
          _ = M ^ 2 * Ceta * Real.exp (2 * (kappa * tA)) := by ring
    rw [integral_indicator hlayerMeas, setIntegral_const] at hmono
    have hmeasure : (volumeMeasureOn Om).real
        {y ∈ Om | fderiv ℝ eta y ≠ 0} =
        (volume {y ∈ Om | fderiv ℝ eta y ≠ 0}).toReal := by
      rw [measureReal_def, Measure.restrict_apply hlayerMeas,
        Set.inter_eq_left.mpr fun _ hy => hy.1]
    rw [hmeasure, smul_eq_mul] at hmono
    have hcnn : (0 : ℝ) ≤ M ^ 2 * Ceta * Real.exp (2 * (kappa * tA)) :=
      mul_nonneg (mul_nonneg (sq_nonneg M) hCeta) (Real.exp_pos _).le
    have hfinal := mul_le_mul_of_nonneg_right hvolLayer hcnn
    linarith only [hmono, hfinal]
  have hweightBound : (∫ y in Om, u.toFun y ^ 2 *
      (eta y ^ 2 * Real.exp (kappa * psi y) ^ 2) ∂volume) ≤
      8 * Lloc ^ 2 / (nu * mass) * Ceta * volLayer * M ^ 2 *
        Real.exp (2 * (kappa * tA)) := by
    have hagmon' : mass / 2 * (∫ y in Om, u.toFun y ^ 2 *
        (eta y ^ 2 * Real.exp (kappa * psi y) ^ 2) ∂volume) ≤
        4 * Lloc ^ 2 / nu * (∫ y in Om, u.toFun y ^ 2 *
          (Real.exp (kappa * psi y) ^ 2 *
            vecNormSq (fun i => (fderiv ℝ eta y) (basisVec i))) ∂volume) := by
      simpa only [hLloc_def] using hagmon
    have hstep := hagmon'.trans (mul_le_mul_of_nonneg_left hlayerBound
      (by positivity : (0 : ℝ) ≤ 4 * Lloc ^ 2 / nu))
    have hmass2 : 0 < mass / 2 := by positivity
    have hX : (∫ y in Om, u.toFun y ^ 2 *
        (eta y ^ 2 * Real.exp (kappa * psi y) ^ 2) ∂volume) ≤
        (4 * Lloc ^ 2 / nu *
          (M ^ 2 * Ceta * Real.exp (2 * (kappa * tA)) * volLayer)) /
            (mass / 2) := by
      rw [le_div_iff₀ hmass2]
      linarith only [hstep]
    refine hX.trans (le_of_eq ?_)
    field_simp
    ring
  exact hweightBound

/-- Frozen pointwise decay of a bounded homogeneous `H¹` solution.  The
rough size and smooth divergence are required only on an active set containing
the topological support of the localization. -/
theorem interior_abs_center_le_exp_localized [NeZero d]
    {a : CoeffField d} {ks kl : Vec d → Mat d} {Om : Set (Vec d)}
    (hOm : IsOpenBoundedConvexDomain Om) {u : H1Function Om}
    {eta psi : Vec d → ℝ} {L : Set (Vec d)}
    {nu LamS Ks Kl mass M Ceta volLayer delta alpha tA tx E : ℝ}
    (hd : 2 ≤ d) (halpha : alpha ∈ Set.Ico (1 / 2 : ℝ) 1)
    (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ smallContrastThreshold d alpha)
    (hnu : 0 < nu) (hKs : 0 ≤ Ks) (hKl : 0 ≤ Kl) (hmass : 0 < mass)
    (hM : 0 ≤ M) (hameas : Measurable a)
    (hEllS : IsEllipticFieldOn nu LamS Om
      (fun y => nu • (1 : Mat d) + ks y))
    (hsplit : ∀ y, a y = nu • (1 : Mat d) + ks y + kl y)
    (hksSkew : ∀ y, matTranspose (ks y) = -ks y)
    (hklSkew : ∀ y, matTranspose (kl y) = -kl y)
    (hklC1 : ∀ p q : Fin d, ContDiff ℝ 1 fun y => kl y p q)
    (hsol : IsScalarForcedWeakSolution a Om (fun y => -(mass * u.toFun y)) u)
    (hMbound : ∀ᵐ y ∂volumeMeasureOn Om, |u.toFun y| ≤ M)
    (heta : ContDiff ℝ (⊤ : ℕ∞) eta) (hetaCompact : HasCompactSupport eta)
    (hetaOm : tsupport eta ⊆ Om) (hetaL : tsupport eta ⊆ L)
    (hCeta : 0 ≤ Ceta)
    (hetaGrad : ∀ y ∈ Om,
      vecNormSq (fun i => (fderiv ℝ eta y) (basisVec i)) ≤ Ceta)
    (hlayer : ∀ y ∈ Om, fderiv ℝ eta y ≠ 0 → psi y ≤ tA)
    (hvolLayer : (volume {y ∈ Om | fderiv ℝ eta y ≠ 0}).toReal ≤ volLayer)
    (hpsi : ContDiff ℝ (⊤ : ℕ∞) psi)
    (hpsiGrad : ∀ᵐ y ∂volumeMeasureOn Om,
      vecNormSq (fun i => (fderiv ℝ psi y) (basisVec i)) ≤ 1)
    (hksSize : ∀ y ∈ L, ∀ v : Vec d,
      vecNormSq (matVecMul (ks y) v) ≤ Ks ^ 2 * vecNormSq v)
    (hklDiv : ∀ y ∈ L, vecNormSq (skewFieldDiv kl y) ≤ Kl ^ 2)
    {x : Vec d} {r₀ : ℝ} (hr₀ : 0 < r₀) (hball : euclideanBall x r₀ ⊆ Om)
    (hsmall : CoefficientIdentityDistanceLE (euclideanBall x r₀)
      (normalizedFrozenCoeff nu a x) delta)
    (hE : vectorLpSizeOn (euclideanBall x r₀) 2 u.grad ≤ E)
    (hinner : ∀ y ∈ euclideanBall x (r₀ / 2), eta y = 1)
    (hphase : ∀ y ∈ euclideanBall x (r₀ / 2), tx ≤ psi y)
    (hlayerLe : tA ≤ tx) :
    ∃ v : Vec d → ℝ,
      ContinuousOn v (euclideanBall x (r₀ / 2)) ∧
      v =ᵐ[volume.restrict (euclideanBall x r₀)] u.toFun ∧
      |v x| ≤ localizedInteriorDecayConstant d nu mass Ks Kl M Ceta
          volLayer alpha E r₀ *
        Real.exp (-(agmonRate nu (localizedInteriorUpper nu mass Ks Kl) mass *
          alpha / (alpha + (d : ℝ) / 2) * (tx - tA))) := by
  classical
  set Lloc := localizedInteriorUpper nu mass Ks Kl with hLloc_def
  set kappa := agmonRate nu Lloc mass with hkappa_def
  have hLloc : 0 < Lloc := localizedInteriorUpper_pos hnu hKs hKl
  have hkappa0 : 0 ≤ kappa := agmonRate_nonneg hLloc
  have hkappa : 8 * Lloc ^ 2 * kappa ^ 2 ≤ nu * mass :=
    agmonRate_admissible' hnu.le hmass.le hLloc
  have hsign : ∀ᵐ y ∂volumeMeasureOn Om, eta y ≠ 0 →
      (-(mass * u.toFun y)) * u.toFun y ≤ -(mass * u.toFun y ^ 2) := by
    filter_upwards with y
    intro _
    have heq : (-(mass * u.toFun y)) * u.toFun y =
        -(mass * u.toFun y ^ 2) := by ring
    exact heq.le
  have hagmon := agmonMass_localizedInterior_le hOm hnu hKs hKl hmass hM
    hEllS hsplit hksSkew hklSkew hklC1 hsol hMbound heta hetaCompact hetaOm
    hetaL hpsi hpsiGrad hsign hksSize hklDiv (by simpa only [hLloc_def] using hkappa)
  have hvol0 : (0 : ℝ) ≤ volLayer := le_trans ENNReal.toReal_nonneg hvolLayer
  let : IsFiniteMeasure (volumeMeasureOn Om) :=
    hOm.isBoundedDomain.isFiniteMeasure_restrict_volume
  have hlayerMeas : MeasurableSet {y ∈ Om | fderiv ℝ eta y ≠ 0} := by
    exact hOm.isOpen.measurableSet.inter
      (isOpen_ne.preimage (heta.continuous_fderiv (by simp))).measurableSet
  have hlayerTop : MemLp (fun y => Real.exp (kappa * psi y) ^ 2 *
      vecNormSq (fun i => (fderiv ℝ eta y) (basisVec i))) ∞
        (volumeMeasureOn Om) := by
    refine (Continuous.memLp_of_hasCompactSupport ?_ ?_).restrict Om
    · exact ((contDiff_exponentialWeight hpsi kappa).continuous.pow 2).mul
        (continuous_gradSq heta)
    · exact (hasCompactSupport_gradSq hetaCompact).mul_left
  have hweightBound : (∫ y in Om, u.toFun y ^ 2 *
      (eta y ^ 2 * Real.exp (kappa * psi y) ^ 2) ∂volume) ≤
      8 * Lloc ^ 2 / (nu * mass) * Ceta * volLayer * M ^ 2 *
        Real.exp (2 * (kappa * tA)) :=
    @localizedInteriorPointwise_comparisonBounds1 (d) (Om) (hOm) (u) (eta) (psi) (nu) (Ks) (Kl)
      (mass) (M) (Ceta) (volLayer) (tA) (hnu) (hmass) (hM) (hMbound) (hCeta) (hetaGrad) (hlayer)
        (hvolLayer) (hLloc_def) (hLloc) (hkappa0) (hagmon) (hlayerMeas) (hlayerTop)
  have hweightTop : MemLp (fun y => eta y ^ 2 * Real.exp (kappa * psi y) ^ 2)
      ∞ (volumeMeasureOn Om) := by
    have hetaSq : HasCompactSupport (fun y => eta y ^ 2) := by
      simpa only [pow_two] using! hetaCompact.mul_left (f := eta)
    refine (Continuous.memLp_of_hasCompactSupport ?_ ?_).restrict Om
    · exact (heta.continuous.pow 2).mul
        ((contDiff_exponentialWeight hpsi kappa).continuous.pow 2)
    · exact hetaSq.mul_right
  have hweightInt := integrable_sq_mul_memLpTop (u := u) hweightTop
  have hsqInt : IntegrableOn (fun y => u.toFun y ^ 2) Om := by
    apply (u.memL2.integrable_mul u.memL2).congr
    filter_upwards with y
    simp only [Pi.mul_apply]
    ring
  set D := M * Real.sqrt (8 * Lloc ^ 2 / (nu * mass) * Ceta * volLayer)
  have hD0 : 0 ≤ D := mul_nonneg hM (Real.sqrt_nonneg _)
  have hrad : ∀ rho : ℝ, 0 < rho → rho ≤ r₀ / 2 →
      (∫ y in euclideanBall x rho, u.toFun y ^ 2 ∂volume) ≤
        D ^ 2 * Real.exp (-(2 * (kappa * (tx - tA)))) := by
    intro rho hrho hrhoHalf
    have hsubHalf : euclideanBall x rho ⊆ euclideanBall x (r₀ / 2) :=
      Algsuperdiff.Section4.Provider.Schauder.euclideanBall_mono hrho.le hrhoHalf
    have hsubOm : euclideanBall x rho ⊆ Om := hsubHalf.trans
      ((Algsuperdiff.Section4.Provider.Schauder.euclideanBall_mono
        (by positivity : 0 ≤ r₀ / 2) (by linarith only [hr₀])).trans hball)
    have hstep := setIntegral_sq_le_exp_mul_localizedWeight hsubOm
      (isOpen_euclideanBall x rho).measurableSet (w := u.toFun) (eta := eta)
      (psi := psi) (kappa := kappa) (t := tx) hkappa0
      (fun y hy => by rw [hinner y (hsubHalf hy)]; norm_num)
      (fun y hy => hphase y (hsubHalf hy)) hsqInt hweightInt
    have hcombine := hstep.trans
      (mul_le_mul_of_nonneg_left hweightBound (Real.exp_pos _).le)
    refine hcombine.trans (le_of_eq ?_)
    have hroot : D ^ 2 = M ^ 2 *
        (8 * Lloc ^ 2 / (nu * mass) * Ceta * volLayer) := by
      change (M * Real.sqrt
        (8 * Lloc ^ 2 / (nu * mass) * Ceta * volLayer)) ^ 2 = _
      rw [mul_pow, Real.sq_sqrt]
      exact mul_nonneg (mul_nonneg (by positivity) hCeta) hvol0
    have hexpid : Real.exp (-(2 * kappa * tx)) *
        Real.exp (2 * (kappa * tA)) =
        Real.exp (-(2 * (kappa * (tx - tA)))) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hroot]
    calc
      Real.exp (-(2 * kappa * tx)) *
          (8 * Lloc ^ 2 / (nu * mass) * Ceta * volLayer * M ^ 2 *
            Real.exp (2 * (kappa * tA))) =
          (Real.exp (-(2 * kappa * tx)) * Real.exp (2 * (kappa * tA))) *
            (M ^ 2 * (8 * Lloc ^ 2 / (nu * mass) * Ceta * volLayer)) := by ring
      _ = M ^ 2 * (8 * Lloc ^ 2 / (nu * mass) * Ceta * volLayer) *
          Real.exp (-(2 * (kappa * (tx - tA)))) := by
        rw [hexpid]
        ring
  let B := euclideanBall x r₀
  have hBopen : IsOpen B := isOpen_euclideanBall x r₀
  let uB := u.restrict hBopen hball
  have hsolB : IsScalarForcedWeakSolution a B (fun y => -(mass * u.toFun y)) uB :=
    isScalarForcedWeakSolution_restrict_interior hOm.isOpen hBopen hball hsol
  have hsymmx : symmPart (a x) = nu • (1 : Mat d) :=
    symmPart_eq_of_splitSkew (hsplit x) (hksSkew x) (hklSkew x)
  have hk : matTranspose (a x - nu • (1 : Mat d)) =
      -(a x - nu • (1 : Mat d)) := sub_scalar_one_isSkew_of_symmPart_eq hsymmx
  have hfrozen := (isScalarForcedWeakSolution_sub_skew_const hk).2 hsolB
  have hnormalized : IsScalarForcedWeakSolution (normalizedFrozenCoeff nu a x) B
      (fun y => nu⁻¹ * (-(mass * u.toFun y))) uB := by
    simpa only [normalizedFrozenCoeff] using!
      isScalarForcedWeakSolution_const_smul_interior (c := nu⁻¹) hfrozen
  have hnormalizedMeas : Measurable (normalizedFrozenCoeff nu a x) := by
    refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
    change Measurable fun y => nu⁻¹ *
      (a y i j - (a x - nu • (1 : Mat d)) i j)
    exact (((measurable_pi_apply j).comp
      ((measurable_pi_apply i).comp hameas)).sub measurable_const).const_mul _
  have hG : 0 ≤ mass * M / nu := by positivity
  have hgb : ∀ᵐ y ∂volumeMeasureOn B,
      |nu⁻¹ * (-(mass * u.toFun y))| ≤ mass * M / nu := by
    filter_upwards [hMbound.filter_mono (ae_mono (Measure.restrict_mono hball le_rfl))]
      with y hy
    have hcoef : 0 ≤ mass / nu := by positivity
    calc
      |nu⁻¹ * (-(mass * u.toFun y))| = mass / nu * |u.toFun y| := by
        rw [abs_mul, abs_neg, abs_mul, abs_of_pos hmass,
          abs_of_pos (inv_pos.2 hnu), inv_eq_one_div]
        field_simp
      _ ≤ mass / nu * M := mul_le_mul_of_nonneg_left hy hcoef
      _ = mass * M / nu := by ring
  have hradB : ∀ rho : ℝ, 0 < rho → rho ≤ r₀ / 2 →
      (∫ y in euclideanBall x rho, uB.toFun y ^ 2 ∂volume) ≤
        D ^ 2 * Real.exp (-(2 * (kappa * (tx - tA)))) := by
    intro rho hrho hrhoHalf
    change (∫ y in euclideanBall x rho, u.toFun y ^ 2 ∂volume) ≤ _
    exact hrad rho hrho hrhoHalf
  have hE' : vectorLpSizeOn B 2 uB.grad ≤ E := by
    change vectorLpSizeOn B 2 u.grad ≤ E
    simpa only [B] using hE
  rw [localizedInteriorDecayConstant]
  have hpoint := exists_representative_abs_center_le_exp hBopen hd halpha
    hdelta0 hdelta hnormalizedMeas hsmall hnormalized hr₀ (fun _ hy => hy)
    hG hgb hE' hkappa0 (by linarith only [hlayerLe]) hD0 hradB
  simpa only [Lloc, kappa, B, uB] using! hpoint

end DivergenceFormProcess.Decay
