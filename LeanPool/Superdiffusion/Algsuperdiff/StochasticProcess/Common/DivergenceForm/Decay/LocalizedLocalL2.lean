/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.Decay.LocalizedWeightedEnergy
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.Decay.WeightedToBall

/-!
# LocalizedLocalL2

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Local `L²` and gradient bounds with layer constants

The two consequences of the weighted energy estimate that the pointwise step
consumes are restated so that the coefficient enters only on the transition
layer of the localization.

* the exponentially weighted mass on an inner ball, from which the plain local
  `L²` bound is read;
* the Caccioppoli gradient bound on an inner ball.

Both are obtained from a weighted energy inequality supplied as a hypothesis,
so the same proofs serve the estimate with a single antisymmetric part and the
estimate with a split antisymmetric part.

## Main results

- `DivergenceFormProcess.Decay.setIntegral_sq_mul_exp_gradSq_layer_le`
- `DivergenceFormProcess.Decay.setIntegral_sq_le_exp_of_agmonMass`
- `DivergenceFormProcess.Decay.setIntegral_gradSq_le_of_localizedBound`
-/

noncomputable section

namespace DivergenceFormProcess.Decay

open HCPolySupport MeasureTheory
open DivergenceFormProcess.Form
open scoped ENNReal

variable {d : ℕ}

/-! ### The layer term -/

/-- The exponentially weighted layer term is paid for by the maximum bound,
the gradient bound of the localization, the phase on the layer and the volume
of the layer. -/
theorem setIntegral_sq_mul_exp_gradSq_layer_le {Om : Set (Vec d)}
    (hOmOpen : IsOpen Om) (hOmBdd : IsBoundedDomain Om)
    {u : H1Function Om} {eta psi : Vec d → ℝ}
    {kappa M Ceta volLayer tA : ℝ}
    (hMbound : ∀ᵐ y ∂volumeMeasureOn Om, |u.toFun y| ≤ M)
    (heta : ContDiff ℝ (⊤ : ℕ∞) eta) (hetaCompact : HasCompactSupport eta)
    (hpsi : ContDiff ℝ (⊤ : ℕ∞) psi) (hCeta : 0 ≤ Ceta)
    (hetaGrad : ∀ y ∈ Om,
      vecNormSq (fun i => (fderiv ℝ eta y) (basisVec i)) ≤ Ceta)
    (hlayer : ∀ y ∈ Om, fderiv ℝ eta y ≠ 0 → psi y ≤ tA)
    (hvolLayer : (volume {y ∈ Om | fderiv ℝ eta y ≠ 0}).toReal ≤ volLayer)
    (hkappa0 : 0 ≤ kappa) :
    (∫ y in Om, u.toFun y ^ 2 *
        (Real.exp (kappa * psi y) ^ 2 *
          vecNormSq (fun i => (fderiv ℝ eta y) (basisVec i))) ∂volume) ≤
      M ^ 2 * Ceta * Real.exp (2 * (kappa * tA)) * volLayer := by
  classical
  have : IsFiniteMeasure (volumeMeasureOn Om) :=
    hOmBdd.isFiniteMeasure_restrict_volume
  have hchi : ContDiff ℝ (⊤ : ℕ∞) (fun y => Real.exp (kappa * psi y)) :=
    contDiff_exponentialWeight hpsi kappa
  have hlayerTop : MemLp (fun y => Real.exp (kappa * psi y) ^ 2 *
      vecNormSq (fun i => (fderiv ℝ eta y) (basisVec i))) ∞
        (volumeMeasureOn Om) := by
    refine (Continuous.memLp_of_hasCompactSupport ?_ ?_).restrict Om
    · exact (hchi.continuous.pow 2).mul (continuous_gradSq heta)
    · exact (hasCompactSupport_gradSq hetaCompact).mul_left
  have hlayerInt := integrable_sq_mul_memLpTop (u := u) hlayerTop
  have hvolLayer0 : (0 : ℝ) ≤ volLayer :=
    le_trans ENNReal.toReal_nonneg hvolLayer
  have hlayerMeas : MeasurableSet {y ∈ Om | fderiv ℝ eta y ≠ 0} := by
    have hcont : Continuous fun y : Vec d => fderiv ℝ eta y :=
      heta.continuous_fderiv (by simp)
    exact hOmOpen.measurableSet.inter (isOpen_ne.preimage hcont).measurableSet
  have hlayerSub : {y ∈ Om | fderiv ℝ eta y ≠ 0} ⊆ Om := fun _ hy => hy.1
  have hcnn : (0 : ℝ) ≤ M ^ 2 * Ceta * Real.exp (2 * (kappa * tA)) :=
    mul_nonneg (mul_nonneg (sq_nonneg M) hCeta) (Real.exp_pos _).le
  have hconstInt : Integrable
      ({y ∈ Om | fderiv ℝ eta y ≠ 0}.indicator
        (fun _ : Vec d => M ^ 2 * Ceta * Real.exp (2 * (kappa * tA))))
      (volumeMeasureOn Om) := (integrable_const _).indicator hlayerMeas
  have hmono : (∫ y, u.toFun y ^ 2 *
      (Real.exp (kappa * psi y) ^ 2 *
        vecNormSq (fun i => (fderiv ℝ eta y) (basisVec i)))
        ∂volumeMeasureOn Om) ≤
      ∫ y, {y ∈ Om | fderiv ℝ eta y ≠ 0}.indicator
        (fun _ : Vec d => M ^ 2 * Ceta * Real.exp (2 * (kappa * tA))) y
        ∂volumeMeasureOn Om := by
    have hmemOm : ∀ᵐ y ∂volumeMeasureOn Om, y ∈ Om :=
      (ae_restrict_iff' hOmOpen.measurableSet).2
        (Filter.Eventually.of_forall fun _ hy => hy)
    refine integral_mono_ae hlayerInt hconstInt ?_
    filter_upwards [hMbound, hmemOm] with y hy hyOm
    have hu2 : u.toFun y ^ 2 ≤ M ^ 2 := by
      have habs : |u.toFun y| ^ 2 ≤ M ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) hy 2
      rwa [sq_abs] at habs
    by_cases hzero : fderiv ℝ eta y = 0
    · have hgz : vecNormSq (fun i => (fderiv ℝ eta y) (basisVec i)) = 0 := by
        rw [hzero]
        simp only [zero_apply, vecNormSq, vecDot,
          mul_zero, Finset.sum_const_zero]
      rw [hgz, mul_zero, mul_zero]
      exact Set.indicator_nonneg (fun _ _ => hcnn) y
    · rw [Set.indicator_of_mem
        (show y ∈ {y ∈ Om | fderiv ℝ eta y ≠ 0} from ⟨hyOm, hzero⟩)]
      have hpsiLe := hlayer y hyOm hzero
      have hexp : Real.exp (kappa * psi y) ^ 2 ≤
          Real.exp (2 * (kappa * tA)) := by
        have hsq : Real.exp (kappa * psi y) ^ 2 =
            Real.exp (2 * (kappa * psi y)) := by
          rw [sq, ← Real.exp_add]
          congr 1
          ring
        rw [hsq]
        refine Real.exp_le_exp.2 ?_
        have hmul := mul_le_mul_of_nonneg_left hpsiLe hkappa0
        linarith only [hmul]
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
  have hmeasEq : (volumeMeasureOn Om).real {y ∈ Om | fderiv ℝ eta y ≠ 0} =
      (volume {y ∈ Om | fderiv ℝ eta y ≠ 0}).toReal := by
    rw [measureReal_def, Measure.restrict_apply hlayerMeas,
      Set.inter_eq_left.mpr hlayerSub]
  rw [hmeasEq, smul_eq_mul] at hmono
  refine hmono.trans ?_
  have hscale := mul_le_mul_of_nonneg_right hvolLayer hcnn
  linarith only [hscale]

/-! ### From a weighted mass estimate to a local `L²` bound -/

/-- **The contrast-free bridge, from a weighted mass estimate.**  Whatever
supplies the exponentially weighted mass estimate, the plain `L²` mass on an
inner ball is controlled by the layer data and the phase gap. -/
theorem setIntegral_sq_le_exp_of_agmonMass {Om : Set (Vec d)}
    (hOmOpen : IsOpen Om) (hOmBdd : IsBoundedDomain Om)
    {u : H1Function Om} {eta psi : Vec d → ℝ}
    {lam Lam mass kappa M Ceta volLayer tA tx : ℝ}
    (hlam : 0 < lam) (hmass : 0 < mass)
    (hMbound : ∀ᵐ y ∂volumeMeasureOn Om, |u.toFun y| ≤ M)
    (heta : ContDiff ℝ (⊤ : ℕ∞) eta) (hetaCompact : HasCompactSupport eta)
    (hpsi : ContDiff ℝ (⊤ : ℕ∞) psi) (hCeta : 0 ≤ Ceta)
    (hetaGrad : ∀ y ∈ Om,
      vecNormSq (fun i => (fderiv ℝ eta y) (basisVec i)) ≤ Ceta)
    (hlayer : ∀ y ∈ Om, fderiv ℝ eta y ≠ 0 → psi y ≤ tA)
    (hvolLayer : (volume {y ∈ Om | fderiv ℝ eta y ≠ 0}).toReal ≤ volLayer)
    (hkappa0 : 0 ≤ kappa)
    (hagmon : mass / 2 * ∫ y in Om, u.toFun y ^ 2 *
        (eta y ^ 2 * Real.exp (kappa * psi y) ^ 2) ∂volume ≤
      4 * Lam ^ 2 / lam *
        ∫ y in Om, u.toFun y ^ 2 *
          (Real.exp (kappa * psi y) ^ 2 *
            vecNormSq (fun i => (fderiv ℝ eta y) (basisVec i))) ∂volume)
    {x : Vec d} {R : ℝ}
    (hinner : ∀ y ∈ euclideanBall x R, eta y = 1)
    (hphase : ∀ y ∈ euclideanBall x R, tx ≤ psi y) :
    ∀ rho : ℝ, 0 < rho → rho ≤ R → euclideanBall x rho ⊆ Om →
      (∫ y in euclideanBall x rho, u.toFun y ^ 2 ∂volume) ≤
        (M * Real.sqrt (8 * Lam ^ 2 / (lam * mass) * Ceta * volLayer)) ^ 2 *
          Real.exp (-(2 * (kappa * (tx - tA)))) := by
  classical
  have hchi : ContDiff ℝ (⊤ : ℕ∞) (fun y => Real.exp (kappa * psi y)) :=
    contDiff_exponentialWeight hpsi kappa
  have hweightTop : MemLp (fun y =>
      eta y ^ 2 * Real.exp (kappa * psi y) ^ 2) ∞ (volumeMeasureOn Om) := by
    refine (Continuous.memLp_of_hasCompactSupport ?_ ?_).restrict Om
    · exact (heta.continuous.pow 2).mul (hchi.continuous.pow 2)
    · have hetaSq : HasCompactSupport (fun y => eta y ^ 2) := by
        simpa only [pow_two] using! hetaCompact.mul_left (f := eta)
      exact hetaSq.mul_right
  have hweightInt := integrable_sq_mul_memLpTop (u := u) hweightTop
  have hsqInt : IntegrableOn (fun y => u.toFun y ^ 2) Om := by
    apply (u.memL2.integrable_mul u.memL2).congr
    filter_upwards with y
    simp only [Pi.mul_apply]
    ring
  have hvolLayer0 : (0 : ℝ) ≤ volLayer :=
    le_trans ENNReal.toReal_nonneg hvolLayer
  have hlayerBound := setIntegral_sq_mul_exp_gradSq_layer_le hOmOpen hOmBdd
    hMbound heta hetaCompact hpsi hCeta hetaGrad hlayer hvolLayer hkappa0
  have hweightBound : (∫ y in Om, u.toFun y ^ 2 *
      (eta y ^ 2 * Real.exp (kappa * psi y) ^ 2) ∂volume) ≤
      8 * Lam ^ 2 / (lam * mass) * Ceta * volLayer * M ^ 2 *
        Real.exp (2 * (kappa * tA)) := by
    have hcoeff : (0 : ℝ) ≤ 4 * Lam ^ 2 / lam := by positivity
    have hstep := le_trans hagmon
      (mul_le_mul_of_nonneg_left hlayerBound hcoeff)
    have hmass2 : (0 : ℝ) < mass / 2 := by positivity
    have hX : (∫ y in Om, u.toFun y ^ 2 *
        (eta y ^ 2 * Real.exp (kappa * psi y) ^ 2) ∂volume) ≤
        4 * Lam ^ 2 / lam *
          (M ^ 2 * Ceta * Real.exp (2 * (kappa * tA)) * volLayer) /
            (mass / 2) := by
      rw [le_div_iff₀ hmass2]
      linarith only [hstep]
    refine le_trans hX (le_of_eq ?_)
    field_simp
    ring
  have hDsq : 0 ≤ 8 * Lam ^ 2 / (lam * mass) * Ceta * volLayer := by
    have hlm : (0 : ℝ) < lam * mass := mul_pos hlam hmass
    have hcoeff : (0 : ℝ) ≤ 8 * Lam ^ 2 / (lam * mass) := by positivity
    exact mul_nonneg (mul_nonneg hcoeff hCeta) hvolLayer0
  intro rho hrho hrhoR hsubOm
  have hsubR : euclideanBall x rho ⊆ euclideanBall x R := by
    intro y hy
    have hy' : euclideanSqDist y x < rho ^ 2 := hy
    exact lt_of_lt_of_le hy' (pow_le_pow_left₀ hrho.le hrhoR 2)
  have hBmeas : MeasurableSet (euclideanBall x rho) :=
    (isOpen_euclideanBall x rho).measurableSet
  have hstep := setIntegral_sq_le_exp_mul_localizedWeight hsubOm hBmeas
    (w := u.toFun) (eta := eta) (psi := psi) (kappa := kappa) (t := tx)
    hkappa0
    (fun y hy => by rw [hinner y (hsubR hy)]; norm_num)
    (fun y hy => hphase y (hsubR hy)) hsqInt hweightInt
  have hcombine := le_trans hstep
    (mul_le_mul_of_nonneg_left hweightBound (Real.exp_pos _).le)
  refine le_trans hcombine (le_of_eq ?_)
  have hsq : (M * Real.sqrt (8 * Lam ^ 2 / (lam * mass) * Ceta *
      volLayer)) ^ 2 =
        M ^ 2 * (8 * Lam ^ 2 / (lam * mass) * Ceta * volLayer) := by
    rw [mul_pow, Real.sq_sqrt hDsq]
  have hexpid : Real.exp (-(2 * kappa * tx)) * Real.exp (2 * (kappa * tA)) =
      Real.exp (-(2 * (kappa * (tx - tA)))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hsq]
  calc
    Real.exp (-(2 * kappa * tx)) *
        (8 * Lam ^ 2 / (lam * mass) * Ceta * volLayer * M ^ 2 *
          Real.exp (2 * (kappa * tA))) =
        (Real.exp (-(2 * kappa * tx)) * Real.exp (2 * (kappa * tA))) *
          (M ^ 2 * (8 * Lam ^ 2 / (lam * mass) * Ceta * volLayer)) := by ring
    _ = M ^ 2 * (8 * Lam ^ 2 / (lam * mass) * Ceta * volLayer) *
        Real.exp (-(2 * (kappa * (tx - tA)))) := by
      rw [hexpid]
      ring

/-! ### The localized local `L²` bound -/

/-! ### The Caccioppoli gradient bound -/

/-- The localized gradient energy dominates the gradient energy on any set
where the localization is one. -/
theorem setIntegral_gradSq_le_of_localizedBound {Om : Set (Vec d)}
    {u : H1Function Om} {eta : Vec d → ℝ} {S : ℝ}
    (heta : ContDiff ℝ (⊤ : ℕ∞) eta) (hetaCompact : HasCompactSupport eta)
    (hgrad : (∫ y in Om, eta y ^ 2 * vecNormSq (u.grad y) ∂volume) ≤ S)
    {W : Set (Vec d)} (hW : MeasurableSet W) (hWOm : W ⊆ Om)
    (hWeta : ∀ y ∈ W, eta y = 1) :
    (∫ y in W, vecNormSq (u.grad y) ∂volume) ≤ S := by
  classical
  have hphiTop : MemLp (fun x => eta x ^ 2) ∞ (volumeMeasureOn Om) :=
    ((sq_weight_smooth heta hetaCompact).1.continuous.memLp_of_hasCompactSupport
      (sq_weight_smooth heta hetaCompact).2).restrict Om
  have hq : MemVectorL2 Om (fun x => (eta x ^ 2) • u.grad x) := by
    simpa only [MemVectorL2, volumeMeasureOn, Pi.smul_apply, smul_eq_mul,
      mul_comm] using!
      (MemLp.of_eval fun i : Fin d =>
        (memScalarL2_coord_of_memVectorL2 u.grad_memVectorL2 i).fun_mul hphiTop)
  have htargetInt : Integrable (fun x => eta x ^ 2 * vecNormSq (u.grad x))
      (volumeMeasureOn Om) := by
    apply (integrableOn_vecDot_of_memVectorL2 u.grad_memVectorL2 hq).congr
    filter_upwards with x
    simp only [vecNormSq, vecDot, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hballLe : (∫ y in W, vecNormSq (u.grad y) ∂volume) ≤
      ∫ y in Om, eta y ^ 2 * vecNormSq (u.grad y) ∂volume := by
    have hcongr : (∫ y in W, vecNormSq (u.grad y) ∂volume) =
        ∫ y in W, eta y ^ 2 * vecNormSq (u.grad y) ∂volume := by
      refine setIntegral_congr_fun hW ?_
      intro y hy
      show vecNormSq (u.grad y) = eta y ^ 2 * vecNormSq (u.grad y)
      rw [hWeta y hy]
      ring
    rw [hcongr]
    refine setIntegral_mono_set htargetInt ?_ ?_
    · filter_upwards with y
      exact mul_nonneg (sq_nonneg _) (vecNormSq_nonneg _)
    · exact Filter.Eventually.of_forall hWOm
  exact hballLe.trans hgrad


/-- The unweighted layer term, the case of a constant weight. -/
theorem setIntegral_sq_mul_gradSq_layer_le {Om : Set (Vec d)}
    (hOmOpen : IsOpen Om) (hOmBdd : IsBoundedDomain Om)
    {u : H1Function Om} {eta : Vec d → ℝ} {M Ceta volLayer : ℝ}
    (hMbound : ∀ᵐ y ∂volumeMeasureOn Om, |u.toFun y| ≤ M)
    (heta : ContDiff ℝ (⊤ : ℕ∞) eta) (hetaCompact : HasCompactSupport eta)
    (hCeta : 0 ≤ Ceta)
    (hetaGrad : ∀ y ∈ Om,
      vecNormSq (fun i => (fderiv ℝ eta y) (basisVec i)) ≤ Ceta)
    (hvolLayer : (volume {y ∈ Om | fderiv ℝ eta y ≠ 0}).toReal ≤ volLayer) :
    (∫ y in Om, u.toFun y ^ 2 *
        vecNormSq (fun i => (fderiv ℝ eta y) (basisVec i)) ∂volume) ≤
      M ^ 2 * Ceta * volLayer := by
  have h := setIntegral_sq_mul_exp_gradSq_layer_le
    (psi := fun _ : Vec d => (0 : ℝ)) (kappa := 0) (tA := 0) hOmOpen hOmBdd
    hMbound heta hetaCompact contDiff_const hCeta hetaGrad
    (fun _ _ _ => le_rfl) hvolLayer le_rfl
  simpa only [zero_mul, mul_zero, Real.exp_zero, one_pow, one_mul,
    mul_one] using h

end DivergenceFormProcess.Decay
