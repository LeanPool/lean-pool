/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.Decay.LocalizedSplitMass
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.Decay.TailFreezing
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.ScalarWeakSolutionRestriction

/-!
# LocalizedTailFreezing

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The resolvent tail with layer constants

The tail estimate is re-run with the coefficient split as
`a = nu • I + ks + kl`, with `ks` merely bounded and `kl` continuously
differentiable and antisymmetric.  Every constant of the conclusion is read off
the ball `euclideanBall x r` about the evaluation point: the size of `ks` and
the size of the divergence of `kl` there.  Uniform ellipticity on the whole
domain enters only qualitatively, through the square integrability of the
flux, and its upper constant never appears in the conclusion.

The two halves of the chain are the localized ones: the exponentially weighted
mass estimate and the Caccioppoli gradient bound, both at the effective upper
constant `localizedAgmonUpper nu mu Ks Kl`.  The pointwise half is unchanged:
it is applied to the normalized coefficient frozen at `x` on the ball of
radius `r₀`, on which small contrast is assumed.

## Main results

- `DivergenceFormProcess.Decay.vectorLpSizeOn_grad_le_agmonTailGradientSize_localized`
- `DivergenceFormProcess.Decay.resolventTail_localized`
- `DivergenceFormProcess.Decay.resolventTail_localized_representative`
-/

noncomputable section

namespace DivergenceFormProcess.Decay

open HCPolySupport MeasureTheory
open DivergenceFormProcess.Form
open Algsuperdiff.StochasticProcess.Common.Regularity.Ported
open Algsuperdiff.StochasticProcess.Common.Regularity.Freezing
open scoped ENNReal

variable {d : ℕ}

/-! ### Elementary restatements -/

/-- The symmetric part of a coefficient split as a scalar plus two
antisymmetric parts. -/
theorem symmPart_eq_of_splitSkew {nu : ℝ} {A K1 K2 : Mat d}
    (hA : A = nu • (1 : Mat d) + K1 + K2)
    (hK1 : matTranspose K1 = -K1) (hK2 : matTranspose K2 = -K2) :
    symmPart A = nu • (1 : Mat d) := by
  refine symmPart_scalar_add_skew (K := K1 + K2) ?_ ?_
  · rw [hA, add_assoc]
  · rw [show matTranspose (K1 + K2) = matTranspose K1 + matTranspose K2 from
      Matrix.transpose_add K1 K2, hK1, hK2]
    exact (neg_add K1 K2).symm

private theorem vectorLpSizeOn_mono_localized {V W : Set (Vec d)} (hVW : V ⊆ W)
    {f : Vec d → Vec d} {E : ℝ}
    (hf : MemVectorL2 W f) (hE : vectorLpSizeOn W 2 f ≤ E) :
    vectorLpSizeOn V 2 f ≤ E := by
  unfold vectorLpSizeOn at hE ⊢
  simp only [ENNReal.ofReal_ofNat] at hE ⊢
  exact (ENNReal.toReal_mono (memLp_euclideanNorm hf).eLpNorm_ne_top
    (eLpNorm_mono_measure _ (Measure.restrict_mono hVW le_rfl))).trans hE

/-! ### The localized gradient size -/

/-- **The Caccioppoli gradient size with layer constants.**  The gradient size
consumed by the interior estimate is the one of the uniformly elliptic chain,
with lower constant `nu` and upper constant the effective one read off the
ball about the evaluation point. -/
theorem vectorLpSizeOn_grad_le_agmonTailGradientSize_localized [NeZero d]
    {a : CoeffField d} {ks kl : Vec d → Mat d} {Om : Set (Vec d)}
    (hOmOpen : IsOpen Om) (hOmBdd : IsBoundedDomain Om)
    {z : H10Function Om} {g : Vec d → ℝ} {nu LamS Ks Kl mu : ℝ}
    (hnu : 0 < nu) (hKs : 0 ≤ Ks) (hKl : 0 ≤ Kl) (hmu : 0 < mu)
    (hEllS : IsEllipticFieldOn nu LamS Om (fun y => nu • (1 : Mat d) + ks y))
    (hsplit : ∀ y, a y = nu • (1 : Mat d) + ks y + kl y)
    (hksSkew : ∀ y, matTranspose (ks y) = -ks y)
    (hklSkew : ∀ y, matTranspose (kl y) = -kl y)
    (hklC1 : ∀ p q : Fin d, ContDiff ℝ 1 fun y => kl y p q)
    (hsol : IsScalarForcedWeakSolution a Om
      (fun y => g y - mu * z.toH1Function.toFun y) z.toH1Function)
    (hMbound : ∀ᵐ y ∂volumeMeasureOn Om,
      |z.toH1Function.toFun y| ≤ 1 / mu)
    {x : Vec d} {r : ℝ} (hr : 0 < r) (hball : euclideanBall x r ⊆ Om)
    (hksSize : ∀ y ∈ euclideanBall x r, ∀ v : Vec d,
      vecNormSq (matVecMul (ks y) v) ≤ Ks ^ 2 * vecNormSq v)
    (hklDiv : ∀ y ∈ euclideanBall x r,
      vecNormSq (skewFieldDiv kl y) ≤ Kl ^ 2)
    (hg : ∀ᵐ y ∂volume, y ∈ euclideanBall x r → g y = 0) :
    vectorLpSizeOn (euclideanBall x (r / 2)) 2 z.toH1Function.grad ≤
      agmonTailGradientSize d nu (localizedAgmonUpper nu mu Ks Kl) mu r := by
  have hLloc : 0 < localizedAgmonUpper nu mu Ks Kl :=
    localizedAgmonUpper_pos hnu hKs hKl
  have hhalf : euclideanBall x (r / 2) ⊆ euclideanBall x r :=
    Algsuperdiff.Section4.Provider.Schauder.euclideanBall_mono
      (by linarith only [hr]) (by linarith only [hr])
  have hmem : MemVectorL2 (euclideanBall x (r / 2)) z.toH1Function.grad :=
    z.toH1Function.grad_memVectorL2.mono_measure
      (Measure.restrict_mono (hhalf.trans hball) le_rfl)
  refine vectorLpSizeOn_two_le hmem
    (agmonTailGradientSize_nonneg d hnu hLloc hmu) ?_
  have hzero : ∀ᵐ y ∂volumeMeasureOn Om,
      agmonTailCutoff x r y ≠ 0 → g y = 0 := by
    filter_upwards [ae_restrict_of_ae (μ := volume) (s := Om) hg] with y hy hne
    exact hy (tsupport_agmonTailCutoff_subset x hr (subset_closure hne))
  have hcacc := setIntegral_gradSq_localizedSplit_le hOmOpen hOmBdd hnu hKs hKl
    hmu hEllS hsplit hksSkew hklSkew hklC1 hsol
    (contDiff_agmonTailCutoff x hr) (hasCompactSupport_agmonTailCutoff x hr)
    (tsupport_agmonTailCutoff_subset x hr) hzero hMbound
    (agmonTailCutoffGradientBound_nonneg d r)
    (fun y _ => vecNormSq_fderiv_agmonTailCutoff_le x hr y)
    (volume_layer_agmonTailCutoff_le x hr Om) hksSize hklDiv
    (isOpen_euclideanBall x (r / 2)).measurableSet (hhalf.trans hball)
    (fun y hy => agmonTailCutoff_eq_one x hr
      (Algsuperdiff.Section4.Provider.Schauder.euclideanBall_mono
        (by linarith only [hr]) (by linarith only [hr]) hy))
  refine hcacc.trans (le_of_eq ?_)
  unfold agmonTailGradientSize
  have hnn : (0 : ℝ) ≤ agmonTailCutoffGradientBound d r *
      agmonTailLayerVolume d r :=
    mul_nonneg (agmonTailCutoffGradientBound_nonneg d r)
      (agmonTailLayerVolume_nonneg d hr.le)
  rw [mul_pow, mul_pow, Real.sq_sqrt hnn]
  field_simp
  ring


/-! ### The localized tail estimate -/

/-- **The resolvent tail with layer constants.**  For a coefficient split as
`nu • I + ks + kl` with both parts antisymmetric and `kl` continuously
differentiable, the tail of the resolvent at `x` is bounded by the two-scale
tail function at lower constant `nu` and upper constant
`localizedAgmonUpper nu mu Ks Kl`, whose ingredients are the size of `ks` and
the size of the divergence of `kl` on the ball `euclideanBall x r` alone.  The
ambient ellipticity constant `LamS` does not appear in the conclusion. -/
theorem resolventTail_localized [NeZero d]
    {a : CoeffField d} {ks kl : Vec d → Mat d} {Om : Set (Vec d)}
    (hOmOpen : IsOpen Om) (hOmBdd : IsBoundedDomain Om)
    {z : H10Function Om} {g : Vec d → ℝ}
    {nu LamS Ks Kl mu delta alpha : ℝ}
    (hd : 2 ≤ d) (halpha : alpha ∈ Set.Ico (1 / 2 : ℝ) 1)
    (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ smallContrastThreshold d alpha)
    (hnu : 0 < nu) (hKs : 0 ≤ Ks) (hKl : 0 ≤ Kl) (hmu : 0 < mu)
    (hameas : Measurable a)
    (hEllS : IsEllipticFieldOn nu LamS Om (fun y => nu • (1 : Mat d) + ks y))
    (hsplit : ∀ y, a y = nu • (1 : Mat d) + ks y + kl y)
    (hksSkew : ∀ y, matTranspose (ks y) = -ks y)
    (hklSkew : ∀ y, matTranspose (kl y) = -kl y)
    (hklC1 : ∀ p q : Fin d, ContDiff ℝ 1 fun y => kl y p q)
    (hsol : IsScalarForcedWeakSolution a Om
      (fun y => g y - mu * z.toH1Function.toFun y) z.toH1Function)
    (hMbound : ∀ᵐ y ∂volumeMeasureOn Om,
      |z.toH1Function.toFun y| ≤ 1 / mu)
    {x : Vec d} {r r₀ : ℝ} (hr : 0 < r) (hr₀ : 0 < r₀)
    (hr₀r : r₀ ≤ r / 2) (hball : euclideanBall x r ⊆ Om)
    (hksSize : ∀ y ∈ euclideanBall x r, ∀ v : Vec d,
      vecNormSq (matVecMul (ks y) v) ≤ Ks ^ 2 * vecNormSq v)
    (hklDiv : ∀ y ∈ euclideanBall x r,
      vecNormSq (skewFieldDiv kl y) ≤ Kl ^ 2)
    (hsmall : CoefficientIdentityDistanceLE (euclideanBall x r₀)
      (normalizedFrozenCoeff nu a x) delta)
    (hg : ∀ᵐ y ∂volume, y ∈ euclideanBall x r → g y = 0) :
    ∃ v : Vec d → ℝ,
      ContinuousOn v (euclideanBall x (r₀ / 2)) ∧
      v =ᵐ[volume.restrict (euclideanBall x r₀)] z.toH1Function.toFun ∧
      mu * |v x| ≤ agmonTailFunctionFrozen d nu
        (localizedAgmonUpper nu mu Ks Kl) nu alpha
        (Real.sqrt mu * r) (Real.sqrt mu * r₀) := by
  classical
  set Lloc : ℝ := localizedAgmonUpper nu mu Ks Kl with hLloc_def
  have hLlocPos : 0 < Lloc := localizedAgmonUpper_pos hnu hKs hKl
  let B : Set (Vec d) := euclideanBall x r₀
  have hBhalf : B ⊆ euclideanBall x (r / 2) := by
    intro y hy
    have hy' : euclideanSqDist y x < r₀ ^ 2 := hy
    exact lt_of_lt_of_le hy' (pow_le_pow_left₀ hr₀.le hr₀r 2)
  have hBr : B ⊆ euclideanBall x r := hBhalf.trans (by
    intro y hy
    have hy' : euclideanSqDist y x < (r / 2) ^ 2 := hy
    exact lt_of_lt_of_le hy'
      (pow_le_pow_left₀ (by positivity : 0 ≤ r / 2) (by linarith only [hr]) 2))
  have hBOm : B ⊆ Om := hBr.trans hball
  have hBopen : IsOpen B := isOpen_euclideanBall x r₀
  let zB : H1Function B := z.toH1Function.restrict hBopen hBOm
  let q : Vec d → ℝ := fun y => g y - mu * z.toH1Function.toFun y
  have hsolB : IsScalarForcedWeakSolution a B q zB :=
    IsScalarForcedWeakSolution.restrictSubset hBopen hBOm hsol
  have hsymmx : symmPart (a x) = nu • (1 : Mat d) :=
    symmPart_eq_of_splitSkew (hsplit x) (hksSkew x) (hklSkew x)
  have hk : matTranspose (a x - nu • (1 : Mat d)) =
      -(a x - nu • (1 : Mat d)) :=
    sub_scalar_one_isSkew_of_symmPart_eq hsymmx
  have hfrozen : IsScalarForcedWeakSolution
      (fun y => a y - (a x - nu • (1 : Mat d))) B q zB :=
    (isScalarForcedWeakSolution_sub_skew_const hk).2 hsolB
  have hnormalized : IsScalarForcedWeakSolution
      (normalizedFrozenCoeff nu a x) B (fun y => nu⁻¹ * q y) zB := by
    simpa only [normalizedFrozenCoeff] using!
      (IsScalarForcedWeakSolution.const_smul_coefficient (c := nu⁻¹) hfrozen)
  have hnormalizedMeas : Measurable (normalizedFrozenCoeff nu a x) := by
    refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
    change Measurable fun y => nu⁻¹ *
      (a y i j - (a x - nu • (1 : Mat d)) i j)
    exact (((measurable_pi_apply j).comp
      ((measurable_pi_apply i).comp hameas)).sub measurable_const).const_mul _
  have hhalfGrad : vectorLpSizeOn (euclideanBall x (r / 2)) 2
      z.toH1Function.grad ≤ agmonTailGradientSize d nu Lloc mu r :=
    vectorLpSizeOn_grad_le_agmonTailGradientSize_localized hOmOpen hOmBdd hnu
      hKs hKl hmu hEllS hsplit hksSkew hklSkew hklC1 hsol hMbound hr hball
      hksSize hklDiv hg
  have hhalfOm : euclideanBall x (r / 2) ⊆ Om := by
    intro y hy
    apply hball
    have hy' : euclideanSqDist y x < (r / 2) ^ 2 := hy
    exact lt_of_lt_of_le hy'
      (pow_le_pow_left₀ (by positivity : 0 ≤ r / 2) (by linarith only [hr]) 2)
  have hgradMem : MemVectorL2 (euclideanBall x (r / 2)) z.toH1Function.grad :=
    z.toH1Function.grad_memVectorL2.mono_measure
      (Measure.restrict_mono hhalfOm le_rfl)
  have hgradB : vectorLpSizeOn B 2 zB.grad ≤
      agmonTailGradientSize d nu Lloc mu r := by
    change vectorLpSizeOn B 2 z.toH1Function.grad ≤ _
    exact vectorLpSizeOn_mono_localized hBhalf hgradMem hhalfGrad
  have hqBound : ∀ᵐ y ∂volume.restrict B, |nu⁻¹ * q y| ≤ 1 / nu := by
    have hMB : ∀ᵐ y ∂volume.restrict B,
        |z.toH1Function.toFun y| ≤ 1 / mu :=
      hMbound.filter_mono (ae_mono (Measure.restrict_mono hBOm le_rfl))
    have hmemB : ∀ᵐ y ∂volume.restrict B, y ∈ B :=
      (ae_restrict_iff' hBopen.measurableSet).2
        (Filter.Eventually.of_forall fun _ hy => hy)
    have hgB : ∀ᵐ y ∂volume.restrict B, g y = 0 := by
      filter_upwards [ae_restrict_of_ae (μ := volume) (s := B) hg, hmemB]
        with y hy hyB
      exact hy (hBr hyB)
    filter_upwards [hMB, hgB] with y hy hgy
    rw [show q y = g y - mu * z.toH1Function.toFun y from rfl, hgy]
    simp only [zero_sub, abs_mul, abs_neg, abs_inv, abs_of_pos hnu,
      abs_of_pos hmu]
    calc
      nu⁻¹ * (mu * |z.toH1Function.toFun y|) ≤
          nu⁻¹ * (mu * (1 / mu)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hy hmu.le) (inv_nonneg.2 hnu.le)
      _ = 1 / nu := by field_simp
  have hG : (0 : ℝ) ≤ 1 / nu := by positivity
  have hkappa0 : 0 ≤ agmonRate nu Lloc mu := agmonRate_nonneg hLlocPos
  have hzero : ∀ᵐ y ∂volumeMeasureOn Om,
      agmonTailCutoff x r y ≠ 0 → g y = 0 := by
    filter_upwards [ae_restrict_of_ae (μ := volume) (s := Om) hg]
      with y hy hne
    exact hy (tsupport_agmonTailCutoff_subset x hr (subset_closure hne))
  have hsign : ∀ᵐ y ∂volumeMeasureOn Om,
      agmonTailCutoff x r y ≠ 0 →
        q y * z.toH1Function.toFun y ≤
          -(mu * z.toH1Function.toFun y ^ 2) := by
    filter_upwards [hzero] with y hy hne
    rw [show q y = g y - mu * z.toH1Function.toFun y from rfl, hy hne]
    ring_nf
    exact le_rfl
  have heps : (0 : ℝ) < r / 8 := by linarith only [hr]
  have hinner : ∀ y ∈ euclideanBall x (r₀ / 2),
      agmonTailCutoff x r y = 1 := by
    intro y hy
    apply agmonTailCutoff_eq_one x hr
    have hy' : euclideanSqDist y x < (r₀ / 2) ^ 2 := hy
    have hquarter : r₀ / 2 ≤ r / 4 := by
      calc
        r₀ / 2 ≤ (r / 2) / 2 :=
          (div_le_div_iff_of_pos_right (by norm_num)).2 hr₀r
        _ = r / 4 := by ring
    have hle : r₀ / 2 ≤ 3 * r / 4 :=
      hquarter.trans (by linarith only [hr])
    exact lt_of_lt_of_le hy'
      (pow_le_pow_left₀ (by positivity : 0 ≤ r₀ / 2) hle 2)
  have hphase : ∀ y ∈ euclideanBall x (r₀ / 2),
      -(r / 4) ≤ inwardPhase x (r / 8) y := by
    intro y hy
    have hsub : euclideanBall x (r₀ / 2) ⊆ euclideanBall x (r / 4) := by
      intro w hw
      have hw' : euclideanSqDist w x < (r₀ / 2) ^ 2 := hw
      have hle : r₀ / 2 ≤ r / 4 := by
        calc
          r₀ / 2 ≤ (r / 2) / 2 :=
            (div_le_div_iff_of_pos_right (by norm_num)).2 hr₀r
          _ = r / 4 := by ring
      exact lt_of_lt_of_le hw'
        (pow_le_pow_left₀ (by positivity : 0 ≤ r₀ / 2) hle 2)
    have hbase := le_inwardPhase_of_mem_euclideanBall (z := x) heps
      (by positivity : (0 : ℝ) ≤ r / 4) (hsub hy)
    rwa [sub_self, euclideanNorm_zero, zero_add] at hbase
  have hagmon := agmonMass_localizedSplit_le (kappa := agmonRate nu Lloc mu)
    (psi := inwardPhase x (r / 8)) (L := euclideanBall x r) hOmOpen hOmBdd hnu
    hKs hKl hmu hEllS hsplit hksSkew hklSkew hklC1 hsol
    (contDiff_agmonTailCutoff x hr) (hasCompactSupport_agmonTailCutoff x hr)
    (tsupport_agmonTailCutoff_subset x hr) (contDiff_inwardPhase heps)
    (Filter.Eventually.of_forall fun y =>
      vecNormSq_fderiv_inwardPhase_le_one heps y)
    hsign hksSize hklDiv
    (agmonRate_admissible' hnu.le hmu.le hLlocPos)
  let D : ℝ := 1 / mu * Real.sqrt (8 * Lloc ^ 2 / (nu * mu) *
    agmonTailCutoffGradientBound d r * agmonTailLayerVolume d r)
  have hD : 0 ≤ D := by
    unfold D
    positivity
  have hL2 : ∀ rho : ℝ, 0 < rho → rho ≤ r₀ / 2 →
      (∫ y in euclideanBall x rho, zB.toFun y ^ 2 ∂volume) ≤
        D ^ 2 * Real.exp (-(2 *
          (agmonRate nu Lloc mu * (3 * r / 8)))) := by
    intro rho hrho hrho0
    have hraw := setIntegral_sq_le_exp_of_agmonMass hOmOpen hOmBdd hnu hmu
      hMbound (contDiff_agmonTailCutoff x hr)
      (hasCompactSupport_agmonTailCutoff x hr) (contDiff_inwardPhase heps)
      (agmonTailCutoffGradientBound_nonneg d r)
      (fun y _ => vecNormSq_fderiv_agmonTailCutoff_le x hr y)
      (fun y _ hy => inwardPhase_le_of_le_euclideanNorm heps
        (le_euclideanNorm_of_fderiv_agmonTailCutoff_ne_zero x hr hy))
      (volume_layer_agmonTailCutoff_le x hr Om) hkappa0 hagmon
      hinner hphase rho hrho hrho0 (by
        intro y hy
        apply hBOm
        change euclideanSqDist y x < r₀ ^ 2
        exact lt_of_lt_of_le hy
          ((pow_le_pow_left₀ hrho.le hrho0 2).trans
            (pow_le_pow_left₀ (by positivity : 0 ≤ r₀ / 2)
              (by linarith only [hr₀]) 2)))
    have hgap : -(r / 4) - (-(3 * r / 4) + r / 8) = 3 * r / 8 := by ring
    rw [hgap] at hraw
    simpa only [zB, D] using! hraw
  obtain ⟨v, hvcont, hvae, hvbound⟩ :=
    exists_representative_abs_center_le_exp hBopen hd halpha hdelta0 hdelta
      hnormalizedMeas hsmall hnormalized hr₀ (fun _ hy => hy) hG hqBound
      hgradB hkappa0 (by positivity : (0 : ℝ) ≤ 3 * r / 8) hD hL2
  refine ⟨v, hvcont, ?_, ?_⟩
  · simpa only [zB, B] using! hvae
  · have hscaled := mul_le_mul_of_nonneg_left hvbound hmu.le
    refine hscaled.trans (le_of_eq ?_)
    have hgapRate := agmonRate_mul_eq d (Lam := Lloc) (mu := mu)
      (r := r) (alpha := alpha) hnu
    have hconst := mul_agmonDecayConstant_frozen_eq (d := d) (nu := nu)
      (alpha := alpha) hnu hLlocPos hmu hr hr₀
    unfold agmonTailFunctionFrozen
    rw [abs_of_pos (mul_pos (Real.sqrt_pos.2 hmu) hr),
      abs_of_pos (mul_pos (Real.sqrt_pos.2 hmu) hr₀)]
    change mu * (agmonFrozenDecayConstant d D alpha
      (agmonTailGradientSize d nu Lloc mu r) (1 / nu) r₀ *
        Real.exp (-(agmonRate nu Lloc mu * alpha /
          (alpha + (d : ℝ) / 2) * (3 * r / 8)))) = _
    rw [mul_assoc, hgapRate]
    rw [← mul_assoc, hconst]
    ring

/-! ### Representatives and families -/

/-- The localized tail bound read on a fixed continuous representative near
the evaluation point. -/
theorem resolventTail_localized_representative [NeZero d]
    {a : CoeffField d} {ks kl : Vec d → Mat d} {Om : Set (Vec d)}
    (hOmOpen : IsOpen Om) (hOmBdd : IsBoundedDomain Om)
    {z : H10Function Om} {g zRep : Vec d → ℝ}
    {nu LamS Ks Kl mu delta alpha : ℝ}
    (hd : 2 ≤ d) (halpha : alpha ∈ Set.Ico (1 / 2 : ℝ) 1)
    (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ smallContrastThreshold d alpha)
    (hnu : 0 < nu) (hKs : 0 ≤ Ks) (hKl : 0 ≤ Kl) (hmu : 0 < mu)
    (hameas : Measurable a)
    (hEllS : IsEllipticFieldOn nu LamS Om (fun y => nu • (1 : Mat d) + ks y))
    (hsplit : ∀ y, a y = nu • (1 : Mat d) + ks y + kl y)
    (hksSkew : ∀ y, matTranspose (ks y) = -ks y)
    (hklSkew : ∀ y, matTranspose (kl y) = -kl y)
    (hklC1 : ∀ p q : Fin d, ContDiff ℝ 1 fun y => kl y p q)
    (hsol : IsScalarForcedWeakSolution a Om
      (fun y => g y - mu * z.toH1Function.toFun y) z.toH1Function)
    (hMbound : ∀ᵐ y ∂volumeMeasureOn Om,
      |z.toH1Function.toFun y| ≤ 1 / mu)
    {x : Vec d} {r r₀ : ℝ} (hr : 0 < r) (hr₀ : 0 < r₀)
    (hr₀r : r₀ ≤ r / 2) (hball : euclideanBall x r ⊆ Om)
    (hksSize : ∀ y ∈ euclideanBall x r, ∀ v : Vec d,
      vecNormSq (matVecMul (ks y) v) ≤ Ks ^ 2 * vecNormSq v)
    (hklDiv : ∀ y ∈ euclideanBall x r,
      vecNormSq (skewFieldDiv kl y) ≤ Kl ^ 2)
    (hsmall : CoefficientIdentityDistanceLE (euclideanBall x r₀)
      (normalizedFrozenCoeff nu a x) delta)
    (hg : ∀ᵐ y ∂volume, y ∈ euclideanBall x r → g y = 0)
    (hRepCont : ContinuousOn zRep (euclideanBall x (r₀ / 2)))
    (hRepAe : zRep =ᵐ[volume.restrict (euclideanBall x (r₀ / 2))]
      z.toH1Function.toFun) :
    mu * |zRep x| ≤ agmonTailFunctionFrozen d nu
      (localizedAgmonUpper nu mu Ks Kl) nu alpha
      (Real.sqrt mu * r) (Real.sqrt mu * r₀) := by
  obtain ⟨v, hvCont, hvAe, hvBound⟩ :=
    resolventTail_localized hOmOpen hOmBdd hd halpha hdelta0 hdelta hnu hKs
      hKl hmu hameas hEllS hsplit hksSkew hklSkew hklC1 hsol hMbound hr hr₀
      hr₀r hball hksSize hklDiv hsmall hg
  have hsub : euclideanBall x (r₀ / 2) ⊆ euclideanBall x r₀ := by
    intro y hy
    have hy' : euclideanSqDist y x < (r₀ / 2) ^ 2 := hy
    exact lt_of_lt_of_le hy'
      (pow_le_pow_left₀ (by positivity : 0 ≤ r₀ / 2)
        (by linarith only [hr₀]) 2)
  have hvAe' : v =ᵐ[volume.restrict (euclideanBall x (r₀ / 2))]
      z.toH1Function.toFun :=
    hvAe.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
  have heq := eqOn_of_ae_eq_euclideanBall hvCont hRepCont
    (hvAe'.trans hRepAe.symm)
  rw [← heq (center_mem_euclideanBall x (by positivity : 0 < r₀ / 2))]
  exact hvBound

/-! ### Exponential domination -/

end DivergenceFormProcess.Decay
