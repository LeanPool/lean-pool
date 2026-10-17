/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.Decay.BallAverage
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.ScalarWeakSolution
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Ported.EquationRestriction
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Ported.ZerothOrderSchauderBall

/-!
# Pointwise

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Pointwise interior bound from a local `L²` bound

The interior Hölder estimate for small contrast turns the local `L²` size of a
solution into a pointwise bound at the centre of a ball: the value at the
centre is bounded by the `L²` average on any concentric sub-ball plus the
Hölder modulus at that radius.  Shrinking the sub-ball trades the two terms
against each other.

The small-contrast hypothesis is the price of using the interior Schauder
chain of the regularity layer.  A general elliptic field would need a
De Giorgi--Nash--Moser local boundedness estimate, which the layer does not
carry.

## Main results

- `DivergenceFormProcess.Decay.zerothOrderOn_restrict_of_isScalarForcedWeakSolution`
- `DivergenceFormProcess.Decay.exists_representative_abs_center_le`
-/

noncomputable section

namespace DivergenceFormProcess.Decay

open HCPolySupport MeasureTheory
open DivergenceFormProcess.Form
open Algsuperdiff.StochasticProcess.Common.Regularity.Ported
open scoped ENNReal

variable {d : ℕ}

/-- The zero extension of a test function pairs with a fixed scalar field
exactly as the original test function does. -/
theorem setIntegral_mul_extendByZero {W V : Set (Vec d)} (hW : IsOpen W)
    (hV : IsOpen V) (hVW : V ⊆ W) (g : Vec d → ℝ) (phi : H10Function V) :
    (∫ p in W, g p *
        (phi.extendByZeroToOpenSuperset hV.measurableSet hW hVW).toH1Function.toFun p
        ∂volume) =
      ∫ p in V, g p * phi.toH1Function.toFun p ∂volume := by
  have hind : (fun p => g p *
        (phi.extendByZeroToOpenSuperset hV.measurableSet hW hVW).toH1Function.toFun p)
      = Set.indicator V (fun p => g p * phi.toH1Function.toFun p) := by
    funext p
    by_cases hp : p ∈ V
    · rw [Set.indicator_of_mem hp,
        HCPolySupport.H10Function.extendByZeroToOpenSuperset_toFun,
        HCPolySupport.H10Function.zeroExtension, Set.indicator_of_mem hp]
    · rw [Set.indicator_of_notMem hp,
        HCPolySupport.H10Function.extendByZeroToOpenSuperset_toFun,
        HCPolySupport.H10Function.zeroExtension, Set.indicator_of_notMem hp,
        mul_zero]
  rw [hind, MeasureTheory.integral_indicator hV.measurableSet,
    Measure.restrict_restrict hV.measurableSet, Set.inter_eq_left.mpr hVW]

/-- The pointwise scalar equation restricts from an open set to an open
subset, in the zeroth-order carrier consumed by the Schauder chain. -/
theorem zerothOrderOn_restrict_of_isScalarForcedWeakSolution
    {a : CoeffField d} {W V : Set (Vec d)} (hW : IsOpen W) (hV : IsOpen V)
    (hVW : V ⊆ W) {g : Vec d → ℝ} {u : H1Function W}
    (h : IsScalarForcedWeakSolution a W g u) :
    IsMatrixDivFormWeakSolutionZerothOrderOn a V (u.restrict hV hVW) g 0 := by
  intro phi
  have hflux := setIntegral_vecDot_extendByZero hW hV hVW
    (fun p => matVecMul (a p) (u.grad p)) phi
  have hforce := setIntegral_mul_extendByZero hW hV hVW g phi
  have hzero : (∫ x in V, vecDot ((0 : Vec d → Vec d) x)
      (phi.toH1Function.grad x) ∂volume) = 0 := by
    have : ∀ x : Vec d, vecDot ((0 : Vec d → Vec d) x)
        (phi.toH1Function.grad x) = 0 := by
      intro x
      simp only [vecDot, Pi.ofNat_apply, zero_mul, Finset.sum_const_zero]
    simp only [this, integral_zero]
  rw [hzero, sub_zero]
  calc
    (∫ x in V, vecDot (matVecMul (a x) ((u.restrict hV hVW).grad x))
        (phi.toH1Function.grad x) ∂volume) =
        ∫ p in W, vecDot (matVecMul (a p) (u.grad p))
          ((phi.extendByZeroToOpenSuperset hV.measurableSet hW hVW).toH1Function.grad p)
          ∂volume := by
      change (∫ p in V, vecDot (matVecMul (a p) (u.grad p))
        (phi.toH1Function.grad p) ∂volume) = _
      exact hflux.symm
    _ = ∫ p in W, g p *
        (phi.extendByZeroToOpenSuperset hV.measurableSet hW hVW).toH1Function.toFun p
        ∂volume :=
      h.2 (phi.extendByZeroToOpenSuperset hV.measurableSet hW hVW)
    _ = ∫ p in V, g p * phi.toH1Function.toFun p ∂volume := hforce

/-- An essential bound gives membership in the `L^infinity` carrier. -/
theorem memScalarLInfOn_of_ae_abs_le {W : Set (Vec d)} {g : Vec d → ℝ} {G : ℝ}
    (hmeas : AEStronglyMeasurable g (volume.restrict W))
    (hbound : ∀ᵐ x ∂volume.restrict W, |g x| ≤ G) :
    MemScalarLInfOn W g := by
  refine memLp_top_of_bound hmeas G ?_
  filter_upwards [hbound] with x hx
  simpa only [Real.norm_eq_abs] using hx

/-- An essential bound bounds the `L^infinity` size. -/
theorem scalarLInfSizeOn_le_of_ae_abs_le {W : Set (Vec d)} {g : Vec d → ℝ}
    {G : ℝ} (hG : 0 ≤ G) (hbound : ∀ᵐ x ∂volume.restrict W, |g x| ≤ G) :
    scalarLInfSizeOn W g ≤ G := by
  by_cases hmeas : AEStronglyMeasurable g (volume.restrict W)
  swap
  · simp only [scalarLInfSizeOn, eLpNorm_of_not_aestronglyMeasurable hmeas, ENNReal.toReal_top]
    exact hG
  have hess : eLpNorm g ⊤ (volume.restrict W) ≤ ENNReal.ofReal G := by
    rw [eLpNorm_exponent_top hmeas]
    refine eLpNormEssSup_le_of_ae_bound ?_
    filter_upwards [hbound] with x hx
    simpa only [Real.norm_eq_abs] using hx
  exact ENNReal.toReal_le_of_le_ofReal hG hess

/-- Interior pointwise bound at the centre of a ball, under small contrast.
The value of the continuous representative at the centre is bounded by the
`L²` average on every concentric sub-ball of radius at most `r / 2`, plus the
Schauder Hölder modulus at that radius. -/
theorem exists_representative_abs_center_le [NeZero d]
    {a : CoeffField d} {Om : Set (Vec d)} (hOm : IsOpen Om)
    {u : H1Function Om} {g : Vec d → ℝ} {G E delta alpha : ℝ}
    (hd : 2 ≤ d) (halpha : alpha ∈ Set.Ico (1 / 2 : ℝ) 1)
    (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ smallContrastThreshold d alpha)
    (hameas : Measurable a)
    (ha : CoefficientIdentityDistanceLE Om a delta)
    (hsol : IsScalarForcedWeakSolution a Om g u)
    {x₀ : Vec d} {r : ℝ} (hr : 0 < r) (hball : euclideanBall x₀ r ⊆ Om)
    (hG : 0 ≤ G)
    (hgb : ∀ᵐ x ∂volumeMeasureOn (euclideanBall x₀ r), |g x| ≤ G)
    (hE : vectorLpSizeOn (euclideanBall x₀ r) 2 u.grad ≤ E) :
    ∃ v : Vec d → ℝ,
      ContinuousOn v (euclideanBall x₀ (r / 2)) ∧
      v =ᵐ[volume.restrict (euclideanBall x₀ r)] u.toFun ∧
      ∀ rho : ℝ, 0 < rho → rho ≤ r / 2 →
        |v x₀| ≤
          Real.sqrt (∫ y in euclideanBall x₀ rho, u.toFun y ^ 2 ∂volume) /
              Real.sqrt ((volume (smallContrastUnitBall d)).toReal * rho ^ d) +
            smallContrastZerothSchauderConstant d *
              (r ^ (1 - alpha - (d : ℝ) / 2) * E + r ^ (2 - alpha) * G) *
              rho ^ alpha := by
  classical
  have halpha0 : 0 < alpha := lt_of_lt_of_le (by norm_num) halpha.1
  have hBopen : IsOpen (euclideanBall x₀ r) := isOpen_euclideanBall x₀ r
  have hEnn : 0 ≤ E := le_trans ENNReal.toReal_nonneg hE
  have haBall : CoefficientIdentityDistanceLE (euclideanBall x₀ r) a delta :=
    ae_restrict_of_ae_restrict_of_subset hball ha
  have hgBall : ∀ᵐ x ∂volume.restrict (euclideanBall x₀ r), |g x| ≤ G := hgb
  have hgmeas : AEStronglyMeasurable g (volume.restrict (euclideanBall x₀ r)) :=
    (hsol.1.mono_measure (Measure.restrict_mono hball le_rfl)).aestronglyMeasurable
  have hgLInf : MemScalarLInfOn (euclideanBall x₀ r) g :=
    memScalarLInfOn_of_ae_abs_le hgmeas hgBall
  have hgSize : scalarLInfSizeOn (euclideanBall x₀ r) g ≤ G :=
    scalarLInfSizeOn_le_of_ae_abs_le hG hgBall
  have hrestrict := zerothOrderOn_restrict_of_isScalarForcedWeakSolution
    hOm hBopen hball hsol
  obtain ⟨v, hvcont, hvae, hvholder⟩ :=
    schauder_holder_euclideanBall_zerothOrder (a := a) x₀ hr hd halpha hdelta0
      hdelta hameas haBall hrestrict hgLInf
  refine ⟨v, hvcont, ?_, ?_⟩
  · exact hvae
  · intro rho hrho hrhor
    set K : ℝ := smallContrastZerothSchauderConstant d *
      (r ^ (1 - alpha - (d : ℝ) / 2) * E + r ^ (2 - alpha) * G) with hK
    have hKnn : 0 ≤ K := by
      refine mul_nonneg (smallContrastZerothSchauderConstant_nonneg d) ?_
      exact add_nonneg (mul_nonneg (Real.rpow_nonneg hr.le _) hEnn)
        (mul_nonneg (Real.rpow_nonneg hr.le _) hG)
    have hKmono : smallContrastZerothSchauderConstant d *
        (r ^ (1 - alpha - (d : ℝ) / 2) *
            vectorLpSizeOn (euclideanBall x₀ r) 2 u.grad +
          r ^ (2 - alpha) * scalarLInfSizeOn (euclideanBall x₀ r) g) ≤ K := by
      rw [hK]
      refine mul_le_mul_of_nonneg_left ?_
        (smallContrastZerothSchauderConstant_nonneg d)
      exact add_le_add
        (mul_le_mul_of_nonneg_left hE (Real.rpow_nonneg hr.le _))
        (mul_le_mul_of_nonneg_left hgSize (Real.rpow_nonneg hr.le _))
    have hballmono : ∀ s t : ℝ, 0 ≤ s → s ≤ t →
        euclideanBall x₀ s ⊆ euclideanBall x₀ t := by
      intro s t hs hst y hy
      have hy' : euclideanSqDist y x₀ < s ^ 2 := hy
      exact lt_of_lt_of_le hy' (pow_le_pow_left₀ hs hst 2)
    have hsubHalf : euclideanBall x₀ rho ⊆ euclideanBall x₀ (r / 2) :=
      hballmono rho (r / 2) hrho.le hrhor
    have hsubR : euclideanBall x₀ rho ⊆ euclideanBall x₀ r :=
      hballmono rho r hrho.le (by linarith only [hrhor, hr])
    have hcenter : x₀ ∈ euclideanBall x₀ (r / 2) := by
      have : euclideanSqDist x₀ x₀ = 0 := euclideanSqDist_self x₀
      change euclideanSqDist x₀ x₀ < (r / 2) ^ 2
      rw [this]
      positivity
    have hoscill : ∀ y ∈ euclideanBall x₀ rho, |v x₀ - v y| ≤ K * rho ^ alpha := by
      intro y hy
      have hyhalf : y ∈ euclideanBall x₀ (r / 2) := hsubHalf hy
      have hbound := hvholder x₀ hcenter y hyhalf
      have hnorm : euclideanNorm (x₀ - y) ≤ rho := by
        have hy' : euclideanSqDist y x₀ < rho ^ 2 := hy
        rw [euclideanSqDist] at hy'
        have hsymm : vecNormSq (x₀ - y) = vecNormSq (y - x₀) := by
          simp only [vecNormSq, vecDot]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [Pi.sub_apply]
          ring
        have hsq : euclideanNorm (x₀ - y) ^ 2 < rho ^ 2 := by
          rw [euclideanNorm_sq, hsymm]
          exact hy'
        exact le_of_lt (lt_of_pow_lt_pow_left₀ 2 hrho.le hsq)
      have hpow : euclideanNorm (x₀ - y) ^ alpha ≤ rho ^ alpha :=
        Real.rpow_le_rpow (euclideanNorm_nonneg _) hnorm halpha0.le
      calc
        |v x₀ - v y| ≤ smallContrastZerothSchauderConstant d *
            (r ^ (1 - alpha - (d : ℝ) / 2) *
                vectorLpSizeOn (euclideanBall x₀ r) 2 u.grad +
              r ^ (2 - alpha) * scalarLInfSizeOn (euclideanBall x₀ r) g) *
            euclideanNorm (x₀ - y) ^ alpha := hbound
        _ ≤ K * euclideanNorm (x₀ - y) ^ alpha :=
          mul_le_mul_of_nonneg_right hKmono (Real.rpow_nonneg (euclideanNorm_nonneg _) _)
        _ ≤ K * rho ^ alpha := mul_le_mul_of_nonneg_left hpow hKnn
    have hvaeRho : v =ᵐ[volume.restrict (euclideanBall x₀ rho)] u.toFun :=
      ae_restrict_of_ae_restrict_of_subset hsubR hvae
    have hwLp : MemLp u.toFun 2 (volume.restrict (euclideanBall x₀ rho)) :=
      u.memL2.mono_measure (Measure.restrict_mono (hsubR.trans hball) le_rfl)
    exact abs_center_le_of_holder hrho hoscill hvaeRho hwLp

end DivergenceFormProcess.Decay
