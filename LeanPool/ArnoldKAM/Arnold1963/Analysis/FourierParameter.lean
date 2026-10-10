/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Analysis.ParameterIntegral
public import LeanPool.ArnoldKAM.Arnold1963.Analysis.FourierDecay

/-!
Analytic dependence of Fourier coefficients and angle averages on action parameters, together
with the centered perturbation and its uniform norm bound.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set Complex
open scoped NNReal
namespace KamProject.Arnold1963

/-- Normalized Haar measure for analytic dependence of Fourier coefficients on the action. -/
local instance fourierParameterMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance fourierParameterProbability :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem analyticAt_fourierMonomial {n : ℕ} (k : FourierIndex n) (q : ComplexSpace n) :
    AnalyticAt ℂ (fourierMonomial k) q := by
  apply AnalyticAt.cexp'
  apply AnalyticAt.mul analyticAt_const
  apply Finset.analyticAt_fun_sum
  intro j hj
  apply analyticAt_const.mul
  convert (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) j).analyticAt q
    using 1
  rfl

namespace AnalyticPhaseFunction
variable {n : ℕ} {G : Set (ComplexSpace n)} {ρ : ℝ≥0}

theorem fourierCoeff_eq_cubeIntegral_all (f : AnalyticPhaseFunction n G ρ)
    (p : ComplexSpace n) (k : FourierIndex n) :
    f.fourierCoeff p k = unitCubeIntegral (fun t =>
      f.toFun (p, scaledAngle t) * fourierMonomial (-k) (scaledAngle t)) := by
  rw [fourierCoeff, UnitAddTorus.mFourierCoeff_eq_integral _ _ (0 : RealSpace n)]
  simp only [Pi.zero_apply, zero_add, smul_eq_mul]
  unfold unitCubeIntegral
  rw [unitCubeMeasure_eq_restrict_Ioc]
  apply setIntegral_congr_fun (show MeasurableSet {t : RealSpace n | ∀ j, t j ∈ Ioc 0 1} by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter (fun j => measurableSet_Ioc.preimage (measurable_pi_apply j)))
  intro t ht
  have he : unitTorusRepr (fun j => (t j : UnitAddCircle)) = t := by
    ext j
    exact AddCircle.equivIoc_coe_of_mem (by simpa using ht j)
  simp only [torusValue, he, mFourier_eq_fourierMonomial, mul_comm]

theorem analyticOnNhd_fourierCoeff (f : AnalyticPhaseFunction n G ρ) (k : FourierIndex n) :
    AnalyticOnNhd ℂ (fun p => f.fourierCoeff p k) G := by
  intro p hp
  have hK : IsCompact (unitCube n) := isCompact_univ_pi (fun _ => isCompact_Icc)
  have hKm : MeasurableSet (unitCube n) :=
    MeasurableSet.univ_pi (fun _ => measurableSet_Icc)
  have hA := analyticAt_integral_compact (μ := unitCubeMeasure n)
    (f := fun z : ComplexPhaseSpace n => f.toFun z * fourierMonomial (-k) z.2)
    (continuous_scaledAngle n) hK hKm (p := p) (by
      intro t ht
      exact (f.analytic _ ⟨hp, scaledAngle_mem_strip t ρ⟩).mul
        ((analyticAt_fourierMonomial (-k) _).comp (f := Prod.snd) analyticAt_snd))
  have hm : (unitCubeMeasure n).restrict (unitCube n) = unitCubeMeasure n := by
    rw [unitCubeMeasure_eq_restrict, Measure.restrict_restrict hKm, inter_self]
  simp only [hm] at hA
  have heq : (fun a => f.fourierCoeff a k) = (fun a => unitCubeIntegral (fun t =>
      f.toFun (a, scaledAngle t) * fourierMonomial (-k) (scaledAngle t))) :=
    funext (fun a => f.fourierCoeff_eq_cubeIntegral_all a k)
  rw [heq]
  exact hA

theorem analyticOnNhd_angleAverage (f : AnalyticPhaseFunction n G ρ) :
    AnalyticOnNhd ℂ f.angleAverage G := f.analyticOnNhd_fourierCoeff 0

theorem analyticOnNhd_fourierTruncation (f : AnalyticPhaseFunction n G ρ) (N : ℝ) :
    AnalyticOnNhd ℂ (fun z : ComplexPhaseSpace n =>
      fourierTruncation (f.fourierCoeff z.1) N z.2) (phaseDomain G ρ) := by
  intro z hz
  apply Finset.analyticAt_fun_sum
  intro k hk
  exact (((f.analyticOnNhd_fourierCoeff k) _ hz.1).comp (f := Prod.fst) analyticAt_fst).mul
    ((analyticAt_fourierMonomial k _).comp (f := Prod.snd) analyticAt_snd)

/-- The angle average packaged as an analytic phase function independent of the angles. -/
def angleAverageFunction (f : AnalyticPhaseFunction n G ρ) : AnalyticPhaseFunction n G ρ where
  toFun z := f.angleAverage z.1
  domain_conj := f.domain_conj
  analytic := fun z hz => (f.analyticOnNhd_angleAverage z.1 hz.1).comp
    (f := Prod.fst) analyticAt_fst
  periodic := by intro p hp q hq m; rfl
  conj_compatible := by
    intro z hz
    exact f.angleAverage_conj hz.1
  bounded := ⟨f.uniformNorm, (f.norm_le_iff.mp le_rfl).nonneg,
    fun z hz => f.norm_angleAverage_le hz.1⟩

theorem uniformNorm_angleAverageFunction_le (f : AnalyticPhaseFunction n G ρ) :
    f.angleAverageFunction.uniformNorm ≤ f.uniformNorm :=
  (norm_le_iff _).mpr ⟨(f.norm_le_iff.mp le_rfl).nonneg, fun _ hz => f.norm_angleAverage_le hz.1⟩

/-- The phase function with its angle average removed. -/
def centered (f : AnalyticPhaseFunction n G ρ) : AnalyticPhaseFunction n G ρ :=
  f.sub f.angleAverageFunction

theorem uniformNorm_centered_le (f : AnalyticPhaseFunction n G ρ) :
    f.centered.uniformNorm ≤ 2 * f.uniformNorm := by
  have h := (f.uniformNorm_sub_le f.angleAverageFunction).trans
    (add_le_add_right f.uniformNorm_angleAverageFunction_le f.uniformNorm)
  simpa only [centered, two_mul] using h

theorem angleAverage_centered_eq_zero (f : AnalyticPhaseFunction n G ρ)
    {p : ComplexSpace n} (hp : p ∈ G) : f.centered.angleAverage p = 0 := by
  rw [angleAverage_eq_integral]
  exact f.integral_centered_eq_zero hp

end AnalyticPhaseFunction
end KamProject.Arnold1963
