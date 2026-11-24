/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.BallSubmean
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.LocalPshDiscControl
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.PshRegularDistribution
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Almost-everywhere comparison for plurisubharmonic functions

An almost-everywhere upper bound by an upper semicontinuous function is a
pointwise upper bound for a plurisubharmonic function. The proof uses the
nonnegative ball deficit estimate, so neither local integrability nor finite
values from below are assumptions. In particular, the function identically
equal to negative infinity is included.
-/

@[expose] public section

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology ENNReal Distributions

namespace SGPT.Foundations.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Almost-everywhere comparison with an upper semicontinuous function implies
pointwise comparison for actual PSH germs. The comparison function may even
take the value `⊤`; no local integrability assumption is needed. -/
theorem PlurisubharmonicOn.le_of_ae_le {u v : E → EReal} {Ω : Set E}
    (hu : PlurisubharmonicOn u Ω) (hΩ : IsOpen Ω)
    (hv : UpperSemicontinuousOn v Ω)
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (hae : ∀ᵐ y ∂μ.restrict Ω, u y ≤ v y) :
    ∀ x ∈ Ω, u x ≤ v x := by
  intro x hx
  by_contra hle
  have hlt : v x < u x := lt_of_not_ge hle
  obtain ⟨q, hvq, hqu⟩ := EReal.exists_rat_btwn_of_lt hlt
  have hux := hu x hx
  have hxbot : u x ≠ ⊥ := ne_of_gt (bot_le.trans_lt hlt)
  have hxreal : ((u x).toReal : EReal) = u x := EReal.coe_toReal hux.ne_top hxbot
  have hqreal : (q : ℝ) < (u x).toReal := by
    apply EReal.coe_lt_coe_iff.mp
    exact hqu.trans_le hxreal.symm.le
  obtain ⟨U, hU, hxU, hdisc⟩ := hux
  have hvc : ∀ᶠ y in 𝓝 x, v y < ((q : ℝ) : EReal) := by
    have h := hv x hx _ hvq
    rwa [nhdsWithin_eq_nhds.mpr (hΩ.mem_nhds hx)] at h
  have hnbhd : {y | y ∈ U ∧ y ∈ Ω ∧ v y < ((q : ℝ) : EReal)} ∈ 𝓝 x := by
    filter_upwards [hU.mem_nhds hxU, hΩ.mem_nhds hx, hvc] with y hyU hyΩ hyv
    exact ⟨hyU, hyΩ, hyv⟩
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hnbhd
  have hR : 0 < ε / 2 := half_pos hε
  have hsmall : closedBall x (ε / 2) ⊆
      {y | y ∈ U ∧ y ∈ Ω ∧ v y < ((q : ℝ) : EReal)} :=
    (closedBall_subset_ball (half_lt_self hε)).trans hεsub
  have hBU : ball x (ε / 2) ⊆ U :=
    fun y hy => (hsmall (ball_subset_closedBall hy)).1
  have hBΩ : ball x (ε / 2) ⊆ Ω :=
    fun y hy => (hsmall (ball_subset_closedBall hy)).2.1
  obtain ⟨C, hC⟩ := hdisc.exists_compact_upper_bound
    (isCompact_closedBall x (ε / 2)) ⟨x, mem_closedBall_self hR.le⟩
    (fun y hy => (hsmall hy).1)
  have hxC : (u x).toReal ≤ C := EReal.coe_le_coe_iff.mp
    (hxreal.le.trans (hC x (mem_closedBall_self hR.le)))
  have huc : ∀ᵐ y ∂μ.restrict (ball x (ε / 2)), u y ≤ ((q : ℝ) : EReal) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hBΩ hae,
      ae_restrict_mem measurableSet_ball] with y hy hyB
    exact hy.trans (hsmall (ball_subset_closedBall hyB)).2.2.le
  have hlower : ENNReal.ofReal (C - (q : ℝ)) * μ (ball 0 (ε / 2)) ≤
      ∫⁻ y in ball x (ε / 2), ((C : EReal) - u y).toENNReal ∂μ := by
    calc
      _ = ∫⁻ y in ball x (ε / 2), ENNReal.ofReal (C - (q : ℝ)) ∂μ := by
        simp [lintegral_const, μ.addHaar_ball_center x (ε / 2)]
      _ ≤ _ := lintegral_mono_ae (huc.mono (fun y hy => by
        calc
          ENNReal.ofReal (C - (q : ℝ)) =
              ((C : EReal) - ((q : ℝ) : EReal)).toENNReal := by
            rw [← EReal.coe_sub, EReal.real_coe_toENNReal]
          _ ≤ _ := EReal.toENNReal_le_toENNReal (EReal.sub_le_sub le_rfl hy)))
  have hupper := hdisc.ball_deficit_le μ x (ε / 2) C hBU
    (fun y hy => hC y (ball_subset_closedBall hy))
  have hcenter : ((C : EReal) - u x).toENNReal =
      ENNReal.ofReal (C - (u x).toReal) := by
    conv_lhs => rw [← hxreal]
    rw [← EReal.coe_sub, EReal.real_coe_toENNReal]
  rw [hcenter, mul_comm (μ (ball 0 (ε / 2)))] at hupper
  have hdeficit : ENNReal.ofReal (C - (q : ℝ)) ≤
      ENNReal.ofReal (C - (u x).toReal) :=
    (ENNReal.mul_le_mul_iff_left (ne_of_gt (Metric.measure_ball_pos μ (0 : E) hR))
      measure_ball_ne_top).mp (hlower.trans hupper)
  have hreal := (ENNReal.ofReal_le_ofReal_iff (sub_nonneg.mpr hxC)).mp hdeficit
  linarith

/-- Two plurisubharmonic functions that agree almost everywhere agree at
every point of their open domain, including points with value `⊥`. -/
theorem PlurisubharmonicOn.eqOn_of_ae_eq {u v : E → EReal} {Ω : Set E}
    (hu : PlurisubharmonicOn u Ω) (hv : PlurisubharmonicOn v Ω) (hΩ : IsOpen Ω)
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (hae : u =ᵐ[μ.restrict Ω] v) : EqOn u v Ω := by
  have huv := hu.le_of_ae_le hΩ hv.upperSemicontinuousOn μ (hae.mono (fun _ h => h.le))
  have hvu := hv.le_of_ae_le hΩ hu.upperSemicontinuousOn μ (hae.mono (fun _ h => h.ge))
  exact fun x hx => le_antisymm (huv x hx) (hvu x hx)

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in
/-- Equality of actual regular distributions determines their locally
integrable real densities almost everywhere on the test-function domain.
The density-separation theorem is supplied by mathlib. -/
theorem ae_eq_of_regularDistribution_eq {Ω : Opens E} {f g : E → ℝ}
    (μ : Measure E) (hf : LocallyIntegrableOn f Ω μ) (hg : LocallyIntegrableOn g Ω μ)
    (heq : regularDistribution μ f hf = regularDistribution μ g hg) :
    f =ᵐ[μ.restrict Ω] g := by
  have hzero : ∀ᵐ x ∂μ, x ∈ Ω → (f - g) x = 0 := by
    apply Ω.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hf.sub hg)
    intro φ hφ hφc hφΩ
    let ψ : 𝓓(Ω, ℝ) := ⟨φ, hφ, hφc, hφΩ⟩
    have htest := congrArg (fun T : 𝓓'(Ω, ℝ) => T ψ) heq
    rw [regularDistribution_apply, regularDistribution_apply] at htest
    simp only [ψ, TestFunction.coe_mk] at htest
    have hfφ : Integrable (fun x => φ x * f x) μ := by
      simpa only [ContinuousLinearMap.mul_apply', ψ, TestFunction.coe_mk] using
        ψ.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ) hf
    have hgφ : Integrable (fun x => φ x * g x) μ := by
      simpa only [ContinuousLinearMap.mul_apply', ψ, TestFunction.coe_mk] using
        ψ.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ) hg
    change (∫ x, φ x * (f x - g x) ∂μ) = 0
    simp_rw [mul_sub]
    rw [integral_sub hfφ hgφ]
    exact sub_eq_zero.mpr htest
  apply (ae_restrict_iff' Ω.isOpen.measurableSet).mpr
  exact hzero.mono (fun x hx hxΩ => sub_eq_zero.mp (hx hxΩ))

/-- Equality of regular distributions of genuine almost-everywhere real
representatives determines their PSH potentials. The representative hypotheses
exclude identifying `⊥` with the zero value of its `toReal`. -/
theorem PlurisubharmonicOn.eqOn_of_regularDistribution_eq
    {u v : E → EReal} {Ω : Opens E}
    (hu : PlurisubharmonicOn u Ω) (hv : PlurisubharmonicOn v Ω)
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (hui : LocallyIntegrableOn (fun x => (u x).toReal) Ω μ)
    (hvi : LocallyIntegrableOn (fun x => (v x).toReal) Ω μ)
    (hua : (fun x => ((u x).toReal : EReal)) =ᵐ[μ.restrict Ω] u)
    (hva : (fun x => ((v x).toReal : EReal)) =ᵐ[μ.restrict Ω] v)
    (heq : regularDistribution μ (fun x => (u x).toReal) hui =
      regularDistribution μ (fun x => (v x).toReal) hvi) : EqOn u v Ω := by
  apply hu.eqOn_of_ae_eq hv Ω.isOpen μ
  have hreal := ae_eq_of_regularDistribution_eq μ hui hvi heq
  filter_upwards [hua, hva, hreal] with x hux hvx hrealx
  exact hux.symm.trans ((congrArg (fun r : ℝ => (r : EReal)) hrealx).trans hvx)

/-- A nontrivial PSH potential on a preconnected open domain is determined by
its actual regular distribution. Local integrability and genuine real
representatives follow from the PSH hypotheses. -/
theorem pshRegularDistribution_eq_iff {u v : E → EReal} {Ω : Opens E}
    (hu : PlurisubharmonicOn u Ω) (hv : PlurisubharmonicOn v Ω)
    (μ : Measure E) [μ.IsAddHaarMeasure] (hΩ : IsPreconnected (Ω : Set E))
    (hnu : ∃ a ∈ Ω, u a ≠ ⊥) (hnv : ∃ a ∈ Ω, v a ≠ ⊥) :
    pshRegularDistribution hu μ hΩ hnu = pshRegularDistribution hv μ hΩ hnv ↔
      EqOn u v Ω := by
  constructor
  · intro heq
    exact hu.eqOn_of_regularDistribution_eq hv μ
      (hu.locallyIntegrableOn_toReal μ hΩ hnu) (hv.locallyIntegrableOn_toReal μ hΩ hnv)
      (hu.ae_coe_toReal μ hΩ hnu) (hv.ae_coe_toReal μ hΩ hnv) heq
  · intro heq
    apply pshRegularDistribution_congr_ae_on hu hv μ hΩ hnu hnv
    filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with x hx
    exact heq hx

end SGPT.Foundations.Analysis
