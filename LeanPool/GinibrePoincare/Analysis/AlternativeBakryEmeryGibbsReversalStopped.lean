/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeBakryEmeryGibbsReversalStopped.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryGibbsReversalAction
public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianOUReferenceProcess
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticCompactItoIntegral
public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianInteractionTilt
public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralTiltPathLaw
public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralTiltVolterra
public import LeanPool.GinibrePoincare.Analysis.BrownianStoppingExitCountableEvaluation
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticContinuousStoppingTime

/-! The actual OU reference admits compact ball stopping for every initial
configuration, without collision restrictions or stochastic witnesses. -/

@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

theorem bakryEmeryGibbsOU_reference_compact_stopped_exists {Ω : Type*} [mAmbient : MeasurableSpace
    Ω]
    (n : ℕ) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P) (α : ℝ)
    (z : Configuration n) (r : ℝ) (hr : 0 < r) (T : ℝ≥0) (hT : 0 < T) :
    ∃ K : Set (Configuration n), K = Metric.closedBall z r ∧ IsCompact K ∧
      ∃ Y : ℝ≥0 → Ω → Configuration n,
      (∀ ω, Continuous (fun t => Y t ω)) ∧ (∀ t ω, Y t ω ∈ K) ∧
      (∀ ω, Y 0 ω = z) ∧
      StronglyAdapted (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal))
          Y ∧
      ∃ θ : Ω → ℝ≥0,
      IsStoppingTime (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal))
        (fun ω => (θ ω : WithTop ℝ≥0)) ∧ (∀ ω, 0 < θ ω ∧ θ ω ≤ T) ∧
      (∀ t ω, Y t ω = ginibreHamiltonianOUReferenceProcess n α z B (min t (θ ω)) ω) ∧
      θ = hittingBtwn (fun t sample => ginibreHamiltonianOUReferenceProcess n α z B t sample-z)
        {x | r ≤ ‖x‖} 0 T ∧
      ∀ᵐ ω ∂P, ∀ t ≤ θ ω, Y t ω = z+ginibreConfigurationBrownianNoise n B α ω t+
        ∫ s in (0 : ℝ)..t, (-2*α/(n : ℝ)) • Y s.toNNReal ω := by
  let K := Metric.closedBall z r
  let U := ginibreHamiltonianOUReferenceProcess n α z B
  have hUC := ginibreHamiltonianOUReferenceProcess_continuous n α z B
  have hUA := ginibreHamiltonianOUReferenceProcess_stronglyAdapted n α z B P hB
  let V : ℝ≥0 → Ω → Configuration n := fun t ω => U t ω-z
  have hVC (ω : Ω) : Continuous (fun t => V t ω) := (hUC ω).sub continuous_const
  have hVA : StronglyAdapted (ginibreBrownianAugmentedFiltration B P (fun i => (hB
      i).toIsPreBrownianReal)) V :=
    fun t => (hUA t).sub stronglyMeasurable_const
  let θ := hittingBtwn V {x | r ≤ ‖x‖} 0 T
  have hStop := ginibreContinuous_norm_exit_isStoppingTime _ V hVA hVC r T
  have hθT (ω : Ω) : θ ω ≤ T := hittingBtwn_le ω
  have hθpos (ω : Ω) : 0 < θ ω :=
    drivenContinuous_closed_hitting_pos V _ (isClosed_le continuous_const continuous_norm) T hT ω
      (hVC ω) (by simpa [V, U, ginibreHamiltonianOUReferenceProcess_zero] using not_le_of_gt hr)
  let Y : ℝ≥0 → Ω → Configuration n := fun t ω => U (min t (θ ω)) ω
  have hYC (ω : Ω) : Continuous (fun t => Y t ω) := (hUC ω).comp (continuous_id.min
      continuous_const)
  have hYR (t : ℝ≥0) (ω : Ω) : Y t ω ∈ K := by
    apply Metric.mem_closedBall.mpr
    rw [dist_eq_norm]
    exact drivenContinuous_norm_le_until_hitting V r T ω (hVC ω)
      (by simp [V, U, ginibreHamiltonianOUReferenceProcess_zero, hr.le]) _ (min_le_right t (θ ω))
  have hYA : StronglyAdapted (ginibreBrownianAugmentedFiltration B P (fun i => (hB
      i).toIsPreBrownianReal)) Y := by
    let F := ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal)
    intro s
    have hm (k : ℕ) : @StronglyMeasurable Ω (Configuration n) _ (F s)
        (fun ω => U (min s (stoppingUpperGrid k (θ ω))) ω) :=
      (adapted_capped_upper_grid_evaluation_measurable F U hUA.adapted θ hStop k
          s).stronglyMeasurable
    apply stronglyMeasurable_of_tendsto atTop hm
    rw [tendsto_pi_nhds]
    intro ω
    exact (hUC ω).continuousAt.tendsto.comp (tendsto_const_nhds.min (stoppingUpperGrid_tendsto (θ
        ω)))
  refine ⟨K, rfl, isCompact_closedBall z r, Y, hYC, hYR,?_, hYA, θ, hStop,
    fun ω => ⟨hθpos ω, hθT ω⟩, fun t ω => rfl, rfl,?_⟩
  · intro ω
    simp [Y, U, ginibreHamiltonianOUReferenceProcess_zero]
  · filter_upwards [ginibreHamiltonianOUReferenceProcess_original_equation n α z B P hB] with ω hω
    intro t ht
    change U (min t (θ ω)) ω = _
    have huEq : U t ω = z+ginibreConfigurationBrownianNoise n B α ω t+
        ∫ s in (0 : ℝ)..t, (-2*α/(n : ℝ)) • U s.toNNReal ω := hω t
    rw [min_eq_left ht, huEq]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    have hsI : s ∈ Icc (0 : ℝ) (t : ℝ) := by
      simpa only [uIcc_of_le (show (0 : ℝ) ≤ (t : ℝ) from t.property)] using hs
    have hst : s.toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.mpr hsI.2
    change (-2*α/(n : ℝ)) • U s.toNNReal ω = (-2*α/(n : ℝ)) • U (min s.toNNReal (θ ω)) ω
    rw [min_eq_left (hst.trans ht)]

/-- Actual stopped unit-diffusion OU and its relative-potential Itô
martingale. The compact stop and all analytic inputs are constructed inside. -/
theorem bakryEmeryGibbsOU_relative_ito_exists {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (W : Configuration n → ℝ) (hW : ContDiff ℝ 2 W)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i sample t => B i t sample) P)
    (z : Configuration n) (r : ℝ) (hr : 0 < r) (T : ℝ≥0) (hT : 0 < T) :
    ∃ Y : ℝ≥0 → Ω → Configuration n,
      (∀ sample, Continuous (fun t => Y t sample)) ∧
      (∀ t sample, Y t sample ∈ Metric.closedBall z r) ∧
      (∀ sample, Y 0 sample = z) ∧
      StronglyAdapted (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal))
          Y ∧
      ∃ θ : Ω → ℝ≥0,
      IsStoppingTime (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal))
        (fun sample => (θ sample : WithTop ℝ≥0)) ∧
      (∀ sample, 0 < θ sample ∧ θ sample ≤ T) ∧
      (∀ t sample, Y t sample = ginibreHamiltonianOUReferenceProcess n ((n : ℝ)^2) z B
        (min t (θ sample)) sample) ∧
      θ = hittingBtwn (fun t sample => ginibreHamiltonianOUReferenceProcess n ((n : ℝ)^2) z B t
          sample-z)
        {x | r ≤ ‖x‖} 0 T ∧
      ∃ J : ℝ≥0 → Ω → ℝ,
      Martingale J (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal)) P
          ∧
      (∀ sample, Continuous (fun t => J t sample)) ∧ (∀ t, MemLp (J t) 2 P) ∧
      J 0 =ᵐ[P] (fun _ => 0) ∧
      (∀ t ≤ T, TendstoInMeasure P
        (ginibreConfigurationBrownianGradientSum n B ((n : ℝ≥0)^2) Y
          (bakryEmeryGibbsRelativePotential W) t) atTop (J t)) ∧
      ∀ᵐ sample ∂P, ∀ t ≤ θ sample,
        bakryEmeryGibbsRelativePotential W (Y t sample) -
        bakryEmeryGibbsRelativePotential W z -
        (∫ s in (0 : ℝ)..t, fderiv ℝ (bakryEmeryGibbsRelativePotential W)
          (Y s.toNNReal sample) ((-2*(n : ℝ)) • Y s.toNNReal sample)) -
        (∫ s in (0 : ℝ)..t, configurationLaplacian (bakryEmeryGibbsRelativePotential W)
          (Y s.toNNReal sample)) = J t sample := by
  let α : ℝ≥0 := (n : ℝ≥0)^2
  have hα : (α : ℝ) = (n : ℝ)^2 := by simp [α]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hcoef : -2*(α : ℝ)/(n : ℝ) = -2*(n : ℝ) := by rw [hα]; field_simp
  obtain ⟨K, hKeq, hK, Y, hYC, hYR, hY0, hAdapt, θ, hStop, hθ, hStopped, hExit, hEq⟩ :=
    bakryEmeryGibbsOU_reference_compact_stopped_exists n B P hB α z r hr T hT
  let b : ℝ → Ω → Configuration n := fun s sample => (-2*(n : ℝ)) • Y s.toNNReal sample
  have hb (sample : Ω) : Continuous (fun s => b s sample) :=
    ((hYC sample).comp continuous_real_toNNReal).const_smul (-2*(n : ℝ))
  obtain ⟨R, hR, hRB⟩ := hK.isBounded.exists_pos_norm_le
  let M := |(-2*(n : ℝ))| * R
  have hM : 0 ≤ M := mul_nonneg (abs_nonneg _) hR.le
  have hbound : ∀ s ∈ Icc (0 : ℝ) T, ∀ sample, ‖b s sample‖ ≤ M := by
    intro s hs sample
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hRB _ (hYR _ _)) (abs_nonneg _)
  have hS : ContDiff ℝ 2 (bakryEmeryGibbsRelativePotential W) :=
    hW.sub (contDiff_const.mul (contDiff_configurationNormSq.of_le (by simp)))
  have hθm : Measurable θ := by
    have hm : Measurable (fun sample => (θ sample : WithTop ℝ≥0)) :=
      hStop.measurable.mono hStop.measurableSpace_le le_rfl
    simpa [Function.comp_def] using ENNReal.measurable_toNNReal.comp hm
  have hVol : ∀ᵐ sample ∂P, ∀ t ≤ θ sample, Y t sample = Y 0 sample +
      (ginibreConfigurationBrownianNoise n B α sample t -
        ginibreConfigurationBrownianNoise n B α sample 0) + ∫ s in (0 : ℝ)..t, b s sample := by
    filter_upwards [hEq, ginibreConfigurationBrownianNoise_actual n B P hB α] with sample hs hnz
    intro t ht
    rw [hY0, hnz.2, sub_zero]
    simpa only [hcoef] using hs t ht
  obtain ⟨J, hJM, hJC, hJL, hJ0, hLimit, hIto⟩ :=
    ginibreCompactVolterra_continuous_ito_integral_exists n B P hB hind α Y hAdapt hYC
      (bakryEmeryGibbsRelativePotential W) univ K isOpen_univ hS.contDiffOn hK
      (subset_univ _) hYR T b hb M hM hbound θ hθm (fun sample => (hθ sample).2) hVol
  refine ⟨Y, hYC,?_, hY0, hAdapt, θ, hStop, hθ,?_,?_, J, hJM, hJC, hJL, hJ0, hLimit,?_⟩
  · simpa [hKeq] using hYR
  · simpa only [hα] using hStopped
  · simpa only [hα] using hExit
  · filter_upwards [hIto] with sample hs
    intro t ht
    have he : (α : ℝ)/(n : ℝ)^2 = 1 := by rw [hα]; exact div_self (pow_ne_zero _ hn0)
    simpa only [ginibreConfigurationTestCompensator, hY0, he, one_mul] using hs t ht

/-- The drift tilt `-(√(2α / n²) / 2) * ∂_i S(z)` of the potential `S` in the real coordinate
direction `i`. -/
def bakryEmeryGibbsPotentialTilt (n : ℕ) (α : ℝ) (S : Configuration n → ℝ)
    (z : Configuration n) (i : Fin n × Fin 2) : ℝ :=
  -(Real.sqrt (2*α/(n : ℝ)^2)/2) * fderiv ℝ S z (ginibreCoordinateDirection i)

theorem bakryEmeryGibbsPotentialTilt_measurable (n : ℕ) (α : ℝ) (S : Configuration n → ℝ)
    (i : Fin n × Fin 2) : Measurable (fun z => bakryEmeryGibbsPotentialTilt n α S z i) :=
  measurable_const.mul (measurable_fderiv_apply_const ℝ S _)

theorem bakryEmeryGibbsPotentialTilt_continuous (n : ℕ) (α : ℝ) (S : Configuration n → ℝ)
    (hS : ContDiff ℝ 2 S) (i : Fin n × Fin 2) :
    Continuous (fun z => bakryEmeryGibbsPotentialTilt n α S z i) := by
  exact continuous_const.mul
    ((hS.fderiv_right (m := 1) (by norm_num)).continuous.clm_apply continuous_const)

theorem bakryEmeryGibbsPotentialTilt_compact_bound (n : ℕ) (α : ℝ) (S : Configuration n → ℝ)
    (hS : ContDiff ℝ 2 S) (K : Set (Configuration n)) (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ K, (∑ i, (bakryEmeryGibbsPotentialTilt n α S z i)^2) ≤ C^2 := by
  have hc : ContinuousOn (fun z => ∑ i, (bakryEmeryGibbsPotentialTilt n α S z i)^2) K :=
    continuousOn_finsetSum _ (fun i _ =>
      ((bakryEmeryGibbsPotentialTilt_continuous n α S hS i).continuousOn).pow 2)
  obtain ⟨R, hR, hb⟩ := (hK.image_of_continuousOn hc).isBounded.exists_pos_norm_le
  refine ⟨R+1, by linarith,?_⟩
  intro z hz
  have hh := hb _ (mem_image_of_mem _ hz)
  rw [Real.norm_eq_abs] at hh
  have hs := (le_abs_self (∑ i, (bakryEmeryGibbsPotentialTilt n α S z i)^2)).trans hh
  nlinarith [sq_nonneg R]

theorem bakryEmeryGibbsPotentialTilt_energy (n : ℕ) (α : ℝ) (hα : 0 ≤ α)
    (S : Configuration n → ℝ) (z : Configuration n) :
    (∑ i, (bakryEmeryGibbsPotentialTilt n α S z i)^2) =
      (α/(2*(n : ℝ)^2))*bakryEmeryGibbsConfigurationGradientSq S z := by
  unfold bakryEmeryGibbsPotentialTilt bakryEmeryGibbsConfigurationGradientSq
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, ginibreCoordinateDirection,
    ite_eq_right (by decide : (1 : Fin 2) ≠ 0)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hs : (Real.sqrt (2*α/(n : ℝ)^2))^2 = 2*α/(n : ℝ)^2 :=
    Real.sq_sqrt (div_nonneg (by linarith) (sq_nonneg _))
  simp only [mul_pow, neg_sq, div_pow, hs, ite_true]
  ring

/-- The actual interaction drift tilt has genuine normalized coordinate
exponential integrals on every compact collision-free adapted path. -/
theorem bakryEmeryGibbsPotentialTilt_exponential_exists {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (S : Configuration n → ℝ) (hS : ContDiff ℝ 2 S) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P :
        Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (α : ℝ≥0)
    (Y : ℝ≥0 → Ω → Configuration n)
    (hY : StronglyAdapted (ginibreBrownianAugmentedFiltration B P (fun i => (hB
        i).toIsPreBrownianReal)) Y)
    (hYC : ∀ ω, Continuous (fun t => Y t ω))
    (K : Set (Configuration n)) (hK : IsCompact K)
    (hRange : ∀ t ω, Y t ω ∈ K) (T : ℝ≥0) :
    ∃ M : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ,
      (∀ i, Martingale (M i) (ginibreBrownianAugmentedFiltration B P
        (fun i => (hB i).toIsPreBrownianReal)) P ∧
        (∀ ω, Continuous (fun t => M i t ω)) ∧ (∀ t, MemLp (M i t) 2 P) ∧
        M i 0 =ᵐ[P] (fun _ => 0) ∧
        ∀ t ≤ T, TendstoInMeasure P
          (fun k => brownianUniformLeftSum (B i)
            (fun r ω => bakryEmeryGibbsPotentialTilt n α S (Y r ω) i) t (k+1)) atTop (M i t)) ∧
      Integrable (brownianVectorExponentialIntegralDensity
        (fun i r ω => bakryEmeryGibbsPotentialTilt n α S (Y r ω) i) T (fun i => M i T)) P ∧
      (∫ ω, brownianVectorExponentialIntegralDensity
        (fun i r ω => bakryEmeryGibbsPotentialTilt n α S (Y r ω) i) T (fun i => M i T) ω ∂P)=1 := by
  obtain ⟨C, hC, hb⟩ := bakryEmeryGibbsPotentialTilt_compact_bound n α S hS K hK
  have hF (i : Fin n × Fin 2) (r : ℝ≥0) :
      @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P
        (fun i => (hB i).toIsPreBrownianReal) r) _
        (fun ω => bakryEmeryGibbsPotentialTilt n α S (Y r ω) i) :=
    (bakryEmeryGibbsPotentialTilt_measurable n α S i).comp (hY r).measurable
  have hc (i : Fin n × Fin 2) : ∀ᵐ ω ∂P,
      ContinuousOn (fun r => bakryEmeryGibbsPotentialTilt n α S (Y r ω) i) (Icc 0 T) :=
    ae_of_all P (fun ω => ((bakryEmeryGibbsPotentialTilt_continuous n α S hS i).comp
      (hYC ω)).continuousOn)
  obtain ⟨M, hM, hDi, hD1, hLimit⟩ := brownianBoundedVector_exponential_integral_exists_normalized
    B P hB hind (fun i r ω => bakryEmeryGibbsPotentialTilt n α S (Y r ω) i)
      hF C hC (fun r ω => hb _ (hRange r ω)) T hc
  exact ⟨M, hM, hDi, hD1⟩

theorem bakryEmeryGibbsPotentialTilt_leftSums {Ω : Type*} (n : ℕ) (S : Configuration n → ℝ)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (α : ℝ)
    (Y : ℝ≥0 → Ω → Configuration n) (T : ℝ≥0) (k : ℕ) (ω : Ω) :
    (∑ i, brownianUniformLeftSum (B i)
      (fun r ω => bakryEmeryGibbsPotentialTilt n α S (Y r ω) i) T (k+1) ω) =
    -(ginibreConfigurationBrownianGradientSum n B α Y (S) T k ω)/2 := by
  rw [ginibreConfigurationBrownianGradientSum_eq]
  unfold brownianUniformLeftSum bakryEmeryGibbsPotentialTilt
  have hc (a : ℝ) : -(Real.sqrt (2*α/(n : ℝ)^2)*a)/2 =
      -(Real.sqrt (2*α/(n : ℝ)^2)/2)*a := by ring
  rw [hc, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  dsimp only
  ring

theorem bakryEmeryGibbsPotentialTilt_integrals_eq_gradient {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (S : Configuration n → ℝ) (hS : ContDiff ℝ 2 S) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P :
        Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (α : ℝ≥0)
    (Y : ℝ≥0 → Ω → Configuration n)
    (hY : StronglyAdapted (ginibreBrownianAugmentedFiltration B P (fun i => (hB
        i).toIsPreBrownianReal)) Y)
    (K : Set (Configuration n)) (hK : IsCompact K)
    (hRange : ∀ t ω, Y t ω ∈ K) (T : ℝ≥0)
    (J : ℝ≥0 → Ω → ℝ) (hJC : ∀ ω, Continuous (fun t => J t ω))
    (hJ : ∀ t ≤ T, TendstoInMeasure P
      (ginibreConfigurationBrownianGradientSum n B α Y (S) t) atTop (J t))
    (M : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ)
    (hMC : ∀ i ω, Continuous (fun t => M i t ω))
    (hM : ∀ i t, t ≤ T → TendstoInMeasure P
      (fun k => brownianUniformLeftSum (B i)
        (fun r ω => bakryEmeryGibbsPotentialTilt n α S (Y r ω) i) t (k + 1)) atTop (M i t)) :
    ∀ᵐ ω ∂P, ∀ t ≤ T, (∑ i, M i t ω) = -J t ω/2 := by
  classical
  obtain ⟨C, hC, hb⟩ := bakryEmeryGibbsPotentialTilt_compact_bound n α S hS K hK
  let F := fun (i : Fin n × Fin 2) r ω => bakryEmeryGibbsPotentialTilt n α S (Y r ω) i
  have hF (i : Fin n × Fin 2) (r : ℝ≥0) :
      @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P
        (fun i => (hB i).toIsPreBrownianReal) r) _ (F i r) :=
    (bakryEmeryGibbsPotentialTilt_measurable n α S i).comp (hY r).measurable
  have hFi (i : Fin n × Fin 2) (r : ℝ≥0) : MemLp (F i r) 2 P := by
    apply MemLp.of_bound (((hF i r).mono ((ginibreBrownianAugmentedFiltration B P
      (fun i => (hB i).toIsPreBrownianReal)).le r) le_rfl).aestronglyMeasurable) C
    apply ae_of_all
    intro ω
    rw [Real.norm_eq_abs]
    apply abs_le_of_sq_le_sq _ hC
    exact (Finset.single_le_sum (fun j _ => sq_nonneg (F j r ω)) (Finset.mem_univ i)).trans
      (hb _ (hRange r ω))
  have hFixed (t : ℝ≥0) : ∀ᵐ ω ∂P, t ≤ T → (∑ i, M i t ω) = -J t ω/2 := by
    by_cases ht : t ≤ T
    · have hs (i : Fin n × Fin 2) (k : ℕ) :=
        (brownianUniformLeftSum_memLp_two B P (fun i => (hB i).toIsPreBrownianReal)
          hind i (F i) (hF i) (hFi i) t (k+1)).aestronglyMeasurable
      have hsum := itoTendstoInMeasure_finset_sum P Finset.univ
        (fun i k => brownianUniformLeftSum (B i) (F i) t (k+1)) (fun i => M i t)
        hs (fun i => hM i t ht)
      have hg := ginibre_tendstoInMeasure_const_mul P
        (ginibreConfigurationBrownianGradientSum n B α Y (S) t)
        (J t) (-(1/2 : ℝ)) (hJ t ht)
      have hh : TendstoInMeasure P
          (fun k ω => ∑ i, brownianUniformLeftSum (B i) (F i) t (k+1) ω) atTop
          (fun ω => -J t ω/2) := by
        convert hg using 1
        · funext k ω
          rw [bakryEmeryGibbsPotentialTilt_leftSums]
          ring
        · funext ω; ring
      filter_upwards [tendstoInMeasure_ae_unique hsum hh] with ω hω
      exact fun _ => hω
    · exact ae_of_all P (fun ω h => False.elim (ht h))
  exact ginibre_ae_continuous_identity_until P (fun t ω => ∑ i, M i t ω)
    (fun t ω => -J t ω/2) (fun _ => T)
    (ae_of_all P (fun ω => continuous_finsetSum _ (fun i _ => hMC i ω)))
    (ae_of_all P (fun ω => (hJC ω).neg.div_const 2)) hFixed

/-- Whole corrected Brownian path law for the same constructed bounded
relative-potential exponential integrals. -/
theorem bakryEmeryGibbsPotentialTilt_girsanov_exists {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (S : Configuration n → ℝ) (hS : ContDiff ℝ 2 S)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i sample t => B i t sample) P) (α : ℝ≥0)
    (Y : ℝ≥0 → Ω → Configuration n)
    (hY : StronglyAdapted (ginibreBrownianAugmentedFiltration B P (fun i => (hB
        i).toIsPreBrownianReal)) Y)
    (hYC : ∀ sample, Continuous (fun t => Y t sample))
    (K : Set (Configuration n)) (hK : IsCompact K) (hRange : ∀ t sample, Y t sample ∈ K)
    (T : ℝ≥0) (hT : 0 < T) :
    let F := fun i s sample => bakryEmeryGibbsPotentialTilt n α S (Y s sample) i
    ∃ M : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ,
      (∀ i, Martingale (M i) (ginibreBrownianAugmentedFiltration B P
        (fun i => (hB i).toIsPreBrownianReal)) P ∧
        (∀ sample, Continuous (fun t => M i t sample)) ∧ (∀ t, MemLp (M i t) 2 P) ∧
        M i 0 =ᵐ[P] (fun _ => 0) ∧
        ∀ t ≤ T, TendstoInMeasure P
          (fun k => brownianUniformLeftSum (B i) (F i) t (k+1)) atTop (M i t)) ∧
      Integrable (brownianVectorExponentialIntegralDensity F T (fun i => M i T)) P ∧
      (∫ sample, brownianVectorExponentialIntegralDensity F T (fun i => M i T) sample ∂P) = 1 ∧
      let Q := P.withDensity (fun sample => ENNReal.ofReal
        (brownianVectorExponentialIntegralDensity F T (fun i => M i T) sample))
      let X := fun sample (t : Icc (0 : ℝ≥0) T) i => B i t.val sample - B i 0 sample -
        ∫ s in (0 : ℝ)..(t.val : ℝ), F i (Real.toNNReal s) sample
      let Z := fun sample (t : Icc (0 : ℝ≥0) T) i => B i t.val sample - B i 0 sample
      Measurable X ∧ Measurable Z ∧ Q.map X = P.map Z ∧
      ∀ i, ∀ᵐ sample ∂Q, ContinuousOn
        (fun t : ℝ≥0 => B i t sample - B i 0 sample -
          ∫ s in (0 : ℝ)..(t : ℝ), F i (Real.toNNReal s) sample) (Icc 0 T) := by
  obtain ⟨C, hC, hb⟩ := bakryEmeryGibbsPotentialTilt_compact_bound n α S hS K hK
  have hF (i : Fin n × Fin 2) (t : ℝ≥0) : @Measurable Ω ℝ
      (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal) t) _
      (fun sample => bakryEmeryGibbsPotentialTilt n α S (Y t sample) i) :=
    (bakryEmeryGibbsPotentialTilt_measurable n α S i).comp (hY t).measurable
  exact brownianBoundedVector_girsanov_whole_path_exists B P hB hind _ hF C hC
    (fun t sample => hb _ (hRange t sample)) T hT (fun i => ae_of_all P (fun sample =>
      ((bakryEmeryGibbsPotentialTilt_continuous n α S hS i).comp (hYC sample)).continuousOn))

/-- The actual normalized compact-stopped Brownian likelihood agrees with
its literal Gibbs OU-relative endpoint/action expression through the stop. -/
theorem bakryEmeryGibbsOU_relative_action_density_exists {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (W : Configuration n → ℝ) (hW : ContDiff ℝ 2 W)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i sample t => B i t sample) P)
    (z : Configuration n) (r : ℝ) (hr : 0 < r) (T : ℝ≥0) (hT : 0 < T) :
    ∃ Y : ℝ≥0 → Ω → Configuration n,
      (∀ sample, Continuous (fun t => Y t sample)) ∧
      (∀ t sample, Y t sample ∈ Metric.closedBall z r) ∧
      (∀ sample, Y 0 sample = z) ∧
      StronglyAdapted (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal))
          Y ∧
      ∃ θ : Ω → ℝ≥0,
      IsStoppingTime (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal))
        (fun sample => (θ sample : WithTop ℝ≥0)) ∧
      (∀ sample, 0 < θ sample ∧ θ sample ≤ T) ∧
      (∀ t sample, Y t sample = ginibreHamiltonianOUReferenceProcess n ((n : ℝ)^2) z B
        (min t (θ sample)) sample) ∧
      θ = hittingBtwn (fun t sample => ginibreHamiltonianOUReferenceProcess n ((n : ℝ)^2) z B t
          sample-z)
        {x | r ≤ ‖x‖} 0 T ∧
      ∃ M : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ,
      (∀ i, Martingale (M i) (ginibreBrownianAugmentedFiltration B P
        (fun i => (hB i).toIsPreBrownianReal)) P ∧
        (∀ sample, Continuous (fun t => M i t sample)) ∧ (∀ t, MemLp (M i t) 2 P) ∧
        M i 0 =ᵐ[P] (fun _ => 0) ∧
        ∀ t ≤ T, TendstoInMeasure P
          (fun k => brownianUniformLeftSum (B i)
            (fun s sample => bakryEmeryGibbsPotentialTilt n ((n : ℝ)^2)
              (bakryEmeryGibbsRelativePotential W) (Y s sample) i) t (k+1)) atTop (M i t)) ∧
      Integrable (brownianVectorExponentialIntegralDensity
        (fun i s sample => bakryEmeryGibbsPotentialTilt n ((n : ℝ)^2)
          (bakryEmeryGibbsRelativePotential W) (Y s sample) i) T (fun i => M i T)) P ∧
      (∫ sample, brownianVectorExponentialIntegralDensity
        (fun i s sample => bakryEmeryGibbsPotentialTilt n ((n : ℝ)^2)
          (bakryEmeryGibbsRelativePotential W) (Y s sample) i) T (fun i => M i T) sample ∂P) = 1 ∧
      ((P.withDensity (fun sample => ENNReal.ofReal (brownianVectorExponentialIntegralDensity
        (fun i s sample => bakryEmeryGibbsPotentialTilt n ((n : ℝ)^2)
          (bakryEmeryGibbsRelativePotential W) (Y s sample) i) T (fun i => M i T) sample))).map
        (fun sample (t : Icc (0 : ℝ≥0) T) i => B i t.val sample - B i 0 sample -
          ∫ s in (0 : ℝ)..(t.val : ℝ), bakryEmeryGibbsPotentialTilt n ((n : ℝ)^2)
            (bakryEmeryGibbsRelativePotential W) (Y s.toNNReal sample) i)) =
        P.map (fun sample (t : Icc (0 : ℝ≥0) T) i => B i t.val sample - B i 0 sample) ∧
      ∀ᵐ sample ∂P, ∀ t ≤ θ sample,
        brownianVectorExponentialIntegralDensity
          (fun i s sample => bakryEmeryGibbsPotentialTilt n ((n : ℝ)^2)
            (bakryEmeryGibbsRelativePotential W) (Y s sample) i) t (fun i => M i t) sample =
        Real.exp (bakryEmeryGibbsRelativePotential W z) *
          Real.exp (-(bakryEmeryGibbsRelativePotential W z +
            bakryEmeryGibbsRelativePotential W (Y t sample))/2 +
            ∫ s in (0 : ℝ)..t, bakryEmeryGibbsOUActionIntegrand W (Y s.toNNReal sample)) := by
  let S := bakryEmeryGibbsRelativePotential W
  have hS : ContDiff ℝ 2 S :=
    hW.sub (contDiff_const.mul (contDiff_configurationNormSq.of_le (by simp)))
  let α : ℝ≥0 := (n : ℝ≥0)^2
  have hα : (α : ℝ) = (n : ℝ)^2 := by simp [α]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  obtain ⟨Y, hYC, hYR, hY0, hY, θ, hStop, hθ, hStopped, hExit, J, hJM, hJC, hJL, hJ0, hLimit, hIto⟩
      :=
    bakryEmeryGibbsOU_relative_ito_exists hn W hW B P hB hind z r hr T hT
  obtain ⟨M, hM, hDi, hD1, hLaw⟩ := bakryEmeryGibbsPotentialTilt_girsanov_exists
    n S hS B P hB hind α Y hY hYC (Metric.closedBall z r) (isCompact_closedBall _ _) hYR T hT
  have hSum := bakryEmeryGibbsPotentialTilt_integrals_eq_gradient n S hS B P hB hind α Y hY
    (Metric.closedBall z r) (isCompact_closedBall _ _) hYR T J hJC hLimit M
    (fun i => (hM i).2.1) (fun i => (hM i).2.2.2.2)
  refine ⟨Y, hYC, hYR, hY0, hY, θ, hStop, hθ, hStopped, hExit, M,?_,?_,?_,?_,?_⟩
  · simpa only [hα] using hM
  · simpa only [hα] using hDi
  · simpa only [hα] using hD1
  · simpa only [hα] using hLaw.2.2.1
  · filter_upwards [hSum, hIto] with sample hSumSample hItoSample
    intro t ht
    have hMt := hSumSample t (ht.trans (hθ sample).2)
    have hIt := hItoSample t ht
    have hcPath : Continuous (fun s : ℝ => Y s.toNNReal sample) :=
      (hYC sample).comp continuous_real_toNNReal
    have hgrad : Continuous (bakryEmeryGibbsConfigurationGradientSq S) := by
      have hd := (hS.fderiv_right (m := 1) (by norm_num)).continuous
      unfold bakryEmeryGibbsConfigurationGradientSq
      exact continuous_finsetSum _ (fun j _ =>
        ((hd.clm_apply continuous_const).pow 2).add ((hd.clm_apply continuous_const).pow 2))
    have hlap : Continuous (configurationLaplacian S) :=
      continuousOn_univ.mp (itoConfigurationLaplacian_continuousOn S univ isOpen_univ hS.contDiffOn)
    have hd : Continuous (fun s : ℝ => fderiv ℝ S (Y s.toNNReal sample)
        ((-2*(n : ℝ)) • Y s.toNNReal sample)) :=
      (((hS.fderiv_right (m := 1) (by norm_num)).continuous.comp hcPath).clm_apply
        (hcPath.const_smul (-2*(n : ℝ))))
    have hiL := (hlap.comp hcPath).intervalIntegrable (μ := volume) (0 : ℝ) (t : ℝ)
    have hiD := hd.intervalIntegrable (μ := volume) (0 : ℝ) (t : ℝ)
    have hiG := (hgrad.comp hcPath).intervalIntegrable (μ := volume) (0 : ℝ) (t : ℝ)
    dsimp only [Function.comp_def] at hiL hiG
    have hA (w : Configuration n) : bakryEmeryGibbsOUActionIntegrand W w =
        configurationLaplacian S w / 2 + fderiv ℝ S w ((-2*(n : ℝ)) • w) / 2 -
          bakryEmeryGibbsConfigurationGradientSq S w / 4 := by
      unfold bakryEmeryGibbsOUActionIntegrand
      rw [map_smul, smul_eq_mul, ginibreRealCoordinateDifferential_radial]
      dsimp only [bakryEmeryGibbsConfigurationRadialGradient, bakryEmeryGibbsConfigurationLaplacian,
        configurationLaplacian, secondDirectionalDerivative, S]
      ring
    have hInt : (∫ s in (0 : ℝ)..t, bakryEmeryGibbsOUActionIntegrand W (Y s.toNNReal sample)) =
        (∫ s in (0 : ℝ)..t, configurationLaplacian S (Y s.toNNReal sample)) / 2 +
        (∫ s in (0 : ℝ)..t, fderiv ℝ S (Y s.toNNReal sample)
          ((-2*(n : ℝ)) • Y s.toNNReal sample)) / 2 -
        (∫ s in (0 : ℝ)..t, bakryEmeryGibbsConfigurationGradientSq S (Y s.toNNReal sample)) / 4 :=
            by
      simp_rw [hA]
      rw [intervalIntegral.integral_sub ((hiL.div_const 2).add (hiD.div_const 2)) (hiG.div_const 4),
        intervalIntegral.integral_add (hiL.div_const 2) (hiD.div_const 2),
        intervalIntegral.integral_div, intervalIntegral.integral_div, intervalIntegral.integral_div]
    have hEnergy : brownianVectorTimeEnergy
        (fun i s sample => bakryEmeryGibbsPotentialTilt n ((n : ℝ)^2) S (Y s sample) i) t sample =
        (1/2 : ℝ) * ∫ s in (0 : ℝ)..t, bakryEmeryGibbsConfigurationGradientSq S (Y s.toNNReal
            sample) := by
      unfold brownianVectorTimeEnergy
      simp_rw [bakryEmeryGibbsPotentialTilt_energy n ((n : ℝ)^2) (sq_nonneg _) S]
      rw [intervalIntegral.integral_const_mul]
      congr 1
      field_simp
    unfold brownianVectorExponentialIntegralDensity
    rw [hInt, ← Real.exp_add, hEnergy]
    simp only []
    rw [hMt, ← hIt]
    congr 1
    ring

/-- Literal ordinary gradient drift on complex coordinates, interpreted as
real and imaginary Euclidean coordinates. -/
def bakryEmeryGibbsConfigurationDrift {n : ℕ} (W : Configuration n → ℝ)
    (z : Configuration n) : Configuration n := fun j =>
  -(fderiv ℝ W z (realCoordinateDirection j) : ℂ) -
    Complex.I * (fderiv ℝ W z (imaginaryCoordinateDirection j) : ℂ)

/-- The configuration-valued drift tilt of the relative potential of `W`: its coordinate tilts
(with `α = n²`) assembled into a configuration by `ginibreBrownianEmbeddingCLM`. -/
def bakryEmeryGibbsConfigurationTilt (n : ℕ) (W : Configuration n → ℝ)
    (z : Configuration n) : Configuration n :=
  ginibreBrownianEmbeddingCLM n ((n : ℝ)^2)
    (fun i => bakryEmeryGibbsPotentialTilt n ((n : ℝ)^2) (bakryEmeryGibbsRelativePotential W) z i)

theorem bakryEmeryGibbsPotentialTilt_noise_drift (n : ℕ) (α : ℝ) (hα : 0 ≤ α)
    (S : Configuration n → ℝ) (z : Configuration n) (i : Fin n × Fin 2) :
    Real.sqrt (2*α/(n : ℝ)^2) * bakryEmeryGibbsPotentialTilt n α S z i =
      -(α/(n : ℝ)^2) * fderiv ℝ S z (ginibreCoordinateDirection i) := by
  unfold bakryEmeryGibbsPotentialTilt
  have hs : (Real.sqrt (2*α/(n : ℝ)^2))^2 = 2*α/(n : ℝ)^2 :=
    Real.sq_sqrt (div_nonneg (by linarith) (sq_nonneg _))
  calc
    _ = -((Real.sqrt (2*α/(n : ℝ)^2))^2/2) * fderiv ℝ S z (ginibreCoordinateDirection i) := by ring
    _ = _ := by rw [hs]; ring

/-- The actual Brownian tilt changes the reference OU drift exactly into
`-∇W`, with no drift identification hypothesis. -/
theorem bakryEmeryGibbsConfigurationTilt_eq_drift {n : ℕ} (hn : 0 < n)
    (W : Configuration n → ℝ) (hW : Differentiable ℝ W) (z : Configuration n) :
    bakryEmeryGibbsConfigurationTilt n W z =
      bakryEmeryGibbsConfigurationDrift W z - (-2*(n : ℝ)) • z := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have he : (n : ℝ)^2/(n : ℝ)^2 = 1 := div_self (pow_ne_zero _ hn0)
  have hS (v : Configuration n) : fderiv ℝ (bakryEmeryGibbsRelativePotential W) z v =
      fderiv ℝ W z v - (n : ℝ) * fderiv ℝ configurationNormSq z v := by
    have hd := (hW z).hasFDerivAt.sub
      (((contDiff_configurationNormSq (n := n)).differentiable (by simp) z).hasFDerivAt.const_mul (n
          : ℝ))
    change HasFDerivAt (bakryEmeryGibbsRelativePotential W) _ z at hd
    rw [hd.fderiv]
    simp
  ext j
  apply Complex.ext
  · have ht := bakryEmeryGibbsPotentialTilt_noise_drift n ((n : ℝ)^2) (sq_nonneg _)
      (bakryEmeryGibbsRelativePotential W) z (j, 0)
    rw [he, neg_one_mul, hS] at ht
    simp only [ginibreCoordinateDirection, ite_true, realCoordinateDirection] at ht
    rw [fderiv_configurationNormSq_coordinate] at ht
    convert ht using 1 <;> simp [bakryEmeryGibbsConfigurationTilt,
        ginibreBrownianEmbeddingCLM_apply,
      bakryEmeryGibbsConfigurationDrift, realCoordinateDirection, 
      Pi.sub_apply, Pi.smul_apply]; ring
  · have ht := bakryEmeryGibbsPotentialTilt_noise_drift n ((n : ℝ)^2) (sq_nonneg _)
      (bakryEmeryGibbsRelativePotential W) z (j, 1)
    rw [he, neg_one_mul, hS] at ht
    simp only [ginibreCoordinateDirection, ite_eq_right (by decide : (1 : Fin 2) ≠ 0),
        imaginaryCoordinateDirection] at ht
    rw [fderiv_configurationNormSq_coordinate] at ht
    convert ht using 1 <;> simp [bakryEmeryGibbsConfigurationTilt,
        ginibreBrownianEmbeddingCLM_apply,
      bakryEmeryGibbsConfigurationDrift, imaginaryCoordinateDirection, 
      Pi.sub_apply, Pi.smul_apply]; ring

end
end GinibrePoincare
