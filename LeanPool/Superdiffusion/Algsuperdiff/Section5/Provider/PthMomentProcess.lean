/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.PthMomentProcessTail
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.RemovalSteps
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.StoppedMoments
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Field.StreamProcess
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.ParameterizedProcessSemigroup
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.StoppedDirichlet

/-!
# PthMomentProcess

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Stream-process moments and stopping-time removal

A square-exponential displacement tail at every triadic radius above a normalization scale gives
all real moments.  The second section combines those moments with an almost-everywhere bound for
the stopped position to remove a stopping time from the first and second moments.
-/

namespace Algsuperdiff.Section5.Provider

open Algsuperdiff.Section5.Field
open Algsuperdiff.Section3
open DivergenceFormProcess.StoppedDirichlet
open DivergenceFormProcess.Form
open HCPolySupport MarkovProcess MeasureTheory ProbabilityTheory
open scoped NNReal

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
private theorem vecNormSq_le_dim_mul_sq_norm_process (v : Vec d) :
    vecNormSq v ≤ (d : ℝ) * ‖v‖ ^ (2 : ℕ) := by
  unfold vecNormSq vecDot
  calc
    ∑ i : Fin d, v i * v i ≤ ∑ _i : Fin d, ‖v‖ ^ (2 : ℕ) := by
      apply Finset.sum_le_sum
      intro i _hi
      have hi : |v i| ≤ ‖v‖ := norm_le_pi_norm v i
      calc
        v i * v i = |v i| ^ (2 : ℕ) := by
          rw [pow_two, ← abs_mul, abs_mul_self]
        _ ≤ ‖v‖ ^ (2 : ℕ) := pow_le_pow_left₀ (abs_nonneg _) hi 2
    _ = (d : ℝ) * ‖v‖ ^ (2 : ℕ) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **The process C2 moment row.**  A restricted all-integer-scale triadic tail for the
stream process gives every real moment `p ≥ 1`, with the interpolation
constant displayed explicitly. -/
theorem integral_norm_onePointRetract_streamProcess_rpow_le_of_triadic_sq_tail
    (M : ABKModel d) (omega : FullSample d M.gamma) (t : NNReal)
    {R c p : ℝ} (hR : 0 < R) (hc : 0 < c) (hc1 : c ≤ 1) (hp : 1 ≤ p) :
    letI := (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
    letI := (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
    let Q := streamProcess M omega ((0 : Vec d) : OnePoint (Vec d))
    let A := (3 / 2 : ℝ) * max 1 (c * Real.log 2)⁻¹
    (∀ k : ℤ, R ≤ (3 : ℝ) ^ k → Q.real {eta | (1 / 2 : ℝ) * (3 : ℝ) ^ k ≤
        ‖onePointRetract (0 : Vec d) (eta t)‖} ≤
      Real.exp (-c * (((3 : ℝ) ^ k / R) ^ (2 : ℕ)))) →
      Integrable (fun eta : ContinuousPath (OnePoint (Vec d)) =>
        ‖onePointRetract (0 : Vec d) (eta t)‖ ^ p) Q ∧
      ∫ eta : ContinuousPath (OnePoint (Vec d)),
          ‖onePointRetract (0 : Vec d) (eta t)‖ ^ p ∂Q ≤
        (6 * p * (A * R)) ^ p := by
  dsimp only
  let streamMetricSpace :=
    (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
  let streamCompleteSpace :=
    (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
  let streamMarkovKernel : IsMarkovKernel (streamProcess M omega) :=
    (streamExhaustionTailInput M omega).wholeSpaceProcess_spec.1
  let Q := streamProcess M omega ((0 : Vec d) : OnePoint (Vec d))
  let Z : ContinuousPath (OnePoint (Vec d)) → ℝ := fun eta =>
    ‖onePointRetract (0 : Vec d) (eta t)‖
  intro htail
  have hZ : AEMeasurable Z Q :=
    (((measurable_onePointRetract (X := Vec d) 0).comp
      (ContinuousPath.measurable_coordinateProcess t)).norm).aemeasurable
  have hZ0 : 0 ≤ᵐ[Q] Z := Filter.Eventually.of_forall fun eta => norm_nonneg _
  exact integral_rpow_le_of_triadic_sq_tail Q hZ hZ0 hR hc hc1 hp htail

/-! ## Removal at the exit time -/

/-- **The process C4 removal row.**  The full and stopped stream-process
positions agree on survival.  The restricted tail supplies the first and second
moments of the full position; a pointwise bound supplies integrability of the
stopped position. -/
theorem vecNormSq_integral_onePointRetract_sub_exitTimeTrunc_le
    (M : ABKModel d) (omega : FullSample d M.gamma)
    {U : Set (OnePoint (Vec d))} (hU : IsOpen U) (t : NNReal)
    {R c B : ℝ} (hR : 0 < R) (hc : 0 < c) (hc1 : c ≤ 1) :
    letI := (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
    letI := (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
    let Q := streamProcess M omega ((0 : Vec d) : OnePoint (Vec d))
    let A := (3 / 2 : ℝ) * max 1 (c * Real.log 2)⁻¹
    (∀ k : ℤ, R ≤ (3 : ℝ) ^ k → Q.real {eta | (1 / 2 : ℝ) * (3 : ℝ) ^ k ≤
        ‖onePointRetract (0 : Vec d) (eta t)‖} ≤
      Real.exp (-c * (((3 : ℝ) ^ k / R) ^ (2 : ℕ)))) →
    (∀ᵐ eta ∂Q, eta ∈ (survivalEvent U t)ᶜ →
      ‖onePointRetract (0 : Vec d)
        (eta (ContinuousPath.exitTimeTrunc U t eta))‖ ≤ B) →
    vecNormSq ((∫ eta, onePointRetract (0 : Vec d) (eta t)
          ∂Q) -
        ∫ eta, onePointRetract (0 : Vec d)
            (eta (ContinuousPath.exitTimeTrunc U t eta)) ∂Q) ≤
      (d : ℝ) * (((6 * 2 * (A * R)) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
          Q.real (survivalEvent U t)ᶜ ^ (1 / 2 : ℝ) +
        B * Q.real (survivalEvent U t)ᶜ) ^ (2 : ℕ) := by
  dsimp only
  let streamMetricSpace :=
    (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
  let streamCompleteSpace :=
    (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
  let streamMarkovKernel : IsMarkovKernel (streamProcess M omega) :=
    (streamExhaustionTailInput M omega).wholeSpaceProcess_spec.1
  let Q := streamProcess M omega ((0 : Vec d) : OnePoint (Vec d))
  let X : ContinuousPath (OnePoint (Vec d)) → Vec d := fun eta =>
    onePointRetract (0 : Vec d) (eta t)
  let Y : ContinuousPath (OnePoint (Vec d)) → Vec d := fun eta =>
    onePointRetract (0 : Vec d) (eta (ContinuousPath.exitTimeTrunc U t eta))
  intro htail hstop
  have hXone := integral_norm_onePointRetract_streamProcess_rpow_le_of_triadic_sq_tail
    M omega t hR hc hc1 (show (1 : ℝ) ≤ 1 by norm_num) htail
  have hXtwo := integral_norm_onePointRetract_streamProcess_rpow_le_of_triadic_sq_tail
    M omega t hR hc hc1 (show (1 : ℝ) ≤ 2 by norm_num) htail
  have hXmeas : StronglyMeasurable X :=
    ((measurable_onePointRetract (X := Vec d) 0).comp
      (ContinuousPath.measurable_coordinateProcess t)).stronglyMeasurable
  have hXnorm : Integrable (fun eta => ‖X eta‖) Q := by
    simpa only [Q, X, Real.rpow_one, norm_norm] using hXone.1
  have hXint : Integrable X Q :=
    (integrable_norm_iff (f := X) (μ := Q) hXmeas.aestronglyMeasurable).1 hXnorm
  have hXsq : Integrable (fun eta => ‖X eta‖ ^ (2 : ℕ)) Q := by
    simpa only [Q, X, Real.rpow_two] using hXtwo.1
  have hYmeas : StronglyMeasurable Y :=
    ((measurable_onePointRetract (X := Vec d) 0).comp
      (ContinuousPath.measurable_eval_stoppingTime_borel _
        (ContinuousPath.isStoppingTime_exitTimeTrunc U hU t))).stronglyMeasurable
  have hYboundAll : ∀ᵐ eta ∂Q, ‖Y eta‖ ≤ ‖X eta‖ + max B 0 := by
    filter_upwards [hstop] with eta hstopEta
    by_cases heta : eta ∈ (survivalEvent U t)ᶜ
    · exact (hstopEta heta).trans
        ((le_max_left _ _).trans (le_add_of_nonneg_left (norm_nonneg _)))
    · simp only [Y, exitTimeTrunc_of_mem_survivalEvent (Set.notMem_compl_iff.mp heta)]
      exact le_add_of_nonneg_right (le_max_right _ _)
  have hdom : Integrable (fun eta => ‖X eta‖ + max B 0) Q :=
    hXint.norm.add (integrable_const (max B 0))
  have hYint : Integrable Y Q := hdom.mono' hYmeas.aestronglyMeasurable
    hYboundAll
  have heq : ∀ eta, eta ∉ (survivalEvent U t)ᶜ → X eta = Y eta := by
    intro eta heta
    simp only [X, Y, exitTimeTrunc_of_mem_survivalEvent (Set.notMem_compl_iff.mp heta)]
  have hresult := norm_integral_sub_le_moment_on_event Q hXint hYint hXsq
    (measurableSet_survivalEvent hU t).compl heq hstop
  have hnorm : ‖(∫ eta, X eta ∂Q) - ∫ eta, Y eta ∂Q‖ ≤
      ((6 * 2 * ((3 / 2 : ℝ) * max 1 (c * Real.log 2)⁻¹ * R)) ^ (2 : ℝ)) ^
          (1 / 2 : ℝ) * Q.real (survivalEvent U t)ᶜ ^ (1 / 2 : ℝ) +
        B * Q.real (survivalEvent U t)ᶜ := hresult.trans (by
    have hmoment : ∫ eta, ‖X eta‖ ^ (2 : ℕ) ∂Q ≤
        (6 * 2 * ((3 / 2 : ℝ) * max 1 (c * Real.log 2)⁻¹ * R)) ^ (2 : ℝ) := by
      simpa only [Q, X, Real.rpow_two] using hXtwo.2
    have hroot := Real.rpow_le_rpow (integral_nonneg fun eta => sq_nonneg ‖X eta‖)
      hmoment (by norm_num : (0 : ℝ) ≤ 1 / 2)
    have hprob : 0 ≤ Q.real (survivalEvent U t)ᶜ ^ (1 / 2 : ℝ) :=
      Real.rpow_nonneg measureReal_nonneg _
    have hmul := mul_le_mul_of_nonneg_right hroot hprob
    simpa only [Q, add_comm, Real.rpow_two] using!
      add_le_add_right hmul (B * Q.real (survivalEvent U t)ᶜ))
  apply (vecNormSq_le_dim_mul_sq_norm_process ((∫ eta, X eta ∂Q) -
    ∫ eta, Y eta ∂Q)).trans
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) hnorm 2) (Nat.cast_nonneg d)

/-- **The process C6 removal row.**  The fourth moment supplied by the
restricted displacement tail controls the Euclidean second-moment observable.  The stopped
integrand is exactly the cutoff-weighted observable used by the quenched composer. -/
theorem abs_integral_vecNormSq_sub_exitTimeTrunc_cutoff_le
    (M : ABKModel d) (omega : FullSample d M.gamma)
    {U : Set (OnePoint (Vec d))} (hU : IsOpen U) (t : NNReal) (cutoff : Vec d → ℝ)
    (hcutoff : Measurable fun z => cutoff z * vecNormSq z)
    {R c B : ℝ} (hR : 0 < R) (hc : 0 < c) (hc1 : c ≤ 1) :
    letI := (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
    letI := (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
    let Q := streamProcess M omega ((0 : Vec d) : OnePoint (Vec d))
    let A := (3 / 2 : ℝ) * max 1 (c * Real.log 2)⁻¹
    (∀ k : ℤ, R ≤ (3 : ℝ) ^ k → Q.real {eta | (1 / 2 : ℝ) * (3 : ℝ) ^ k ≤
        ‖onePointRetract (0 : Vec d) (eta t)‖} ≤
      Real.exp (-c * (((3 : ℝ) ^ k / R) ^ (2 : ℕ)))) →
    (∀ eta, eta ∉ (survivalEvent U t)ᶜ →
      vecNormSq (onePointRetract (0 : Vec d) (eta t)) =
        onePointRealExtension (fun z => cutoff z * vecNormSq z)
          (eta (ContinuousPath.exitTimeTrunc U t eta))) →
    (∀ᵐ eta ∂Q, eta ∈ (survivalEvent U t)ᶜ →
      |onePointRealExtension (fun z => cutoff z * vecNormSq z)
        (eta (ContinuousPath.exitTimeTrunc U t eta))| ≤ B) →
    |∫ eta, vecNormSq (onePointRetract (0 : Vec d) (eta t)) ∂Q -
        ∫ eta, onePointRealExtension (fun z => cutoff z * vecNormSq z)
          (eta (ContinuousPath.exitTimeTrunc U t eta)) ∂Q| ≤
      (((d : ℝ) ^ (2 : ℕ) * (6 * 4 * (A * R)) ^ (4 : ℝ)) ^
          (1 / 2 : ℝ)) *
          Q.real (survivalEvent U t)ᶜ ^ (1 / 2 : ℝ) +
        B * Q.real (survivalEvent U t)ᶜ := by
  dsimp only
  let streamMetricSpace :=
    (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
  let streamCompleteSpace :=
    (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
  let streamMarkovKernel : IsMarkovKernel (streamProcess M omega) :=
    (streamExhaustionTailInput M omega).wholeSpaceProcess_spec.1
  let Q := streamProcess M omega ((0 : Vec d) : OnePoint (Vec d))
  let V : ContinuousPath (OnePoint (Vec d)) → Vec d := fun eta =>
    onePointRetract (0 : Vec d) (eta t)
  let X : ContinuousPath (OnePoint (Vec d)) → ℝ := fun eta => vecNormSq (V eta)
  let Y : ContinuousPath (OnePoint (Vec d)) → ℝ := fun eta =>
    onePointRealExtension (fun z => cutoff z * vecNormSq z)
      (eta (ContinuousPath.exitTimeTrunc U t eta))
  intro htail heq hstop
  have hXtwo := integral_norm_onePointRetract_streamProcess_rpow_le_of_triadic_sq_tail
    M omega t hR hc hc1 (show (1 : ℝ) ≤ 2 by norm_num) htail
  have hXfour := integral_norm_onePointRetract_streamProcess_rpow_le_of_triadic_sq_tail
    M omega t hR hc hc1 (show (1 : ℝ) ≤ 4 by norm_num) htail
  have hVtwo : Integrable (fun eta => ‖V eta‖ ^ (2 : ℕ)) Q := by
    simpa only [Q, V, Real.rpow_two] using hXtwo.1
  have hVfour : Integrable (fun eta => ‖V eta‖ ^ (4 : ℕ)) Q := by
    simpa only [Q, V, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast] using hXfour.1
  have hVmeas : Measurable V :=
    (measurable_onePointRetract (X := Vec d) 0).comp
      (ContinuousPath.measurable_coordinateProcess t)
  have hXmeas : StronglyMeasurable X := by
    apply Measurable.stronglyMeasurable
    have hEq : X = fun eta => ∑ i, V eta i * V eta i := rfl
    rw [hEq]
    exact Finset.measurable_sum _ fun i _ =>
      ((measurable_pi_apply i).comp hVmeas).mul
        ((measurable_pi_apply i).comp hVmeas)
  have hYmeas : StronglyMeasurable Y := by
    apply Measurable.stronglyMeasurable
    exact (measurable_onePointRealExtension hcutoff).comp
      (ContinuousPath.measurable_eval_stoppingTime_borel _
        (ContinuousPath.isStoppingTime_exitTimeTrunc U hU t))
  have hXint : Integrable X Q := by
    apply (hVtwo.const_mul (d : ℝ)).mono' hXmeas.aestronglyMeasurable
    filter_upwards [] with eta
    rw [Real.norm_of_nonneg (vecNormSq_nonneg _)]
    simpa only [Real.norm_of_nonneg (Nat.cast_nonneg d), Real.norm_of_nonneg (sq_nonneg _)]
      using vecNormSq_le_dim_mul_sq_norm_process (V eta)
  have hXsq : Integrable (fun eta => ‖X eta‖ ^ (2 : ℕ)) Q := by
    apply (hVfour.const_mul ((d : ℝ) ^ (2 : ℕ))).mono'
      (hXmeas.norm.pow 2).aestronglyMeasurable
    filter_upwards [] with eta
    have hdim := vecNormSq_le_dim_mul_sq_norm_process (V eta)
    change ‖‖vecNormSq (V eta)‖ ^ (2 : ℕ)‖ ≤
      (d : ℝ) ^ (2 : ℕ) * ‖V eta‖ ^ (4 : ℕ)
    rw [Real.norm_of_nonneg (sq_nonneg _), Real.norm_of_nonneg (vecNormSq_nonneg _)]
    exact (pow_le_pow_left₀ (vecNormSq_nonneg _) hdim 2).trans_eq (by ring)
  have hYboundAll : ∀ᵐ eta ∂Q, ‖Y eta‖ ≤ ‖X eta‖ + max B 0 := by
    filter_upwards [hstop] with eta hstopEta
    by_cases heta : eta ∈ (survivalEvent U t)ᶜ
    · calc
        ‖Y eta‖ = |Y eta| := Real.norm_eq_abs _
        _ ≤ B := hstopEta heta
        _ ≤ max B 0 := le_max_left _ _
        _ ≤ ‖X eta‖ + max B 0 := le_add_of_nonneg_left (norm_nonneg _)
    · have heqXY : X eta = Y eta := heq eta heta
      rw [← heqXY]
      exact le_add_of_nonneg_right (le_max_right _ _)
  have hYint : Integrable Y Q :=
    (hXint.norm.add (integrable_const (max B 0))).mono'
      hYmeas.aestronglyMeasurable hYboundAll
  have hresult := norm_integral_sub_le_moment_on_event Q hXint hYint hXsq
    (measurableSet_survivalEvent hU t).compl heq hstop
  refine hresult.trans ?_
  have hmomentV : ∫ eta, ‖V eta‖ ^ (4 : ℕ) ∂Q ≤
      (6 * 4 * ((3 / 2 : ℝ) * max 1 (c * Real.log 2)⁻¹ * R)) ^ (4 : ℝ) := by
    simpa only [Q, V, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast] using hXfour.2
  have hmomentX : ∫ eta, ‖X eta‖ ^ (2 : ℕ) ∂Q ≤
      (d : ℝ) ^ (2 : ℕ) *
        (6 * 4 * ((3 / 2 : ℝ) * max 1 (c * Real.log 2)⁻¹ * R)) ^ (4 : ℝ) := by
    calc
      ∫ eta, ‖X eta‖ ^ (2 : ℕ) ∂Q ≤
          ∫ eta, (d : ℝ) ^ (2 : ℕ) * ‖V eta‖ ^ (4 : ℕ) ∂Q := by
        apply integral_mono hXsq (hVfour.const_mul _)
        intro eta
        have hdim := vecNormSq_le_dim_mul_sq_norm_process (V eta)
        change ‖vecNormSq (V eta)‖ ^ (2 : ℕ) ≤
          (d : ℝ) ^ (2 : ℕ) * ‖V eta‖ ^ (4 : ℕ)
        rw [Real.norm_of_nonneg (vecNormSq_nonneg _)]
        exact (pow_le_pow_left₀ (vecNormSq_nonneg _) hdim 2).trans_eq (by ring)
      _ = (d : ℝ) ^ (2 : ℕ) * ∫ eta, ‖V eta‖ ^ (4 : ℕ) ∂Q := by
        rw [integral_const_mul]
      _ ≤ (d : ℝ) ^ (2 : ℕ) *
          (6 * 4 * ((3 / 2 : ℝ) * max 1 (c * Real.log 2)⁻¹ * R)) ^ (4 : ℝ) :=
        mul_le_mul_of_nonneg_left hmomentV (sq_nonneg _)
  have hroot := Real.rpow_le_rpow (integral_nonneg fun eta => sq_nonneg ‖X eta‖)
    hmomentX (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hprob : 0 ≤ Q.real (survivalEvent U t)ᶜ ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg measureReal_nonneg _
  have hmul := mul_le_mul_of_nonneg_right hroot hprob
  simpa only [Q, X, Y, V, Real.norm_eq_abs, add_comm, Real.rpow_two] using!
    add_le_add_right hmul (B * Q.real (survivalEvent U t)ᶜ)

end

end Algsuperdiff.Section5.Provider
