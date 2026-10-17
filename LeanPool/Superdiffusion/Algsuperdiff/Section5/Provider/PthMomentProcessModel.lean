/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.PthMomentProcess
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.StoppedMomentsCubeModel
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.StoppedPositionStream
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.EarlyExitConfinementModel
public import LeanPool.Superdiffusion.Algsuperdiff.Probability.SepEnvelope

/-!
# PthMomentProcessModel

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Stopping-time removal at the model confinement scale

The theorem in this module preserves a caller-supplied confinement-scale family.  Its one
probabilistic input beyond the lift's scale data is the restricted displacement tail used
verbatim by the process C4 and C6 estimates.
-/

namespace Algsuperdiff.Section5.Provider

open Algsuperdiff.Section3 Algsuperdiff.Section5.Field Algsuperdiff.Section5.Support
open DivergenceFormProcess.Form DivergenceFormProcess.StoppedDirichlet
open HCPolySupport MarkovProcess MeasureTheory ProbabilityTheory Set
open scoped NNReal

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
private theorem closure_image_cubeSetAt_subset_model (m : ℤ) :
    closure (((↑) : Vec d → OnePoint (Vec d)) '' cubeSetAt (0 : Vec d) m) ⊆
      ((↑) : Vec d → OnePoint (Vec d)) '' closure (cubeSetAt (0 : Vec d) m) := by
  apply closure_minimal (Set.image_mono subset_closure)
  apply OnePoint.isClosed_image_coe.mpr
  exact ⟨isClosed_closure,
    (isOpenBoundedConvexDomain_cubeSetAt (0 : Vec d) m).isBoundedDomain.isBounded.isCompact_closure⟩

private theorem ae_norm_stopped_le_half_scale_model
    (M : ABKModel d) (omega : FullSample d M.gamma) (m : ℤ) (t : NNReal) :
    letI := (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
    letI := (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
    ∀ᵐ eta ∂streamProcess M omega ((0 : Vec d) : OnePoint (Vec d)),
      ‖onePointRetract (0 : Vec d)
        (eta (ContinuousPath.exitTimeTrunc
          (((↑) : Vec d → OnePoint (Vec d)) '' cubeSetAt (0 : Vec d) m) t eta))‖ ≤
        (1 / 2 : ℝ) * (3 : ℝ) ^ m := by
  let _ := (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
  let _ := (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
  let streamMarkovKernel : IsMarkovKernel (streamProcess M omega) :=
    (streamExhaustionTailInput M omega).wholeSpaceProcess_spec.1
  filter_upwards [ae_eval_exitTimeTrunc_mem_closure_streamProcess_cubeSetAt_self
    M omega (0 : Vec d) m t] with eta heta
  obtain ⟨z, hz, heq⟩ := closure_image_cubeSetAt_subset_model m heta
  rw [← heq, onePointRetract_coe]
  simpa only [sub_zero] using (mem_closure_cubeSetAt_iff.mp hz)

private theorem integral_stopped_eq_cubeStoppedMean_model
    (M : ABKModel d) (omega : FullSample d M.gamma) (m : ℤ) (t : NNReal) :
    letI := (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
    letI := (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
    ∫ eta, onePointRetract (0 : Vec d)
        (eta (ContinuousPath.exitTimeTrunc
          (((↑) : Vec d → OnePoint (Vec d)) '' cubeSetAt (0 : Vec d) m) t eta))
      ∂streamProcess M omega ((0 : Vec d) : OnePoint (Vec d)) =
        cubeStoppedMean M omega m t := by
  let _ := (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
  let _ := (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
  let streamMarkovKernel : IsMarkovKernel (streamProcess M omega) :=
    (streamExhaustionTailInput M omega).wholeSpaceProcess_spec.1
  let F : ContinuousPath (OnePoint (Vec d)) → Vec d := fun eta =>
    onePointRetract (0 : Vec d)
      (eta (ContinuousPath.exitTimeTrunc
        (((↑) : Vec d → OnePoint (Vec d)) '' cubeSetAt (0 : Vec d) m) t eta))
  have hFmeas : StronglyMeasurable F :=
    ((measurable_onePointRetract (X := Vec d) 0).comp
      (ContinuousPath.measurable_eval_stoppingTime_borel _
        (ContinuousPath.isStoppingTime_exitTimeTrunc _
          (isOpen_image_coe_of_isOpen (isOpen_cubeSetAt (0 : Vec d) m)) t))).stronglyMeasurable
  have hFbound : ∀ᵐ eta ∂streamProcess M omega ((0 : Vec d) : OnePoint (Vec d)),
      ‖F eta‖ ≤ (1 / 2 : ℝ) * (3 : ℝ) ^ m :=
    ae_norm_stopped_le_half_scale_model M omega m t
  have hFint : Integrable F (streamProcess M omega ((0 : Vec d) : OnePoint (Vec d))) := by
    apply (integrable_const ((1 / 2 : ℝ) * (3 : ℝ) ^ m)).mono'
      hFmeas.aestronglyMeasurable
    filter_upwards [hFbound] with eta heta
    simpa only [Real.norm_of_nonneg
      (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) * (3 : ℝ) ^ m)]
      using heta
  funext i
  rw [MeasureTheory.eval_integral (fun j => hFint.eval j) i]
  change (∫ eta, onePointRetract (0 : Vec d)
      (eta (ContinuousPath.exitTimeTrunc
        (((↑) : Vec d → OnePoint (Vec d)) '' cubeSetAt (0 : Vec d) m) t eta)) i
    ∂streamProcess M omega ((0 : Vec d) : OnePoint (Vec d))) = _
  apply integral_congr_ae
  filter_upwards [ae_eval_exitTimeTrunc_mem_closure_streamProcess_cubeSetAt_self
    M omega (0 : Vec d) m t] with eta heta
  obtain ⟨z, hz, heq⟩ := closure_image_cubeSetAt_subset_model m heta
  rw [← heq, onePointRetract_coe, onePointRealExtension_coe,
    cubeCutoff_eq_one_of_mem_closure hz, one_mul]
  exact (vecDot_basisVec_left i z).symm

omit [NeZero d] in
private theorem measurable_vecNormSq_model : Measurable (vecNormSq : Vec d → ℝ) := by
  classical
  unfold vecNormSq vecDot
  exact Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).mul (measurable_pi_apply i)

omit [NeZero d] in
private theorem vecNormSq_le_dim_mul_sq_norm_model (z : Vec d) :
    vecNormSq z ≤ (d : ℝ) * ‖z‖ ^ (2 : ℕ) := by
  unfold vecNormSq vecDot
  calc
    ∑ i : Fin d, z i * z i ≤ ∑ _i : Fin d, ‖z‖ ^ (2 : ℕ) := by
      apply Finset.sum_le_sum
      intro i _hi
      have hi : |z i| ≤ ‖z‖ := norm_le_pi_norm z i
      calc
        z i * z i = |z i| ^ (2 : ℕ) := by rw [pow_two, ← abs_mul, abs_mul_self]
        _ ≤ ‖z‖ ^ (2 : ℕ) := pow_le_pow_left₀ (abs_nonneg _) hi 2
    _ = (d : ℝ) * ‖z‖ ^ (2 : ℕ) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

omit [NeZero d] in
private theorem abs_cubeCutoff_mul_vecNormSq_le_model (m : ℤ) (z : Vec d) :
    |cubeCutoff d m z * vecNormSq z| ≤
      (d : ℝ) * ((1 / 2 : ℝ) * (3 : ℝ) ^ (m + 1)) ^ (2 : ℕ) := by
  by_cases hz : z ∈ cubeSetAt (0 : Vec d) (m + 1)
  · have hnorm := (norm_lt_of_mem_cubeSetAt_zero hz).le
    rw [abs_mul, abs_of_nonneg (vecNormSq_nonneg _)]
    calc
      |cubeCutoff d m z| * vecNormSq z ≤ 1 * ((d : ℝ) * ‖z‖ ^ (2 : ℕ)) :=
        mul_le_mul (abs_cubeCutoff_le_one d m z)
          (vecNormSq_le_dim_mul_sq_norm_model z) (vecNormSq_nonneg _) zero_le_one
      _ ≤ 1 * ((d : ℝ) * ((1 / 2 : ℝ) * (3 : ℝ) ^ (m + 1)) ^ (2 : ℕ)) := by
        gcongr
      _ = _ := by ring
  · rw [cubeCutoff_eq_zero_of_notMem hz, zero_mul, abs_zero]
    positivity

omit [NeZero d] in
private theorem abs_onePoint_cubeCutoff_mul_vecNormSq_le_model (m : ℤ)
    (x : OnePoint (Vec d)) :
    |onePointRealExtension (fun z => cubeCutoff d m z * vecNormSq z) x| ≤
      (d : ℝ) * ((1 / 2 : ℝ) * (3 : ℝ) ^ (m + 1)) ^ (2 : ℕ) := by
  induction x using OnePoint.rec with
  | infty => simp only [onePointRealExtension_infty, abs_zero]; positivity
  | coe z => simpa only [onePointRealExtension_coe] using
      abs_cubeCutoff_mul_vecNormSq_le_model m z

private theorem vecNormSq_eq_stopped_cutoff_of_survival_model
    (M : ABKModel d) (omega : FullSample d M.gamma) (m : ℤ) (t : NNReal) :
    letI := (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
    letI := (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
    ∀ eta : ContinuousPath (OnePoint (Vec d)),
      eta ∉ (survivalEvent
        (((↑) : Vec d → OnePoint (Vec d)) '' cubeSetAt (0 : Vec d) m) t)ᶜ →
      vecNormSq (onePointRetract (0 : Vec d) (eta t)) =
        onePointRealExtension (fun z => cubeCutoff d m z * vecNormSq z)
          (eta (ContinuousPath.exitTimeTrunc
            (((↑) : Vec d → OnePoint (Vec d)) '' cubeSetAt (0 : Vec d) m) t eta)) := by
  let _ := (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
  let _ := (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
  intro eta heta
  have hsurvival : eta ∈ survivalEvent
      (((↑) : Vec d → OnePoint (Vec d)) '' cubeSetAt (0 : Vec d) m) t :=
    Set.notMem_compl_iff.mp heta
  have hmem := ContinuousPath.mem_of_lt_exitTime
    (((↑) : Vec d → OnePoint (Vec d)) '' cubeSetAt (0 : Vec d) m) eta t hsurvival
  obtain ⟨z, hz, heq⟩ := hmem
  have hgoal : vecNormSq (onePointRetract (0 : Vec d) ((z : OnePoint (Vec d)))) =
      onePointRealExtension (fun w => cubeCutoff d m w * vecNormSq w)
        ((z : OnePoint (Vec d))) := by
    rw [onePointRetract_coe, onePointRealExtension_coe,
      cubeCutoff_eq_one_of_mem hz, one_mul]
  rw [exitTimeTrunc_of_mem_survivalEvent hsurvival]
  exact heq ▸ hgoal

private theorem rpow_half_pow_hundred_le_pow_fifty_model {q gamma : ℝ}
    (hq0 : 0 ≤ q) (hgamma0 : 0 ≤ gamma) (hq : q ≤ gamma ^ (100 : ℕ)) :
    q ^ (1 / 2 : ℝ) ≤ gamma ^ (50 : ℕ) := by
  have h := Real.rpow_le_rpow hq0 hq (by norm_num : (0 : ℝ) ≤ 1 / 2)
  calc
    q ^ (1 / 2 : ℝ) ≤ (gamma ^ (100 : ℕ)) ^ (1 / 2 : ℝ) := h
    _ = gamma ^ (50 : ℕ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hgamma0]
      norm_num

private theorem pow_hundred_le_pow_fifty_model {gamma : ℝ} (hgamma0 : 0 ≤ gamma)
    (hgamma1 : gamma ≤ 1) : gamma ^ (100 : ℕ) ≤ gamma ^ (50 : ℕ) := by
  rw [show gamma ^ (100 : ℕ) = gamma ^ (50 : ℕ) * gamma ^ (50 : ℕ) by rw [← pow_add]]
  exact mul_le_of_le_one_right (pow_nonneg hgamma0 50) (pow_le_one₀ hgamma0 hgamma1)

private theorem rpow_two_rpow_half_model {x : ℝ} (hx : 0 ≤ x) :
    (x ^ (2 : ℝ)) ^ (1 / 2 : ℝ) = x := by
  rw [Real.rpow_two]
  have hs := Real.sqrt_sq_eq_abs x
  rw [Real.sqrt_eq_rpow] at hs
  exact hs.trans (abs_of_nonneg hx)

/-- The C4 and C6 stopping-time removal bounds at the lift's confinement scale.  The
restricted tail hypothesis is stated at the same family and scale supplied by the caller. -/
theorem streamProcess_moment_removal_bounds_of_confinement
    (d : ℕ) [NeZero d] (hdim : 2 ≤ d) (cstar : ℝ) (hcstar : 0 < cstar)
    (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) :
    ∃ gamma4 C4 C6 Kc : ℝ, 0 < gamma4 ∧ gamma4 = 1 / 4 ∧
      0 ≤ C4 ∧ 0 ≤ C6 ∧ 1 ≤ Kc ∧ Kc = 1 ∧
      ∀ M : ABKModel d, Disorder.cstar M = cstar → M.gamma ≤ gamma4 →
      ∀ t : ℝ, 0 < t →
      ∀ (S : ℤ → Cutoff.CutoffSample d → ℝ) (K L delta : ℝ)
        (Y : ℤ → Cutoff.CutoffSample d → ℕ),
        1 ≤ K → Kc ≤ K →
        L = K * Real.sqrt |Real.log M.gamma| * intrinsicScale M.nu cstar M.gamma t →
        0 < delta → delta ≤ 1 → (∀ i : ℤ, Measurable (Y i)) →
        (∀ (i : ℤ) (omega : Cutoff.CutoffSample d),
          S i omega = displacementScale delta M.gamma (Y i omega)) →
        (∀ᵐ omega ∂(fullSampleLaw M).toMeasure,
          IsConfinementScale (fun n => widenedScale (fun i => S i omega.1) n) L
            (confinementScale S L omega.1)) →
        (∀ᵐ omega ∂(fullSampleLaw M).toMeasure,
          letI := (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
          letI := (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
          let m := confinementScale S L omega.1
          let R : ℝ := (3 : ℝ) ^ m
          let Q := (streamExhaustionTailInput M omega).wholeSpaceProcess
            ((0 : Vec d) : OnePoint (Vec d))
          ∀ k : ℤ, R ≤ (3 : ℝ) ^ k →
            Q.real {eta | (1 / 2 : ℝ) * (3 : ℝ) ^ k ≤
              ‖onePointRetract (0 : Vec d) (eta t.toNNReal)‖} ≤
              Real.exp (-c * ((((3 : ℝ) ^ k) / R) ^ (2 : ℕ)))) →
        (∀ᵐ omega ∂(fullSampleLaw M).toMeasure,
          letI := (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
          letI := (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
          cubeExitProbability M omega (confinementScale S L omega.1) t.toNNReal ≤
            M.gamma ^ (100 : ℕ)) →
        (∀ᵐ omega ∂(fullSampleLaw M).toMeasure,
          letI := (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
          letI := (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
          let m := confinementScale S L omega.1
          vecNormSq ((∫ path, onePointRetract (0 : Vec d) (path t.toNNReal)
              ∂((streamExhaustionTailInput M omega).wholeSpaceProcess
                ((0 : Vec d) : OnePoint (Vec d)))) -
            cubeStoppedMean M omega m t.toNNReal) ≤
              C4 * M.gamma ^ (100 : ℕ) * ((3 : ℝ) ^ m) ^ (2 : ℕ)) ∧
        (∀ᵐ omega ∂(fullSampleLaw M).toMeasure,
          letI := (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
          letI := (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
          let m := confinementScale S L omega.1
          abs ((∫ path, vecNormSq (onePointRetract (0 : Vec d) (path t.toNNReal))
              ∂((streamExhaustionTailInput M omega).wholeSpaceProcess
                ((0 : Vec d) : OnePoint (Vec d)))) -
            (∫ path, onePointRealExtension (fun z => cubeCutoff d m z * vecNormSq z)
                (path (ContinuousPath.exitTimeTrunc
                  (((↑) : Vec d → OnePoint (Vec d)) '' cubeSetAt (0 : Vec d) m)
                  t.toNNReal path))
              ∂((streamExhaustionTailInput M omega).wholeSpaceProcess
                ((0 : Vec d) : OnePoint (Vec d))))) ≤
              C6 * M.gamma ^ (50 : ℕ) * ((3 : ℝ) ^ m) ^ (2 : ℕ)) := by
  classical
  let Kc : ℝ := 1
  let A : ℝ := (3 / 2 : ℝ) * max 1 (c * Real.log 2)⁻¹
  let C4 : ℝ := (d : ℝ) * (12 * A + 1 / 2) ^ (2 : ℕ)
  let C6 : ℝ := (d : ℝ) * (24 * A) ^ (2 : ℕ) + (9 / 4 : ℝ) * d
  refine ⟨1 / 4, C4, C6, Kc, by norm_num, rfl, by positivity, by positivity,
    by norm_num, rfl, ?_⟩
  intro M hcs hgamma t ht S K L delta Y hK hKc hL hdelta hdelta1 hYmeas hS hconf htail hearly
  have hgamma1 : M.gamma ≤ 1 := hgamma.trans (by norm_num)
  have hA0 : 0 ≤ A := by
    dsimp only [A]
    positivity
  have hSmeas : ∀ i : ℤ, Measurable (S i) := by
    intro i
    rw [funext (hS i)]
    exact measurable_displacementScale (hYmeas i) delta M.gamma
  have _hSpos : ∀ (i : ℤ) (omega : Cutoff.CutoffSample d), 0 < S i omega := by
    intro i omega
    rw [hS i omega]
    exact displacementScale_pos hdelta M.gamma (Y i omega)
  have _hLpos : 0 < L := by
    rw [hL]
    exact mul_pos (mul_pos (lt_of_lt_of_le zero_lt_one hK)
      (zero_lt_one.trans_le (one_le_sqrt_abs_log M.shellPrefix.gamma_pos hgamma)))
      (intrinsicScale_pos M.nu_pos hcstar M.shellPrefix.gamma_pos ht)
  constructor
  · filter_upwards [hconf, htail, hearly] with omega hm htailOmega hearlyOmega
    let _ := (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
    let _ := (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
    let streamMarkovKernel : IsMarkovKernel (streamProcess M omega) :=
      (streamExhaustionTailInput M omega).wholeSpaceProcess_spec.1
    let m : ℤ := confinementScale S L omega.1
    let U : Set (OnePoint (Vec d)) := ((↑) : Vec d → OnePoint (Vec d)) '' cubeSetAt (0 : Vec d) m
    have hR : 0 < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
    have hU : IsOpen U := isOpen_image_coe_of_isOpen (isOpen_cubeSetAt (0 : Vec d) m)
    have hstop : ∀ᵐ eta ∂streamProcess M omega ((0 : Vec d) : OnePoint (Vec d)),
        eta ∈ (survivalEvent U t.toNNReal)ᶜ →
          ‖onePointRetract (0 : Vec d)
            (eta (ContinuousPath.exitTimeTrunc U t.toNNReal eta))‖ ≤
              (1 / 2 : ℝ) * (3 : ℝ) ^ m := by
      filter_upwards [ae_norm_stopped_le_half_scale_model M omega m t.toNNReal] with eta heta
      exact fun _ => heta
    have hraw := vecNormSq_integral_onePointRetract_sub_exitTimeTrunc_le
      M omega hU t.toNNReal hR hc hc1 htailOmega hstop
    dsimp only
    rw [← integral_stopped_eq_cubeStoppedMean_model M omega m t.toNNReal]
    have hqhalf := rpow_half_pow_hundred_le_pow_fifty_model measureReal_nonneg
      M.shellPrefix.gamma_pos.le hearlyOmega
    have hqpow := pow_hundred_le_pow_fifty_model M.shellPrefix.gamma_pos.le hgamma1
    dsimp only [U] at hraw
    have hroot : (((6 * 2 * (A * (3 : ℝ) ^ m)) ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) =
        12 * A * (3 : ℝ) ^ m := by
      calc
        _ = 6 * 2 * (A * (3 : ℝ) ^ m) := rpow_two_rpow_half_model (by positivity)
        _ = _ := by ring
    rw [hroot] at hraw
    have hinside1 :
        12 * A * (3 : ℝ) ^ m * cubeExitProbability M omega m t.toNNReal ^ (1 / 2 : ℝ) +
            (1 / 2 : ℝ) * (3 : ℝ) ^ m * cubeExitProbability M omega m t.toNNReal ≤
          12 * A * (3 : ℝ) ^ m * M.gamma ^ (50 : ℕ) +
            (1 / 2 : ℝ) * (3 : ℝ) ^ m * M.gamma ^ (100 : ℕ) :=
      add_le_add (mul_le_mul_of_nonneg_left hqhalf (by positivity))
        (mul_le_mul_of_nonneg_left hearlyOmega (by positivity))
    have hbase1 : 0 ≤
        12 * A * (3 : ℝ) ^ m * cubeExitProbability M omega m t.toNNReal ^ (1 / 2 : ℝ) +
          (1 / 2 : ℝ) * (3 : ℝ) ^ m * cubeExitProbability M omega m t.toNNReal := by
      exact add_nonneg
        (mul_nonneg (by positivity) (Real.rpow_nonneg measureReal_nonneg _))
        (mul_nonneg (by positivity) measureReal_nonneg)
    have hinside2 :
        12 * A * (3 : ℝ) ^ m * M.gamma ^ (50 : ℕ) +
            (1 / 2 : ℝ) * (3 : ℝ) ^ m * M.gamma ^ (100 : ℕ) ≤
          (12 * A + 1 / 2) * (3 : ℝ) ^ m * M.gamma ^ (50 : ℕ) := by
      calc
        _ ≤ 12 * A * (3 : ℝ) ^ m * M.gamma ^ (50 : ℕ) +
            (1 / 2 : ℝ) * (3 : ℝ) ^ m * M.gamma ^ (50 : ℕ) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left hqpow (by positivity))
        _ = _ := by ring
    have hbase2 : 0 ≤
        12 * A * (3 : ℝ) ^ m * M.gamma ^ (50 : ℕ) +
          (1 / 2 : ℝ) * (3 : ℝ) ^ m * M.gamma ^ (100 : ℕ) := by
      exact add_nonneg
        (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hA0)
          (zpow_nonneg (by norm_num) m)) (pow_nonneg M.shellPrefix.gamma_pos.le 50))
        (mul_nonneg (mul_nonneg (by norm_num) (zpow_nonneg (by norm_num) m))
          (pow_nonneg M.shellPrefix.gamma_pos.le 100))
    calc
      _ ≤ (d : ℝ) *
          (12 * A * (3 : ℝ) ^ m * M.gamma ^ (50 : ℕ) +
            (1 / 2 : ℝ) * (3 : ℝ) ^ m * M.gamma ^ (100 : ℕ)) ^ (2 : ℕ) := by
        exact hraw.trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hbase1 hinside1 2) (Nat.cast_nonneg d))
      _ ≤ (d : ℝ) *
          ((12 * A + 1 / 2) * (3 : ℝ) ^ m * M.gamma ^ (50 : ℕ)) ^ (2 : ℕ) := by
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hbase2 hinside2 2)
          (Nat.cast_nonneg d)
      _ = C4 * M.gamma ^ (100 : ℕ) * ((3 : ℝ) ^ m) ^ (2 : ℕ) := by
        dsimp only [C4]
        rw [show M.gamma ^ (100 : ℕ) = (M.gamma ^ (50 : ℕ)) ^ (2 : ℕ) by rw [← pow_mul]]
        ring
  · filter_upwards [hconf, htail, hearly] with omega hm htailOmega hearlyOmega
    let _ := (streamExhaustionTailInput M omega).toOnePointRegular.metricSpace
    let _ := (streamExhaustionTailInput M omega).toOnePointRegular.completeSpace
    let streamMarkovKernel : IsMarkovKernel (streamProcess M omega) :=
      (streamExhaustionTailInput M omega).wholeSpaceProcess_spec.1
    let m : ℤ := confinementScale S L omega.1
    let U : Set (OnePoint (Vec d)) := ((↑) : Vec d → OnePoint (Vec d)) '' cubeSetAt (0 : Vec d) m
    have hR : 0 < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
    have hU : IsOpen U := isOpen_image_coe_of_isOpen (isOpen_cubeSetAt (0 : Vec d) m)
    have hcutoffMeas : Measurable fun z : Vec d => cubeCutoff d m z * vecNormSq z :=
      (continuous_cubeCutoff d m).measurable.mul measurable_vecNormSq_model
    have hstop : ∀ᵐ eta ∂streamProcess M omega ((0 : Vec d) : OnePoint (Vec d)),
        eta ∈ (survivalEvent U t.toNNReal)ᶜ →
          |onePointRealExtension (fun z => cubeCutoff d m z * vecNormSq z)
            (eta (ContinuousPath.exitTimeTrunc U t.toNNReal eta))| ≤
              (d : ℝ) * ((1 / 2 : ℝ) * (3 : ℝ) ^ (m + 1)) ^ (2 : ℕ) := by
      filter_upwards [] with eta
      exact fun _ => abs_onePoint_cubeCutoff_mul_vecNormSq_le_model m _
    have hraw := abs_integral_vecNormSq_sub_exitTimeTrunc_cutoff_le
      M omega hU t.toNNReal (cubeCutoff d m) hcutoffMeas hR hc hc1 htailOmega
      (vecNormSq_eq_stopped_cutoff_of_survival_model M omega m t.toNNReal) hstop
    have hqhalf := rpow_half_pow_hundred_le_pow_fifty_model measureReal_nonneg
      M.shellPrefix.gamma_pos.le hearlyOmega
    have hqpow := pow_hundred_le_pow_fifty_model M.shellPrefix.gamma_pos.le hgamma1
    dsimp only
    have hroot : ((((d : ℝ) ^ (2 : ℕ) *
        (6 * 4 * (A * (3 : ℝ) ^ m)) ^ (4 : ℝ)) ^ (1 / 2 : ℝ))) =
        (d : ℝ) * (24 * A * (3 : ℝ) ^ m) ^ (2 : ℕ) := by
      have hbase : (d : ℝ) ^ (2 : ℕ) *
          (6 * 4 * (A * (3 : ℝ) ^ m)) ^ (4 : ℝ) =
            ((d : ℝ) * (6 * 4 * (A * (3 : ℝ) ^ m)) ^ (2 : ℕ)) ^ (2 : ℝ) := by
        rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
          show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        ring
      rw [hbase, rpow_two_rpow_half_model (mul_nonneg (Nat.cast_nonneg d) (sq_nonneg _))]
      ring
    have hthree : (3 : ℝ) ^ (m + 1) = 3 * (3 : ℝ) ^ m := by
      rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
      ring
    dsimp only [U] at hraw
    rw [hroot, hthree] at hraw
    calc
      _ ≤ ((d : ℝ) * (24 * A * (3 : ℝ) ^ m) ^ (2 : ℕ)) * M.gamma ^ (50 : ℕ) +
          ((d : ℝ) * ((1 / 2 : ℝ) * (3 * (3 : ℝ) ^ m)) ^ (2 : ℕ)) *
            M.gamma ^ (100 : ℕ) := by
        exact hraw.trans (add_le_add (mul_le_mul_of_nonneg_left hqhalf (by positivity))
          (mul_le_mul_of_nonneg_left hearlyOmega (by positivity)))
      _ ≤ ((d : ℝ) * (24 * A * (3 : ℝ) ^ m) ^ (2 : ℕ)) * M.gamma ^ (50 : ℕ) +
          ((d : ℝ) * ((1 / 2 : ℝ) * (3 * (3 : ℝ) ^ m)) ^ (2 : ℕ)) *
            M.gamma ^ (50 : ℕ) := by
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hqpow (by positivity))
      _ = C6 * M.gamma ^ (50 : ℕ) * ((3 : ℝ) ^ m) ^ (2 : ℕ) := by
        dsimp only [C6]
        ring

end

end Algsuperdiff.Section5.Provider
