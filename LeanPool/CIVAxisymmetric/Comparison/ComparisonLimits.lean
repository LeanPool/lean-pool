/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Comparison.CommutatorConvergence
public import LeanPool.CIVAxisymmetric.Comparison.EnergyInequality
public import LeanPool.CIVAxisymmetric.Comparison.MollifiedEquation
public import LeanPool.CIVAxisymmetric.Comparison.SliceBounds

/-!
# Analytic infrastructure for the `ε ↓ 0` limit of `lem:aniso:comparison`

This module supplies the two analytic limits used in step 5b of the comparison lemma, where the
mollification parameter `ε` is sent to zero in the energy `E` of `CIV.Comparison.EnergyInequality`.

The spatial mollifier `η_ε` of `CIV.Comparison.Mollifier` has unit mass, so convolving a
bounded measurable function against it does not increase the squared `L²` mass on a ball, up
to enlarging the ball by `ε`; this is the quantitative form of the classical fact that an
approximate identity contracts on `L²` (`integral_sq_mollifierKernel_convolution_le`).
Combined with the uniform convergence of the mollification of a smooth compactly supported
approximant (from `CIV.Comparison.CommutatorConvergence`), this gives the
`L²`-of-every-ball convergence of the spatial mollification of a bounded a.e.-measurable time
slice to that slice as `ε → 0` (`tendsto_integral_sq_mollifySlice_sub`).

The second limit concerns the DiPerna–Lions commutator. Its squared `L²` mass on a ball,
`commutatorL2Sq`, is a.e. strongly measurable in the time slice
(`aestronglyMeasurable_commutatorL2Sq`), and its time integral over a compact interval vanishes
as `ε ↓ 0` (`tendsto_integral_commutatorL2Sq`), by dominated convergence from the per-slice
vanishing of `CIV.Comparison.CommutatorConvergence`.

The comparison proof uses both limits to pass to `ε ↓ 0` in the integrated energy inequality
(`CIV.ae_ae_le_barrier_of_referenceTime`).
-/

public section

open MeasureTheory Set Filter Topology
open CKN

noncomputable section
namespace CIV

variable {m : ℕ}

/-! ### The mollifier is an `L²` contraction -/

/-- Cauchy–Schwarz for the mollification of a bounded measurable function, keeping the
function explicit: since `η_ε` has unit mass, the value of the mollification at `x` is
controlled by the mollification of the square. -/
private theorem sq_integral_mollifierKernel_mul_le {ε M : ℝ} (hε : 0 < ε) {h : Vec m → ℝ}
    (hh : ∀ y, |h y| ≤ M) (hhm : AEStronglyMeasurable h volume) (x : Vec m) :
    (∫ y, mollifierKernel m ε (x - y) * h y) ^ 2
      ≤ ∫ y, mollifierKernel m ε (x - y) * h y ^ 2 := by
  have hK_nonneg : ∀ y, 0 ≤ mollifierKernel m ε (x - y) := fun y => mollifierKernel_nonneg hε _
  have hK_int : Integrable (fun y => mollifierKernel m ε (x - y)) volume :=
    (integrable_mollifierKernel hε).comp_sub_left x
  have hK_cont : Continuous fun y => mollifierKernel m ε (x - y) :=
    (contDiff_mollifierKernel (m := m) ε).continuous.comp (continuous_const.sub continuous_id)
  have habs_eq : ∀ y, mollifierKernel m ε (x - y) * |h y|
      = |mollifierKernel m ε (x - y) * h y| := by
    intro y
    rw [abs_mul, abs_of_nonneg (hK_nonneg y)]
  have hhm_abs : AEStronglyMeasurable (fun y => |h y|) volume :=
    continuous_abs.comp_aestronglyMeasurable hhm
  have hKh_int : Integrable (fun y => mollifierKernel m ε (x - y) * |h y|) volume := by
    have hint : Integrable (fun y => mollifierKernel m ε (x - y) * M) volume := hK_int.mul_const M
    refine hint.mono' (hK_cont.aestronglyMeasurable.mul hhm_abs)
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hK_nonneg y) (abs_nonneg _))]
    exact mul_le_mul_of_nonneg_left (hh y) (hK_nonneg y)
  have hKh2_int : Integrable (fun y => mollifierKernel m ε (x - y) * h y ^ 2) volume := by
    have hint : Integrable (fun y => mollifierKernel m ε (x - y) * M ^ 2) volume :=
      hK_int.mul_const (M ^ 2)
    refine hint.mono' (hK_cont.aestronglyMeasurable.mul (hhm.pow 2))
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hK_nonneg y) (sq_nonneg _))]
    refine mul_le_mul_of_nonneg_left ?_ (hK_nonneg y)
    obtain ⟨h1, h2⟩ := abs_le.mp (hh y)
    exact sq_le_sq' h1 h2
  have hKh_int' : Integrable (fun y => mollifierKernel m ε (x - y) * h y) volume :=
    hKh_int.mono' (hK_cont.aestronglyMeasurable.mul hhm)
      (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs, ← habs_eq y])
  have hcs := cauchy_schwarz_kernel hK_nonneg hK_int hKh_int hKh2_int
  have habs_le : |∫ y, mollifierKernel m ε (x - y) * h y|
      ≤ ∫ y, mollifierKernel m ε (x - y) * |h y| := by
    calc |∫ y, mollifierKernel m ε (x - y) * h y|
        ≤ ∫ y, |mollifierKernel m ε (x - y) * h y| := abs_integral_le_integral_abs
      _ = ∫ y, mollifierKernel m ε (x - y) * |h y| :=
          integral_congr_ae (Filter.Eventually.of_forall fun y => (habs_eq y).symm)
  have hsq_le : (∫ y, mollifierKernel m ε (x - y) * h y) ^ 2
      ≤ (∫ y, mollifierKernel m ε (x - y) * |h y|) ^ 2 := by
    obtain ⟨l1, l2⟩ := abs_le.mp habs_le
    exact sq_le_sq' l1 l2
  have htotal : (∫ y, mollifierKernel m ε (x - y)) = 1 := by
    rw [integral_sub_left_eq_self (mollifierKernel m ε) volume x, integral_mollifierKernel hε]
  calc (∫ y, mollifierKernel m ε (x - y) * h y) ^ 2
      ≤ (∫ y, mollifierKernel m ε (x - y) * |h y|) ^ 2 := hsq_le
    _ ≤ (∫ y, mollifierKernel m ε (x - y)) * ∫ y, mollifierKernel m ε (x - y) * h y ^ 2 := hcs
    _ = ∫ y, mollifierKernel m ε (x - y) * h y ^ 2 := by rw [htotal, one_mul]

/-- The `L²` bound on a ball for the spatial mollification of a bounded measurable function:
the mollification on `closedBall 0 R` is controlled by the function itself on the slightly
larger `closedBall 0 (R + ε)`. This is the quantitative approximate-identity contraction on
`L²`, with constant exactly `1` because `η_ε` has unit mass. -/
private theorem integral_sq_mollifierKernel_convolution_le {ε R M : ℝ} (hε : 0 < ε)
    {h : Vec m → ℝ} (hh : ∀ y, |h y| ≤ M) (hhm : AEStronglyMeasurable h volume) :
    ∫ x in Metric.closedBall (0 : Vec m) R, (∫ y, mollifierKernel m ε (x - y) * h y) ^ 2
      ≤ ∫ y in Metric.closedBall (0 : Vec m) (R + ε), h y ^ 2 := by
  set s := Metric.closedBall (0 : Vec m) R with hs_def
  set t := Metric.closedBall (0 : Vec m) (R + ε) with ht_def
  have hM : 0 ≤ M := (abs_nonneg (h (0 : Vec m))).trans (hh 0)
  have hsMeas : MeasurableSet s := measurableSet_closedBall
  have htMeas : MeasurableSet t := measurableSet_closedBall
  have hsFin : IsFiniteMeasure (volume.restrict s) :=
    isFiniteMeasure_restrict.2 (isCompact_closedBall (0 : Vec m) R).measure_ne_top
  have htFin : IsFiniteMeasure (volume.restrict t) :=
    isFiniteMeasure_restrict.2 (isCompact_closedBall (0 : Vec m) (R + ε)).measure_ne_top
  have hK_nonneg : ∀ x y : Vec m, 0 ≤ mollifierKernel m ε (x - y) := fun x y =>
    mollifierKernel_nonneg hε _
  have hK_int_y : ∀ x, Integrable (fun y => mollifierKernel m ε (x - y)) volume := fun x =>
    (integrable_mollifierKernel hε).comp_sub_left x
  have hK_int_x : ∀ y, Integrable (fun x => mollifierKernel m ε (x - y)) volume := fun y =>
    (integrable_mollifierKernel hε).comp_sub_right y
  have hK_cont_y : ∀ x, Continuous fun y => mollifierKernel m ε (x - y) := fun x =>
    (contDiff_mollifierKernel (m := m) ε).continuous.comp (continuous_const.sub continuous_id)
  have hhm2 : AEStronglyMeasurable (fun y => h y ^ 2) volume := hhm.pow 2
  have hKh2_int : ∀ x, Integrable (fun y => mollifierKernel m ε (x - y) * h y ^ 2) volume := by
    intro x
    have hint : Integrable (fun y => mollifierKernel m ε (x - y) * M ^ 2) volume :=
      (hK_int_y x).mul_const (M ^ 2)
    refine hint.mono' ((hK_cont_y x).aestronglyMeasurable.mul hhm2)
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hK_nonneg x y) (sq_nonneg _))]
    refine mul_le_mul_of_nonneg_left ?_ (hK_nonneg x y)
    obtain ⟨h1, h2⟩ := abs_le.mp (hh y)
    exact sq_le_sq' h1 h2
  have hsqx : ∀ x, (∫ y, mollifierKernel m ε (x - y) * h y) ^ 2
      ≤ ∫ y, mollifierKernel m ε (x - y) * h y ^ 2 :=
    fun x => sq_integral_mollifierKernel_mul_le hε hh hhm x
  have hFmeas : AEStronglyMeasurable (fun x => ∫ y, mollifierKernel m ε (x - y) * h y) volume := by
    have hjcont : Continuous fun p : Vec m × Vec m => mollifierKernel m ε (p.1 - p.2) :=
      (contDiff_mollifierKernel (m := m) ε).continuous.comp (continuous_fst.sub continuous_snd)
    have hjoint : AEStronglyMeasurable (fun p : Vec m × Vec m =>
        mollifierKernel m ε (p.1 - p.2) * h p.2) (volume.prod volume) :=
      hjcont.aestronglyMeasurable.mul hhm.comp_snd
    exact hjoint.integral_prod_right'
  have hFbound : ∀ x, |∫ y, mollifierKernel m ε (x - y) * h y| ≤ M := by
    intro x
    have hthis := abs_mollifySlice_le (q := fun z : Vec m × ℝ => h z.1) (τ := (0 : ℝ)) hε
      hhm (Filter.Eventually.of_forall hh) x
    rwa [mollifySlice_apply] at hthis
  have hLHSint : IntegrableOn (fun x => (∫ y, mollifierKernel m ε (x - y) * h y) ^ 2) s volume := by
    have hbound : Integrable (fun _ : Vec m => M ^ 2) (volume.restrict s) := integrable_const _
    refine hbound.mono' ((hFmeas.pow 2).mono_measure Measure.restrict_le_self)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    obtain ⟨h1, h2⟩ := abs_le.mp (hFbound x)
    exact sq_le_sq' h1 h2
  have hFmeasK : AEStronglyMeasurable (fun x => ∫ y, mollifierKernel m ε (x - y) * h y ^ 2)
      volume := by
    have hjcont : Continuous fun p : Vec m × Vec m => mollifierKernel m ε (p.1 - p.2) :=
      (contDiff_mollifierKernel (m := m) ε).continuous.comp (continuous_fst.sub continuous_snd)
    have hjoint : AEStronglyMeasurable (fun p : Vec m × Vec m =>
        mollifierKernel m ε (p.1 - p.2) * h p.2 ^ 2) (volume.prod volume) :=
      hjcont.aestronglyMeasurable.mul hhm2.comp_snd
    exact hjoint.integral_prod_right'
  have hFKbound : ∀ x, (∫ y, mollifierKernel m ε (x - y) * h y ^ 2) ≤ M ^ 2 := by
    intro x
    have hmaj : Integrable (fun y => mollifierKernel m ε (x - y) * M ^ 2) volume :=
      (hK_int_y x).mul_const (M ^ 2)
    calc ∫ y, mollifierKernel m ε (x - y) * h y ^ 2
        ≤ ∫ y, mollifierKernel m ε (x - y) * M ^ 2 :=
          integral_mono (hKh2_int x) hmaj (fun y =>
            mul_le_mul_of_nonneg_left (by
              obtain ⟨h1, h2⟩ := abs_le.mp (hh y); exact sq_le_sq' h1 h2) (hK_nonneg x y))
      _ = (∫ y, mollifierKernel m ε (x - y)) * M ^ 2 := integral_mul_const _ _
      _ = 1 * M ^ 2 := by
          rw [integral_sub_left_eq_self (mollifierKernel m ε) volume x, integral_mollifierKernel hε]
      _ = M ^ 2 := one_mul _
  have hRHSint : IntegrableOn (fun x => ∫ y, mollifierKernel m ε (x - y) * h y ^ 2) s volume := by
    have hbound : Integrable (fun _ : Vec m => M ^ 2) (volume.restrict s) := integrable_const _
    refine hbound.mono' (hFmeasK.mono_measure Measure.restrict_le_self)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs,
      abs_of_nonneg (integral_nonneg fun y => mul_nonneg (hK_nonneg x y) (sq_nonneg _))]
    exact hFKbound x
  have hstep1 : (∫ x in s, (∫ y, mollifierKernel m ε (x - y) * h y) ^ 2)
      ≤ ∫ x in s, ∫ y, mollifierKernel m ε (x - y) * h y ^ 2 := setIntegral_mono hLHSint hRHSint
        hsqx
  have hrestrict : ∀ x ∈ s, (∫ y, mollifierKernel m ε (x - y) * h y ^ 2)
      = ∫ y in t, mollifierKernel m ε (x - y) * h y ^ 2 := by
    intro x hx
    rw [← integral_indicator htMeas]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    by_cases hy : y ∈ t
    · rw [Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy]
      have hxle : ‖x‖ ≤ R := by simpa [hs_def, Metric.mem_closedBall, dist_zero_right] using hx
      have hygt : R + ε < ‖y‖ := by
        simpa [ht_def, Metric.mem_closedBall, dist_zero_right, not_le] using hy
      have hrev : ‖y‖ - ‖x‖ ≤ ‖y - x‖ := norm_sub_norm_le y x
      have hnormeq : ‖y - x‖ = ‖x - y‖ := norm_sub_rev y x
      rw [hnormeq] at hrev
      have hxy : ε < ‖x - y‖ := by linarith only [hxle, hygt, hrev]
      show mollifierKernel m ε (x - y) * h y ^ 2 = 0
      rw [mollifierKernel_eq_zero hε hxy.le, zero_mul]
  have hstep2 : (∫ x in s, ∫ y, mollifierKernel m ε (x - y) * h y ^ 2)
      = ∫ x in s, ∫ y in t, mollifierKernel m ε (x - y) * h y ^ 2 :=
    setIntegral_congr_fun hsMeas hrestrict
  have hFubInt : Integrable (fun p : Vec m × Vec m => mollifierKernel m ε (p.1 - p.2) * h p.2 ^ 2)
      ((volume.restrict s).prod (volume.restrict t)) := by
    obtain ⟨w0, hw0⟩ := (contDiff_mollifierKernel (m := m) ε).continuous
      |>.exists_forall_ge_of_hasCompactSupport (hasCompactSupport_mollifierKernel hε)
    set C0 := mollifierKernel m ε w0 with hC0_def
    have hC0nonneg : 0 ≤ C0 := (hK_nonneg 0 0).trans (hw0 (0 - 0))
    have hjcont : Continuous fun p : Vec m × Vec m => mollifierKernel m ε (p.1 - p.2) :=
      (contDiff_mollifierKernel (m := m) ε).continuous.comp (continuous_fst.sub continuous_snd)
    have hmeas : AEStronglyMeasurable (fun p : Vec m × Vec m =>
        mollifierKernel m ε (p.1 - p.2) * h p.2 ^ 2)
        ((volume.restrict s).prod (volume.restrict t)) :=
      hjcont.aestronglyMeasurable.mul
        ((hhm.mono_measure Measure.restrict_le_self).pow 2).comp_snd
    refine (integrable_const (C0 * M ^ 2)).mono' hmeas (Filter.Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hK_nonneg p.1 p.2) (sq_nonneg _))]
    refine mul_le_mul (hw0 (p.1 - p.2)) ?_ (sq_nonneg _) hC0nonneg
    obtain ⟨h1, h2⟩ := abs_le.mp (hh p.2)
    exact sq_le_sq' h1 h2
  have hstep3 : (∫ x in s, ∫ y in t, mollifierKernel m ε (x - y) * h y ^ 2)
      = ∫ y in t, ∫ x in s, mollifierKernel m ε (x - y) * h y ^ 2 := integral_integral_swap hFubInt
  have hmarginal_x : ∀ y, (∫ x in s, mollifierKernel m ε (x - y)) ≤ 1 := by
    intro y
    calc ∫ x in s, mollifierKernel m ε (x - y)
        ≤ ∫ x, mollifierKernel m ε (x - y) :=
          setIntegral_le_integral (hK_int_x y) (Filter.Eventually.of_forall fun x => hK_nonneg x y)
      _ = 1 := by
          rw [integral_sub_right_eq_self (mollifierKernel m ε) y, integral_mollifierKernel hε]
  have hstep4 : ∀ y ∈ t, (∫ x in s, mollifierKernel m ε (x - y) * h y ^ 2)
      = (∫ x in s, mollifierKernel m ε (x - y)) * h y ^ 2 := fun y _ => integral_mul_const _ _
  have hmarginal_meas : AEStronglyMeasurable (fun y => ∫ x in s, mollifierKernel m ε (x - y))
      volume := by
    have hjcont : Continuous fun q : Vec m × Vec m => mollifierKernel m ε (q.2 - q.1) :=
      (contDiff_mollifierKernel (m := m) ε).continuous.comp (continuous_snd.sub continuous_fst)
    exact hjcont.aestronglyMeasurable.integral_prod_right'
  have hRHSfinal : (∫ y in t, (∫ x in s, mollifierKernel m ε (x - y)) * h y ^ 2)
      ≤ ∫ y in t, h y ^ 2 := by
    have hgint : IntegrableOn (fun y => h y ^ 2) t volume := by
      have hgbound : Integrable (fun _ : Vec m => M ^ 2) (volume.restrict t) := integrable_const _
      exact hgbound.mono' ((hhm.pow 2).mono_measure Measure.restrict_le_self)
        (Filter.Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          obtain ⟨h1, h2⟩ := abs_le.mp (hh y); exact sq_le_sq' h1 h2)
    have hLmeas : AEStronglyMeasurable
        (fun y => (∫ x in s, mollifierKernel m ε (x - y)) * h y ^ 2) volume :=
      hmarginal_meas.mul hhm2
    have hLint : IntegrableOn
        (fun y => (∫ x in s, mollifierKernel m ε (x - y)) * h y ^ 2) t volume := by
      refine hgint.mono' (hLmeas.mono_measure Measure.restrict_le_self)
        (Filter.Eventually.of_forall fun y => ?_)
      have hmnn : 0 ≤ ∫ x in s, mollifierKernel m ε (x - y) :=
        setIntegral_nonneg hsMeas (fun x _ => hK_nonneg x y)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hmnn (sq_nonneg _))]
      calc (∫ x in s, mollifierKernel m ε (x - y)) * h y ^ 2
          ≤ 1 * h y ^ 2 := mul_le_mul_of_nonneg_right (hmarginal_x y) (sq_nonneg _)
        _ = h y ^ 2 := one_mul _
    exact setIntegral_mono hLint hgint
      (fun y => (mul_le_mul_of_nonneg_right (hmarginal_x y) (sq_nonneg _)).trans (le_of_eq
        (one_mul _)))
  calc ∫ x in s, (∫ y, mollifierKernel m ε (x - y) * h y) ^ 2
      ≤ ∫ x in s, ∫ y, mollifierKernel m ε (x - y) * h y ^ 2 := hstep1
    _ = ∫ x in s, ∫ y in t, mollifierKernel m ε (x - y) * h y ^ 2 := hstep2
    _ = ∫ y in t, ∫ x in s, mollifierKernel m ε (x - y) * h y ^ 2 := hstep3
    _ = ∫ y in t, (∫ x in s, mollifierKernel m ε (x - y)) * h y ^ 2 :=
        setIntegral_congr_fun htMeas hstep4
    _ ≤ ∫ y in t, h y ^ 2 := hRHSfinal

/-! ### `L²` convergence of the spatial mollification -/

/-- Step 5b's core analytic fact, for a `∀`-bounded function: the spatial mollification of a
bounded measurable function converges to it in `L²` of every ball as `ε → 0`. -/
private theorem tendsto_integral_sq_mollifierKernel_sub_of_forall_abs_le {M R : ℝ}
    {h : Vec m → ℝ} (hh : ∀ y, |h y| ≤ M) (hhm : AEStronglyMeasurable h volume) :
    Filter.Tendsto (fun ε : ℝ => ∫ x in Metric.closedBall (0 : Vec m) R,
        ((∫ y, mollifierKernel m ε (x - y) * h y) - h x) ^ 2) (𝓝[>] 0) (𝓝 0) := by
  have hM : 0 ≤ M := (abs_nonneg (h (0 : Vec m))).trans (hh 0)
  have hhae : ∀ᵐ y ∂(volume : Measure (Vec m)), |h y| ≤ M := Filter.Eventually.of_forall hh
  set V : ℝ := (volume : Measure (Vec m)).real (Metric.closedBall (0 : Vec m) R) with hV_def
  have hVnn : 0 ≤ V := measureReal_nonneg
  rw [Metric.tendsto_nhds]
  intro θ hθ
  obtain ⟨φ, hφSmooth, hφCs, hφApprox⟩ :=
    exists_contDiff_hasCompactSupport_integral_sq_sub_le (R := R + 1) (M := M) hhae hhm
      (θ := θ / 32) (by positivity)
  have hφcont : Continuous φ := hφSmooth.continuous
  have hφm : AEStronglyMeasurable φ volume := hφcont.aestronglyMeasurable
  have hφunif : UniformContinuous φ := hφCs.uniformContinuous_of_continuous hφcont
  set δ : ℝ := Real.sqrt (θ / (8 * (V + 1))) with hδ_def
  have hδpos : 0 < δ := Real.sqrt_pos.mpr (by positivity)
  have hδsq : δ ^ 2 = θ / (8 * (V + 1)) := Real.sq_sqrt (by positivity)
  obtain ⟨η, hηpos, hmoddist⟩ := Metric.uniformContinuous_iff.mp hφunif δ hδpos
  have hmodη : ∀ y z : Vec m, ‖y - z‖ < η → |φ y - φ z| ≤ δ := by
    intro y z hyz
    have hd : dist y z < η := by rwa [dist_eq_norm]
    have hdd := hmoddist hd
    rw [Real.dist_eq] at hdd
    exact hdd.le
  obtain ⟨Cφ, hCφnn, hCφ⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ y, |φ y| ≤ C := by
    obtain ⟨C, hC⟩ := hφCs.exists_bound_of_continuousOn hφcont.continuousOn
    refine ⟨max C 0, le_max_right _ _, fun y => ?_⟩
    by_cases hy : y ∈ tsupport φ
    · exact (by simpa [Real.norm_eq_abs] using hC y hy : |φ y| ≤ C).trans (le_max_left _ _)
    · rw [image_eq_zero_of_notMem_tsupport hy, abs_zero]; exact le_max_right _ _
  have hsMeas : MeasurableSet (Metric.closedBall (0 : Vec m) R) := measurableSet_closedBall
  have hsFin : IsFiniteMeasure (volume.restrict (Metric.closedBall (0 : Vec m) R)) :=
    isFiniteMeasure_restrict.2 (isCompact_closedBall (0 : Vec m) R).measure_ne_top
  have hs1Fin : IsFiniteMeasure (volume.restrict (Metric.closedBall (0 : Vec m) (R + 1))) :=
    isFiniteMeasure_restrict.2 (isCompact_closedBall (0 : Vec m) (R + 1)).measure_ne_top
  have hRemBound : ∀ y, |h y - φ y| ≤ M + Cφ := fun y => (abs_sub _ _).trans (add_le_add (hh y)
    (hCφ y))
  have hRemm : AEStronglyMeasurable (fun y => h y - φ y) volume := hhm.sub hφm
  filter_upwards [Ioo_mem_nhdsGT (lt_min hηpos one_pos)] with ε hεmem
  obtain ⟨hεpos, hεltmin⟩ := hεmem
  have hεltη : ε < η := lt_of_lt_of_le hεltmin (min_le_left _ _)
  have hεlt1 : ε < 1 := lt_of_lt_of_le hεltmin (min_le_right _ _)
  have hK_int_y : ∀ x : Vec m, Integrable (fun y => mollifierKernel m ε (x - y)) volume := fun x =>
    (integrable_mollifierKernel hεpos).comp_sub_left x
  have hIntPhi : ∀ x, Integrable (fun y => mollifierKernel m ε (x - y) * φ y) volume := fun x =>
    (hK_int_y x).mul_bdd hφm (Filter.Eventually.of_forall fun y => by
      simpa [Real.norm_eq_abs] using hCφ y)
  have hIntRem : ∀ x, Integrable (fun y => mollifierKernel m ε (x - y) * (h y - φ y)) volume :=
    fun x => (hK_int_y x).mul_bdd hRemm (Filter.Eventually.of_forall fun y => by
      simpa [Real.norm_eq_abs] using hRemBound y)
  have hdecomp : ∀ x : Vec m, (∫ y, mollifierKernel m ε (x - y) * h y) - h x
      = ((∫ y, mollifierKernel m ε (x - y) * φ y) - φ x)
        + ((∫ y, mollifierKernel m ε (x - y) * (h y - φ y)) - (h x - φ x)) := by
    intro x
    have hsplit : (∫ y, mollifierKernel m ε (x - y) * h y)
        = (∫ y, mollifierKernel m ε (x - y) * φ y)
          + ∫ y, mollifierKernel m ε (x - y) * (h y - φ y) := by
      rw [← integral_add (hIntPhi x) (hIntRem x)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      ring
    rw [hsplit]; ring
  have hUnifPhi : ∀ x : Vec m, |(∫ y, mollifierKernel m ε (x - y) * φ y) - φ x| ≤ δ := fun x =>
    abs_integral_mollifierKernel_mul_sub_le hεpos hφcont
      (fun y z hyz => hmodη y z (hyz.trans hεltη)) x
  have hsqbound : ∀ x : Vec m,
      ((∫ y, mollifierKernel m ε (x - y) * h y) - h x) ^ 2
        ≤ 2 * ((∫ y, mollifierKernel m ε (x - y) * φ y) - φ x) ^ 2
          + 2 * ((∫ y, mollifierKernel m ε (x - y) * (h y - φ y)) - (h x - φ x)) ^ 2 := by
    intro x
    rw [hdecomp x]
    nlinarith only [sq_nonneg (((∫ y, mollifierKernel m ε (x - y) * φ y) - φ x)
      - ((∫ y, mollifierKernel m ε (x - y) * (h y - φ y)) - (h x - φ x)))]
  have hFφmeas : AEStronglyMeasurable (fun x => ∫ y, mollifierKernel m ε (x - y) * φ y) volume := by
    have hjcont : Continuous fun p : Vec m × Vec m => mollifierKernel m ε (p.1 - p.2) * φ p.2 :=
      ((contDiff_mollifierKernel (m := m) ε).continuous.comp
        (continuous_fst.sub continuous_snd)).mul (hφcont.comp continuous_snd)
    exact hjcont.aestronglyMeasurable.integral_prod_right'
  have hIntPhiSqOn : IntegrableOn
      (fun x => ((∫ y, mollifierKernel m ε (x - y) * φ y) - φ x) ^ 2)
      (Metric.closedBall (0 : Vec m) R) volume := by
    refine (integrable_const (δ ^ 2)).mono' (((hFφmeas.sub hφm).pow 2).mono_measure
      Measure.restrict_le_self)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    obtain ⟨l1, l2⟩ := abs_le.mp (hUnifPhi x)
    exact sq_le_sq' l1 l2
  have hstepPhi : (∫ x in Metric.closedBall (0 : Vec m) R,
      ((∫ y, mollifierKernel m ε (x - y) * φ y) - φ x) ^ 2) ≤ V * δ ^ 2 := by
    calc (∫ x in Metric.closedBall (0 : Vec m) R,
        ((∫ y, mollifierKernel m ε (x - y) * φ y) - φ x) ^ 2)
        ≤ ∫ _x in Metric.closedBall (0 : Vec m) R, δ ^ 2 :=
          setIntegral_mono_on hIntPhiSqOn (integrable_const _) hsMeas (fun x _ => by
            obtain ⟨l1, l2⟩ := abs_le.mp (hUnifPhi x); exact sq_le_sq' l1 l2)
      _ = V * δ ^ 2 := by rw [setIntegral_const, smul_eq_mul]
  have hRemFbound : ∀ x : Vec m, |∫ y, mollifierKernel m ε (x - y) * (h y - φ y)| ≤ M + Cφ := by
    intro x
    have hthis := abs_mollifySlice_le (q := fun z : Vec m × ℝ => h z.1 - φ z.1) (τ := (0 : ℝ))
      hεpos hRemm (Filter.Eventually.of_forall hRemBound) x
    rwa [mollifySlice_apply] at hthis
  have hFremmeas : AEStronglyMeasurable
      (fun x => ∫ y, mollifierKernel m ε (x - y) * (h y - φ y)) volume := by
    have hjcont : Continuous fun p : Vec m × Vec m => mollifierKernel m ε (p.1 - p.2) :=
      (contDiff_mollifierKernel (m := m) ε).continuous.comp (continuous_fst.sub continuous_snd)
    have hjoint : AEStronglyMeasurable
        (fun p : Vec m × Vec m => mollifierKernel m ε (p.1 - p.2) * (h p.2 - φ p.2))
        (volume.prod volume) :=
      hjcont.aestronglyMeasurable.mul hRemm.comp_snd
    exact hjoint.integral_prod_right'
  have hIntRemDiffSqOn : IntegrableOn
      (fun x => ((∫ y, mollifierKernel m ε (x - y) * (h y - φ y)) - (h x - φ x)) ^ 2)
      (Metric.closedBall (0 : Vec m) R) volume := by
    refine (integrable_const ((2 * (M + Cφ)) ^ 2)).mono' (((hFremmeas.sub hRemm).pow
      2).mono_measure Measure.restrict_le_self)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have habs : |(∫ y, mollifierKernel m ε (x - y) * (h y - φ y)) - (h x - φ x)|
        ≤ 2 * (M + Cφ) := by
      calc |(∫ y, mollifierKernel m ε (x - y) * (h y - φ y)) - (h x - φ x)|
          ≤ |∫ y, mollifierKernel m ε (x - y) * (h y - φ y)| + |h x - φ x| := abs_sub _ _
        _ ≤ (M + Cφ) + (M + Cφ) := add_le_add (hRemFbound x) (hRemBound x)
        _ = 2 * (M + Cφ) := by ring
    obtain ⟨l1, l2⟩ := abs_le.mp habs
    exact sq_le_sq' l1 l2
  have hIntRemSqOn : IntegrableOn
      (fun x => (∫ y, mollifierKernel m ε (x - y) * (h y - φ y)) ^ 2)
      (Metric.closedBall (0 : Vec m) R) volume := by
    refine (integrable_const ((M + Cφ) ^ 2)).mono' ((hFremmeas.pow 2).mono_measure
      Measure.restrict_le_self)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    obtain ⟨l1, l2⟩ := abs_le.mp (hRemFbound x)
    exact sq_le_sq' l1 l2
  have hRemSqOn1 : IntegrableOn (fun x => (h x - φ x) ^ 2) (Metric.closedBall (0 : Vec m) (R + 1))
      volume := by
    refine (integrable_const ((M + Cφ) ^ 2)).mono' ((hRemm.pow 2).mono_measure
      Measure.restrict_le_self)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    obtain ⟨l1, l2⟩ := abs_le.mp (hRemBound x)
    exact sq_le_sq' l1 l2
  have hcontr : (∫ x in Metric.closedBall (0 : Vec m) R,
      (∫ y, mollifierKernel m ε (x - y) * (h y - φ y)) ^ 2)
      ≤ θ / 32 := by
    have hstep := integral_sq_mollifierKernel_convolution_le (m := m) (ε := ε) (R := R)
      (M := M + Cφ) hεpos hRemBound hRemm
    have hmono : (∫ y in Metric.closedBall (0 : Vec m) (R + ε), (h y - φ y) ^ 2)
        ≤ ∫ y in Metric.closedBall (0 : Vec m) (R + 1), (h y - φ y) ^ 2 := by
      refine setIntegral_mono_set hRemSqOn1 (Filter.Eventually.of_forall fun _y => sq_nonneg _) ?_
      have hsub : Metric.closedBall (0 : Vec m) (R + ε) ⊆ Metric.closedBall (0 : Vec m) (R + 1) :=
        Metric.closedBall_subset_closedBall (by linarith only [hεlt1])
      exact LE.le.eventuallySubset hsub
    exact hstep.trans (hmono.trans hφApprox)
  have hRemBaseBound : (∫ x in Metric.closedBall (0 : Vec m) R, (h x - φ x) ^ 2) ≤ θ / 32 := by
    have hmono : (∫ x in Metric.closedBall (0 : Vec m) R, (h x - φ x) ^ 2)
        ≤ ∫ x in Metric.closedBall (0 : Vec m) (R + 1), (h x - φ x) ^ 2 := by
      refine setIntegral_mono_set hRemSqOn1 (Filter.Eventually.of_forall fun _x => sq_nonneg _) ?_
      have hsub : Metric.closedBall (0 : Vec m) R ⊆ Metric.closedBall (0 : Vec m) (R + 1) :=
        Metric.closedBall_subset_closedBall (by linarith only [hθ])
      exact LE.le.eventuallySubset hsub
    exact hmono.trans hφApprox
  have hRHSint : IntegrableOn (fun x =>
      2 * ((∫ y, mollifierKernel m ε (x - y) * φ y) - φ x) ^ 2
        + 2 * ((∫ y, mollifierKernel m ε (x - y) * (h y - φ y)) - (h x - φ x)) ^ 2)
      (Metric.closedBall (0 : Vec m) R) volume :=
    (hIntPhiSqOn.const_mul 2).add (hIntRemDiffSqOn.const_mul 2)
  have hLHSint : IntegrableOn (fun x => ((∫ y, mollifierKernel m ε (x - y) * h y) - h x) ^ 2)
      (Metric.closedBall (0 : Vec m) R) volume := by
    have hFhmeas : AEStronglyMeasurable (fun x => ∫ y, mollifierKernel m ε (x - y) * h y) volume
      := by
      have hjcont : Continuous fun p : Vec m × Vec m => mollifierKernel m ε (p.1 - p.2) :=
        (contDiff_mollifierKernel (m := m) ε).continuous.comp (continuous_fst.sub continuous_snd)
      have hjoint : AEStronglyMeasurable
          (fun p : Vec m × Vec m => mollifierKernel m ε (p.1 - p.2) * h p.2) (volume.prod volume) :=
        hjcont.aestronglyMeasurable.mul hhm.comp_snd
      exact hjoint.integral_prod_right'
    refine hRHSint.mono' (((hFhmeas.sub hhm).pow 2).mono_measure Measure.restrict_le_self)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hsqbound x
  have hstep : (∫ x in Metric.closedBall (0 : Vec m) R,
      ((∫ y, mollifierKernel m ε (x - y) * h y) - h x) ^ 2)
      ≤ 2 * (∫ x in Metric.closedBall (0 : Vec m) R,
            ((∫ y, mollifierKernel m ε (x - y) * φ y) - φ x) ^ 2)
        + 2 * ∫ x in Metric.closedBall (0 : Vec m) R,
            ((∫ y, mollifierKernel m ε (x - y) * (h y - φ y)) - (h x - φ x)) ^ 2 := by
    calc (∫ x in Metric.closedBall (0 : Vec m) R,
        ((∫ y, mollifierKernel m ε (x - y) * h y) - h x) ^ 2)
        ≤ ∫ x in Metric.closedBall (0 : Vec m) R,
            (2 * ((∫ y, mollifierKernel m ε (x - y) * φ y) - φ x) ^ 2
              + 2 * ((∫ y, mollifierKernel m ε (x - y) * (h y - φ y)) - (h x - φ x)) ^ 2) :=
          setIntegral_mono hLHSint hRHSint (fun x => hsqbound x)
      _ = 2 * (∫ x in Metric.closedBall (0 : Vec m) R,
              ((∫ y, mollifierKernel m ε (x - y) * φ y) - φ x) ^ 2)
            + 2 * ∫ x in Metric.closedBall (0 : Vec m) R,
              ((∫ y, mollifierKernel m ε (x - y) * (h y - φ y)) - (h x - φ x)) ^ 2 := by
          rw [integral_add (hIntPhiSqOn.const_mul 2) (hIntRemDiffSqOn.const_mul 2),
            integral_const_mul, integral_const_mul]
  have hTermB : (∫ x in Metric.closedBall (0 : Vec m) R,
      ((∫ y, mollifierKernel m ε (x - y) * (h y - φ y)) - (h x - φ x)) ^ 2)
      ≤ 2 * (θ / 32) + 2 * (θ / 32) := by
    have hpt : ∀ x ∈ Metric.closedBall (0 : Vec m) R,
        ((∫ y, mollifierKernel m ε (x - y) * (h y - φ y)) - (h x - φ x)) ^ 2
          ≤ 2 * (∫ y, mollifierKernel m ε (x - y) * (h y - φ y)) ^ 2 + 2 * (h x - φ x) ^ 2 := by
      intro x _
      nlinarith only [sq_nonneg ((∫ y, mollifierKernel m ε (x - y) * (h y - φ y)) + (h x - φ x))]
    have hRHS2 : IntegrableOn (fun x => 2 * (∫ y, mollifierKernel m ε (x - y) * (h y - φ y)) ^ 2
        + 2 * (h x - φ x) ^ 2) (Metric.closedBall (0 : Vec m) R) volume :=
      (hIntRemSqOn.const_mul 2).add ((hRemSqOn1.mono_set
        (Metric.closedBall_subset_closedBall (by linarith only [hθ]))).const_mul 2)
    calc (∫ x in Metric.closedBall (0 : Vec m) R,
        ((∫ y, mollifierKernel m ε (x - y) * (h y - φ y)) - (h x - φ x)) ^ 2)
        ≤ ∫ x in Metric.closedBall (0 : Vec m) R,
            (2 * (∫ y, mollifierKernel m ε (x - y) * (h y - φ y)) ^ 2 + 2 * (h x - φ x) ^ 2) :=
          setIntegral_mono_on hIntRemDiffSqOn hRHS2 hsMeas hpt
      _ = 2 * (∫ x in Metric.closedBall (0 : Vec m) R,
              (∫ y, mollifierKernel m ε (x - y) * (h y - φ y)) ^ 2)
            + 2 * ∫ x in Metric.closedBall (0 : Vec m) R, (h x - φ x) ^ 2 := by
          rw [integral_add (hIntRemSqOn.const_mul 2)
            ((hRemSqOn1.mono_set (Metric.closedBall_subset_closedBall
              (by linarith only [hθ]))).const_mul 2), integral_const_mul, integral_const_mul]
      _ ≤ 2 * (θ / 32) + 2 * (θ / 32) := by
          have h1 : (∫ x in Metric.closedBall (0 : Vec m) R,
              (∫ y, mollifierKernel m ε (x - y) * (h y - φ y)) ^ 2) ≤ θ / 32 := hcontr
          have h2 : (∫ x in Metric.closedBall (0 : Vec m) R, (h x - φ x) ^ 2) ≤ θ / 32 :=
            hRemBaseBound
          linarith only [h1, h2]
  have hTermA : (∫ x in Metric.closedBall (0 : Vec m) R,
      ((∫ y, mollifierKernel m ε (x - y) * φ y) - φ x) ^ 2) ≤ θ / 8 := by
    have hVfrac : V * δ ^ 2 ≤ θ / 8 := by
      rw [hδsq]
      have hVle : V / (V + 1) ≤ 1 := by
        rw [div_le_one (by linarith only [hVnn])]
        linarith only [hVnn]
      have heq : V * (θ / (8 * (V + 1))) = (θ / 8) * (V / (V + 1)) := by
        field_simp
      rw [heq]
      have hθ8 : (0 : ℝ) ≤ θ / 8 := by linarith only [hθ]
      calc (θ / 8) * (V / (V + 1)) ≤ (θ / 8) * 1 := mul_le_mul_of_nonneg_left hVle hθ8
        _ = θ / 8 := mul_one _
    exact hstepPhi.trans hVfrac
  have hfinal : (∫ x in Metric.closedBall (0 : Vec m) R,
      ((∫ y, mollifierKernel m ε (x - y) * h y) - h x) ^ 2) ≤ θ / 2 := by
    have h1 := hTermA
    have h2 := hTermB
    linarith only [hstep, h1, h2]
  have hnn : (0:ℝ) ≤ ∫ x in Metric.closedBall (0 : Vec m) R,
      ((∫ y, mollifierKernel m ε (x - y) * h y) - h x) ^ 2 := integral_nonneg fun _x => sq_nonneg _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
  linarith only [hfinal, hθ]

/-- An a.e. bounded, a.e. strongly measurable function agrees a.e. with an everywhere bounded,
a.e. strongly measurable representative. -/
private theorem exists_stronglyMeasurable_bound {M : ℝ} (hM : 0 ≤ M) {g : Vec m → ℝ}
    (hg : ∀ᵐ y ∂(volume : Measure (Vec m)), |g y| ≤ M) (hgm : AEStronglyMeasurable g volume) :
    ∃ g' : Vec m → ℝ, (∀ y, |g' y| ≤ M) ∧ AEStronglyMeasurable g' volume ∧ g =ᵐ[volume] g' := by
  classical
  obtain ⟨f, hfmeas, hae⟩ := hgm
  have hmeas : Measurable f := hfmeas.measurable
  have habs : Measurable fun y : Vec m => |f y| := continuous_abs.measurable.comp hmeas
  have hset : MeasurableSet {y : Vec m | |f y| ≤ M} := measurableSet_le habs measurable_const
  refine ⟨fun y => if |f y| ≤ M then f y else 0, ?_, ?_, ?_⟩
  · intro y
    show |if |f y| ≤ M then f y else 0| ≤ M
    split_ifs with hy
    · exact hy
    · rw [abs_zero]; exact hM
  · exact (StronglyMeasurable.ite hset hfmeas stronglyMeasurable_const).aestronglyMeasurable
  · filter_upwards [hae, hg] with y hy1 hy2
    have hy3 : |f y| ≤ M := by rw [← hy1]; exact hy2
    have hif : (if |f y| ≤ M then f y else 0) = f y :=
      ite_eq_left_iff.mpr fun hcond => absurd hy3 hcond
    show g y = if |f y| ≤ M then f y else 0
    rw [hif]; exact hy1

/-! ### `L²` convergence of `mollifySlice` -/

/-- Step 5b's core analytic fact: the spatial mollification of a bounded a.e.-measurable time
slice converges to it in `L²` of every ball as `ε → 0`. -/
theorem tendsto_integral_sq_mollifySlice_sub {M R τ : ℝ} {q : Vec m × ℝ → ℝ}
    (hqb : ∀ᵐ y ∂(volume : Measure (Vec m)), |q (y, τ)| ≤ M)
    (hqm : AEStronglyMeasurable (fun y => q (y, τ)) volume) :
    Filter.Tendsto (fun ε : ℝ => ∫ x in Metric.closedBall (0 : Vec m) R,
        (mollifySlice m ε q (x, τ) - q (x, τ)) ^ 2) (𝓝[>] 0) (𝓝 0) := by
  have hM : 0 ≤ M := by
    obtain ⟨y, hy⟩ := hqb.exists
    exact (abs_nonneg _).trans hy
  obtain ⟨h', hh'bound, hh'meas, hqh'⟩ := exists_stronglyMeasurable_bound hM hqb hqm
  have hcore := tendsto_integral_sq_mollifierKernel_sub_of_forall_abs_le
    (M := M) (R := R) hh'bound hh'meas
  have heq : ∀ ε : ℝ, (∫ x in Metric.closedBall (0 : Vec m) R,
        (mollifySlice m ε q (x, τ) - q (x, τ)) ^ 2)
      = ∫ x in Metric.closedBall (0 : Vec m) R,
        ((∫ y, mollifierKernel m ε (x - y) * h' y) - h' x) ^ 2 := by
    intro ε
    have hAEfun : (fun x => (mollifySlice m ε q (x, τ) - q (x, τ)) ^ 2)
        =ᵐ[volume] (fun x => ((∫ y, mollifierKernel m ε (x - y) * h' y) - h' x) ^ 2) := by
      filter_upwards [hqh'] with x hx
      have hK : (∫ y, mollifierKernel m ε (x - y) * q (y, τ))
          = ∫ y, mollifierKernel m ε (x - y) * h' y :=
        integral_congr_ae (hqh'.mono fun y hy => by simp only [hy])
      rw [mollifySlice_apply, hK, hx]
    exact setIntegral_congr_ae measurableSet_closedBall (hAEfun.mono fun x hx _ => hx)
  simpa only [heq] using hcore

/-! ### Vanishing of the commutator, integrated over a compact time interval -/

/-- The full four-conjunct slice data of `IsAdmissibleDrift`, for a.e. `τ` in a compact
sub-interval: the drift bound, Lipschitz bound, divergence bound, and the weak-divergence
testing property that `CIV.Comparison.SliceBounds.IsAdmissibleDrift.ae_slice` does not
retain. -/
private theorem isAdmissibleDrift_ae_slice_full {I J : Set ℝ} {B : Vec m × ℝ → Vec m}
    {divB : Vec m × ℝ → ℝ} (hB : IsAdmissibleDrift m I B divB) (hJ : IsCompact J)
    (hJI : J ⊆ I) :
    ∃ Λ : NNReal, ∀ᵐ τ ∂(volume.restrict J),
      (∀ x, ‖B (x, τ)‖ ≤ Λ) ∧ LipschitzWith Λ (fun x => B (x, τ)) ∧ (∀ x, |divB (x, τ)| ≤ Λ) ∧
        ∀ ψ : Vec m → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
          ∫ x, divB (x, τ) * ψ x = -∫ x, ∑ i, B (x, τ) i * fderiv ℝ ψ x (basisVec i) :=
  hB.2.2 J hJ hJI

/-- The commutator does not see an a.e.-change of the transported function: both defining
integrals of `diPernaLionsCommutator` are Bochner integrals against `g`. -/
private theorem diPernaLionsCommutator_congr_ae {ε : ℝ} {b : Vec m → Vec m} {divb g g' : Vec m → ℝ}
    (hgg' : g =ᵐ[volume] g') (x : Vec m) :
    diPernaLionsCommutator m ε b divb g x = diPernaLionsCommutator m ε b divb g' x := by
  unfold diPernaLionsCommutator
  have h1 : (∫ y : Vec m, g y *
        ∑ i, (b x i - b y i) * fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i))
      = ∫ y : Vec m, g' y *
        ∑ i, (b x i - b y i) * fderiv ℝ (mollifierKernel m ε) (x - y) (basisVec i) :=
    integral_congr_ae (hgg'.mono fun y hy => by simp only [hy])
  have h2 : (∫ y : Vec m, mollifierKernel m ε (x - y) * (divb y * g y))
      = ∫ y : Vec m, mollifierKernel m ε (x - y) * (divb y * g' y) :=
    integral_congr_ae (hgg'.mono fun y hy => by simp only [hy])
  rw [h1, h2]

/-- The squared `L²` mass on a ball of the DiPerna–Lions commutator of one time slice. -/
@[expose] def commutatorL2Sq (m : ℕ) (ε Rb : ℝ) (B : Vec m × ℝ → Vec m) (divB q : Vec m × ℝ → ℝ)
  (s : ℝ) :
    ℝ :=
  ∫ x in Metric.closedBall (0 : Vec m) Rb,
    diPernaLionsCommutator m ε (fun y => B (y, s)) (fun y => divB (y, s)) (fun y => q (y, s)) x ^ 2

/-! ### Joint measurability of the commutator's ball mass in the time slice -/

/-- Joint `AEStronglyMeasurable`ness, in the pair `(x, s) : Vec m × ℝ`, of the DiPerna–Lions
commutator transported along a time-parametrized drift `B`, its divergence, and a time-parametrized
function `q`: from `B` and its divergence jointly measurable in space-time and `q` jointly
`AEStronglyMeasurable` on `Vec m × ℝ` against `(volume : Measure (Vec m)).prod μs` for any
`SFinite` measure `μs` on the time axis, the commutator itself — built at each fixed time slice
`s` from the space-time restrictions of `B`, its divergence, and `q`, and evaluated at the
spatial point `x` — is jointly `AEStronglyMeasurable` against the product measure. This is the
three-variable extension of
`aestronglyMeasurable_diPernaLionsCommutator`'s two-variable argument: it bundles `(x, s)` into
one product factor and integrates the spatial variable `y` of the commutator's two defining
integrals out of it. It is the shared step behind `aestronglyMeasurable_commutatorL2Sq`, which
squares and ball-restricts this fact before integrating `x` out entirely. -/
theorem aestronglyMeasurable_diPernaLionsCommutator_prod {ε : ℝ} {B : Vec m × ℝ → Vec m}
    {divB q : Vec m × ℝ → ℝ} {μs : Measure ℝ} [SFinite μs] (hBmeas : Measurable B)
    (hdivBmeas : Measurable divB)
    (hqmeas : AEStronglyMeasurable q ((volume : Measure (Vec m)).prod μs)) :
    AEStronglyMeasurable
      (fun p : Vec m × ℝ =>
        diPernaLionsCommutator m ε (fun y => B (y, p.2)) (fun y => divB (y, p.2))
          (fun y => q (y, p.2)) p.1)
      ((volume : Measure (Vec m)).prod μs) := by
  set μx : Measure (Vec m) := (volume : Measure (Vec m)) with hμx_def
  -- `q` composed with the coordinate map that drops `x` and swaps `(y, s)` to match `q`'s
  -- own argument order, jointly measurable on the full `(x, s, y)` triple
  have hqjoint : AEStronglyMeasurable (fun t : (Vec m × ℝ) × Vec m => q (t.2, t.1.2))
      ((μx.prod μs).prod μx) := by
    have hg : AEStronglyMeasurable (fun z : ℝ × Vec m => q z.swap) (μs.prod μx) :=
      hqmeas.prod_swap
    have hf : Measure.QuasiMeasurePreserving
        (Prod.map (Prod.snd : Vec m × ℝ → ℝ) (id : Vec m → Vec m))
        ((μx.prod μs).prod μx) (μs.prod μx) :=
      QuasiMeasurePreserving.prodMap Measure.quasiMeasurePreserving_snd
        (Measure.QuasiMeasurePreserving.id μx)
    exact hg.comp_quasiMeasurePreserving hf
  have hswapMeas :
      Measurable (fun t : (Vec m × ℝ) × Vec m => (t.2, t.1.2) : (Vec m × ℝ) × Vec m → Vec m × ℝ) :=
    measurable_snd.prodMk (measurable_snd.comp measurable_fst)
  have hB1 : Measurable (fun t : (Vec m × ℝ) × Vec m => B t.1) := hBmeas.comp measurable_fst
  have hB2 : Measurable (fun t : (Vec m × ℝ) × Vec m => B (t.2, t.1.2)) := hBmeas.comp hswapMeas
  have hdivB2 : Measurable (fun t : (Vec m × ℝ) × Vec m => divB (t.2, t.1.2)) :=
    hdivBmeas.comp hswapMeas
  have hxminusy : Continuous (fun t : (Vec m × ℝ) × Vec m => t.1.1 - t.2) :=
    (continuous_fst.comp continuous_fst).sub continuous_snd
  have hfderiv : ∀ i : Fin m, Continuous (fun t : (Vec m × ℝ) × Vec m =>
      fderiv ℝ (mollifierKernel m ε) (t.1.1 - t.2) (basisVec i)) :=
    fun i => (continuous_fderiv_mollifierKernel ε (basisVec i)).comp hxminusy
  have hmk : Continuous (fun t : (Vec m × ℝ) × Vec m => mollifierKernel m ε (t.1.1 - t.2)) :=
    (contDiff_mollifierKernel (m := m) ε).continuous.comp hxminusy
  -- the two commutator integrands, jointly measurable on the `(x, s, y)` triple
  have hΦ1 : AEStronglyMeasurable (fun t : (Vec m × ℝ) × Vec m =>
      q (t.2, t.1.2) * ∑ i, (B t.1 i - B (t.2, t.1.2) i) *
        fderiv ℝ (mollifierKernel m ε) (t.1.1 - t.2) (basisVec i))
      ((μx.prod μs).prod μx) := by
    have hsum : Measurable (fun t : (Vec m × ℝ) × Vec m =>
        ∑ i, (B t.1 i - B (t.2, t.1.2) i) *
          fderiv ℝ (mollifierKernel m ε) (t.1.1 - t.2) (basisVec i)) :=
      Finset.measurable_sum Finset.univ (fun i _ =>
        (((measurable_pi_apply i).comp hB1).sub ((measurable_pi_apply i).comp hB2)).mul
          (hfderiv i).measurable)
    exact hqjoint.mul hsum.aestronglyMeasurable
  have hΦ2 : AEStronglyMeasurable (fun t : (Vec m × ℝ) × Vec m =>
      mollifierKernel m ε (t.1.1 - t.2) * (divB (t.2, t.1.2) * q (t.2, t.1.2)))
      ((μx.prod μs).prod μx) :=
    hmk.aestronglyMeasurable.mul (hdivB2.aestronglyMeasurable.mul hqjoint)
  -- integrate `y` out, keeping `(x, s)` bundled: the joint measurability of the commutator
  -- itself, in `(x, s)`
  have hT1 : AEStronglyMeasurable (fun p : Vec m × ℝ => ∫ y : Vec m,
      q (y, p.2) * ∑ i, (B p i - B (y, p.2) i) *
        fderiv ℝ (mollifierKernel m ε) (p.1 - y) (basisVec i)) (μx.prod μs) :=
    hΦ1.integral_prod_right'
  have hT2 : AEStronglyMeasurable (fun p : Vec m × ℝ => ∫ y : Vec m,
      mollifierKernel m ε (p.1 - y) * (divB (y, p.2) * q (y, p.2))) (μx.prod μs) :=
    hΦ2.integral_prod_right'
  exact hT1.add hT2

/-- Joint measurability of the DiPerna–Lions commutator's squared `L²` mass on a ball in the
time slice `s`: given `B` and its divergence jointly measurable in space-time and `q` a.e. strongly
measurable on `ℝ^m × (τ₀, τ₊]`, the ball integral `commutatorL2Sq` is a.e. strongly measurable
as a function of `s` alone. This reduces to `aestronglyMeasurable_diPernaLionsCommutator_prod`
for the joint `(x, s)`-measurability of the commutator itself, then repeats a `y`-integration a
second time to remove `x` itself, over the ball, threading the ball restriction through an
indicator since `AEStronglyMeasurable.integral_prod_right'` integrates over the whole space. -/
theorem aestronglyMeasurable_commutatorL2Sq {ε Rb τ₀ tplus : ℝ} {B : Vec m × ℝ → Vec m}
    {divB q : Vec m × ℝ → ℝ} (hBmeas : Measurable B) (hdivBmeas : Measurable divB)
    (hqmeas : AEStronglyMeasurable q (volume.restrict (univ ×ˢ Ioc τ₀ tplus))) :
    AEStronglyMeasurable (fun s => commutatorL2Sq m ε Rb B divB q s)
      (volume.restrict (Ioc τ₀ tplus)) := by
  set μx : Measure (Vec m) := (volume : Measure (Vec m)) with hμx_def
  set μs : Measure ℝ := volume.restrict (Ioc τ₀ tplus) with hμs_def
  -- rewrite `q`'s hypothesis to match `aestronglyMeasurable_diPernaLionsCommutator_prod`'s
  -- `μx.prod μs` shape, then hand off the whole `(x, s, y)`-bundling argument to that lemma
  have hqmeas' : AEStronglyMeasurable q (μx.prod μs) := by
    have heq : μx.prod μs = volume.restrict (univ ×ˢ Ioc τ₀ tplus) := by
      rw [hμx_def, hμs_def, ← Measure.restrict_univ (μ := (volume : Measure (Vec m))),
        Measure.prod_restrict, ← Measure.volume_eq_prod]
    rw [heq]
    exact hqmeas
  have hH : AEStronglyMeasurable
      (fun p : Vec m × ℝ =>
        diPernaLionsCommutator m ε (fun y => B (y, p.2)) (fun y => divB (y, p.2))
          (fun y => q (y, p.2)) p.1)
      (μx.prod μs) :=
    aestronglyMeasurable_diPernaLionsCommutator_prod hBmeas hdivBmeas hqmeas'
  have hHsq : AEStronglyMeasurable
      (fun p : Vec m × ℝ =>
        diPernaLionsCommutator m ε (fun y => B (y, p.2)) (fun y => divB (y, p.2))
          (fun y => q (y, p.2)) p.1 ^ 2)
      (μx.prod μs) := hH.pow 2
  -- integrate `x` out over the ball, via an indicator, keeping `s` alone
  have hGind : AEStronglyMeasurable
      ((Metric.closedBall (0 : Vec m) Rb ×ˢ (univ : Set ℝ)).indicator
        (fun p : Vec m × ℝ =>
          diPernaLionsCommutator m ε (fun y => B (y, p.2)) (fun y => divB (y, p.2))
            (fun y => q (y, p.2)) p.1 ^ 2))
      (μx.prod μs) :=
    hHsq.indicator (measurableSet_closedBall.prod MeasurableSet.univ)
  have hGswap : AEStronglyMeasurable (fun z : ℝ × Vec m =>
      (Metric.closedBall (0 : Vec m) Rb ×ˢ (univ : Set ℝ)).indicator
        (fun p : Vec m × ℝ =>
          diPernaLionsCommutator m ε (fun y => B (y, p.2)) (fun y => divB (y, p.2))
            (fun y => q (y, p.2)) p.1 ^ 2) z.swap)
      (μs.prod μx) := hGind.prod_swap
  have hfinal := hGswap.integral_prod_right'
  refine hfinal.congr (Filter.Eventually.of_forall fun s => ?_)
  simp only [Prod.swap_prod_mk]
  have hpt : ∀ x : Vec m,
      (Metric.closedBall (0 : Vec m) Rb ×ˢ (univ : Set ℝ)).indicator
        (fun p : Vec m × ℝ =>
          diPernaLionsCommutator m ε (fun y => B (y, p.2)) (fun y => divB (y, p.2))
            (fun y => q (y, p.2)) p.1 ^ 2) (x, s)
      = (Metric.closedBall (0 : Vec m) Rb).indicator
        (fun x => diPernaLionsCommutator m ε (fun y => B (y, s)) (fun y => divB (y, s))
            (fun y => q (y, s)) x ^ 2) x := by
    intro x
    by_cases hx : x ∈ Metric.closedBall (0 : Vec m) Rb
    · rw [Set.indicator_of_mem (Set.mem_prod.mpr ⟨hx, mem_univ s⟩), Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem (fun hmem => hx (Set.mem_prod.mp hmem).1),
        Set.indicator_of_notMem hx]
  simp only [hpt]
  rw [integral_indicator measurableSet_closedBall]
  rfl

/-! ### The integrated vanishing of the commutator as `ε ↓ 0` -/

/-- Step 5b's remaining analytic core: for an admissible drift and a locally bounded transported
function on a common domain `I ⊇ [τ₀, τ₊]`, the commutator's squared `L²` mass, time-integrated
over `(τ₀, τ₊]`, vanishes as `ε ↓ 0`. This combines the joint measurability just proved with the
per-slice `ε → 0` vanishing `tendsto_diPernaLionsCommutator_sq_integral` and the per-slice `L²`
domination `integral_sq_diPernaLionsCommutator_le` via dominated convergence along the
countably-generated filter `𝓝[>] 0`
(`MeasureTheory.tendsto_integral_filter_of_dominated_convergence`). -/
theorem tendsto_integral_commutatorL2Sq {I : Set ℝ} {Rb τ₀ tplus : ℝ} (hτ : τ₀ ≤ tplus)
    {B : Vec m × ℝ → Vec m} {divB q : Vec m × ℝ → ℝ} (hB : IsAdmissibleDrift m I B divB)
    (hq : IsLocallyBoundedOn m I q) (hsub : Icc τ₀ tplus ⊆ I) :
    Tendsto (fun ε : ℝ => ∫ s in τ₀..tplus, commutatorL2Sq m ε Rb B divB q s) (𝓝[>] 0) (𝓝 0) := by
  have hJ : IsCompact (Icc τ₀ tplus) := isCompact_Icc
  obtain ⟨Λ, hΛae⟩ := isAdmissibleDrift_ae_slice_full hB hJ hsub
  obtain ⟨M, hMnn, hMae⟩ := IsLocallyBoundedOn.ae_slice_bound hq hJ hsub
  have hIocIcc : Ioc τ₀ tplus ⊆ Icc τ₀ tplus := Ioc_subset_Icc_self
  have hIocI : Ioc τ₀ tplus ⊆ I := hIocIcc.trans hsub
  have hμmono : (volume.restrict (Ioc τ₀ tplus) : Measure ℝ) ≤ volume.restrict (Icc τ₀ tplus) :=
    Measure.restrict_mono hIocIcc le_rfl
  have hΛae' : ∀ᵐ τ ∂(volume.restrict (Ioc τ₀ tplus)),
      (∀ x, ‖B (x, τ)‖ ≤ Λ) ∧ LipschitzWith Λ (fun x => B (x, τ)) ∧ (∀ x, |divB (x, τ)| ≤ Λ) ∧
        ∀ ψ : Vec m → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
          ∫ x, divB (x, τ) * ψ x = -∫ x, ∑ i, B (x, τ) i * fderiv ℝ ψ x (basisVec i) :=
    hΛae.filter_mono (ae_mono hμmono)
  have hMae' : ∀ᵐ τ ∂(volume.restrict (Ioc τ₀ tplus)), ∀ᵐ x : Vec m, |q (x, τ)| ≤ M :=
    hMae.filter_mono (ae_mono hμmono)
  have hqSliceAe : ∀ᵐ τ ∂(volume.restrict I), AEStronglyMeasurable (fun x => q (x, τ)) volume :=
    IsLocallyBoundedOn.ae_slice_measurable hq
  have hqSliceAe' : ∀ᵐ τ ∂(volume.restrict (Ioc τ₀ tplus)),
      AEStronglyMeasurable (fun x => q (x, τ)) volume :=
    hqSliceAe.filter_mono (ae_mono (Measure.restrict_mono hIocI le_rfl))
  have hqmeasI : AEStronglyMeasurable q (volume.restrict (univ ×ˢ Ioc τ₀ tplus)) :=
    hq.1.mono_measure (Measure.restrict_mono (Set.prod_mono le_rfl hIocI) le_rfl)
  -- the per-slice, uniform-in-`ε ∈ (0, 1)` domination bound on `commutatorL2Sq`
  have hCommBound : ∀ᵐ τ ∂(volume.restrict (Ioc τ₀ tplus)), ∀ ε : ℝ, 0 < ε → ε < 1 →
      commutatorL2Sq m ε Rb B divB q τ
        ≤ ((Λ : ℝ) * (mollifierGradConst m + 1)) ^ 2 *
            (M ^ 2 * volume.real (Metric.closedBall (0 : Vec m) (Rb + 1))) := by
    filter_upwards [hΛae', hMae', hqSliceAe'] with τ hΛτ hMτ hqτmeas ε hεpos hεlt1
    obtain ⟨q', hq'bound, hq'meas, hqq'⟩ := exists_stronglyMeasurable_bound hMnn hMτ hqτmeas
    have hdivbm : AEStronglyMeasurable (fun y => divB (y, τ)) volume :=
      (hB.2.1.comp measurable_prodMk_right).aestronglyMeasurable
    have hcongr : commutatorL2Sq m ε Rb B divB q τ
        = ∫ x in Metric.closedBall (0 : Vec m) Rb,
            diPernaLionsCommutator m ε (fun y => B (y, τ)) (fun y => divB (y, τ)) q' x ^ 2 := by
      refine setIntegral_congr_fun measurableSet_closedBall (fun x _ => ?_)
      exact congrArg (· ^ 2) (diPernaLionsCommutator_congr_ae hqq' x)
    rw [hcongr]
    have hle := integral_sq_diPernaLionsCommutator_le (ε := ε) (R := Rb) (M := M) hεpos hMnn
      hΛτ.2.1 hΛτ.2.2.1 hdivbm hq'bound hq'meas
    refine hle.trans ?_
    have hq'sqle : ∀ y : Vec m, q' y ^ 2 ≤ M ^ 2 := fun y => by
      obtain ⟨l1, l2⟩ := abs_le.mp (hq'bound y); exact sq_le_sq' l1 l2
    have hballsub : Metric.closedBall (0 : Vec m) (Rb + ε) ⊆ Metric.closedBall (0 : Vec m) (Rb +
      1) :=
      Metric.closedBall_subset_closedBall (by linarith only [hεlt1])
    have hstep1 : (∫ y in Metric.closedBall (0 : Vec m) (Rb + ε), q' y ^ 2)
        ≤ M ^ 2 * volume.real (Metric.closedBall (0 : Vec m) (Rb + ε)) := by
      have hconstInt : IntegrableOn (fun _ : Vec m => M ^ 2)
          (Metric.closedBall (0 : Vec m) (Rb + ε)) volume :=
        integrableOn_const (isCompact_closedBall (0 : Vec m) (Rb + ε)).measure_ne_top
          (by simp)
      have hq'sqInt : IntegrableOn (fun y => q' y ^ 2)
          (Metric.closedBall (0 : Vec m) (Rb + ε)) volume := by
        refine hconstInt.mono' ((hq'meas.mono_measure Measure.restrict_le_self).pow 2)
          (Filter.Eventually.of_forall fun y => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact hq'sqle y
      calc (∫ y in Metric.closedBall (0 : Vec m) (Rb + ε), q' y ^ 2)
          ≤ ∫ _y in Metric.closedBall (0 : Vec m) (Rb + ε), M ^ 2 :=
            setIntegral_mono_on hq'sqInt hconstInt measurableSet_closedBall (fun y _ => hq'sqle y)
        _ = M ^ 2 * volume.real (Metric.closedBall (0 : Vec m) (Rb + ε)) := by
            rw [setIntegral_const, smul_eq_mul, mul_comm]
    have hstep2 : M ^ 2 * volume.real (Metric.closedBall (0 : Vec m) (Rb + ε))
        ≤ M ^ 2 * volume.real (Metric.closedBall (0 : Vec m) (Rb + 1)) :=
      mul_le_mul_of_nonneg_left
        (measureReal_mono hballsub (isCompact_closedBall (0 : Vec m) (Rb + 1)).measure_ne_top)
        (sq_nonneg _)
    have hC1nn : (0 : ℝ) ≤ ((Λ : ℝ) * (mollifierGradConst m + 1)) ^ 2 := sq_nonneg _
    calc ((Λ : ℝ) * (mollifierGradConst m + 1)) ^ 2 *
          (∫ y in Metric.closedBall (0 : Vec m) (Rb + ε), q' y ^ 2)
        ≤ ((Λ : ℝ) * (mollifierGradConst m + 1)) ^ 2 *
            (M ^ 2 * volume.real (Metric.closedBall (0 : Vec m) (Rb + ε))) :=
          mul_le_mul_of_nonneg_left hstep1 hC1nn
      _ ≤ ((Λ : ℝ) * (mollifierGradConst m + 1)) ^ 2 *
            (M ^ 2 * volume.real (Metric.closedBall (0 : Vec m) (Rb + 1))) :=
          mul_le_mul_of_nonneg_left hstep2 hC1nn
  -- the per-slice `ε → 0` vanishing of `commutatorL2Sq`
  have hLim : ∀ᵐ τ ∂(volume.restrict (Ioc τ₀ tplus)),
      Tendsto (fun ε => commutatorL2Sq m ε Rb B divB q τ) (𝓝[>] 0) (𝓝 (0 : ℝ)) := by
    filter_upwards [hΛae', hMae', hqSliceAe'] with τ hΛτ hMτ hqτmeas
    have hdivbm : AEStronglyMeasurable (fun y => divB (y, τ)) volume :=
      (hB.2.1.comp measurable_prodMk_right).aestronglyMeasurable
    exact tendsto_diPernaLionsCommutator_sq_integral hΛτ.2.1 hΛτ.2.2.1 hdivbm hΛτ.2.2.2 hMτ hqτmeas
  have hFin : IsFiniteMeasure (volume.restrict (Ioc τ₀ tplus)) :=
    isFiniteMeasure_restrict.2 (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have hF_meas : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      AEStronglyMeasurable (fun s => commutatorL2Sq m ε Rb B divB q s)
        (volume.restrict (Ioc τ₀ tplus)) :=
    Filter.Eventually.of_forall fun ε => aestronglyMeasurable_commutatorL2Sq hB.1 hB.2.1 hqmeasI
  have h_bound : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ∀ᵐ τ ∂(volume.restrict (Ioc τ₀ tplus)),
      ‖commutatorL2Sq m ε Rb B divB q τ‖
        ≤ ((Λ : ℝ) * (mollifierGradConst m + 1)) ^ 2 *
            (M ^ 2 * volume.real (Metric.closedBall (0 : Vec m) (Rb + 1))) := by
    filter_upwards [Ioo_mem_nhdsGT (one_pos : (0 : ℝ) < 1)] with ε hεmem
    obtain ⟨hεpos, hεlt1⟩ := hεmem
    filter_upwards [hCommBound] with τ hτbound
    have hnn : 0 ≤ commutatorL2Sq m ε Rb B divB q τ := integral_nonneg fun _ => sq_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    exact hτbound ε hεpos hεlt1
  have hres := tendsto_integral_filter_of_dominated_convergence
    (fun _ : ℝ => ((Λ : ℝ) * (mollifierGradConst m + 1)) ^ 2 *
      (M ^ 2 * volume.real (Metric.closedBall (0 : Vec m) (Rb + 1))))
    hF_meas h_bound (integrable_const _) hLim
  rw [integral_zero] at hres
  have heq : (fun ε : ℝ => ∫ s in τ₀..tplus, commutatorL2Sq m ε Rb B divB q s)
      = fun ε => ∫ s in Ioc τ₀ tplus, commutatorL2Sq m ε Rb B divB q s := by
    funext ε
    exact intervalIntegral.integral_of_le hτ
  rw [heq]
  exact hres

end CIV
