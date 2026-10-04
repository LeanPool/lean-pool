/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

-- Adapted for Lean Pool's pinned Lean and Mathlib; upstream commit is recorded in projects.yml.
module

public import Mathlib.Analysis.Convolution
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Group.LIntegral
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Normed.Lp.SmoothApprox
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Function.LocallyIntegrable


/-!
# Young's `Lᵖ` inequality for a probability kernel

This file collects the reusable convolution machinery feeding the weak-gradient Morrey
embedding. The headline result `eLpNorm_convolution_le` is a specialised Young inequality:
convolving an `Lᵖ` function against a non-negative kernel of unit mass does not increase its
`Lᵖ` seminorm. The classical proof uses the (currently absent) Minkowski integral inequality;
we instead derive the pointwise bound directly from Hölder's inequality in `ℝ≥0∞` and close
with Tonelli, so no Minkowski inequality is required.

The mollifier kernel `φ.normed volume` is the intended instance (non-negative by
`ContDiffBump.nonneg_normed`, unit mass by `ContDiffBump.integral_normed`), and the restricted
corollary `eLpNorm_convolution_restrict_le` is the form consumed downstream.

The second result `tendsto_eLpNorm_convolution_sub` records the `Lᵖ` convergence of the
mollifications `h ⋆ ρ_ε` to `h` as the bump radii shrink. It is proved by a density `3ε`
argument: approximate `h` in `Lᵖ` by a smooth compactly supported `w`
(`MeasureTheory.MemLp.exist_eLpNorm_sub_le`), control the tail `(h - w) ⋆ ρ_ε` by the Young
bound above, and drive the middle term `w ⋆ ρ_ε - w` to zero using the uniform convergence
supplied by `ContDiffBump.dist_normed_convolution_le` on the fixed compact support. No
`Lᵖ`-continuity of translation is required, and the argument is valid along an arbitrary filter.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped NNReal ENNReal Convolution Topology Pointwise

noncomputable section

namespace EllipticPdes.Embedding

variable {d : ℕ}

/-- **Young's `Lᵖ` inequality for a probability kernel.** For `1 ≤ p`, a non-negative kernel
`ρ` with unit mass `∫ ρ = 1`, and `h ∈ Lᵖ`, the convolution against `ρ` does not increase the
`Lᵖ` seminorm: `‖h ⋆ ρ‖_{Lᵖ} ≤ ‖h‖_{Lᵖ}`. Proved by the pointwise Hölder bound
`|(h ⋆ ρ)(x)|^p ≤ ∫ |h(t)|^p ρ(x - t)` together with Tonelli and unit mass; no Minkowski
integral inequality is required. -/
theorem eLpNorm_convolution_le
    {p : ℝ} (hp : 1 ≤ p) {ρ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hρ0 : 0 ≤ ρ) (hρm : AEStronglyMeasurable ρ volume) (hρ1 : ∫ y, ρ y ∂volume = 1)
    {h : EuclideanSpace ℝ (Fin d) → ℝ} (hh : MemLp h (ENNReal.ofReal p) volume) :
    eLpNorm (h ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ) (ENNReal.ofReal p) volume
      ≤ eLpNorm h (ENNReal.ofReal p) volume := by
  have hp0 : 0 < p := lt_of_lt_of_le one_pos hp
  have hP0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp0).ne'
  have hPtop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hPreal : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp0.le
  -- basic measurability of the enorms
  have hhen : AEMeasurable (fun z => ‖h z‖ₑ) volume := hh.aestronglyMeasurable.enorm
  have hρen : AEMeasurable (fun z => ‖ρ z‖ₑ) volume := hρm.enorm
  -- the kernel is integrable, with unit `ℝ≥0∞`-mass
  have hρint : Integrable ρ volume := by
    by_contra hcon
    rw [integral_undef hcon] at hρ1
    exact one_ne_zero hρ1.symm
  have hmass : ∫⁻ z, ‖ρ z‖ₑ ∂volume = 1 := by
    have h1 : ∫⁻ z, ‖ρ z‖ₑ ∂volume = ∫⁻ z, ENNReal.ofReal (ρ z) ∂volume :=
      lintegral_congr fun z => Real.enorm_of_nonneg (hρ0 z)
    rw [h1, ← ofReal_integral_eq_lintegral_ofReal hρint (ae_of_all _ fun z => hρ0 z), hρ1,
      ENNReal.ofReal_one]
  -- measurability of the uncurried Tonelli integrand
  have hswapmeas : AEMeasurable
      (fun q : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
        ‖h q.2‖ₑ ^ p * ‖ρ (q.1 - q.2)‖ₑ) (volume.prod volume) :=
    ((hhen.pow_const p).comp_snd).mul
      (hρen.comp_quasiMeasurePreserving
        (quasiMeasurePreserving_sub_of_right_invariant volume volume))
  -- pointwise Hölder bound: `|(h ⋆ ρ)(x)|^p ≤ ∫ |h(t)|^p ρ(x - t)`
  have key : ∀ x, ‖(h ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ) x‖ₑ ^ p
      ≤ ∫⁻ t, ‖h t‖ₑ ^ p * ‖ρ (x - t)‖ₑ ∂volume := by
    intro x
    have hρxen : AEMeasurable (fun t => ‖ρ (x - t)‖ₑ) volume :=
      hρen.comp_quasiMeasurePreserving
        (Measure.measurePreserving_sub_left volume x).quasiMeasurePreserving
    have hwmass : ∫⁻ t, ‖ρ (x - t)‖ₑ ∂volume = 1 :=
      (lintegral_sub_left_eq_self (fun z => ‖ρ z‖ₑ) x).trans hmass
    have hbound : ‖(h ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ) x‖ₑ
        ≤ ∫⁻ t, ‖h t‖ₑ * ‖ρ (x - t)‖ₑ ∂volume := by
      rw [convolution_def]
      refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
      refine lintegral_congr fun t => ?_
      rw [ContinuousLinearMap.lsmul_apply, smul_eq_mul, enorm_mul]
    refine le_trans (ENNReal.rpow_le_rpow hbound hp0.le) ?_
    rcases eq_or_lt_of_le hp with hp1 | hp1
    · rw [← hp1, ENNReal.rpow_one]
      exact le_of_eq (lintegral_congr fun t => by rw [ENNReal.rpow_one])
    · have hpq : p.HolderConjugate (Real.conjExponent p) := Real.HolderConjugate.conjExponent hp1
      set q := Real.conjExponent p with hq_def
      have hq_pos : 0 < q := hpq.symm.pos
      have hsum : 1 / p + 1 / q = 1 := by simpa using hpq.one_div_add_one_div
      have e1 : ∀ t, ‖h t‖ₑ * ‖ρ (x - t)‖ₑ ^ (1 / p) * ‖ρ (x - t)‖ₑ ^ (1 / q)
          = ‖h t‖ₑ * ‖ρ (x - t)‖ₑ := by
        intro t
        rw [mul_assoc,
          ← ENNReal.rpow_add_of_nonneg _ _ hpq.one_div_nonneg hpq.symm.one_div_nonneg, hsum,
          ENNReal.rpow_one]
      have e2 : ∀ t, (‖h t‖ₑ * ‖ρ (x - t)‖ₑ ^ (1 / p)) ^ p
          = ‖h t‖ₑ ^ p * ‖ρ (x - t)‖ₑ := by
        intro t
        rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul, one_div,
          inv_mul_cancel₀ hp0.ne', ENNReal.rpow_one]
      have e3 : ∀ t, (‖ρ (x - t)‖ₑ ^ (1 / q)) ^ q = ‖ρ (x - t)‖ₑ := by
        intro t
        rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hq_pos.ne', ENNReal.rpow_one]
      have hol : ∫⁻ t, ‖h t‖ₑ * ‖ρ (x - t)‖ₑ ∂volume
          ≤ (∫⁻ t, ‖h t‖ₑ ^ p * ‖ρ (x - t)‖ₑ ∂volume) ^ (1 / p) := by
        have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq volume hpq
          (hhen.mul (hρxen.pow_const (1 / p))) (hρxen.pow_const (1 / q))
        simp only [Pi.mul_apply] at hH
        rwa [lintegral_congr e1, lintegral_congr e2, lintegral_congr e3, hwmass, ENNReal.one_rpow,
          mul_one] at hH
      calc (∫⁻ t, ‖h t‖ₑ * ‖ρ (x - t)‖ₑ ∂volume) ^ p
          ≤ ((∫⁻ t, ‖h t‖ₑ ^ p * ‖ρ (x - t)‖ₑ ∂volume) ^ (1 / p)) ^ p :=
            ENNReal.rpow_le_rpow hol hp0.le
        _ = ∫⁻ t, ‖h t‖ₑ ^ p * ‖ρ (x - t)‖ₑ ∂volume := by
            rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp0.ne', ENNReal.rpow_one]
  -- reduce the seminorm inequality to the `lintegral` inequality
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hP0 hPtop
      (hh.aestronglyMeasurable.convolution (ContinuousLinearMap.lsmul ℝ ℝ) hρm),
    eLpNorm_eq_lintegral_rpow_enorm_toReal hP0 hPtop hh.aestronglyMeasurable, hPreal]
  refine ENNReal.rpow_le_rpow ?_ (one_div_nonneg.mpr hp0.le)
  calc ∫⁻ x, ‖(h ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ) x‖ₑ ^ p ∂volume
      ≤ ∫⁻ x, ∫⁻ t, ‖h t‖ₑ ^ p * ‖ρ (x - t)‖ₑ ∂volume ∂volume := lintegral_mono key
    _ = ∫⁻ t, ∫⁻ x, ‖h t‖ₑ ^ p * ‖ρ (x - t)‖ₑ ∂volume ∂volume :=
        lintegral_lintegral_swap hswapmeas
    _ = ∫⁻ t, ‖h t‖ₑ ^ p * ∫⁻ x, ‖ρ (x - t)‖ₑ ∂volume ∂volume := by
        refine lintegral_congr fun t => ?_
        have hmt : AEMeasurable (fun x => ‖ρ (x - t)‖ₑ) volume :=
          hρen.comp_quasiMeasurePreserving
            (measurePreserving_sub_right volume t).quasiMeasurePreserving
        exact lintegral_const_mul'' (‖h t‖ₑ ^ p) hmt
    _ = ∫⁻ t, ‖h t‖ₑ ^ p * 1 ∂volume := by
        refine lintegral_congr fun t => ?_
        rw [lintegral_sub_right_eq_self (fun z => ‖ρ z‖ₑ) t, hmass]
    _ = ∫⁻ x, ‖h x‖ₑ ^ p ∂volume := by simp

/-- Young bound restricted to a set `s` on the left, upper-bounded by the full `Lᵖ` norm. -/
theorem eLpNorm_convolution_restrict_le {p : ℝ} (hp : 1 ≤ p)
    {ρ : EuclideanSpace ℝ (Fin d) → ℝ} (hρ0 : 0 ≤ ρ) (hρm : AEStronglyMeasurable ρ volume)
    (hρ1 : ∫ y, ρ y ∂volume = 1) {h : EuclideanSpace ℝ (Fin d) → ℝ}
    (hh : MemLp h (ENNReal.ofReal p) volume) (s : Set (EuclideanSpace ℝ (Fin d))) :
    eLpNorm (h ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ) (ENNReal.ofReal p)
        (volume.restrict s)
      ≤ eLpNorm h (ENNReal.ofReal p) volume :=
  le_trans (eLpNorm_mono_measure _ Measure.restrict_le_self)
    (eLpNorm_convolution_le hp hρ0 hρm hρ1 hh)

/-- **Middle `3ε` term.** For a continuous compactly supported `w`, the mollifications
`w ⋆ ρ_ε` converge to `w` in `Lᵖ` as the outer bump radii shrink. The convolutions are
uniformly close to `w` on the fixed compact `closedBall 0 1 + tsupport w` (uniform continuity
of `w` plus `ContDiffBump.dist_normed_convolution_le`), and the `Lᵖ` seminorm of a uniformly
small function on a fixed finite-measure set is small. This needs only `rOut → 0`, not the
inner/outer ratio bound. -/
private theorem tendsto_eLpNorm_bump_convolution_sub {p : ℝ} (hp : 1 ≤ p)
    {w : EuclideanSpace ℝ (Fin d) → ℝ} (hwc : Continuous w) (hwcs : HasCompactSupport w)
    {ι : Type*} {l : Filter ι} {φ : ι → ContDiffBump (0 : EuclideanSpace ℝ (Fin d))}
    (hφ : Filter.Tendsto (fun i => (φ i).rOut) l (𝓝 0)) :
    Filter.Tendsto
      (fun i => eLpNorm
          (w ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ((φ i).normed volume) - w)
          (ENNReal.ofReal p) volume) l (𝓝 0) := by
  have hp0 : 0 < p := lt_of_lt_of_le one_pos hp
  -- the scalar convolution operator is symmetric
  have hflip : (ContinuousLinearMap.lsmul ℝ ℝ).flip = ContinuousLinearMap.lsmul ℝ ℝ := by
    refine ContinuousLinearMap.ext fun a => ContinuousLinearMap.ext fun b => ?_
    simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
    exact mul_comm b a
  have hunif : UniformContinuous w := hwcs.uniformContinuous_of_continuous hwc
  -- the fixed compact set that contains every `w ⋆ ρ_i - w`
  set S1 := Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 + tsupport w with hS1def
  have hS1cpt : IsCompact S1 := (isCompact_closedBall _ _).add hwcs
  have hS1fin : volume S1 ≠ ∞ := hS1cpt.measure_lt_top.ne
  have hAtop : volume S1 ^ p⁻¹ ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by positivity) hS1fin
  have htsuppS1 : tsupport w ⊆ S1 := by
    intro y hy
    rw [hS1def]
    have h0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 :=
      Metric.mem_closedBall_self zero_le_one
    simpa using Set.add_mem_add h0 hy
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  rcases eq_or_ne η ∞ with rfl | hηtop
  · exact Filter.Eventually.of_forall fun _ => le_top
  -- choose the sup tolerance `ε`
  have hA1top : volume S1 ^ p⁻¹ + 1 ≠ ∞ := by simp [hAtop]
  have hA1pos : volume S1 ^ p⁻¹ + 1 ≠ 0 := by positivity
  set ε := (η / (volume S1 ^ p⁻¹ + 1)).toReal with hεdef
  have hε0 : 0 < ε := by
    rw [hεdef]
    exact ENNReal.toReal_pos (ENNReal.div_pos hη.ne' hA1top).ne'
      (ENNReal.div_ne_top hηtop hA1pos)
  have hofε : ENNReal.ofReal ε = η / (volume S1 ^ p⁻¹ + 1) := by
    rw [hεdef, ENNReal.ofReal_toReal (ENNReal.div_ne_top hηtop hA1pos)]
  have hAε : volume S1 ^ p⁻¹ * ENNReal.ofReal ε ≤ η := by
    rw [hofε]
    calc volume S1 ^ p⁻¹ * (η / (volume S1 ^ p⁻¹ + 1))
        ≤ (volume S1 ^ p⁻¹ + 1) * (η / (volume S1 ^ p⁻¹ + 1)) := by gcongr; exact le_self_add
      _ ≤ η := ENNReal.mul_div_le
  obtain ⟨δ, hδ0, hδ⟩ := Metric.uniformContinuous_iff.mp hunif ε hε0
  filter_upwards [Metric.tendsto_nhds.mp hφ δ hδ0, Metric.tendsto_nhds.mp hφ 1 one_pos]
    with i hiδ hi1
  have hrδ : (φ i).rOut < δ := by
    rwa [Real.dist_0_eq_abs, abs_of_pos (φ i).rOut_pos] at hiδ
  have hr1 : (φ i).rOut < 1 := by
    rwa [Real.dist_0_eq_abs, abs_of_pos (φ i).rOut_pos] at hi1
  -- swap the convolution so the bump is on the left
  have hcomm : w ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ((φ i).normed volume)
      = ((φ i).normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] w := by
    rw [← convolution_flip, hflip]
  -- uniform closeness on the whole space
  have hpt : ∀ x₀, dist ((((φ i).normed volume)
      ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] w) x₀) (w x₀) ≤ ε := by
    intro x₀
    refine (φ i).dist_normed_convolution_le hwc.aestronglyMeasurable ?_
    intro x hx
    rw [mem_ball] at hx
    exact (hδ (lt_trans hx hrδ)).le
  -- support of the difference lies in the fixed compact `S1`
  have hsuppconv : Function.support (((φ i).normed volume)
      ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] w) ⊆ S1 := by
    refine (support_convolution_subset _).trans ?_
    rw [hS1def]
    refine Set.add_subset_add ?_ (subset_tsupport w)
    rw [(φ i).support_normed_eq]
    exact Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall hr1.le)
  have hsupp : Function.support ((((φ i).normed volume)
      ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] w) - w) ⊆ S1 := by
    intro x hx
    by_contra hxS1
    refine Function.mem_support.mp hx ?_
    have hwx : w x = 0 := image_eq_zero_of_notMem_tsupport fun hxt => hxS1 (htsuppS1 hxt)
    have hcx : (((φ i).normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] w) x = 0 :=
      Function.notMem_support.mp fun hxs => hxS1 (hsuppconv hxs)
    rw [Pi.sub_apply, hwx, hcx, sub_zero]
  -- assemble the `Lᵖ` bound
  rw [hcomm]
  calc eLpNorm ((((φ i).normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] w) - w)
        (ENNReal.ofReal p) volume
      = eLpNorm ((((φ i).normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] w) - w)
          (ENNReal.ofReal p) (volume.restrict S1) :=
        (eLpNorm_restrict_eq_of_support_subset
          ((((φ i).continuous_normed).aestronglyMeasurable.convolution
            (ContinuousLinearMap.lsmul ℝ ℝ) hwc.aestronglyMeasurable).sub
            hwc.aestronglyMeasurable)
          hsupp).symm
    _ ≤ (volume.restrict S1) Set.univ ^ ((ENNReal.ofReal p).toReal⁻¹) * ENNReal.ofReal ε :=
        eLpNorm_le_of_ae_bound
          ((((φ i).continuous_normed).aestronglyMeasurable.convolution
            (ContinuousLinearMap.lsmul ℝ ℝ) hwc.aestronglyMeasurable).sub
            hwc.aestronglyMeasurable).restrict
          (Filter.Eventually.of_forall fun x => by
          rw [Pi.sub_apply, ← dist_eq_norm]; exact hpt x)
    _ = volume S1 ^ p⁻¹ * ENNReal.ofReal ε := by
        rw [Measure.restrict_apply_univ, ENNReal.toReal_ofReal hp0.le]
    _ ≤ η := hAε

/-- **`Lᵖ` convergence of mollifications.** For `1 ≤ p`, an `Lᵖ` function `h`, and a family of
normalised bumps whose outer radii tend to `0` (with a bounded inner/outer ratio), the
mollifications `h ⋆ ρ_ε` converge to `h` in `Lᵖ`. Proved by a density `3ε` argument: approximate
`h` in `Lᵖ` by a smooth compactly supported `w` (`MeasureTheory.MemLp.exist_eLpNorm_sub_le`),
bound the tail `(h - w) ⋆ ρ_ε` by `eLpNorm_convolution_le`, and send `w ⋆ ρ_ε - w` to zero with
`tendsto_eLpNorm_bump_convolution_sub`. No `Lᵖ`-continuity of translation is used. -/
theorem tendsto_eLpNorm_convolution_sub {p : ℝ} (hp : 1 ≤ p)
    {h : EuclideanSpace ℝ (Fin d) → ℝ} (hh : MemLp h (ENNReal.ofReal p) volume)
    {ι : Type*} {l : Filter ι} {φ : ι → ContDiffBump (0 : EuclideanSpace ℝ (Fin d))} {K : ℝ}
    (hφ : Filter.Tendsto (fun i => (φ i).rOut) l (𝓝 0))
    (_hK : ∀ᶠ i in l, (φ i).rOut ≤ K * (φ i).rIn) :
    Filter.Tendsto
      (fun i => eLpNorm
          (h ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ((φ i).normed volume) - h)
          (ENNReal.ofReal p) volume) l (𝓝 0) := by
  have hp0 : 0 < p := lt_of_lt_of_le one_pos hp
  have hq1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp
  have hqtop : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  rcases eq_or_ne η ∞ with rfl | hηtop
  · exact Filter.Eventually.of_forall fun _ => le_top
  -- density: pick a smooth compactly supported `w` within `δ = η/3` of `h`
  set δ : ℝ := η.toReal / 3 with hδdef
  have hηpos : 0 < η.toReal := ENNReal.toReal_pos hη.ne' hηtop
  have hδ0 : 0 < δ := by positivity
  obtain ⟨w, hwcs, hwsmooth, hwle⟩ := hh.exist_eLpNorm_sub_le hqtop hq1 hδ0
  have hwc : Continuous w := hwsmooth.continuous
  have hwml : MemLp w (ENNReal.ofReal p) volume := hwc.memLp_of_hasCompactSupport hwcs
  have hlocw : LocallyIntegrable w volume := hwml.locallyIntegrable hq1
  have hlochw : LocallyIntegrable (h - w) volume := (hh.sub hwml).locallyIntegrable hq1
  -- third term of the triangle inequality is `≤ δ`
  have ha3 : eLpNorm (w - h) (ENNReal.ofReal p) volume ≤ ENNReal.ofReal δ := by
    rw [eLpNorm_sub_comm]; exact hwle
  -- middle term tends to zero, hence is eventually `≤ δ`
  have hmid := tendsto_eLpNorm_bump_convolution_sub hp hwc hwcs hφ
  have hmid_ev : ∀ᶠ i in l,
      eLpNorm (w ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ((φ i).normed volume) - w)
        (ENNReal.ofReal p) volume ≤ ENNReal.ofReal δ :=
    ENNReal.tendsto_nhds_zero.mp hmid (ENNReal.ofReal δ) (ENNReal.ofReal_pos.mpr hδ0)
  filter_upwards [hmid_ev] with i hi
  -- abbreviations for the fixed bump `ρ`
  have hρnn : (0 : EuclideanSpace ℝ (Fin d) → ℝ) ≤ (φ i).normed volume :=
    fun x => (φ i).nonneg_normed x
  have hρcont : Continuous ((φ i).normed volume) := ((φ i).contDiff_normed (n := 1)).continuous
  have hρm : AEStronglyMeasurable ((φ i).normed volume) volume := hρcont.aestronglyMeasurable
  have hρ1 : ∫ y, (φ i).normed volume y ∂volume = 1 := (φ i).integral_normed
  have hρcs : HasCompactSupport ((φ i).normed volume) := (φ i).hasCompactSupport_normed
  -- first term `≤ δ` by the Young bound applied to `h - w`
  have ha1 : eLpNorm ((h - w) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ((φ i).normed volume))
      (ENNReal.ofReal p) volume ≤ ENNReal.ofReal δ :=
    le_trans (eLpNorm_convolution_le hp hρnn hρm hρ1 (hh.sub hwml)) hwle
  -- left linearity of the convolution
  have hCE1 : ConvolutionExists (h - w) ((φ i).normed volume) (ContinuousLinearMap.lsmul ℝ ℝ)
      volume :=
    HasCompactSupport.convolutionExists_right (L := ContinuousLinearMap.lsmul ℝ ℝ) hρcs hlochw
      hρcont
  have hCE2 : ConvolutionExists w ((φ i).normed volume) (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
    HasCompactSupport.convolutionExists_right (L := ContinuousLinearMap.lsmul ℝ ℝ) hρcs hlocw
      hρcont
  have key_add : h ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ((φ i).normed volume)
      = (h - w) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ((φ i).normed volume)
        + w ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ((φ i).normed volume) := by
    have hd := ConvolutionExists.add_distrib hCE1 hCE2
    rwa [show (h - w) + w = h from by funext x; simp] at hd
  -- rewrite the target function as a sum of the three `3ε` pieces
  have hfun : h ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ((φ i).normed volume) - h
      = (h - w) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ((φ i).normed volume)
        + ((w ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ((φ i).normed volume) - w) + (w - h)) := by
    funext x
    have hpt := congrFun key_add x
    simp only [Pi.sub_apply, Pi.add_apply] at hpt ⊢
    rw [hpt]; ring
  -- measurability of each piece
  have ha1m : AEStronglyMeasurable ((h - w)
      ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ((φ i).normed volume)) volume :=
    (HasCompactSupport.continuous_convolution_right (L := ContinuousLinearMap.lsmul ℝ ℝ)
      hρcs hlochw hρcont).aestronglyMeasurable
  have hwconvm : AEStronglyMeasurable (w
      ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ((φ i).normed volume)) volume :=
    (HasCompactSupport.continuous_convolution_right (L := ContinuousLinearMap.lsmul ℝ ℝ)
      hρcs hlocw hρcont).aestronglyMeasurable
  have ha2m : AEStronglyMeasurable (w
      ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ((φ i).normed volume) - w) volume :=
    hwconvm.sub hwc.aestronglyMeasurable
  have ha3m : AEStronglyMeasurable (w - h) volume :=
    hwc.aestronglyMeasurable.sub hh.aestronglyMeasurable
  rw [hfun]
  calc eLpNorm ((h - w) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ((φ i).normed volume)
        + ((w ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ((φ i).normed volume) - w) + (w - h)))
        (ENNReal.ofReal p) volume
      ≤ eLpNorm ((h - w) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ((φ i).normed volume))
          (ENNReal.ofReal p) volume
        + eLpNorm ((w ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ((φ i).normed volume) - w)
            + (w - h)) (ENNReal.ofReal p) volume :=
        eLpNorm_add_le hq1
    _ ≤ eLpNorm ((h - w) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ((φ i).normed volume))
          (ENNReal.ofReal p) volume
        + (eLpNorm (w ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ((φ i).normed volume) - w)
            (ENNReal.ofReal p) volume + eLpNorm (w - h) (ENNReal.ofReal p) volume) := by
        gcongr
        exact eLpNorm_add_le hq1
    _ ≤ ENNReal.ofReal δ + (ENNReal.ofReal δ + ENNReal.ofReal δ) := by
        gcongr
    _ = η := by
        rw [← ENNReal.ofReal_add hδ0.le (by positivity),
          ← ENNReal.ofReal_add hδ0.le (by positivity : (0 : ℝ) ≤ δ + δ),
          show δ + (δ + δ) = η.toReal from by rw [hδdef]; ring, ENNReal.ofReal_toReal hηtop]

end EllipticPdes.Embedding
