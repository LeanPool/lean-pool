/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Field.UniformExhaustionProfile
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.C0AllShifts
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.FunctionalAnalysis.CompactSupportDenseCore

/-!
# WholeSpaceC0

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Vanishing at infinity for the stream-field whole-space resolvent

The localized split-skew estimate is used at a radius proportional to the
distance of the evaluation point from the origin.  Radius amplification still
leaves a fixed fraction of that distance between the evaluation ball and a
compactly supported datum, while the uniform stretched-exponential envelope
tends to zero.  Sharp resolvent stability then extends the conclusion from
compactly supported data to all continuous functions vanishing at infinity.
-/

namespace Algsuperdiff.Section5.Field

open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3
open CompactlySupported Filter HCPolySupport MeasureTheory Set Topology
open DivergenceFormProcess.Form MarkovProcess.Semigroup
open scoped ENNReal ZeroAtInfty

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
/-- The common stretched-exponential envelope tends to zero at infinity. -/
theorem tendsto_streamUniformExhaustionEnvelope_atTop
    (M : ABKModel d) (omega : FullSample d M.gamma) :
    Tendsto (streamUniformExhaustionEnvelope M omega) atTop (nhds 0) := by
  have hpow : Tendsto (fun s : ℝ ↦ s ^ (1 / 3 : ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  have hrate : 0 < streamUniformExhaustionRate M omega := by
    unfold streamUniformExhaustionRate
    exact div_pos (streamTailDecayConst_pos M omega) (by norm_num)
  have hscale : Tendsto (fun s : ℝ ↦
      streamUniformExhaustionRate M omega * s ^ (1 / 3 : ℝ)) atTop atTop :=
    hpow.const_mul_atTop hrate
  have hmain : Tendsto (fun s : ℝ ↦ streamTailAmplitudeConst M omega *
      Real.exp (-(streamUniformExhaustionRate M omega * s ^ (1 / 3 : ℝ))))
      atTop (nhds 0) := by
    simpa only [mul_zero] using!
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp hscale).const_mul
        (streamTailAmplitudeConst M omega)
  apply hmain.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
  unfold streamUniformExhaustionEnvelope
  rw [max_eq_left hs]

omit [NeZero d] in
private theorem abs_le_norm_streamC0 (f : C₀(Vec d, ℝ)) (x : Vec d) :
    |f x| ≤ ‖f‖ := by
  rw [← Real.norm_eq_abs, ← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  exact BoundedContinuousFunction.norm_coe_le_norm f.toBCF x

omit [NeZero d] in
private theorem exists_compactSupportCore_close_stream
    (f : C₀(Vec d, ℝ)) {eps : ℝ} (heps : 0 < eps) :
    ∃ g : DivergenceFormProcess.FunctionalAnalysis.CompactSupportCore (Vec d),
      ‖DivergenceFormProcess.FunctionalAnalysis.compactSupportCoreToC0 g - f‖ < eps := by
  have hdense :=
    DivergenceFormProcess.FunctionalAnalysis.denseRange_compactSupportCoreToC0
      (X := Vec d)
  change Dense (Set.range
    (DivergenceFormProcess.FunctionalAnalysis.compactSupportCoreToC0
      (X := Vec d))) at hdense
  rw [Metric.dense_iff] at hdense
  obtain ⟨_, hy, ⟨g, rfl⟩⟩ := hdense f eps heps
  rw [Metric.mem_ball, dist_eq_norm] at hy
  exact ⟨g, hy⟩

/-- The positive analytic minimal resolvent of a normalized compactly
supported datum vanishes at infinity for every shift at least one. -/
theorem zero_at_infty_toReal_streamAnalyticMinimalResolvent
    (M : ABKModel d) (omega : FullSample d M.gamma)
    (mu : PositiveShift) (hmu : 1 ≤ (mu : ℝ))
    {f : Vec d → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hf1 : ∀ x, |f x| ≤ 1) (hfcompact : HasCompactSupport f) :
    Tendsto (fun x ↦ ((streamWholeSpaceAnalyticData M omega).analyticMinimalResolvent
      mu f hf hf1 x).toReal) (cocompact (Vec d)) (nhds 0) := by
  let A := streamWholeSpaceAnalyticData M omega
  obtain ⟨R, hR⟩ := hfcompact.isCompact.isBounded.subset_closedBall (0 : Vec d)
  rw [Metric.tendsto_nhds]
  intro eps heps
  have htarget : 0 < (mu : ℝ) * eps := mul_pos mu.property heps
  have henv := tendsto_streamUniformExhaustionEnvelope_atTop M omega
  rw [Metric.tendsto_atTop] at henv
  obtain ⟨s₀, hs₀⟩ := henv ((mu : ℝ) * eps) htarget
  let cutoff := streamUniformExhaustionCutoff M omega (mu : ℝ)
  let T : ℝ := max (max (max (8 * R + 1) 4)
      (4 * cutoff / (3 * Real.sqrt (mu : ℝ)) + 1))
      (4 * s₀ / (3 * Real.sqrt (mu : ℝ)) + 1)
  have hsqrt : 0 < Real.sqrt (mu : ℝ) := Real.sqrt_pos.2 mu.property
  have hnormTop : Tendsto (fun x : Vec d ↦ ‖x‖)
      (cocompact (Vec d)) atTop := tendsto_norm_cocompact_atTop
  filter_upwards [hnormTop.eventually (eventually_gt_atTop T)] with x hx
  let r : ℝ := 3 / 4 * ‖x‖
  let ar := streamExhaustionAmp x r
  have hxR : 8 * R < ‖x‖ := by
    have := (le_max_left (8 * R + 1) 4).trans
      ((le_max_left _ (4 * cutoff / (3 * Real.sqrt (mu : ℝ)) + 1)).trans
        (le_max_left _ (4 * s₀ / (3 * Real.sqrt (mu : ℝ)) + 1)))
    linarith only [hx, this]
  have hx4 : 4 < ‖x‖ := by
    have := (le_max_right (8 * R + 1) 4).trans
      ((le_max_left _ (4 * cutoff / (3 * Real.sqrt (mu : ℝ)) + 1)).trans
        (le_max_left _ (4 * s₀ / (3 * Real.sqrt (mu : ℝ)) + 1)))
    linarith only [hx, this]
  have hr : 0 < r := mul_pos (by norm_num) (by linarith only [hx4])
  have harLe : ar ≤ 7 / 8 * ‖x‖ := by
    unfold ar streamExhaustionAmp
    split_ifs
    · rw [max_le_iff]
      constructor
      · unfold r
        exact mul_le_mul_of_nonneg_right (by norm_num) (norm_nonneg x)
      · have : 2 / 3 * (1 + ‖x‖) ≤ 7 / 8 * ‖x‖ := by
          linarith only [hx4]
        exact this
    · unfold r
      exact mul_le_mul_of_nonneg_right (by norm_num) (norm_nonneg x)
  have hzero : ∀ y ∈ euclideanBall x ar, f y = 0 := by
    intro y hy
    by_contra hfy
    have hyR : ‖y‖ ≤ R := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using
        hR (subset_tsupport _ (show y ∈ Function.support f from hfy))
    have hdistE :=
      DivergenceFormProcess.Decay.euclideanNorm_sub_lt_of_mem_euclideanBall
        (streamExhaustionAmp_pos hr).le hy
    have hdist : dist x y < ar := by
      rw [dist_eq_norm, show x - y = -(y - x) by ring, norm_neg]
      exact (norm_le_euclideanNorm (y - x)).trans_lt hdistE
    have htri : ‖x‖ ≤ dist x y + ‖y‖ := by
      rw [dist_eq_norm]
      calc
        ‖x‖ = ‖(x - y) + y‖ := by rw [sub_add_cancel]
        _ ≤ ‖x - y‖ + ‖y‖ := norm_add_le _ _
    have : ‖x‖ < 7 / 8 * ‖x‖ + R :=
      htri.trans_lt (add_lt_add_of_lt_of_le (hdist.trans_le harLe) hyR)
    linarith only [this, hxR]
  have hcut : cutoff < Real.sqrt (mu : ℝ) * r := by
    have hTcut : 4 * cutoff / (3 * Real.sqrt (mu : ℝ)) + 1 ≤ T :=
      (le_max_right (max (8 * R + 1) 4) _).trans (le_max_left _ _)
    unfold r
    have := lt_of_le_of_lt hTcut hx
    field_simp [hsqrt.ne'] at this ⊢
    linarith only [this, hsqrt]
  have hs₀r : s₀ ≤ Real.sqrt (mu : ℝ) * r := by
    have hTs : 4 * s₀ / (3 * Real.sqrt (mu : ℝ)) + 1 ≤ T :=
      le_max_right _ _
    unfold r
    have := lt_of_le_of_lt hTs hx
    field_simp [hsqrt.ne'] at this ⊢
    linarith only [this, hsqrt]
  have har : 0 < ar := streamExhaustionAmp_pos hr
  have hscaleLe : Real.sqrt (mu : ℝ) * r ≤ Real.sqrt (mu : ℝ) * ar :=
    mul_le_mul_of_nonneg_left (by
      unfold ar streamExhaustionAmp
      split_ifs
      · exact le_max_left _ _
      · exact le_rfl) hsqrt.le
  have hone : 1 < Real.sqrt (mu : ℝ) * ar :=
    lt_of_le_of_lt (one_le_streamUniformExhaustionCutoff M omega (mu : ℝ))
      (hcut.trans_le hscaleLe)
  have htail := mul_toReal_streamAnalyticMinimalResolvent_le_profile
    M omega mu hmu hf hf0 hf1 har hone hzero
  have hdom := streamLocalizedTailProfile_amp_le_uniform
    M omega hmu x hr hcut
  have hprofile : streamUniformExhaustionProfile M omega (mu : ℝ)
      (Real.sqrt (mu : ℝ) * r) =
      streamUniformExhaustionEnvelope M omega (Real.sqrt (mu : ℝ) * r) := by
    unfold streamUniformExhaustionProfile
    rw [ite_eq_left hcut]
  have hsmall : streamUniformExhaustionEnvelope M omega
      (Real.sqrt (mu : ℝ) * r) < (mu : ℝ) * eps := by
    have hd := hs₀ (Real.sqrt (mu : ℝ) * r) hs₀r
    have henv0 : 0 ≤ streamUniformExhaustionEnvelope M omega
        (Real.sqrt (mu : ℝ) * r) := by
      unfold streamUniformExhaustionEnvelope
      exact mul_nonneg (streamTailAmplitudeConst_nonneg M omega) (Real.exp_pos _).le
    simpa only [Real.dist_eq, sub_zero,
      abs_of_nonneg henv0] using hd
  have hdom' : streamLocalizedTailProfile M omega x
      (Real.sqrt (mu : ℝ) * ar) ≤
      streamUniformExhaustionProfile M omega (mu : ℝ)
        (Real.sqrt (mu : ℝ) * r) := by
    simpa only [ar] using hdom
  have hmul := (htail.trans (hdom'.trans_eq hprofile)).trans_lt hsmall
  change dist ((A.analyticMinimalResolvent mu f hf hf1 x).toReal) 0 < eps
  rw [Real.dist_eq, sub_zero, abs_of_nonneg ENNReal.toReal_nonneg]
  exact lt_of_mul_lt_mul_left hmul mu.property.le

/-- Scaling removes the normalization from a nonnegative compactly supported
datum in the stream-field vanishing theorem. -/
theorem zero_at_infty_toReal_streamAnalyticMinimalResolvent_of_compact
    (M : ABKModel d) (omega : FullSample d M.gamma)
    (mu : PositiveShift) (hmu : 1 ≤ (mu : ℝ))
    {f : Vec d → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    {D : ℝ} (hfD : ∀ x, |f x| ≤ D) (hfcompact : HasCompactSupport f) :
    Tendsto (fun x ↦ ((streamWholeSpaceAnalyticData M omega).analyticMinimalResolvent
      mu f hf hfD x).toReal) (cocompact (Vec d)) (nhds 0) := by
  let A := streamWholeSpaceAnalyticData M omega
  let C : ℝ := max D 1
  have hC : 0 < C := one_pos.trans_le (le_max_right _ _)
  let g : Vec d → ℝ := fun x ↦ C⁻¹ * f x
  have hg : Measurable g := hf.const_smul C⁻¹
  have hg0 : ∀ x, 0 ≤ g x := fun x ↦
    mul_nonneg (inv_nonneg.mpr hC.le) (hf0 x)
  have hg1 : ∀ x, |g x| ≤ 1 := by
    intro x
    rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr hC.le)]
    exact (inv_mul_le_one₀ hC).2 ((hfD x).trans (le_max_left _ _))
  have hgcompact : HasCompactSupport g := by
    refine hfcompact.mono ?_
    intro x hx
    rw [Function.mem_support] at hx ⊢
    intro hfx
    apply hx
    simp only [g, hfx, mul_zero]
  have hzero := zero_at_infty_toReal_streamAnalyticMinimalResolvent
    M omega mu hmu hg hg0 hg1 hgcompact
  have hscaled := hzero.const_mul C
  have hfg : (fun x ↦ C * g x) = f := by
    funext x
    dsimp only [g]
    rw [← mul_assoc, mul_inv_cancel₀ hC.ne', one_mul]
  have hvalue : (fun x ↦ C * (A.analyticMinimalResolvent mu g hg hg1 x).toReal) =
      fun x ↦ (A.analyticMinimalResolvent mu f hf hfD x).toReal := by
    funext x
    have hsmul := A.toReal_analyticMinimalResolvent_smul mu hC.le hg hg0
      (by norm_num) hg1 x
    have hcf : ∀ y, |C * g y| ≤ C := by
      intro y
      rw [abs_mul, abs_of_nonneg hC.le]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (hg1 y) hC.le
    have hle₁ := A.analyticMinimalResolvent_mono mu (hg.const_smul C) hf
      hcf hfD (fun y ↦ (congrFun hfg y).le) x
    have hle₂ := A.analyticMinimalResolvent_mono mu hf (hg.const_smul C)
      hfD hcf (fun y ↦ (congrFun hfg y).ge) x
    calc
      C * (A.analyticMinimalResolvent mu g hg hg1 x).toReal =
          (A.analyticMinimalResolvent mu (fun y ↦ C * g y)
            (hg.const_smul C) hcf x).toReal := hsmul.symm
      _ = (A.analyticMinimalResolvent mu f hf hfD x).toReal :=
        congrArg ENNReal.toReal (le_antisymm hle₁ hle₂)
  rw [hvalue] at hscaled
  simpa only [mul_zero] using hscaled

/-- Compactly supported signed `C₀` data have vanishing real resolvent for
every shift at least one. -/
theorem zero_at_infty_streamAnalyticMinimalResolventReal_of_compact
    (M : ABKModel d) (omega : FullSample d M.gamma)
    (mu : PositiveShift) (hmu : 1 ≤ (mu : ℝ))
    (f : C₀(Vec d, ℝ)) (hfcompact : HasCompactSupport f) :
    Tendsto ((streamWholeSpaceAnalyticData M omega).analyticMinimalResolventReal
      mu f f.continuous.measurable (D := ‖f‖) (by exact abs_le_norm_streamC0 f))
      (cocompact (Vec d)) (nhds 0) := by
  let fp : Vec d → ℝ := fun x ↦ max (f x) 0
  let fn : Vec d → ℝ := fun x ↦ max (-f x) 0
  have hfp0 : ∀ x, 0 ≤ fp x := fun x ↦ le_max_right _ _
  have hfn0 : ∀ x, 0 ≤ fn x := fun x ↦ le_max_right _ _
  have hnorm0 : 0 ≤ ‖f‖ := norm_nonneg _
  have hfpD : ∀ x, |fp x| ≤ ‖f‖ := by
    intro x
    rw [abs_of_nonneg (hfp0 x)]
    exact max_le ((le_abs_self _).trans (abs_le_norm_streamC0 f x)) hnorm0
  have hfnD : ∀ x, |fn x| ≤ ‖f‖ := by
    intro x
    rw [abs_of_nonneg (hfn0 x)]
    exact max_le ((le_abs_self (-f x)).trans (by
      simpa only [abs_neg] using abs_le_norm_streamC0 f x)) hnorm0
  have hfpcompact : HasCompactSupport fp := by
    refine hfcompact.mono ?_
    intro x hx
    rw [Function.mem_support] at hx ⊢
    intro hfx
    apply hx
    simp only [fp, hfx, max_self]
  have hfncompact : HasCompactSupport fn := by
    refine hfcompact.mono ?_
    intro x hx
    rw [Function.mem_support] at hx ⊢
    intro hfx
    apply hx
    simp only [fn, hfx, neg_zero, max_self]
  have hp := zero_at_infty_toReal_streamAnalyticMinimalResolvent_of_compact
    M omega mu hmu (f.continuous.measurable.max measurable_const) hfp0 hfpD hfpcompact
  have hn := zero_at_infty_toReal_streamAnalyticMinimalResolvent_of_compact
    M omega mu hmu (f.continuous.measurable.neg.max measurable_const) hfn0 hfnD hfncompact
  have hsub := hp.sub hn
  rw [sub_zero] at hsub
  refine hsub.congr' ?_
  filter_upwards with x
  rfl

/-- The stream-field analytic minimal resolvent maps every `C₀` datum to a
function vanishing at infinity. -/
theorem hasVanishing_streamAnalyticMinimalResolvent
    (M : ABKModel d) (omega : FullSample d M.gamma) :
    (streamWholeSpaceAnalyticData M omega).HasVanishingAnalyticMinimalResolvent := by
  let A := streamWholeSpaceAnalyticData M omega
  apply A.hasVanishingAnalyticMinimalResolvent_of_aboveOne
  intro mu hmu f
  rw [Metric.tendsto_nhds]
  intro eps heps
  let delta : ℝ := eps * (mu : ℝ) / 8
  have hdelta : 0 < delta := by
    unfold delta
    positivity
  obtain ⟨g, hgclose⟩ := exists_compactSupportCore_close_stream f hdelta
  let g0 : C₀(Vec d, ℝ) :=
    DivergenceFormProcess.FunctionalAnalysis.compactSupportCoreToC0 g
  have hclose : ∀ y, |f y - g0 y| ≤ delta := by
    intro y
    have hpoint : |(g0 - f) y| ≤ ‖g0 - f‖ := abs_le_norm_streamC0 (g0 - f) y
    have hpoint' : |g0 y - f y| ≤ ‖g0 - f‖ := by
      simpa only using! hpoint
    simpa only [abs_sub_comm] using
      hpoint'.trans (le_of_lt (by simpa only [g0] using hgclose))
  have hgcompact : HasCompactSupport g0 := mem_compactlySupported.mp g.property
  have hgzero := zero_at_infty_streamAnalyticMinimalResolventReal_of_compact
    M omega mu hmu g0 hgcompact
  have hevent := (Metric.tendsto_nhds.mp hgzero) (eps / 2) (half_pos heps)
  filter_upwards [hevent] with x hx
  rw [Real.dist_eq, sub_zero] at hx ⊢
  have hstable := A.abs_analyticMinimalResolventReal_sub_le mu
    f.continuous.measurable g0.continuous.measurable
    (abs_le_norm_streamC0 f) (abs_le_norm_streamC0 g0) hclose x
  have hcalc : delta / (mu : ℝ) = eps / 8 := by
    unfold delta
    field_simp [ne_of_gt (show 0 < (mu : ℝ) from mu.property)]
  rw [hcalc] at hstable
  calc
    |A.analyticMinimalResolventReal mu f f.continuous.measurable
        (abs_le_norm_streamC0 f) x| ≤
      |A.analyticMinimalResolventReal mu f f.continuous.measurable
          (abs_le_norm_streamC0 f) x -
        A.analyticMinimalResolventReal mu g0 g0.continuous.measurable
          (abs_le_norm_streamC0 g0) x| +
      |A.analyticMinimalResolventReal mu g0 g0.continuous.measurable
          (abs_le_norm_streamC0 g0) x| := by
        simpa only [sub_add_cancel] using abs_add_le
          (A.analyticMinimalResolventReal mu f f.continuous.measurable
            (abs_le_norm_streamC0 f) x -
            A.analyticMinimalResolventReal mu g0 g0.continuous.measurable
              (abs_le_norm_streamC0 g0) x)
          (A.analyticMinimalResolventReal mu g0 g0.continuous.measurable
            (abs_le_norm_streamC0 g0) x)
    _ < eps / 8 + eps / 2 := add_lt_add_of_le_of_lt hstable hx
    _ < eps := by linarith only [heps]

end

end Algsuperdiff.Section5.Field
