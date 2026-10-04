/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

-- Adapted for Lean Pool's pinned Lean and Mathlib; upstream commit is recorded in projects.yml.
module

public import LeanPool.EllipticPDE.Regularity.MollifyWkInfty
public import LeanPool.EllipticPDE.Regularity.Interior
public import LeanPool.EllipticPDE.Embedding.Convolution


/-!
# Leibniz rule for a `W^{1,∞}` weight

`EllipticPdes.Regularity.HasWeakDerivOn.mul_contDiff_left` proves the weak-derivative product
rule for a `C¹` weight. Guo's hypothesis supplies no classical derivative, and this file
replaces that route.

## Smooth case

For a weight that is already `C^∞`, no mollification is needed at all and no product rule for
weak derivatives has to be proved: `b · φ` is itself a smooth compactly supported test function
supported where `φ` is, so it may be fed straight to `HasWeakDerivOn`, and the classical
Leibniz rule splits the result. That is `weakDerivOn_smul_test_contDiff` below, the whole
content of the mollified stage.

## Entry point of the weak hypothesis

The mollification `a ⋆ ρ_ε` of a `W^{1,∞}` weight is `C^∞`, and its derivative is the
mollification of the weak derivative (`partialD_convolution_eq_of_hasWeakPartial`). Feeding it to
the smooth case gives the identity for every `ε`, and what remains is to pass to the limit.

## Passing to the limit

The `C¹` route mollifies and lets dominated convergence take the limit, which needs
`a ⋆ ρ_ε → a` pointwise and so needs `a` continuous. A merely measurable weight has no such
convergence, and the limit is taken in `L²` instead: the pairing is bounded by Cauchy-Schwarz
(`abs_setIntegral_mul_le`), leaving `‖a ⋆ ρ_ε - a‖_{L²}` on the support of the test function.

A bounded weight lies in no `Lᵖ` on the whole space, so the `L²` convergence of
`EllipticPdes.Embedding.tendsto_eLpNorm_convolution_sub` does not apply to `a` itself. It applies
to the truncation `a · 1_B` on a large ball, and `convolution_congr_of_eqOn` says the truncation
changes the mollification nowhere near the test function once the kernel radius is below the
margin. That is `tendsto_setIntegral_mul_convolution_of_measurable`, which replaces the
`C¹`-weight dominated-convergence lemma and is applied three times, once per term.

## Main declarations

* `weakDerivOn_smul_test_contDiff`: the identity for a `C^∞` weight, with no mollification.
* `abs_setIntegral_mul_le`: Cauchy-Schwarz, with the second factor left as an `eLpNorm`.
* `tendsto_setIntegral_mul_convolution_of_measurable`: the mollification limit against an `L²`
  class, for a weight that is measurable and essentially bounded and nothing more.
* `HasWeakDerivOn.mul_isWkInfty_left`: the Leibniz rule for a `W^{1,∞}` weight.
-/

@[expose] public section

open MeasureTheory
open scoped Topology ENNReal Convolution

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

variable {d : ℕ}

/-- A continuous compactly supported function is in `L²` of any restricted Lebesgue measure. -/
theorem memLp_two_restrict_of_continuous_hasCompactSupport
    {V : Set (EuclideanSpace ℝ (Fin d))} {h : EuclideanSpace ℝ (Fin d) → ℝ}
    (hc : Continuous h) (hcs : HasCompactSupport h) :
    MemLp h 2 (volume.restrict V) :=
  (hc.memLp_of_hasCompactSupport (μ := volume) hcs).restrict V

/-- **Leibniz identity for a `C^∞` weight.** If `g` has weak `ℓ`-derivative `g'` on `V` and
`b` is smooth, then for every test function `φ` supported in `V`,

`∫_V g · (b · ∂_ℓφ) = - ∫_V (g' · b + g · ∂_ℓ b) · φ`.

No mollification and no product rule for weak derivatives is involved: `b · φ` is a smooth
compactly supported test function supported inside `V`, so `HasWeakDerivOn` applies to it
directly, and the classical Leibniz rule splits the derivative of the product. -/
theorem weakDerivOn_smul_test_contDiff {V : Set (EuclideanSpace ℝ (Fin d))} (ℓ : Fin d)
    {g g' : Lp ℝ 2 (volume.restrict V)} (hg : HasWeakDerivOn V ℓ g g')
    {b : EuclideanSpace ℝ (Fin d) → ℝ} (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφc : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφcs : HasCompactSupport φ) (hφV : tsupport φ ⊆ V) :
    ∫ x in V, (g x : ℝ) * (b x * partialD ℓ φ x)
      = - ∫ x in V, ((g' x : ℝ) * b x + (g x : ℝ) * partialD ℓ b x) * φ x := by
  have hbd : Differentiable ℝ b := hb.differentiable (by simp)
  have hφd : Differentiable ℝ φ := hφc.differentiable (by simp)
  -- `b · φ` is a test function supported where `φ` is.
  have hbφ_cd : ContDiff ℝ (⊤ : ℕ∞) (fun x => b x * φ x) := hb.mul hφc
  have hbφ_cs : HasCompactSupport (fun x => b x * φ x) := hφcs.mul_left
  have hbφ_V : tsupport (fun x => b x * φ x) ⊆ V :=
    Set.Subset.trans (closure_mono (Function.support_mul_subset_right b φ)) hφV
  have key := hg _ hbφ_cd hbφ_cs hbφ_V
  rw [partialD_mul hbd hφd ℓ] at key
  -- Both halves of the split integrand are `L¹(V)`: `g` is `L²` and each cofactor is
  -- continuous with compact support, hence `L²` on the restriction.
  have hcont_bdφ : Continuous (fun x => b x * partialD ℓ φ x) :=
    hb.continuous.mul ((hφc.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hcs_bdφ : HasCompactSupport (fun x => b x * partialD ℓ φ x) :=
    (hφcs.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single ℓ 1)).mul_left
  have hcont_dbφ : Continuous (fun x => partialD ℓ b x * φ x) :=
    ((hb.continuous_fderiv (by simp)).clm_apply continuous_const).mul hφc.continuous
  have hcs_dbφ : HasCompactSupport (fun x => partialD ℓ b x * φ x) := hφcs.mul_left
  have hint1 : Integrable (fun x => (g x : ℝ) * (b x * partialD ℓ φ x))
      (volume.restrict V) :=
    (Lp.memLp g).integrable_mul
      (memLp_two_restrict_of_continuous_hasCompactSupport hcont_bdφ hcs_bdφ)
  have hint2 : Integrable (fun x => (g x : ℝ) * (partialD ℓ b x * φ x))
      (volume.restrict V) :=
    (Lp.memLp g).integrable_mul
      (memLp_two_restrict_of_continuous_hasCompactSupport hcont_dbφ hcs_dbφ)
  have hsplit : ∫ x in V, (g x : ℝ) * (b x * partialD ℓ φ x + partialD ℓ b x * φ x)
      = (∫ x in V, (g x : ℝ) * (b x * partialD ℓ φ x))
        + ∫ x in V, (g x : ℝ) * (partialD ℓ b x * φ x) := by
    rw [← integral_add hint1 hint2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    ring
  rw [hsplit] at key
  -- Reassemble the right-hand side into one integrand.
  have hintR1 : Integrable (fun x => (g' x : ℝ) * (b x * φ x)) (volume.restrict V) :=
    (Lp.memLp g').integrable_mul
      (memLp_two_restrict_of_continuous_hasCompactSupport
        (hb.continuous.mul hφc.continuous) hbφ_cs)
  have hcollect : ∫ x in V, ((g' x : ℝ) * b x + (g x : ℝ) * partialD ℓ b x) * φ x
      = (∫ x in V, (g' x : ℝ) * (b x * φ x))
        + ∫ x in V, (g x : ℝ) * (partialD ℓ b x * φ x) := by
    rw [← integral_add hintR1 hint2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    ring
  rw [hcollect]
  linarith [key]

/-! ### Pairing against an `L²` class -/

/-- **Cauchy-Schwarz on a restricted measure.** The pairing of an `L²(V)` class with an `L²(V)`
function is bounded by the product of the norms, with the second factor left as an `eLpNorm` so
that a convergence statement about `eLpNorm` transfers to the pairing with no further work. -/
theorem abs_setIntegral_mul_le {V : Set (EuclideanSpace ℝ (Fin d))}
    (h : Lp ℝ 2 (volume.restrict V)) {F : EuclideanSpace ℝ (Fin d) → ℝ}
    (hF : MemLp F 2 (volume.restrict V)) :
    |∫ x in V, (h x : ℝ) * F x| ≤ ‖h‖ * (eLpNorm F 2 (volume.restrict V)).toReal := by
  have hrepr : (inner ℝ h (hF.toLp F) : ℝ) = ∫ x in V, (h x : ℝ) * F x := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hF.coeFn_toLp] with x hx
    rw [Real.inner_apply, hx]
  calc |∫ x in V, (h x : ℝ) * F x| = |(inner ℝ h (hF.toLp F) : ℝ)| := by rw [hrepr]
    _ ≤ ‖h‖ * ‖hF.toLp F‖ := abs_real_inner_le_norm _ _
    _ = ‖h‖ * (eLpNorm F 2 (volume.restrict V)).toReal := by rw [Lp.norm_toLp]

/-- An essentially bounded measurable function times a continuous compactly supported one is in
`L²` of any restricted Lebesgue measure. The bound is not assumed non-negative, so the proof
compares against `max M 0`. -/
theorem memLp_two_restrict_mul_of_ae_bound {V : Set (EuclideanSpace ℝ (Fin d))}
    {c η : EuclideanSpace ℝ (Fin d) → ℝ} (hcm : Measurable c) {M : ℝ}
    (hcM : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), |c x| ≤ M)
    (hηc : Continuous η) (hηcs : HasCompactSupport η) :
    MemLp (fun x => c x * η x) 2 (volume.restrict V) := by
  have hM0 : (0 : ℝ) ≤ max M 0 := le_max_right _ _
  have hcM' : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), |c x| ≤ max M 0 :=
    hcM.mono fun x hx => hx.trans (le_max_left _ _)
  have hbase : MemLp (fun x => max M 0 * η x) 2 (volume : Measure (EuclideanSpace ℝ (Fin d))) :=
    (continuous_const.mul hηc).memLp_of_hasCompactSupport (μ := volume) hηcs.mul_left
  have hfull : MemLp (fun x => c x * η x) 2 (volume : Measure (EuclideanSpace ℝ (Fin d))) := by
    refine lt_of_le_of_lt (eLpNorm_mono_ae (g := fun x => max M 0 * η x)
      (hcm.aestronglyMeasurable.mul hηc.aestronglyMeasurable) ?_) hbase.eLpNorm_lt_top
    filter_upwards [hcM'] with x hx
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hM0]
    exact mul_le_mul_of_nonneg_right hx (abs_nonneg _)
  exact hfull.restrict V

/-! ### Mollification limit for a measurable weight -/

/-- **Mollification limit against an `L²` class.** For a measurable, essentially bounded `c`,
an `L²(V)` class `h` and a continuous compactly supported `η`,

`∫_V h · ((c ⋆ ρ_ε) · η) → ∫_V h · (c · η)`.

Continuity of `c` is not assumed, so `c ⋆ ρ_ε → c` pointwise is unavailable and the limit is
taken in `L²`. Cauchy-Schwarz leaves `‖(c ⋆ ρ_ε - c) · η‖_{L²}`, which sees `c` only on the
compact support of `η`. Replacing `c` there by its truncation to a large closed ball, which
`convolution_congr_of_eqOn` shows to change nothing once the kernel radius is under the margin,
puts the difference inside the reach of `tendsto_eLpNorm_convolution_sub`. -/
theorem tendsto_setIntegral_mul_convolution_of_measurable
    {V : Set (EuclideanSpace ℝ (Fin d))}
    (φ : ℕ → ContDiffBump (0 : EuclideanSpace ℝ (Fin d)))
    (hφ : Filter.Tendsto (fun n => (φ n).rOut) Filter.atTop (𝓝 0))
    (hφK : ∀ n, (φ n).rOut ≤ 2 * (φ n).rIn)
    {c : EuclideanSpace ℝ (Fin d) → ℝ} (hcm : Measurable c) {Mc : ℝ}
    (hcM : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), |c x| ≤ Mc)
    (h : Lp ℝ 2 (volume.restrict V))
    {η : EuclideanSpace ℝ (Fin d) → ℝ} (hηc : Continuous η) (hηcs : HasCompactSupport η) :
    Filter.Tendsto
      (fun n => ∫ x in V, (h x : ℝ)
        * ((c ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ((φ n).normed volume)) x * η x))
      Filter.atTop (𝓝 (∫ x in V, (h x : ℝ) * (c x * η x))) := by
  classical
  have hM0 : (0 : ℝ) ≤ max Mc 0 := le_max_right _ _
  have hcM' : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), |c x| ≤ max Mc 0 :=
    hcM.mono fun x hx => hx.trans (le_max_left _ _)
  obtain ⟨C, hC⟩ := hηc.norm.bounded_above_of_compact_support hηcs.norm
  have hC0 : (0 : ℝ) ≤ C := le_trans (norm_nonneg _) (hC 0)
  have hcpt : IsCompact (tsupport η) := hηcs
  obtain ⟨R, hR⟩ := hcpt.isBounded.subset_closedBall (0 : EuclideanSpace ℝ (Fin d))
  -- The truncation to a ball wide enough to leave a unit margin around the test factor.
  set B : Set (EuclideanSpace ℝ (Fin d)) := Metric.closedBall 0 (R + 1) with hBdef
  set ct : EuclideanSpace ℝ (Fin d) → ℝ := Set.indicator B c with hctdef
  have hBm : MeasurableSet B := measurableSet_closedBall
  have hctm : Measurable ct := hcm.indicator hBm
  have hctcs : HasCompactSupport ct :=
    HasCompactSupport.intro (isCompact_closedBall 0 (R + 1)) fun x hx =>
      Set.indicator_of_notMem hx c
  have hctLp : MemLp ct 2 (volume : Measure (EuclideanSpace ℝ (Fin d))) := by
    change eLpNorm ct 2 volume < ⊤
    rw [hctdef, eLpNorm_indicator_eq_eLpNorm_restrict hBm]
    refine lt_of_le_of_lt (eLpNorm_le_of_ae_bound (C := max Mc 0)
        hcm.aestronglyMeasurable.restrict ?_) ?_
    · filter_upwards [ae_restrict_of_ae hcM'] with x hx
      simpa [Real.norm_eq_abs] using hx
    · rw [Measure.restrict_apply_univ]
      exact ENNReal.mul_lt_top
        (ENNReal.rpow_lt_top_of_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg)
          measure_closedBall_lt_top.ne)
        ENNReal.ofReal_lt_top
  have hctLI : LocallyIntegrable ct (volume : Measure (EuclideanSpace ℝ (Fin d))) :=
    hctLp.locallyIntegrable (by norm_num)
  have hcLI : LocallyIntegrable c (volume : Measure (EuclideanSpace ℝ (Fin d))) :=
    (memLp_top_of_bound hcm.aestronglyMeasurable (max Mc 0)
      (by filter_upwards [hcM'] with x hx; simpa [Real.norm_eq_abs] using hx)).locallyIntegrable
      le_top
  -- The `L²` convergence of the mollifications of the truncation.
  have h2 : ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) := by simp
  have hconvE : Filter.Tendsto
      (fun n => eLpNorm
        (ct ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ((φ n).normed volume) - ct) 2 volume)
      Filter.atTop (𝓝 0) := by
    have hmem : MemLp ct (ENNReal.ofReal (2 : ℝ)) volume := by rwa [h2]
    have := EllipticPdes.Embedding.tendsto_eLpNorm_convolution_sub (p := (2 : ℝ)) (by norm_num)
      hmem hφ (K := 2) (Filter.Eventually.of_forall hφK)
    rwa [h2] at this
  -- Continuity and compact support of the mollifications.
  have hcnC : ∀ n, Continuous (c ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      ((φ n).normed volume)) := fun n =>
    (φ n).hasCompactSupport_normed.continuous_convolution_right
      (L := ContinuousLinearMap.lsmul ℝ ℝ) hcLI ((φ n).contDiff_normed (n := 1)).continuous
  have hctnC : ∀ n, Continuous (ct ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      ((φ n).normed volume)) := fun n =>
    (φ n).hasCompactSupport_normed.continuous_convolution_right
      (L := ContinuousLinearMap.lsmul ℝ ℝ) hctLI ((φ n).contDiff_normed (n := 1)).continuous
  have hctnCS : ∀ n, HasCompactSupport (ct ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      ((φ n).normed volume)) := fun n =>
    HasCompactSupport.convolution (L := ContinuousLinearMap.lsmul ℝ ℝ) hctcs
      (φ n).hasCompactSupport_normed
  have hdiffLp : ∀ n, MemLp (ct ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      ((φ n).normed volume) - ct) 2 (volume : Measure (EuclideanSpace ℝ (Fin d))) := fun n =>
    (((hctnC n).memLp_of_hasCompactSupport (μ := volume) (hctnCS n))).sub hctLp
  -- Near the test factor the truncation is invisible.
  have hagree : ∀ n, (φ n).rOut < 1 → ∀ x ∈ tsupport η,
      (c ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ((φ n).normed volume)) x
        = (ct ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ((φ n).normed volume)) x := by
    intro n hn x hx
    have hxR : ‖x‖ ≤ R := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hR hx
    refine convolution_congr_of_eqOn (r := (φ n).rOut) (fun y hy => ?_) (fun t ht => ?_)
    · have hy' : y ∉ Function.support ((φ n).normed volume) := by
        rw [(φ n).support_normed_eq]
        simpa [Metric.mem_ball, dist_zero_right] using not_lt.mpr hy
      exact Function.notMem_support.mp hy'
    · have h1 : ‖t‖ ≤ ‖x‖ + ‖x - t‖ := by
        calc ‖t‖ = ‖x - (x - t)‖ := by rw [sub_sub_cancel]
          _ ≤ ‖x‖ + ‖x - t‖ := norm_sub_le _ _
      have htB : t ∈ B := by
        have : ‖t‖ ≤ R + 1 := by linarith
        simpa [hBdef, Metric.mem_closedBall, dist_zero_right] using this
      rw [hctdef, Set.indicator_of_mem htB]
  -- The two difference functions, which agree once the kernel radius is under the margin.
  set Fn : ℕ → EuclideanSpace ℝ (Fin d) → ℝ := fun n x =>
    ((c ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ((φ n).normed volume)) x - c x) * η x with hFn
  set Gn : ℕ → EuclideanSpace ℝ (Fin d) → ℝ := fun n x =>
    ((ct ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ((φ n).normed volume)) x - ct x) * η x with hGn
  have hFG : ∀ n, (φ n).rOut < 1 → ∀ x, Fn n x = Gn n x := by
    intro n hn x
    by_cases hx : x ∈ tsupport η
    · have hxB : x ∈ B := by
        have hxR : ‖x‖ ≤ R := by
          simpa [Metric.mem_closedBall, dist_zero_right] using hR hx
        have : ‖x‖ ≤ R + 1 := by linarith
        simpa [hBdef, Metric.mem_closedBall, dist_zero_right] using this
      simp only [hFn, hGn]
      rw [hagree n hn x hx, hctdef, Set.indicator_of_mem hxB]
    · have hη0 : η x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp only [hFn, hGn, hη0, mul_zero]
  -- `Gn` is `L²` and its norm is controlled by the `L²` distance of the mollification.
  have hGvol : ∀ n, eLpNorm (Gn n) 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))
      ≤ ENNReal.ofReal C * eLpNorm (ct ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          ((φ n).normed volume) - ct) 2 volume := by
    intro n
    have hstep : eLpNorm (Gn n) 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))
        ≤ eLpNorm (C • (ct ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ((φ n).normed volume) - ct))
            2 volume := by
      refine eLpNorm_mono_ae ((hdiffLp n).aestronglyMeasurable.mul
        hηc.aestronglyMeasurable) (Filter.Eventually.of_forall fun x => ?_)
      have hb : |(ct ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ((φ n).normed volume)) x - ct x|
            * ‖η x‖
          ≤ |(ct ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ((φ n).normed volume)) x - ct x| * C :=
        mul_le_mul_of_nonneg_left (by simpa using hC x) (abs_nonneg _)
      calc ‖Gn n x‖
          = |(ct ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ((φ n).normed volume)) x - ct x|
              * ‖η x‖ := by
            simp only [hGn, Real.norm_eq_abs, abs_mul]
        _ ≤ |(ct ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ((φ n).normed volume)) x - ct x|
              * C := hb
        _ = ‖(C • (ct ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ((φ n).normed volume) - ct)) x‖ := by
            simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Real.norm_eq_abs, abs_mul,
              abs_of_nonneg hC0]
            ring
    refine hstep.trans ?_
    rw [eLpNorm_const_smul]
    exact mul_le_mul_of_nonneg_right (le_of_eq (Real.enorm_eq_ofReal hC0)) (by simp)
  have hGLp : ∀ n, MemLp (Gn n) 2 (volume : Measure (EuclideanSpace ℝ (Fin d))) := by
    intro n
    exact lt_of_le_of_lt (hGvol n)
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hdiffLp n).eLpNorm_lt_top)
  -- The two integrands, both `L¹(V)`.
  have hIntc : ∀ n, Integrable (fun x => (h x : ℝ)
      * ((c ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ((φ n).normed volume)) x * η x))
      (volume.restrict V) := fun n =>
    (Lp.memLp h).integrable_mul
      (memLp_two_restrict_of_continuous_hasCompactSupport ((hcnC n).mul hηc) hηcs.mul_left)
  have hIntlim : Integrable (fun x => (h x : ℝ) * (c x * η x)) (volume.restrict V) :=
    (Lp.memLp h).integrable_mul (memLp_two_restrict_mul_of_ae_bound hcm hcM hηc hηcs)
  -- The bound, valid once the kernel radius is under the margin.
  have hsmall : ∀ᶠ n in Filter.atTop, (φ n).rOut < 1 :=
    Filter.Tendsto.eventually_lt_const one_pos hφ
  have hbound : ∀ᶠ n in Filter.atTop,
      ‖(∫ x in V, (h x : ℝ)
          * ((c ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ((φ n).normed volume)) x * η x))
        - ∫ x in V, (h x : ℝ) * (c x * η x)‖
      ≤ ‖h‖ * (C * (eLpNorm (ct ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          ((φ n).normed volume) - ct) 2 volume).toReal) := by
    filter_upwards [hsmall] with n hn
    have hrew : (∫ x in V, (h x : ℝ)
          * ((c ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ((φ n).normed volume)) x * η x))
        - (∫ x in V, (h x : ℝ) * (c x * η x))
        = ∫ x in V, (h x : ℝ) * Gn n x := by
      rw [← integral_sub (hIntc n) hIntlim]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      have hxe := hFG n hn x
      simp only [hFn, hGn] at hxe
      simp only [hGn]
      rw [← hxe]
      ring
    rw [Real.norm_eq_abs, hrew]
    refine le_trans (abs_setIntegral_mul_le h ((hGLp n).restrict V)) ?_
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have hfin : ENNReal.ofReal C * eLpNorm (ct ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        ((φ n).normed volume) - ct) 2 volume ≠ ⊤ :=
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hdiffLp n).eLpNorm_lt_top).ne
    calc (eLpNorm (Gn n) 2 (volume.restrict V)).toReal
        ≤ (ENNReal.ofReal C * eLpNorm (ct ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
            ((φ n).normed volume) - ct) 2 volume).toReal :=
          ENNReal.toReal_mono hfin
            ((eLpNorm_mono_measure _ Measure.restrict_le_self).trans (hGvol n))
      _ = C * (eLpNorm (ct ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
            ((φ n).normed volume) - ct) 2 volume).toReal := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC0]
  -- Pass to the limit.
  have hεtend : Filter.Tendsto
      (fun n => ‖h‖ * (C * (eLpNorm (ct ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        ((φ n).normed volume) - ct) 2 volume).toReal)) Filter.atTop (𝓝 0) := by
    have h0 : Filter.Tendsto
        (fun n => (eLpNorm (ct ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          ((φ n).normed volume) - ct) 2 volume).toReal) Filter.atTop (𝓝 0) := by
      simpa [Function.comp_def] using (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hconvE
    simpa using (h0.const_mul C).const_mul ‖h‖
  rw [← tendsto_sub_nhds_zero_iff]
  exact squeeze_zero_norm' hbound hεtend

/-! ### Leibniz rule -/

/-- **Weak-derivative Leibniz with a `W^{1,∞}` weight.** If `g` has weak `ℓ`-derivative `g'` on
`V`, and `a` is measurable and essentially bounded with an essentially bounded weak `ℓ`-derivative
`a'`, then `a·g` has weak `ℓ`-derivative `a'·g + a·g'` on `V`.

This is `HasWeakDerivOn.mul_contDiff_left` with the `C¹` hypothesis on the weight removed, which
is what Guo, *Partial Differential Equations I and II* (Course Lecture Notes), Theorem VIII.3.2
(p. 65) asks for. The weight is mollified, the smooth case
`weakDerivOn_smul_test_contDiff` gives the identity at every radius, and
`tendsto_setIntegral_mul_convolution_of_measurable` sends each of the three terms to its
limit. -/
theorem HasWeakDerivOn.mul_isWkInfty_left {V : Set (EuclideanSpace ℝ (Fin d))} (ℓ : Fin d)
    {g g' : Lp ℝ 2 (volume.restrict V)} (hg : HasWeakDerivOn V ℓ g g')
    {a a' : EuclideanSpace ℝ (Fin d) → ℝ} (ham : Measurable a) (ha'm : Measurable a')
    (ha : HasWeakPartial ℓ a a') {Ma Mda : ℝ}
    (haM : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), |a x| ≤ Ma)
    (hdaM : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), |a' x| ≤ Mda)
    (ag : Lp ℝ 2 (volume.restrict V))
    (hag : ag =ᵐ[volume.restrict V] fun x => a x * (g x : ℝ))
    (dag : Lp ℝ 2 (volume.restrict V))
    (hdag : dag =ᵐ[volume.restrict V] fun x => a' x * (g x : ℝ) + a x * (g' x : ℝ)) :
    HasWeakDerivOn V ℓ ag dag := by
  classical
  -- A shrinking family of bumps, with the inner and outer radii in a fixed ratio.
  let φ : ℕ → ContDiffBump (0 : EuclideanSpace ℝ (Fin d)) := fun n =>
    { rIn := 1 / (n + 2 : ℝ) / 2
      rOut := 1 / (n + 2 : ℝ)
      rIn_pos := by positivity
      rIn_lt_rOut := half_lt_self (by positivity) }
  have hφrOut : Filter.Tendsto (fun n => (φ n).rOut) Filter.atTop (𝓝 0) := by
    have hval : ∀ n : ℕ, (φ n).rOut = 1 / (n + 2 : ℝ) := fun _ => rfl
    simp only [hval]
    exact tendsto_const_nhds.div_atTop
      (Filter.tendsto_atTop_add_const_right Filter.atTop 2 tendsto_natCast_atTop_atTop)
  have hφK : ∀ n, (φ n).rOut ≤ 2 * (φ n).rIn := fun n =>
    le_of_eq (by change (1 / (n + 2 : ℝ)) = 2 * (1 / (n + 2 : ℝ) / 2); ring)
  have haLI : LocallyIntegrable a (volume : Measure (EuclideanSpace ℝ (Fin d))) :=
    (memLp_top_of_bound ham.aestronglyMeasurable (max Ma 0)
      (by
        filter_upwards [haM] with x hx
        rw [Real.norm_eq_abs]
        exact hx.trans (le_max_left _ _))).locallyIntegrable le_top
  have ha'LI : LocallyIntegrable a' (volume : Measure (EuclideanSpace ℝ (Fin d))) :=
    (memLp_top_of_bound ha'm.aestronglyMeasurable (max Mda 0)
      (by
        filter_upwards [hdaM] with x hx
        rw [Real.norm_eq_abs]
        exact hx.trans (le_max_left _ _))).locallyIntegrable le_top
  intro ψ hψc hψcs hψV
  have hdψc : Continuous (partialD ℓ ψ) :=
    (hψc.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdψcs : HasCompactSupport (partialD ℓ ψ) :=
    hψcs.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single ℓ 1)
  -- Read the goal through the chosen representatives.
  have hagInt : ∫ x in V, (ag x : ℝ) * partialD ℓ ψ x
      = ∫ x in V, (a x * (g x : ℝ)) * partialD ℓ ψ x :=
    integral_congr_ae (by filter_upwards [hag] with x hx; rw [hx])
  have hdagInt : ∫ x in V, (dag x : ℝ) * ψ x
      = ∫ x in V, (a' x * (g x : ℝ) + a x * (g' x : ℝ)) * ψ x :=
    integral_congr_ae (by filter_upwards [hdag] with x hx; rw [hx])
  rw [hagInt, hdagInt]
  -- The identity at each radius, from the smooth case.
  have hPn : ∀ n,
      (∫ x in V, (g x : ℝ)
          * ((a ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ((φ n).normed volume)) x
              * partialD ℓ ψ x))
        + (∫ x in V, (g x : ℝ)
          * ((a' ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ((φ n).normed volume)) x * ψ x))
      = -(∫ x in V, (g' x : ℝ)
          * ((a ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ((φ n).normed volume)) x * ψ x)) := by
    intro n
    have hbcd : ContDiff ℝ (⊤ : ℕ∞)
        (a ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ((φ n).normed volume)) :=
      (φ n).hasCompactSupport_normed.contDiff_convolution_right
        (L := ContinuousLinearMap.lsmul ℝ ℝ) haLI (φ n).contDiff_normed
    have hkey := weakDerivOn_smul_test_contDiff ℓ hg hbcd hψc hψcs hψV
    rw [partialD_convolution_eq_of_hasWeakPartial haLI ha (φ n).contDiff_normed
      (φ n).hasCompactSupport_normed] at hkey
    have hi1 : Integrable (fun x => (g' x : ℝ)
        * ((a ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ((φ n).normed volume)) x * ψ x))
        (volume.restrict V) :=
      (Lp.memLp g').integrable_mul
        (memLp_two_restrict_of_continuous_hasCompactSupport
          (hbcd.continuous.mul hψc.continuous) hψcs.mul_left)
    have hi2 : Integrable (fun x => (g x : ℝ)
        * ((a' ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ((φ n).normed volume)) x * ψ x))
        (volume.restrict V) :=
      (Lp.memLp g).integrable_mul
        (memLp_two_restrict_of_continuous_hasCompactSupport
          (((φ n).hasCompactSupport_normed.continuous_convolution_right
            (L := ContinuousLinearMap.lsmul ℝ ℝ) ha'LI
            ((φ n).contDiff_normed (n := 1)).continuous).mul hψc.continuous)
          hψcs.mul_left)
    have hsplit : ∫ x in V, ((g' x : ℝ)
          * (a ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ((φ n).normed volume)) x
          + (g x : ℝ)
            * (a' ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ((φ n).normed volume)) x) * ψ x
        = (∫ x in V, (g' x : ℝ)
            * ((a ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ((φ n).normed volume)) x * ψ x))
          + ∫ x in V, (g x : ℝ)
            * ((a' ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ((φ n).normed volume)) x * ψ x) := by
      rw [← integral_add hi1 hi2]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
    rw [hsplit] at hkey
    linarith [hkey]
  -- Each of the three terms converges.
  have hL1 := tendsto_setIntegral_mul_convolution_of_measurable (V := V) φ hφrOut hφK ham haM g
    hdψc hdψcs
  have hL2 := tendsto_setIntegral_mul_convolution_of_measurable (V := V) φ hφrOut hφK ham haM g'
    hψc.continuous hψcs
  have hL3 := tendsto_setIntegral_mul_convolution_of_measurable (V := V) φ hφrOut hφK ha'm hdaM g
    hψc.continuous hψcs
  have hlim : (∫ x in V, (g x : ℝ) * (a x * partialD ℓ ψ x))
        + (∫ x in V, (g x : ℝ) * (a' x * ψ x))
      = -(∫ x in V, (g' x : ℝ) * (a x * ψ x)) :=
    tendsto_nhds_unique (hL1.add hL3) (Filter.Tendsto.congr (fun n => (hPn n).symm) hL2.neg)
  -- Reorganise both sides into the shape of the limits.
  have hlhs : ∫ x in V, (a x * (g x : ℝ)) * partialD ℓ ψ x
      = ∫ x in V, (g x : ℝ) * (a x * partialD ℓ ψ x) :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  have hj1 : Integrable (fun x => (g x : ℝ) * (a' x * ψ x)) (volume.restrict V) :=
    (Lp.memLp g).integrable_mul (memLp_two_restrict_mul_of_ae_bound ha'm hdaM hψc.continuous hψcs)
  have hj2 : Integrable (fun x => (g' x : ℝ) * (a x * ψ x)) (volume.restrict V) :=
    (Lp.memLp g').integrable_mul (memLp_two_restrict_mul_of_ae_bound ham haM hψc.continuous hψcs)
  have hrhs : ∫ x in V, (a' x * (g x : ℝ) + a x * (g' x : ℝ)) * ψ x
      = (∫ x in V, (g x : ℝ) * (a' x * ψ x)) + ∫ x in V, (g' x : ℝ) * (a x * ψ x) := by
    rw [← integral_add hj1 hj2]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  rw [hlhs, hrhs]
  linarith [hlim]

end EllipticPdes.Regularity
