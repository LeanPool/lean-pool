/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Field.BoundaryConservativity
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Field.ShiftAsymptotics
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Semigroup.ResolventDenseRange

/-!
# WholeSpaceDenseRange

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Dense range of the stream-field whole-space resolvent

At large shift, the normalized analytic minimal resolvent is an approximate
identity on compactly supported continuous data.  Near the support this uses
uniform continuity and a fixed ball on which radius amplification is inactive.
Far from the support, the amplified radius remains disjoint from the datum and
the same shift-uniform envelope controls the resolvent.  Contractivity and the
density of compactly supported data give strong normalization on all of `C₀`,
and hence dense range.
-/

namespace Algsuperdiff.Section5.Field

open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open CompactlySupported Filter HCPolySupport MeasureTheory Set Topology
open DivergenceFormProcess.Form MarkovProcess MarkovProcess.Semigroup
open scoped ENNReal ZeroAtInfty

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
theorem abs_le_norm_dense (f : C₀(Vec d, ℝ)) (x : Vec d) :
    |f x| ≤ ‖f‖ := by
  rw [← Real.norm_eq_abs, ← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  exact BoundedContinuousFunction.norm_coe_le_norm f.toBCF x

omit [NeZero d] in
theorem measurable_complBall (x : Vec d) (r : ℝ) :
    Measurable fun y ↦ (Metric.ball x r)ᶜ.indicator (fun _ ↦ (1 : ℝ)) y :=
  measurable_const.indicator Metric.isOpen_ball.measurableSet.compl

omit [NeZero d] in
private theorem complBall_nonneg (x : Vec d) (r : ℝ) (y : Vec d) :
    0 ≤ (Metric.ball x r)ᶜ.indicator (fun _ ↦ (1 : ℝ)) y := by
  classical
  rw [Set.indicator_apply]
  split_ifs <;> norm_num

omit [NeZero d] in
theorem abs_complBall_le_one (x : Vec d) (r : ℝ) (y : Vec d) :
    |(Metric.ball x r)ᶜ.indicator (fun _ ↦ (1 : ℝ)) y| ≤ 1 := by
  classical
  rw [Set.indicator_apply]
  split_ifs <;> norm_num

/-- The analytic tail outside the amplified ball is bounded by the common
envelope whenever the base scale is beyond the logarithmic cutoff. -/
theorem mul_toReal_streamAnalyticMinimalResolvent_compl_amp_le_envelope
    (M : ABKModel d) (omega : FullSample d M.gamma)
    (mu : PositiveShift) (hmu : 1 ≤ (mu : ℝ)) (x : Vec d)
    {r : ℝ} (hr : 0 < r)
    (hcut : streamUniformExhaustionCutoff M omega (mu : ℝ) <
      Real.sqrt (mu : ℝ) * r) :
    (mu : ℝ) * ((streamWholeSpaceAnalyticData M omega).analyticMinimalResolvent
        mu ((Metric.ball x (streamExhaustionAmp x r))ᶜ.indicator fun _ ↦ (1 : ℝ))
        (measurable_complBall x (streamExhaustionAmp x r))
        (abs_complBall_le_one x (streamExhaustionAmp x r)) x).toReal ≤
      streamUniformExhaustionEnvelope M omega (Real.sqrt (mu : ℝ) * r) := by
  let ar := streamExhaustionAmp x r
  have har : 0 < ar := streamExhaustionAmp_pos hr
  have hsqrt : 0 ≤ Real.sqrt (mu : ℝ) := Real.sqrt_nonneg _
  have hra : r ≤ ar := by
    unfold ar streamExhaustionAmp
    split_ifs
    · exact le_max_left _ _
    · exact le_rfl
  have hone : 1 < Real.sqrt (mu : ℝ) * ar :=
    lt_of_le_of_lt (one_le_streamUniformExhaustionCutoff M omega (mu : ℝ))
      (hcut.trans_le (mul_le_mul_of_nonneg_left hra hsqrt))
  have hzero : ∀ y ∈ euclideanBall x ar,
      (Metric.ball x ar)ᶜ.indicator (fun _ ↦ (1 : ℝ)) y = 0 := by
    intro y hy
    rw [Set.indicator_of_notMem]
    exact fun hyc ↦ hyc (euclideanBall_subset_metricBall har hy)
  have htail := mul_toReal_streamAnalyticMinimalResolvent_le_profile
    M omega mu hmu (measurable_complBall x ar) (complBall_nonneg x ar)
      (abs_complBall_le_one x ar) har hone hzero
  have hdom := streamLocalizedTailProfile_amp_le_uniform
    M omega hmu x hr hcut
  have hprofile : streamUniformExhaustionProfile M omega (mu : ℝ)
      (Real.sqrt (mu : ℝ) * r) =
      streamUniformExhaustionEnvelope M omega (Real.sqrt (mu : ℝ) * r) := by
    unfold streamUniformExhaustionProfile
    rw [ite_eq_left hcut]
  exact htail.trans (by
    simpa only [ar, hprofile] using hdom)

/-- If amplification is inactive, the preceding estimate is the ordinary
complement-of-ball tail bound. -/
theorem mul_toReal_streamAnalyticMinimalResolvent_complBall_le_envelope
    (M : ABKModel d) (omega : FullSample d M.gamma)
    (mu : PositiveShift) (hmu : 1 ≤ (mu : ℝ)) (x : Vec d)
    {r : ℝ} (hr : 0 < r) (hamp : streamExhaustionAmp x r = r)
    (hcut : streamUniformExhaustionCutoff M omega (mu : ℝ) <
      Real.sqrt (mu : ℝ) * r) :
    (mu : ℝ) * ((streamWholeSpaceAnalyticData M omega).analyticMinimalResolvent
        mu ((Metric.ball x r)ᶜ.indicator fun _ ↦ (1 : ℝ))
        (measurable_complBall x r) (abs_complBall_le_one x r) x).toReal ≤
      streamUniformExhaustionEnvelope M omega (Real.sqrt (mu : ℝ) * r) := by
  simpa only [hamp] using
    mul_toReal_streamAnalyticMinimalResolvent_compl_amp_le_envelope
      M omega mu hmu x hr hcut

private theorem abs_streamAnalyticMinimalResolventReal_le_toReal_of_abs_le
    (M : ABKModel d) (omega : FullSample d M.gamma)
    (mu : PositiveShift) {f g : Vec d → ℝ}
    (hf : Measurable f) (hg : Measurable g) (hg0 : ∀ y, 0 ≤ g y)
    {D E : ℝ} (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hfD : ∀ y, |f y| ≤ D) (hgE : ∀ y, |g y| ≤ E)
    (hfg : ∀ y, |f y| ≤ g y) (x : Vec d) :
    |(streamWholeSpaceAnalyticData M omega).analyticMinimalResolventReal
        mu f hf hfD x| ≤
      ((streamWholeSpaceAnalyticData M omega).analyticMinimalResolvent
        mu g hg hgE x).toReal := by
  let A := streamWholeSpaceAnalyticData M omega
  let fp : Vec d → ℝ := fun y ↦ max (f y) 0
  let fn : Vec d → ℝ := fun y ↦ max (-f y) 0
  have hfp0 : ∀ y, 0 ≤ fp y := fun y ↦ le_max_right _ _
  have hfn0 : ∀ y, 0 ≤ fn y := fun y ↦ le_max_right _ _
  have hfpD : ∀ y, |fp y| ≤ D := by
    intro y
    rw [abs_of_nonneg (hfp0 y)]
    exact max_le ((le_abs_self _).trans (hfD y)) hD
  have hfnD : ∀ y, |fn y| ≤ D := by
    intro y
    rw [abs_of_nonneg (hfn0 y)]
    exact max_le ((le_abs_self (-f y)).trans (by simpa only [abs_neg] using hfD y)) hD
  have hfpLe : (A.analyticMinimalResolvent mu fp
      (hf.max measurable_const) hfpD x).toReal ≤
      (A.analyticMinimalResolvent mu g hg hgE x).toReal := by
    apply (ENNReal.toReal_le_toReal
      (A.analyticMinimalResolvent_ne_top mu (hf.max measurable_const)
        hfp0 hD hfpD x)
      (A.analyticMinimalResolvent_ne_top mu hg hg0 hE hgE x)).2
    exact A.analyticMinimalResolvent_mono mu (hf.max measurable_const) hg
      hfpD hgE (fun y ↦ max_le ((le_abs_self _).trans (hfg y)) (hg0 y)) x
  have hfnLe : (A.analyticMinimalResolvent mu fn
      (hf.neg.max measurable_const) hfnD x).toReal ≤
      (A.analyticMinimalResolvent mu g hg hgE x).toReal := by
    apply (ENNReal.toReal_le_toReal
      (A.analyticMinimalResolvent_ne_top mu (hf.neg.max measurable_const)
        hfn0 hD hfnD x)
      (A.analyticMinimalResolvent_ne_top mu hg hg0 hE hgE x)).2
    exact A.analyticMinimalResolvent_mono mu (hf.neg.max measurable_const) hg
      hfnD hgE (fun y ↦ max_le ((le_abs_self (-f y)).trans (by
        simpa only [abs_neg] using hfg y)) (hg0 y)) x
  change |(A.analyticMinimalResolvent mu fp _ hfpD x).toReal -
      (A.analyticMinimalResolvent mu fn _ hfnD x).toReal| ≤ _
  rw [abs_sub_le_iff]
  constructor
  · exact (sub_le_self _ ENNReal.toReal_nonneg).trans hfpLe
  · exact (sub_le_self _ ENNReal.toReal_nonneg).trans hfnLe

private theorem streamAnalyticMinimalResolventReal_congr
    (M : ABKModel d) (omega : FullSample d M.gamma)
    (mu : PositiveShift) {f g : Vec d → ℝ} (hfg : f = g)
    (hf : Measurable f) (hg : Measurable g) {D E : ℝ}
    (hfD : ∀ y, |f y| ≤ D) (hgE : ∀ y, |g y| ≤ E) (x : Vec d) :
    (streamWholeSpaceAnalyticData M omega).analyticMinimalResolventReal
        mu f hf hfD x =
      (streamWholeSpaceAnalyticData M omega).analyticMinimalResolventReal
        mu g hg hgE x := by
  subst g
  exact (streamWholeSpaceAnalyticData M omega).analyticMinimalResolventReal_bound_irrel
    mu hf hfD hgE x

/-- The signed real stream resolvent has the exact constant-one
normalization. -/
theorem mul_streamAnalyticMinimalResolventReal_one_eq
    (M : ABKModel d) (omega : FullSample d M.gamma)
    (mu : PositiveShift) (x : Vec d) :
    (mu : ℝ) * (streamWholeSpaceAnalyticData M omega).analyticMinimalResolventReal
      mu (fun _ : Vec d ↦ (1 : ℝ)) measurable_const
      (D := 1) (fun _ ↦ by norm_num) x = 1 := by
  let A := streamWholeSpaceAnalyticData M omega
  rw [A.analyticMinimalResolventReal_eq_toReal mu measurable_const
    (fun _ ↦ by norm_num) (fun _ ↦ by norm_num) x]
  have h := ofReal_mul_streamAnalyticMinimalResolvent_one_eq M omega mu x
  apply_fun ENNReal.toReal at h
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal mu.property.le,
    ENNReal.toReal_one] using h

def streamBallPart (f : Vec d → ℝ) (x : Vec d) (r : ℝ) : Vec d → ℝ :=
  (Metric.ball x r).indicator fun y ↦ f y - f x

def streamComplementBallPart (f : Vec d → ℝ) (x : Vec d) (r : ℝ) :
    Vec d → ℝ :=
  (Metric.ball x r)ᶜ.indicator fun y ↦ f y - f x

omit [NeZero d] in
private theorem measurable_streamBallPart (f : C₀(Vec d, ℝ)) (x : Vec d) (r : ℝ) :
    Measurable (streamBallPart f x r) :=
  (f.continuous.measurable.sub measurable_const).indicator
    Metric.isOpen_ball.measurableSet

omit [NeZero d] in
private theorem measurable_streamComplementBallPart (f : C₀(Vec d, ℝ))
    (x : Vec d) (r : ℝ) : Measurable (streamComplementBallPart f x r) :=
  (f.continuous.measurable.sub measurable_const).indicator
    Metric.isOpen_ball.measurableSet.compl

omit [NeZero d] in
private theorem streamBallPart_add_streamComplementBallPart
    (f : C₀(Vec d, ℝ)) (x : Vec d) (r : ℝ) :
    (fun y ↦ streamBallPart f x r y + streamComplementBallPart f x r y) =
      fun y ↦ f y - f x := by
  funext y
  classical
  by_cases hy : y ∈ Metric.ball x r
  · rw [streamBallPart, streamComplementBallPart, Set.indicator_of_mem hy,
      Set.indicator_of_notMem (show y ∉ (Metric.ball x r)ᶜ from fun hyc ↦ hyc hy),
      add_zero]
  · rw [streamBallPart, streamComplementBallPart, Set.indicator_of_notMem hy,
      Set.indicator_of_mem (show y ∈ (Metric.ball x r)ᶜ from hy), zero_add]

omit [NeZero d] in
private theorem abs_streamBallPart_le (f : C₀(Vec d, ℝ)) (x : Vec d)
    (r delta : ℝ) (hdelta : 0 ≤ delta)
    (hmod : ∀ y, dist y x < r → |f y - f x| ≤ delta) (y : Vec d) :
    |streamBallPart f x r y| ≤ delta := by
  classical
  by_cases hy : y ∈ Metric.ball x r
  · rw [streamBallPart, Set.indicator_of_mem hy]
    exact hmod y (by simpa only [Metric.mem_ball] using hy)
  · rw [streamBallPart, Set.indicator_of_notMem hy, abs_zero]
    exact hdelta

omit [NeZero d] in
private theorem abs_streamPart_le_two_norm (f : C₀(Vec d, ℝ))
    (x : Vec d) (r : ℝ) (y : Vec d) :
    |streamBallPart f x r y| ≤ 2 * ‖f‖ ∧
      |streamComplementBallPart f x r y| ≤ 2 * ‖f‖ := by
  have hxy : |f y - f x| ≤ 2 * ‖f‖ := by
    calc
      |f y - f x| ≤ |f y| + |f x| := abs_sub _ _
      _ ≤ ‖f‖ + ‖f‖ := add_le_add (abs_le_norm_dense f y) (abs_le_norm_dense f x)
      _ = 2 * ‖f‖ := by ring
  constructor
  · classical
    by_cases hy : y ∈ Metric.ball x r
    · simpa only [streamBallPart, Set.indicator_of_mem hy] using hxy
    · rw [streamBallPart, Set.indicator_of_notMem hy, abs_zero]
      positivity
  · classical
    by_cases hy : y ∈ Metric.ball x r
    · rw [streamComplementBallPart,
        Set.indicator_of_notMem (show y ∉ (Metric.ball x r)ᶜ from fun hyc ↦ hyc hy),
        abs_zero]
      positivity
    · simpa only [streamComplementBallPart,
        Set.indicator_of_mem (show y ∈ (Metric.ball x r)ᶜ from hy)] using hxy

private theorem abs_scaled_streamResolvent_sub_lt_of_amp_eq
    (M : ABKModel d) (omega : FullSample d M.gamma)
    (mu : PositiveShift) (hmu : 1 ≤ (mu : ℝ))
    (f : C₀(Vec d, ℝ)) (x : Vec d) {r eps : ℝ} (hr : 0 < r)
    (heps : 0 < eps)
    (hmod : ∀ y, dist y x < r → |f y - f x| ≤ eps / 2)
    (hamp : streamExhaustionAmp x r = r)
    (hcut : streamUniformExhaustionCutoff M omega (mu : ℝ) <
      Real.sqrt (mu : ℝ) * r)
    (hfar : 2 * ‖f‖ * streamUniformExhaustionEnvelope M omega
      (Real.sqrt (mu : ℝ) * r) < eps / 2) :
    |(mu : ℝ) * (streamWholeSpaceAnalyticData M omega).analyticMinimalResolventReal
        mu f f.continuous.measurable (abs_le_norm_dense f) x - f x| < eps := by
  let A := streamWholeSpaceAnalyticData M omega
  let g : Vec d → ℝ := fun y ↦ f y - f x
  let u := streamBallPart f x r
  let v := streamComplementBallPart f x r
  have huMeas : Measurable u := measurable_streamBallPart f x r
  have hvMeas : Measurable v := measurable_streamComplementBallPart f x r
  have huBound : ∀ y, |u y| ≤ 2 * ‖f‖ := fun y ↦
    (abs_streamPart_le_two_norm f x r y).1
  have hvBound : ∀ y, |v y| ≤ 2 * ‖f‖ := fun y ↦
    (abs_streamPart_le_two_norm f x r y).2
  have hgBound : ∀ y, |g y| ≤ 2 * ‖f‖ := by
    intro y
    calc
      |f y - f x| ≤ |f y| + |f x| := abs_sub _ _
      _ ≤ ‖f‖ + ‖f‖ := add_le_add (abs_le_norm_dense f y) (abs_le_norm_dense f x)
      _ = 2 * ‖f‖ := by ring
  have hsumBound : ∀ y, |u y + v y| ≤ 4 * ‖f‖ := by
    intro y
    exact (abs_add_le (u y) (v y)).trans
      (by linarith only [huBound y, hvBound y])
  have hdecomp : (fun y ↦ u y + v y) = g :=
    streamBallPart_add_streamComplementBallPart f x r
  have hRdecomp := A.analyticMinimalResolventReal_add mu huMeas hvMeas
    huBound hvBound x
  have hRsum : A.analyticMinimalResolventReal mu g
      (f.continuous.measurable.sub measurable_const) hgBound x =
      A.analyticMinimalResolventReal mu u huMeas huBound x +
        A.analyticMinimalResolventReal mu v hvMeas hvBound x := by
    exact (streamAnalyticMinimalResolventReal_congr M omega mu hdecomp.symm
      (f.continuous.measurable.sub measurable_const) (huMeas.add hvMeas)
      hgBound hsumBound x).trans hRdecomp
  have huSmall : ∀ y, |u y| ≤ eps / 2 :=
    abs_streamBallPart_le f x r (eps / 2) (by positivity) hmod
  have huR := A.abs_analyticMinimalResolventReal_le mu huMeas huSmall x
  let c : ℝ := 2 * ‖f‖
  let w : Vec d → ℝ := fun y ↦ c *
    (Metric.ball x r)ᶜ.indicator (fun _ ↦ (1 : ℝ)) y
  have hc : 0 ≤ c := by unfold c; positivity
  have hwMeas : Measurable w :=
    (measurable_complBall x r).const_smul c
  have hw0 : ∀ y, 0 ≤ w y := fun y ↦ mul_nonneg hc (complBall_nonneg x r y)
  have hwBound : ∀ y, |w y| ≤ c := by
    intro y
    change |c * (Metric.ball x r)ᶜ.indicator (fun _ ↦ (1 : ℝ)) y| ≤ c
    rw [abs_mul, abs_of_nonneg hc]
    exact mul_le_of_le_one_right hc (abs_complBall_le_one x r y)
  have hvPoint : ∀ y, |v y| ≤ w y := by
    intro y
    dsimp only [v, w, streamComplementBallPart]
    classical
    by_cases hy : y ∈ Metric.ball x r
    · rw [Set.indicator_of_notMem
          (show y ∉ (Metric.ball x r)ᶜ from fun hyc ↦ hyc hy),
        Set.indicator_of_notMem
          (show y ∉ (Metric.ball x r)ᶜ from fun hyc ↦ hyc hy),
        abs_zero, mul_zero]
    · rw [Set.indicator_of_mem (show y ∈ (Metric.ball x r)ᶜ from hy),
        Set.indicator_of_mem (show y ∈ (Metric.ball x r)ᶜ from hy), mul_one]
      unfold c
      calc
        |f y - f x| ≤ |f y| + |f x| := abs_sub _ _
        _ ≤ ‖f‖ + ‖f‖ :=
          add_le_add (abs_le_norm_dense f y) (abs_le_norm_dense f x)
        _ = 2 * ‖f‖ := by ring
  have hvDomRaw := abs_streamAnalyticMinimalResolventReal_le_toReal_of_abs_le
    M omega mu hvMeas hwMeas hw0 hc hc hvBound hwBound hvPoint x
  have hwResolvent := A.toReal_analyticMinimalResolvent_smul mu hc
    (measurable_complBall x r) (complBall_nonneg x r)
    (by norm_num : (0 : ℝ) ≤ 1) (abs_complBall_le_one x r) x
  have hvDom : |A.analyticMinimalResolventReal mu v hvMeas hvBound x| ≤
      c * (A.analyticMinimalResolvent mu
        ((Metric.ball x r)ᶜ.indicator fun _ ↦ (1 : ℝ))
        (measurable_complBall x r) (abs_complBall_le_one x r) x).toReal := by
    exact hvDomRaw.trans_eq (by simpa only [w] using! hwResolvent)
  have htailAt := mul_toReal_streamAnalyticMinimalResolvent_complBall_le_envelope
    M omega mu hmu x hr hamp hcut
  have hvScaled : (mu : ℝ) *
      |A.analyticMinimalResolventReal mu v hvMeas hvBound x| ≤
      2 * ‖f‖ * streamUniformExhaustionEnvelope M omega
        (Real.sqrt (mu : ℝ) * r) := by
    calc
      (mu : ℝ) * |A.analyticMinimalResolventReal mu v hvMeas hvBound x| ≤
          (mu : ℝ) * (c * (A.analyticMinimalResolvent mu
            ((Metric.ball x r)ᶜ.indicator fun _ ↦ (1 : ℝ))
            (measurable_complBall x r) (abs_complBall_le_one x r) x).toReal) :=
        mul_le_mul_of_nonneg_left hvDom mu.property.le
      _ = 2 * ‖f‖ * ((mu : ℝ) * (A.analyticMinimalResolvent mu
            ((Metric.ball x r)ᶜ.indicator fun _ ↦ (1 : ℝ))
            (measurable_complBall x r) (abs_complBall_le_one x r) x).toReal) := by
        ring
      _ ≤ 2 * ‖f‖ * streamUniformExhaustionEnvelope M omega
          (Real.sqrt (mu : ℝ) * r) :=
        mul_le_mul_of_nonneg_left htailAt (by positivity)
  have hlinear := A.analyticMinimalResolventReal_add mu
    (f := fun y ↦ f y) (g := fun _ : Vec d ↦ -f x)
    f.continuous.measurable measurable_const
    (D := ‖f‖) (E := |f x|) (abs_le_norm_dense f)
    (fun _ ↦ by rw [abs_neg]) x
  have hconst := A.analyticMinimalResolventReal_smul mu (-f x)
    (f := fun _ : Vec d ↦ (1 : ℝ)) measurable_const
    (D := 1) (fun _ ↦ by norm_num) x
  have hidentity : (mu : ℝ) * A.analyticMinimalResolventReal mu g
      (f.continuous.measurable.sub measurable_const) hgBound x =
      (mu : ℝ) * A.analyticMinimalResolventReal mu f
        f.continuous.measurable (abs_le_norm_dense f) x - f x := by
    have hgfun : g = fun y ↦ f y + -f x := by
      funext y
      simp only [g]
      ring
    have hsumBound' : ∀ y, |f y + -f x| ≤ ‖f‖ + |f x| := by
      intro y
      exact (abs_add_le _ _).trans
        (add_le_add (abs_le_norm_dense f y) (by rw [abs_neg]))
    have hRg : A.analyticMinimalResolventReal mu g
        (f.continuous.measurable.sub measurable_const) hgBound x =
        A.analyticMinimalResolventReal mu (fun y ↦ f y + -f x)
          (f.continuous.measurable.add measurable_const) hsumBound' x := by
      subst g
      exact A.analyticMinimalResolventReal_bound_irrel mu
        (f.continuous.measurable.add measurable_const) hgBound hsumBound' x
    have hconst' : A.analyticMinimalResolventReal mu (fun _ : Vec d ↦ -f x)
        measurable_const (D := |f x|) (fun _ ↦ by rw [abs_neg]) x =
        -f x * A.analyticMinimalResolventReal mu (fun _ : Vec d ↦ (1 : ℝ))
          measurable_const (D := 1) (fun _ ↦ by norm_num) x := by
      simpa only [mul_one] using! hconst
    calc
      (mu : ℝ) * A.analyticMinimalResolventReal mu g _ hgBound x =
          (mu : ℝ) * A.analyticMinimalResolventReal mu
            (fun y ↦ f y + -f x) _ hsumBound' x := congrArg ((mu : ℝ) * ·) hRg
      _ = (mu : ℝ) * (A.analyticMinimalResolventReal mu f _
            (abs_le_norm_dense f) x +
          A.analyticMinimalResolventReal mu (fun _ : Vec d ↦ -f x)
            measurable_const (D := |f x|) (fun _ ↦ by rw [abs_neg]) x) :=
        congrArg ((mu : ℝ) * ·) hlinear
      _ = _ := by
        rw [hconst', mul_add]
        calc
          (mu : ℝ) * A.analyticMinimalResolventReal mu f _ _ x +
              (mu : ℝ) * (-f x * A.analyticMinimalResolventReal mu
                (fun _ : Vec d ↦ (1 : ℝ)) _ _ x) =
              (mu : ℝ) * A.analyticMinimalResolventReal mu f _ _ x +
                (-f x) * ((mu : ℝ) * A.analyticMinimalResolventReal mu
                  (fun _ : Vec d ↦ (1 : ℝ)) _ _ x) := by ring
          _ = _ := by rw [mul_streamAnalyticMinimalResolventReal_one_eq M omega mu x]; ring
  rw [← hidentity, hRsum, mul_add]
  calc
    |(mu : ℝ) * A.analyticMinimalResolventReal mu u huMeas huBound x +
        (mu : ℝ) * A.analyticMinimalResolventReal mu v hvMeas hvBound x| ≤
        (mu : ℝ) * |A.analyticMinimalResolventReal mu u huMeas huBound x| +
          (mu : ℝ) * |A.analyticMinimalResolventReal mu v hvMeas hvBound x| := by
      calc
        _ ≤ |(mu : ℝ) * A.analyticMinimalResolventReal mu u huMeas huBound x| +
            |(mu : ℝ) * A.analyticMinimalResolventReal mu v hvMeas hvBound x| :=
          abs_add_le _ _
        _ = _ := by rw [abs_mul, abs_mul, abs_of_pos mu.property]
    _ ≤ eps / 2 + 2 * ‖f‖ * streamUniformExhaustionEnvelope M omega
        (Real.sqrt (mu : ℝ) * r) := by
      exact add_le_add
        (by
          calc
            (mu : ℝ) * |A.analyticMinimalResolventReal mu u huMeas huBound x| ≤
                (mu : ℝ) * (eps / 2 / (mu : ℝ)) :=
              mul_le_mul_of_nonneg_left huR mu.property.le
            _ = eps / 2 := by
              rw [← mul_div_assoc, mul_div_cancel_left₀ _ (ne_of_gt mu.property)])
        hvScaled
    _ < eps := by linarith only [hfar]

private theorem abs_scaled_streamResolvent_le_envelope_of_zero_on_amp
    (M : ABKModel d) (omega : FullSample d M.gamma)
    (mu : PositiveShift) (hmu : 1 ≤ (mu : ℝ))
    (f : C₀(Vec d, ℝ)) (x : Vec d) {r : ℝ} (hr : 0 < r)
    (hcut : streamUniformExhaustionCutoff M omega (mu : ℝ) <
      Real.sqrt (mu : ℝ) * r)
    (hzero : ∀ y ∈ Metric.ball x (streamExhaustionAmp x r), f y = 0) :
    (mu : ℝ) * |(streamWholeSpaceAnalyticData M omega).analyticMinimalResolventReal
        mu f f.continuous.measurable (abs_le_norm_dense f) x| ≤
      ‖f‖ * streamUniformExhaustionEnvelope M omega
        (Real.sqrt (mu : ℝ) * r) := by
  let A := streamWholeSpaceAnalyticData M omega
  let ar := streamExhaustionAmp x r
  let w : Vec d → ℝ := fun y ↦ ‖f‖ *
    (Metric.ball x ar)ᶜ.indicator (fun _ ↦ (1 : ℝ)) y
  have hwMeas : Measurable w := (measurable_complBall x ar).const_smul ‖f‖
  have hw0 : ∀ y, 0 ≤ w y := fun y ↦
    mul_nonneg (norm_nonneg f) (complBall_nonneg x ar y)
  have hwBound : ∀ y, |w y| ≤ ‖f‖ := by
    intro y
    change |‖f‖ * (Metric.ball x ar)ᶜ.indicator (fun _ ↦ (1 : ℝ)) y| ≤ ‖f‖
    rw [abs_mul, abs_of_nonneg (norm_nonneg f)]
    exact mul_le_of_le_one_right (norm_nonneg f) (abs_complBall_le_one x ar y)
  have hfw : ∀ y, |f y| ≤ w y := by
    intro y
    dsimp only [w]
    classical
    by_cases hy : y ∈ Metric.ball x ar
    · rw [hzero y hy, abs_zero,
        Set.indicator_of_notMem (show y ∉ (Metric.ball x ar)ᶜ from fun hyc ↦ hyc hy),
        mul_zero]
    · rw [Set.indicator_of_mem (show y ∈ (Metric.ball x ar)ᶜ from hy), mul_one]
      exact abs_le_norm_dense f y
  have hdom := abs_streamAnalyticMinimalResolventReal_le_toReal_of_abs_le
    M omega mu f.continuous.measurable hwMeas hw0 (norm_nonneg f) (norm_nonneg f)
    (abs_le_norm_dense f) hwBound hfw x
  have hwResolvent := A.toReal_analyticMinimalResolvent_smul mu (norm_nonneg f)
    (measurable_complBall x ar) (complBall_nonneg x ar)
    (by norm_num : (0 : ℝ) ≤ 1) (abs_complBall_le_one x ar) x
  have hdom' : |A.analyticMinimalResolventReal mu f f.continuous.measurable
      (abs_le_norm_dense f) x| ≤ ‖f‖ *
      (A.analyticMinimalResolvent mu
        ((Metric.ball x ar)ᶜ.indicator fun _ ↦ (1 : ℝ))
        (measurable_complBall x ar) (abs_complBall_le_one x ar) x).toReal :=
    hdom.trans_eq (by simpa only [w] using! hwResolvent)
  have htail := mul_toReal_streamAnalyticMinimalResolvent_compl_amp_le_envelope
    M omega mu hmu x hr hcut
  calc
    (mu : ℝ) * |A.analyticMinimalResolventReal mu f _ _ x| ≤
        (mu : ℝ) * (‖f‖ * (A.analyticMinimalResolvent mu
          ((Metric.ball x ar)ᶜ.indicator fun _ ↦ (1 : ℝ))
          (measurable_complBall x ar) (abs_complBall_le_one x ar) x).toReal) :=
      mul_le_mul_of_nonneg_left hdom' mu.property.le
    _ = ‖f‖ * ((mu : ℝ) * (A.analyticMinimalResolvent mu
          ((Metric.ball x ar)ᶜ.indicator fun _ ↦ (1 : ℝ))
          (measurable_complBall x ar) (abs_complBall_le_one x ar) x).toReal) := by
      ring
    _ ≤ ‖f‖ * streamUniformExhaustionEnvelope M omega
        (Real.sqrt (mu : ℝ) * r) :=
      mul_le_mul_of_nonneg_left htail (norm_nonneg f)

/-- On compactly supported `C₀` data, the normalized stream analytic minimal
resolvent converges uniformly to the datum. -/
theorem eventually_forall_abs_mul_streamAnalyticMinimalResolventReal_sub_lt
    (M : ABKModel d) (omega : FullSample d M.gamma)
    (f : C₀(Vec d, ℝ)) (hf : HasCompactSupport f) {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ mu : PositiveShift in atTop, ∀ x : Vec d,
      |(mu : ℝ) * (streamWholeSpaceAnalyticData M omega).analyticMinimalResolventReal
          mu f f.continuous.measurable (abs_le_norm_dense f) x - f x| < eps := by
  obtain ⟨R, hRone, hR⟩ := hf.isBounded.subset_ball_lt 1 (0 : Vec d)
  let B : ℝ := 3 * R + 3
  have hR0 : 0 < R := one_pos.trans hRone
  have hB0 : 0 < B := by unfold B; positivity
  obtain ⟨delta, hdelta, hmodDelta⟩ := Metric.uniformContinuous_iff.mp
    (ZeroAtInftyContinuousMap.uniformContinuous (F := C₀(Vec d, ℝ)) f)
    (eps / 2) (by positivity)
  let r : ℝ := min delta (2 / (1 + B))
  have hdenB : 0 < 1 + B := by linarith only [hB0]
  have hr : 0 < r := lt_min hdelta (div_pos (by norm_num) hdenB)
  have hrDelta : r ≤ delta := min_le_left _ _
  have hrB : r ≤ 2 / (1 + B) := min_le_right _ _
  have hmod : ∀ x y, dist y x < r → |f y - f x| ≤ eps / 2 := by
    intro x y hy
    exact le_of_lt (by
      simpa only [Real.dist_eq] using hmodDelta (hy.trans_le hrDelta))
  have hcut := eventually_streamUniformExhaustionCutoff_lt_sqrt_mul M omega hr
  have henv0 := tendsto_streamUniformExhaustionEnvelope_sqrt_mul M omega hr
  have hscaled : Tendsto (fun mu : PositiveShift ↦
      2 * ‖f‖ * streamUniformExhaustionEnvelope M omega
        (Real.sqrt (mu : ℝ) * r)) atTop (nhds 0) := by
    simpa only [mul_zero] using henv0.const_mul (2 * ‖f‖)
  have henvClose : ∀ᶠ mu : PositiveShift in atTop,
      2 * ‖f‖ * streamUniformExhaustionEnvelope M omega
        (Real.sqrt (mu : ℝ) * r) < eps / 2 := by
    have hevent := (Metric.tendsto_nhds.mp hscaled) (eps / 2) (by positivity)
    filter_upwards [hevent] with mu hmu
    rw [Real.dist_eq, sub_zero, abs_of_nonneg] at hmu
    · exact hmu
    · exact mul_nonneg (mul_nonneg (by norm_num) (norm_nonneg f))
        (mul_nonneg (streamTailAmplitudeConst_nonneg M omega) (Real.exp_pos _).le)
  let oneShift : PositiveShift := ⟨1, Set.mem_Ioi.mpr one_pos⟩
  filter_upwards [eventually_ge_atTop oneShift, hcut, henvClose] with mu hmu hcutMu henvMu
  have hmu1 : 1 ≤ (mu : ℝ) := by exact_mod_cast hmu
  intro x
  by_cases hactive : 4 * streamExhaustionRho x ≤ r
  · have hxB : B ≤ ‖x‖ := by
      by_contra hnot
      have hxlt : ‖x‖ < B := lt_of_not_ge hnot
      have hdenx : 0 < 1 + ‖x‖ := by positivity
      have hinv : 1 / (1 + B) < 1 / (1 + ‖x‖) :=
        one_div_lt_one_div_of_lt hdenx (by linarith only [hxlt])
      have hrho : r < 4 * streamExhaustionRho x := by
        unfold streamExhaustionRho
        change r < 4 / (1 + ‖x‖)
        calc
          r ≤ 2 / (1 + B) := hrB
          _ < 4 / (1 + ‖x‖) := by
            have hleft : 2 / (1 + B) < 2 / (1 + ‖x‖) := by
              simpa only [div_eq_mul_inv, one_mul] using
                mul_lt_mul_of_pos_left hinv (by norm_num : (0 : ℝ) < 2)
            have hright : 2 / (1 + ‖x‖) < 4 / (1 + ‖x‖) :=
              div_lt_div_of_pos_right (by norm_num) hdenx
            exact hleft.trans hright
      exact (not_lt_of_ge hactive) hrho
    have hrTwo : r ≤ 2 := by
      exact hrB.trans ((div_le_iff₀ hdenB).2 (by
        nlinarith only [hB0]))
    have htwoAmp : 2 ≤ 2 / 3 * (1 + ‖x‖) := by
      unfold B at hxB
      nlinarith only [hxB, hR0]
    have hamp : streamExhaustionAmp x r = 2 / 3 * (1 + ‖x‖) := by
      unfold streamExhaustionAmp
      rw [ite_eq_left hactive, max_eq_right (hrTwo.trans htwoAmp)]
    have hxzero : f x = 0 := by
      by_contra hfx
      have hxt : x ∈ tsupport f := subset_closure hfx
      have hxball := hR hxt
      rw [Metric.mem_ball, dist_zero_right] at hxball
      unfold B at hxB
      linarith only [hxB, hxball, hR0]
    have hzero : ∀ y ∈ Metric.ball x (streamExhaustionAmp x r), f y = 0 := by
      intro y hy
      by_contra hfy
      have hyt : y ∈ tsupport f := subset_closure hfy
      have hyball := hR hyt
      rw [Metric.mem_ball, dist_zero_right] at hyball
      have hyDist : dist y x < 2 / 3 * (1 + ‖x‖) := by
        simpa only [Metric.mem_ball, hamp] using hy
      have hreverse : ‖x‖ - ‖y‖ ≤ dist y x := by
        rw [dist_eq_norm, ← norm_neg (y - x), neg_sub]
        exact norm_sub_norm_le x y
      unfold B at hxB
      nlinarith only [hxB, hyball, hyDist, hreverse]
    have hbound := abs_scaled_streamResolvent_le_envelope_of_zero_on_amp
      M omega mu hmu1 f x hr hcutMu hzero
    have henvNonneg : 0 ≤ streamUniformExhaustionEnvelope M omega
        (Real.sqrt (mu : ℝ) * r) := by
      unfold streamUniformExhaustionEnvelope
      exact mul_nonneg (streamTailAmplitudeConst_nonneg M omega) (Real.exp_pos _).le
    rw [hxzero, sub_zero, abs_mul, abs_of_pos mu.property]
    exact hbound.trans_lt (lt_of_le_of_lt
      (mul_le_mul_of_nonneg_right
        (by nlinarith only [norm_nonneg f] : ‖f‖ ≤ 2 * ‖f‖) henvNonneg)
      (henvMu.trans (half_lt_self heps)))
  · have hamp : streamExhaustionAmp x r = r := by
      unfold streamExhaustionAmp
      rw [ite_eq_right hactive]
    exact abs_scaled_streamResolvent_sub_lt_of_amp_eq M omega mu hmu1 f x
      hr heps (hmod x) hamp hcutMu henvMu

omit [NeZero d] in
private theorem exists_streamCompactCore_close (f : C₀(Vec d, ℝ)) {eps : ℝ}
    (heps : 0 < eps) :
    ∃ g : DivergenceFormProcess.FunctionalAnalysis.CompactSupportCore (Vec d),
      ‖DivergenceFormProcess.FunctionalAnalysis.compactSupportCoreToC0 g - f‖ < eps := by
  have hdense :=
    DivergenceFormProcess.FunctionalAnalysis.denseRange_compactSupportCoreToC0
      (X := Vec d)
  change Dense (range
    (DivergenceFormProcess.FunctionalAnalysis.compactSupportCoreToC0 (X := Vec d))) at hdense
  rw [Metric.dense_iff] at hdense
  obtain ⟨g0, hg0, g, rfl⟩ := hdense f eps heps
  exact ⟨g, by simpa only [Metric.mem_ball, dist_eq_norm] using hg0⟩

/-- The stream-field analytic minimal `C₀` resolvent is strongly normalized
at large shifts. -/
theorem tendsto_smul_streamAnalyticMinimalC0Resolvent
    (M : ABKModel d) (omega : FullSample d M.gamma) (f : C₀(Vec d, ℝ)) :
    Tendsto (fun mu : PositiveShift ↦
      (mu : ℝ) • (streamWholeSpaceAnalyticData M omega).analyticMinimalC0ResolventOfVanishing
          (hasVanishing_streamAnalyticMinimalResolvent M omega) mu f)
      atTop (nhds f) := by
  rw [Metric.tendsto_atTop]
  intro eps heps
  let delta : ℝ := eps / 8
  have hdelta : 0 < delta := by unfold delta; positivity
  obtain ⟨g, hgclose⟩ := exists_streamCompactCore_close f hdelta
  let g0 : C₀(Vec d, ℝ) :=
    DivergenceFormProcess.FunctionalAnalysis.compactSupportCoreToC0 g
  have hgcompact : HasCompactSupport g0 := mem_compactlySupported.mp g.property
  have hevent := eventually_forall_abs_mul_streamAnalyticMinimalResolventReal_sub_lt
    M omega g0 hgcompact (by positivity : 0 < eps / 4)
  rw [eventually_atTop] at hevent
  obtain ⟨mu0, hmu0⟩ := hevent
  refine ⟨mu0, fun mu hmu ↦ ?_⟩
  rw [dist_eq_norm, ← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  apply lt_of_le_of_lt ((BoundedContinuousFunction.norm_le (half_pos heps).le).2 ?_)
    (half_lt_self heps)
  intro x
  rw [Real.norm_eq_abs]
  have hclosePoint : ∀ y, |f y - g0 y| ≤ delta := by
    intro y
    have hp := abs_le_norm_dense (g0 - f) y
    have hp' : |g0 y - f y| ≤ ‖g0 - f‖ := by simpa only using! hp
    simpa only [abs_sub_comm] using hp'.trans (le_of_lt (by simpa only [g0] using hgclose))
  let A := streamWholeSpaceAnalyticData M omega
  let uf : ℝ := A.analyticMinimalResolventReal mu f f.continuous.measurable
    (abs_le_norm_dense f) x
  let ug : ℝ := A.analyticMinimalResolventReal mu g0 g0.continuous.measurable
    (abs_le_norm_dense g0) x
  have hstable := A.abs_analyticMinimalResolventReal_sub_le mu
    f.continuous.measurable g0.continuous.measurable
    (abs_le_norm_dense f) (abs_le_norm_dense g0) hclosePoint x
  have hstableScaled : (mu : ℝ) * |uf - ug| ≤ delta := by
    calc
      (mu : ℝ) * |uf - ug| ≤ (mu : ℝ) * (delta / (mu : ℝ)) :=
        mul_le_mul_of_nonneg_left (by simpa only [uf, ug] using! hstable) mu.property.le
      _ = delta := by
        rw [← mul_div_assoc, mul_div_cancel_left₀ _ (ne_of_gt mu.property)]
  have hgApprox : |(mu : ℝ) * ug - g0 x| < eps / 4 := by
    simpa only [ug, A] using hmu0 mu hmu x
  change |(mu : ℝ) * A.analyticMinimalResolventReal mu f
    f.continuous.measurable (abs_le_norm_dense f) x - f x| ≤ eps / 2
  change |(mu : ℝ) * uf - f x| ≤ eps / 2
  apply le_of_lt
  calc
    |(mu : ℝ) * uf - f x| =
        |(mu : ℝ) * (uf - ug) + ((mu : ℝ) * ug - g0 x) + (g0 x - f x)| := by
      congr 1
      ring
    _ ≤ |(mu : ℝ) * (uf - ug)| + |(mu : ℝ) * ug - g0 x| +
        |g0 x - f x| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) (le_refl _))
    _ = (mu : ℝ) * |uf - ug| + |(mu : ℝ) * ug - g0 x| +
        |g0 x - f x| := by rw [abs_mul, abs_of_pos mu.property]
    _ ≤ delta + |(mu : ℝ) * ug - g0 x| + delta :=
      add_le_add (add_le_add hstableScaled (le_refl _))
        (by simpa only [abs_sub_comm] using hclosePoint x)
    _ < delta + eps / 4 + delta :=
      by linarith only [hgApprox]
    _ = eps / 2 := by unfold delta; ring

/-- Every operator in the stream analytic minimal `C₀` resolvent has dense
range. -/
theorem hasDenseRange_streamAnalyticMinimalC0
    (M : ABKModel d) (omega : FullSample d M.gamma) :
    (streamWholeSpaceAnalyticData M omega).HasDenseRangeAnalyticMinimalC0OfVanishing
      (hasVanishing_streamAnalyticMinimalResolvent M omega) := by
  let A := streamWholeSpaceAnalyticData M omega
  apply DivergenceFormProcess.Semigroup.denseRange_of_resolvent_identity_of_tendsto_scaled
    (A.analyticMinimalC0ResolventCLMOfVanishing
      (hasVanishing_streamAnalyticMinimalResolvent M omega))
    (A.analyticMinimalC0ResolventCLMOfVanishing_resolvent_identity
      (hasVanishing_streamAnalyticMinimalResolvent M omega))
  exact tendsto_smul_streamAnalyticMinimalC0Resolvent M omega

/-- The model's split-skew analytic minimal resolver, assembled as a positive
contractive `C₀` resolvent.  Its operator is definitionally the analytic
minimal operator. -/
noncomputable def streamAnalyticMinimalPositiveC0ContractiveResolvent
    (M : ABKModel d) (omega : FullSample d M.gamma) :
    PositiveC0ContractiveResolvent (Vec d) :=
  (streamWholeSpaceAnalyticData M omega).analyticMinimalPositiveC0ContractiveResolventOfVanishing
      (hasVanishing_streamAnalyticMinimalResolvent M omega)
      (hasDenseRange_streamAnalyticMinimalC0 M omega)

@[simp] theorem streamAnalyticMinimalPositiveC0ContractiveResolvent_operator
    (M : ABKModel d) (omega : FullSample d M.gamma)
    (mu : PositiveShift) (f : C₀(Vec d, ℝ)) :
    (streamAnalyticMinimalPositiveC0ContractiveResolvent M omega).toContractiveResolvent.operator
      mu f =
      (streamWholeSpaceAnalyticData M omega).analyticMinimalC0ResolventOfVanishing
          (hasVanishing_streamAnalyticMinimalResolvent M omega) mu f := rfl

end

end Algsuperdiff.Section5.Field
