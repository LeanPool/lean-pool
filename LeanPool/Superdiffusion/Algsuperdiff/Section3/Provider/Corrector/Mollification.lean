/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Corrector.StationaryStrip
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Convolution

/-!
# Mollification

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Provider: mollification along the stationary translation action

The cutoff core of part (i) of `l.approximation.stationary.by.local`
(`Algsuperdiff/Section3/Provider/Corrector/PotentialApproximation.lean`, ABK26)
consumes a stationary field `p` together with a stationary square-integrable
primitive `φ` whose spatial realizations are *smooth* and satisfy `∇(realize φ
ω) = realize p ω`.

This file builds the smoothing operator that produces such primitives.  For a
mollifier `ρ ∈ C_c^∞(ℝᵈ)` and a stationary field `X` on the abstract carrier
`Ω` it defines

`mollify ρ X ω := ∫ y, ρ y • X ((-y) +ᵥ ω)`,

and proves the two facts that make it useful:

* `realize_mollify`: the spatial realization of `mollify ρ X` is the honest
  convolution `ρ ⋆ realize X ω` (this is the point of the sign convention
  `(-y) +ᵥ ω`), so the smoothness of a realization is that of a convolution
  against `ρ`, and every `L²` field has locally integrable realizations for
  almost every sample (`ae_locallyIntegrable_realize`);
* `memLp_two_mollify`: mollification does not leave the stationary `L²` layer.

Nothing here uses the potential structure; the file is a pure smoothing
toolkit over the abstract stationary carrier of
`Algsuperdiff/Probability/StationaryProjection.lean`.
-/

open MeasureTheory
open HCPolySupport

namespace Algsuperdiff.Section3.Provider.Corrector

noncomputable section

/-! ### A weighted Cauchy-Schwarz inequality -/

/-- Cauchy-Schwarz against a probability density: for a weight `ρ ≥ 0` of unit
mass, the square of the weighted mean is at most the weighted mean of the
square. -/
theorem sq_weighted_integral_le {α : Type*} [MeasurableSpace α] {ν : Measure α}
    {ρ g : α → ℝ} (hρ0 : ∀ a, 0 ≤ ρ a)
    (hρ : Integrable ρ ν) (h1 : Integrable (fun a => ρ a * g a) ν)
    (h2 : Integrable (fun a => ρ a * g a ^ 2) ν) :
    (∫ a, ρ a * g a ∂ν) ^ 2 ≤ (∫ a, ρ a ∂ν) * ∫ a, ρ a * g a ^ 2 ∂ν := by
  have hexp : ∀ c : ℝ, ∫ a, ρ a * (g a - c) ^ 2 ∂ν
      = ((∫ a, ρ a * g a ^ 2 ∂ν) - 2 * c * ∫ a, ρ a * g a ∂ν) + c ^ 2 * ∫ a, ρ a ∂ν := by
    intro c
    have hpt : ∀ a, ρ a * (g a - c) ^ 2
        = ρ a * g a ^ 2 - 2 * c * (ρ a * g a) + c ^ 2 * ρ a := by
      intro a; ring
    have hmul1 : Integrable (fun a => 2 * c * (ρ a * g a)) ν := h1.const_mul (2 * c)
    have hmul2 : Integrable (fun a => c ^ 2 * ρ a) ν := hρ.const_mul (c ^ 2)
    have hA : Integrable (fun a => ρ a * g a ^ 2 - 2 * c * (ρ a * g a)) ν := h2.sub hmul1
    calc ∫ a, ρ a * (g a - c) ^ 2 ∂ν
        = ∫ a, ((ρ a * g a ^ 2 - 2 * c * (ρ a * g a)) + c ^ 2 * ρ a) ∂ν := by
          simp only [hpt]
      _ = (∫ a, (ρ a * g a ^ 2 - 2 * c * (ρ a * g a)) ∂ν) + ∫ a, c ^ 2 * ρ a ∂ν :=
          integral_add hA hmul2
      _ = ((∫ a, ρ a * g a ^ 2 ∂ν) - 2 * c * ∫ a, ρ a * g a ∂ν) + c ^ 2 * ∫ a, ρ a ∂ν := by
          rw [integral_sub h2 hmul1, integral_const_mul, integral_const_mul]
  have hquad : ∀ c : ℝ, 0 ≤ (∫ a, ρ a ∂ν) * (c * c)
      + (-2 * ∫ a, ρ a * g a ∂ν) * c + ∫ a, ρ a * g a ^ 2 ∂ν := by
    intro c
    have hnn : 0 ≤ ∫ a, ρ a * (g a - c) ^ 2 ∂ν :=
      integral_nonneg fun a => mul_nonneg (hρ0 a) (sq_nonneg _)
    rw [hexp c] at hnn
    nlinarith [hnn]
  have hdisc := discrim_le_zero hquad
  rw [discrim] at hdisc
  nlinarith [hdisc]

/-- The normalized form of `sq_weighted_integral_le` for a probability density. -/
theorem sq_weighted_integral_le_of_integral_eq_one {α : Type*} [MeasurableSpace α]
    {ν : Measure α} {ρ g : α → ℝ} (hρ0 : ∀ a, 0 ≤ ρ a) (hρ1 : ∫ a, ρ a ∂ν = 1)
    (hρ : Integrable ρ ν) (h1 : Integrable (fun a => ρ a * g a) ν)
    (h2 : Integrable (fun a => ρ a * g a ^ 2) ν) :
    (∫ a, ρ a * g a ∂ν) ^ 2 ≤ ∫ a, ρ a * g a ^ 2 ∂ν := by
  have h := sq_weighted_integral_le hρ0 hρ h1 h2
  rwa [hρ1, one_mul] at h

/-! ### Mollifiers -/

/-- A smooth compactly supported probability density on `ℝᵈ`, supported in the
ball of radius `radius` about the origin.  This is the kernel `ρ` of the
mollification below. -/
structure Mollifier (d : ℕ) where
  /-- The density itself. -/
  toFun : Vec d → ℝ
  /-- The scale of the mollifier: the density vanishes outside `B_radius(0)`. -/
  radius : ℝ
  /-- The density is nonnegative. -/
  nonneg : ∀ y, 0 ≤ toFun y
  /-- The density is smooth. -/
  smooth : ContDiff ℝ (⊤ : ℕ∞) toFun
  /-- The density is compactly supported. -/
  compactSupport : HasCompactSupport toFun
  /-- The density has unit mass. -/
  integral_eq_one : ∫ y, toFun y = 1
  /-- The density is supported in the ball of radius `radius`. -/
  support_subset : Function.support toFun ⊆ Metric.ball 0 radius

namespace Mollifier

variable {d : ℕ}

theorem continuous (ρ : Mollifier d) : Continuous ρ.toFun := ρ.smooth.continuous

theorem integrable (ρ : Mollifier d) : Integrable ρ.toFun volume :=
  ρ.continuous.integrable_of_hasCompactSupport ρ.compactSupport

/-- The standard mollifier at a positive scale, built from Mathlib's smooth
bump functions. -/
def ofRadius (d : ℕ) {r : ℝ} (hr : 0 < r) : Mollifier d where
  toFun := (ContDiffBump.mk (c := (0 : Vec d)) (r / 2) r (by linarith) (by linarith)).normed volume
  radius := r
  nonneg := fun y => ContDiffBump.nonneg_normed _ y
  smooth := ContDiffBump.contDiff_normed _
  compactSupport := ContDiffBump.hasCompactSupport_normed _
  integral_eq_one := ContDiffBump.integral_normed _
  support_subset := le_of_eq (ContDiffBump.support_normed_eq _)

end Mollifier

/-! ### Mollification of a stationary field -/

section Mollify

variable {d : ℕ} {Ω : Type*} [AddAction (Vec d) Ω]

/-- Mollification of a stationary field along the translation action.  The sign
convention `(-y) +ᵥ ω` is chosen so that the spatial realization is literally
the convolution `ρ ⋆ realize X ω` (`realize_mollify`). -/
def mollify {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ρ : Vec d → ℝ) (X : Ω → E) (ω : Ω) : E :=
  ∫ y, ρ y • X ((-y) +ᵥ ω)

/-- **The realization of a mollified field is a convolution.** -/
theorem realize_mollify {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ρ : Vec d → ℝ) (X : Ω → E) (ω : Ω) :
    realize (d := d) (mollify ρ X) ω
      = convolution ρ (realize (d := d) X ω) (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
  funext x
  have hshift : ∀ y : Vec d, (-y) +ᵥ (x +ᵥ ω) = (x - y) +ᵥ ω := by
    intro y
    rw [vadd_vadd, neg_add_eq_sub]
  simp only [realize, mollify, convolution_def, ContinuousLinearMap.lsmul_apply, hshift]

end Mollify

/-! ### Local integrability of realizations -/

section LocallyIntegrable

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] [AddAction (Vec d) Ω]
variable {μ : Measure Ω} [SFinite μ]
variable [MeasurableConstVAdd (Vec d) Ω] [MeasurableVAdd₂ (Vec d) Ω]
variable [VAddInvariantMeasure (Vec d) Ω μ]

/-- For almost every sample, the spatial realization of a stationary `L²` field
is locally integrable.  This is the hypothesis of the convolution smoothness
theorems. -/
theorem ae_locallyIntegrable_realize {E : Type*} [NormedAddCommGroup E]
    {X : Ω → E} (hXm : StronglyMeasurable X) (hX : MemLp X 2 μ) :
    ∀ᵐ ω ∂μ, LocallyIntegrable (realize (d := d) X ω) volume := by
  have hball : ∀ n : ℕ, volume (Metric.closedBall (0 : Vec d) (n : ℝ)) ≠ ⊤ := fun n =>
    (isCompact_closedBall (0 : Vec d) (n : ℝ)).measure_lt_top.ne
  have hae : ∀ n : ℕ, ∀ᵐ ω ∂μ,
      MemLp (realize (d := d) X ω) 2 (volume.restrict (Metric.closedBall (0 : Vec d) (n : ℝ))) :=
    fun n => ae_memLp_two_realize (μ := μ) (hball n) hXm hX
  rw [← ae_all_iff] at hae
  filter_upwards [hae] with ω hω
  intro x
  obtain ⟨n, hn⟩ := exists_nat_gt (‖x‖ + 1)
  have : IsFiniteMeasure (volume.restrict (Metric.closedBall (0 : Vec d) (n : ℝ))) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.2 (hball n)
  have hint : IntegrableOn (realize (d := d) X ω) (Metric.closedBall (0 : Vec d) (n : ℝ)) volume :=
    (hω n).integrable (by norm_num)
  refine ⟨Metric.ball x 1, Metric.ball_mem_nhds x one_pos, hint.mono_set ?_⟩
  intro z hz
  have hz1 : dist z x < 1 := Metric.mem_ball.1 hz
  have : ‖z‖ ≤ ‖x‖ + 1 := by
    have := norm_sub_norm_le z x
    have hd : ‖z - x‖ < 1 := by rwa [← dist_eq_norm]
    linarith
  exact Metric.mem_closedBall.2 (by
    rw [dist_eq_norm, sub_zero]
    linarith)

end LocallyIntegrable

section Smooth

variable {d : ℕ} {Ω : Type*} [AddAction (Vec d) Ω]

end Smooth

/-! ### Mollification preserves the stationary `L²` layer -/

section Lp

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] [AddAction (Vec d) Ω]
variable {μ : Measure Ω} [SFinite μ]
variable [MeasurableConstVAdd (Vec d) Ω] [MeasurableVAdd₂ (Vec d) Ω]
variable [VAddInvariantMeasure (Vec d) Ω μ]

omit [MeasurableConstVAdd (Vec d) Ω] [VAddInvariantMeasure (Vec d) Ω μ] in
/-- The mollification of a measurable field is measurable. -/
theorem stronglyMeasurable_mollify {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ρ : Vec d → ℝ} (hρ : Continuous ρ) {X : Ω → E} (hX : StronglyMeasurable X) :
    StronglyMeasurable (mollify (Ω := Ω) ρ X) := by
  have hmeas : Measurable fun q : Ω × Vec d => (-q.2) +ᵥ q.1 :=
    measurable_vadd_pair_swap.comp (measurable_fst.prodMk measurable_snd.neg)
  have hjm : StronglyMeasurable fun q : Ω × Vec d => ρ q.2 • X ((-q.2) +ᵥ q.1) :=
    ((hρ.measurable.comp measurable_snd).stronglyMeasurable).smul (hX.comp_measurable hmeas)
  exact hjm.integral_prod_right'

/-- Joint integrability of `(ω, y) ↦ ρ y · g((-y) +ᵥ ω)` for an integrable
weight `ρ` and an integrable stationary observable `g`. -/
theorem integrable_prod_weighted_comp_vadd {ρ : Vec d → ℝ} (hρm : Continuous ρ)
    (hρ : Integrable ρ volume) {g : Ω → ℝ} (hgm : StronglyMeasurable g)
    (hg : Integrable g μ) :
    Integrable (fun q : Ω × Vec d => ρ q.2 * g ((-q.2) +ᵥ q.1)) (μ.prod volume) := by
  have hmeas : Measurable fun q : Ω × Vec d => (-q.2) +ᵥ q.1 :=
    measurable_vadd_pair_swap.comp (measurable_fst.prodMk measurable_snd.neg)
  have hjm : StronglyMeasurable fun q : Ω × Vec d => ρ q.2 * g ((-q.2) +ᵥ q.1) :=
    ((hρm.measurable.comp measurable_snd).stronglyMeasurable).mul (hgm.comp_measurable hmeas)
  refine (integrable_prod_iff' hjm.aestronglyMeasurable).2 ⟨?_, ?_⟩
  · exact Filter.Eventually.of_forall fun y =>
      (integrable_comp_const_vadd hg (-y)).const_mul (ρ y)
  · have hval : ∀ y : Vec d, (∫ ω, ‖ρ y * g ((-y) +ᵥ ω)‖ ∂μ) = |ρ y| * ∫ ω, ‖g ω‖ ∂μ := by
      intro y
      simp only [norm_mul, Real.norm_eq_abs]
      rw [integral_const_mul]
      exact congrArg (fun t => |ρ y| * t) (integral_comp_const_vadd (fun ω => |g ω|) (-y))
    refine (integrable_congr (Filter.Eventually.of_forall hval)).2 ?_
    exact hρ.abs.mul_const _

/-- Almost every sample admits the two weighted integrability facts used by the
`L²` bound on a mollification. -/
theorem ae_integrable_weighted_realize {E : Type*} [NormedAddCommGroup E]
    {w : Vec d → ℝ} (hw0 : ∀ y, 0 ≤ w y) (hwc : Continuous w) (hwi : Integrable w volume)
    {X : Ω → E} (hXm : StronglyMeasurable X) (hX : MemLp X 2 μ) :
    ∀ᵐ ω ∂μ, Integrable (fun y => w y * ‖X ((-y) +ᵥ ω)‖ ^ 2) volume ∧
      Integrable (fun y => w y * ‖X ((-y) +ᵥ ω)‖) volume := by
  have hnormsq : StronglyMeasurable fun ω => ‖X ω‖ ^ 2 := hXm.norm.pow 2
  have hsq : Integrable (fun ω => ‖X ω‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hX.aestronglyMeasurable).1 hX
  have hprod := integrable_prod_weighted_comp_vadd (μ := μ) hwc hwi hnormsq hsq
  filter_upwards [hprod.prod_right_ae] with ω hω
  refine ⟨hω, ?_⟩
  have hsum : Integrable
      (fun y => w y * ‖X ((-y) +ᵥ ω)‖ ^ 2 + w y) volume := hω.add hwi
  have hdom : Integrable
      (fun y => (1 / 2 : ℝ) * (w y * ‖X ((-y) +ᵥ ω)‖ ^ 2 + w y)) volume :=
    hsum.const_mul _
  refine Integrable.mono' hdom ?_ ?_
  · exact ((hwc.stronglyMeasurable).mul
      (((hXm.comp_measurable (measurable_vadd_const_sample ω)).comp_measurable
        measurable_neg).norm)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun y => ?_
    have h0 := hw0 y
    have hn := norm_nonneg (X ((-y) +ᵥ ω))
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h0 hn)]
    nlinarith [sq_nonneg (‖X ((-y) +ᵥ ω)‖ - 1)]

/-- The pointwise square bound behind the `L²` estimates on a mollification. -/
theorem normSq_mollify_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {κ : Vec d → ℝ} (hκc : Continuous κ) (hκi : Integrable κ volume)
    {X : Ω → E} (hXm : StronglyMeasurable X) (hX : MemLp X 2 μ) :
    ∀ᵐ ω ∂μ, ‖mollify κ X ω‖ ^ 2
      ≤ (∫ y, |κ y|) * ∫ y, |κ y| * ‖X ((-y) +ᵥ ω)‖ ^ 2 := by
  filter_upwards [ae_integrable_weighted_realize (μ := μ) (fun y => abs_nonneg (κ y))
    hκc.abs hκi.abs hXm hX] with ω hω
  have hb : ‖mollify κ X ω‖ ≤ ∫ y, |κ y| * ‖X ((-y) +ᵥ ω)‖ := by
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [norm_smul, Real.norm_eq_abs]
  have hjensen := sq_weighted_integral_le (ν := (volume : Measure (Vec d)))
    (g := fun y => ‖X ((-y) +ᵥ ω)‖) (fun y => abs_nonneg (κ y)) hκi.abs hω.2 hω.1
  calc ‖mollify κ X ω‖ ^ 2
      ≤ (∫ y, |κ y| * ‖X ((-y) +ᵥ ω)‖) ^ 2 := by
        have := norm_nonneg (mollify κ X ω)
        nlinarith [hb]
    _ ≤ (∫ y, |κ y|) * ∫ y, |κ y| * ‖X ((-y) +ᵥ ω)‖ ^ 2 := hjensen

/-- **Mollification preserves the stationary `L²` layer.** -/
theorem memLp_two_mollify {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {κ : Vec d → ℝ} (hκc : Continuous κ) (hκi : Integrable κ volume)
    {X : Ω → E} (hXm : StronglyMeasurable X) (hX : MemLp X 2 μ) :
    MemLp (mollify κ X) 2 μ := by
  have hsm := stronglyMeasurable_mollify hκc hXm
  have hnormsq : StronglyMeasurable fun ω => ‖X ω‖ ^ 2 := hXm.norm.pow 2
  have hsq : Integrable (fun ω => ‖X ω‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hX.aestronglyMeasurable).1 hX
  have hprod := integrable_prod_weighted_comp_vadd (μ := μ) hκc.abs hκi.abs hnormsq hsq
  have hdom : Integrable (fun ω => (∫ y, |κ y|) * ∫ y, |κ y| * ‖X ((-y) +ᵥ ω)‖ ^ 2) μ :=
    hprod.integral_prod_left.const_mul _
  refine (memLp_two_iff_integrable_sq_norm hsm.aestronglyMeasurable).2 ?_
  refine Integrable.mono' hdom (hsm.norm.pow 2).aestronglyMeasurable ?_
  filter_upwards [normSq_mollify_le (μ := μ) hκc hκi hXm hX] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact hω

/-- **The `L²` contraction estimate for mollification**: the mollification by a
kernel of total mass `‖κ‖₁` has `L²` norm at most `‖κ‖₁` times that of the
field.  For a `Mollifier` the factor is `1`. -/
theorem integral_normSq_mollify_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {κ : Vec d → ℝ} (hκc : Continuous κ) (hκi : Integrable κ volume)
    {X : Ω → E} (hXm : StronglyMeasurable X) (hX : MemLp X 2 μ) :
    ∫ ω, ‖mollify κ X ω‖ ^ 2 ∂μ ≤ (∫ y, |κ y|) ^ 2 * ∫ ω, ‖X ω‖ ^ 2 ∂μ := by
  have hnormsq : StronglyMeasurable fun ω => ‖X ω‖ ^ 2 := hXm.norm.pow 2
  have hsq : Integrable (fun ω => ‖X ω‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hX.aestronglyMeasurable).1 hX
  have hprod := integrable_prod_weighted_comp_vadd (μ := μ) hκc.abs hκi.abs hnormsq hsq
  have hdom : Integrable (fun ω => (∫ y, |κ y|) * ∫ y, |κ y| * ‖X ((-y) +ᵥ ω)‖ ^ 2) μ :=
    hprod.integral_prod_left.const_mul _
  have hswap : ∫ ω, (∫ y, |κ y| * ‖X ((-y) +ᵥ ω)‖ ^ 2) ∂μ
      = (∫ y, |κ y|) * ∫ ω, ‖X ω‖ ^ 2 ∂μ := by
    calc ∫ ω, (∫ y, |κ y| * ‖X ((-y) +ᵥ ω)‖ ^ 2) ∂μ
        = ∫ y, (∫ ω, |κ y| * ‖X ((-y) +ᵥ ω)‖ ^ 2 ∂μ) := integral_integral_swap hprod
      _ = ∫ y, |κ y| * ∫ ω, ‖X ω‖ ^ 2 ∂μ := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
          show ∫ ω, |κ y| * ‖X ((-y) +ᵥ ω)‖ ^ 2 ∂μ = |κ y| * ∫ ω, ‖X ω‖ ^ 2 ∂μ
          rw [integral_const_mul]
          exact congrArg (fun t => |κ y| * t)
            (integral_comp_const_vadd (fun ω => ‖X ω‖ ^ 2) (-y))
      _ = (∫ y, |κ y|) * ∫ ω, ‖X ω‖ ^ 2 ∂μ := by
          rw [integral_mul_const]
  calc ∫ ω, ‖mollify κ X ω‖ ^ 2 ∂μ
      ≤ ∫ ω, (∫ y, |κ y|) * (∫ y, |κ y| * ‖X ((-y) +ᵥ ω)‖ ^ 2) ∂μ := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => by positivity)
          hdom ?_
        filter_upwards [normSq_mollify_le (μ := μ) hκc hκi hXm hX] with ω hω using hω
    _ = (∫ y, |κ y|) ^ 2 * ∫ ω, ‖X ω‖ ^ 2 ∂μ := by
        rw [integral_const_mul, hswap]
        ring

end Lp

end

end Algsuperdiff.Section3.Provider.Corrector
