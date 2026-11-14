/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Corrector.MollifiedPrimitive

/-!
# MollifierConvergence

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Provider: mollification converges in `L²(Ω)` as the radius shrinks

`Algsuperdiff/Section3/Provider/Corrector/Mollification.lean` builds the
smoothing operator `mollify ρ X ω = ∫ ρ(y) • X((-y) +ᵥ ω)` along the stationary
translation action and shows that it stays inside the stationary `L²` layer.
This file supplies the quantitative half needed by part (i) of
`l.approximation.stationary.by.local`: mollification is an approximate identity
on `L²(Ω)`,

`‖mollify ρ X − X‖²_{L²(Ω)} ≤ sup_{|y| < radius ρ} ‖X((−y) + ·) − X‖²_{L²(Ω)}`,

and the right-hand side tends to `0` with the radius because the Koopman orbit
`y ↦ X((−y) + ·)` is `L²`-continuous
(`Algsuperdiff.Probability.Stationary.continuous_koopman_orbit`).

Along the way the file records the elementary algebra of `mollify` (linearity
and equivariance under the translation action) and the identity
`‖f‖²_{L²} = ∫ ‖f‖²`, both of which are also consumed by the gradient
identification of
`Algsuperdiff/Section3/Provider/Corrector/GradientIdentification.lean`.
-/

open MeasureTheory
open HCPolySupport

namespace Algsuperdiff.Section3.Provider.Corrector

noncomputable section

/-! ### The squared `L²` norm as an integral -/

section L2Norm

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The squared norm of an `L²` class is the integral of the squared pointwise
norms of any of its representatives. -/
theorem norm_sq_eq_integral_normSq (f : Lp E 2 μ) :
    ‖f‖ ^ 2 = ∫ ω, ‖f ω‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def (𝕜 := ℝ)]
  exact integral_congr_ae
    (Filter.Eventually.of_forall fun ω => real_inner_self_eq_norm_sq (f ω))

/-- The `L²` energy of a square-integrable function is the squared norm of its
class. -/
theorem integral_normSq_eq_norm_sq_toLp {f : Ω → E} (hf : MemLp f 2 μ) :
    ∫ ω, ‖f ω‖ ^ 2 ∂μ = ‖hf.toLp f‖ ^ 2 := by
  rw [norm_sq_eq_integral_normSq (hf.toLp f)]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp] with ω hω
  rw [hω]

end L2Norm

/-! ### Elementary algebra of the mollification -/

section Algebra

variable {d : ℕ} {Ω : Type*} [AddAction (Vec d) Ω]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Mollification commutes with the translation action: this is the pointwise
form of the fact that the Koopman operators commute with the smoothing. -/
theorem mollify_comp_vadd (κ : Vec d → ℝ) (X : Ω → E) (x : Vec d) (ω : Ω) :
    mollify κ (fun ω' => X (x +ᵥ ω')) ω = mollify κ X (x +ᵥ ω) := by
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  change κ y • X (x +ᵥ ((-y) +ᵥ ω)) = κ y • X ((-y) +ᵥ (x +ᵥ ω))
  rw [vadd_vadd, vadd_vadd, add_comm]

/-- Mollification is additive, given the integrability of the two pieces. -/
theorem mollify_sub {κ : Vec d → ℝ} {X Y : Ω → E} {ω : Ω}
    (hX : Integrable (fun y => κ y • X ((-y) +ᵥ ω)) volume)
    (hY : Integrable (fun y => κ y • Y ((-y) +ᵥ ω)) volume) :
    mollify κ (fun ω' => X ω' - Y ω') ω = mollify κ X ω - mollify κ Y ω := by
  simp only [mollify, smul_sub]
  exact integral_sub hX hY

/-- Mollification is homogeneous. -/
theorem mollify_smul (κ : Vec d → ℝ) (c : ℝ) (X : Ω → E) (ω : Ω) :
    mollify κ (fun ω' => c • X ω') ω = c • mollify κ X ω := by
  simp only [mollify, smul_comm (κ _) c]
  exact integral_smul c _

end Algebra

/-! ### Integrability of the mollification kernel -/

section Integrability

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] [AddAction (Vec d) Ω]
variable {μ : Measure Ω} [SFinite μ]
variable [MeasurableConstVAdd (Vec d) Ω] [MeasurableVAdd₂ (Vec d) Ω]
variable [VAddInvariantMeasure (Vec d) Ω μ]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The integrand of the mollification is integrable for almost every sample. -/
theorem ae_integrable_smul_comp_vadd {κ : Vec d → ℝ} (hκc : Continuous κ)
    (hκi : Integrable κ volume) {X : Ω → E} (hXm : StronglyMeasurable X) (hX : MemLp X 2 μ) :
    ∀ᵐ ω ∂μ, Integrable (fun y => κ y • X ((-y) +ᵥ ω)) volume := by
  filter_upwards [ae_integrable_weighted_realize (μ := μ) (fun y => abs_nonneg (κ y))
    hκc.abs hκi.abs hXm hX] with ω hω
  refine Integrable.mono' hω.2 ?_ (Filter.Eventually.of_forall fun y => ?_)
  · refine (hκc.stronglyMeasurable.smul ?_).aestronglyMeasurable
    exact (hXm.comp_measurable (measurable_vadd_const_sample ω)).comp_measurable measurable_neg
  · rw [norm_smul, Real.norm_eq_abs]

omit [NormedSpace ℝ E] in
/-- Joint integrability of the weighted squared increment of a stationary `L²`
field. -/
theorem integrable_prod_weighted_normSq_sub {w : Vec d → ℝ} (hw0 : ∀ y, 0 ≤ w y)
    (hwc : Continuous w) (hwi : Integrable w volume)
    {X : Ω → E} (hXm : StronglyMeasurable X) (hX : MemLp X 2 μ) :
    Integrable (fun q : Ω × Vec d => w q.2 * ‖X ((-q.2) +ᵥ q.1) - X q.1‖ ^ 2)
      (μ.prod volume) := by
  have hswap : Measurable fun q : Ω × Vec d => (-q.2) +ᵥ q.1 :=
    measurable_vadd_pair_swap.comp (measurable_fst.prodMk measurable_snd.neg)
  have hsq : Integrable (fun ω => ‖X ω‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hX.aestronglyMeasurable).1 hX
  have hA : Integrable (fun q : Ω × Vec d => w q.2 * ‖X ((-q.2) +ᵥ q.1)‖ ^ 2)
      (μ.prod volume) :=
    integrable_prod_weighted_comp_vadd (μ := μ) hwc hwi (hXm.norm.pow 2) hsq
  have hB : Integrable (fun q : Ω × Vec d => ‖X q.1‖ ^ 2 * w q.2) (μ.prod volume) :=
    hsq.mul_prod hwi
  have hdom : Integrable (fun q : Ω × Vec d =>
      2 * (w q.2 * ‖X ((-q.2) +ᵥ q.1)‖ ^ 2) + 2 * (‖X q.1‖ ^ 2 * w q.2)) (μ.prod volume) :=
    (hA.const_mul 2).add (hB.const_mul 2)
  refine Integrable.mono' hdom ?_ ?_
  · refine (((hwc.measurable.comp measurable_snd).stronglyMeasurable).mul ?_).aestronglyMeasurable
    exact (((hXm.comp_measurable hswap).sub (hXm.comp_measurable measurable_fst)).norm).pow 2
  · refine Filter.Eventually.of_forall fun q => ?_
    have h0 := hw0 q.2
    have hnn : 0 ≤ w q.2 * ‖X ((-q.2) +ᵥ q.1) - X q.1‖ ^ 2 := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    have htri : ‖X ((-q.2) +ᵥ q.1) - X q.1‖ ≤ ‖X ((-q.2) +ᵥ q.1)‖ + ‖X q.1‖ :=
      norm_sub_le _ _
    have hns : 0 ≤ ‖X ((-q.2) +ᵥ q.1) - X q.1‖ := norm_nonneg _
    have hsq2 : ‖X ((-q.2) +ᵥ q.1) - X q.1‖ ^ 2
        ≤ 2 * ‖X ((-q.2) +ᵥ q.1)‖ ^ 2 + 2 * ‖X q.1‖ ^ 2 := by
      nlinarith [sq_nonneg (‖X ((-q.2) +ᵥ q.1)‖ - ‖X q.1‖), norm_nonneg (X ((-q.2) +ᵥ q.1)),
        norm_nonneg (X q.1)]
    nlinarith [mul_le_mul_of_nonneg_left hsq2 h0]

omit [NormedSpace ℝ E] in
/-- The weighted increment integrability facts used by the approximate-identity
estimate, for almost every sample. -/
theorem ae_integrable_weighted_normSq_sub {w : Vec d → ℝ} (hw0 : ∀ y, 0 ≤ w y)
    (hwc : Continuous w) (hwi : Integrable w volume)
    {X : Ω → E} (hXm : StronglyMeasurable X) (hX : MemLp X 2 μ) :
    ∀ᵐ ω ∂μ, Integrable (fun y => w y * ‖X ((-y) +ᵥ ω) - X ω‖ ^ 2) volume ∧
      Integrable (fun y => w y * ‖X ((-y) +ᵥ ω) - X ω‖) volume := by
  have hprod := integrable_prod_weighted_normSq_sub (μ := μ) hw0 hwc hwi hXm hX
  filter_upwards [hprod.prod_right_ae] with ω hω
  refine ⟨hω, ?_⟩
  have hdom : Integrable (fun y => (1 / 2 : ℝ) *
      (w y * ‖X ((-y) +ᵥ ω) - X ω‖ ^ 2 + w y)) volume := (hω.add hwi).const_mul _
  refine Integrable.mono' hdom ?_ ?_
  · refine (hwc.stronglyMeasurable.mul ?_).aestronglyMeasurable
    exact ((((hXm.comp_measurable (measurable_vadd_const_sample ω)).comp_measurable
      measurable_neg).sub stronglyMeasurable_const).norm)
  · refine Filter.Eventually.of_forall fun y => ?_
    have h0 := hw0 y
    have hn := norm_nonneg (X ((-y) +ᵥ ω) - X ω)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h0 hn)]
    nlinarith [sq_nonneg (‖X ((-y) +ᵥ ω) - X ω‖ - 1)]

end Integrability

/-! ### The approximate-identity estimate -/

section ApproximateIdentity

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] [AddAction (Vec d) Ω]
variable {μ : Measure Ω} [SFinite μ]
variable [MeasurableConstVAdd (Vec d) Ω] [MeasurableVAdd₂ (Vec d) Ω]
variable [VAddInvariantMeasure (Vec d) Ω μ]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The pointwise Jensen bound behind the approximate-identity estimate. -/
theorem normSq_mollify_sub_le (ρ : Mollifier d)
    {X : Ω → E} (hXm : StronglyMeasurable X) (hX : MemLp X 2 μ) :
    ∀ᵐ ω ∂μ, ‖mollify ρ.toFun X ω - X ω‖ ^ 2
      ≤ ∫ y, ρ.toFun y * ‖X ((-y) +ᵥ ω) - X ω‖ ^ 2 := by
  filter_upwards [ae_integrable_weighted_normSq_sub (μ := μ) ρ.nonneg ρ.continuous ρ.integrable
      hXm hX,
    ae_integrable_smul_comp_vadd (μ := μ) ρ.continuous ρ.integrable hXm hX] with ω hω hint
  have hconst : Integrable (fun y => ρ.toFun y • X ω) volume := ρ.integrable.smul_const (X ω)
  have hrepr : mollify ρ.toFun X ω - X ω
      = ∫ y, ρ.toFun y • (X ((-y) +ᵥ ω) - X ω) := by
    have hsplit : ∫ y, ρ.toFun y • (X ((-y) +ᵥ ω) - X ω)
        = (∫ y, ρ.toFun y • X ((-y) +ᵥ ω)) - ∫ y, ρ.toFun y • X ω := by
      simp only [smul_sub]
      exact integral_sub hint hconst
    rw [hsplit, integral_smul_const, ρ.integral_eq_one, one_smul]
    rfl
  have hb : ‖mollify ρ.toFun X ω - X ω‖ ≤ ∫ y, ρ.toFun y * ‖X ((-y) +ᵥ ω) - X ω‖ := by
    rw [hrepr]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    change ‖ρ.toFun y • (X ((-y) +ᵥ ω) - X ω)‖ = ρ.toFun y * ‖X ((-y) +ᵥ ω) - X ω‖
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (ρ.nonneg y)]
  have hjensen := sq_weighted_integral_le_of_integral_eq_one (ν := (volume : Measure (Vec d)))
    (g := fun y => ‖X ((-y) +ᵥ ω) - X ω‖) ρ.nonneg ρ.integral_eq_one ρ.integrable hω.2 hω.1
  have hnn := norm_nonneg (mollify ρ.toFun X ω - X ω)
  nlinarith [hb, hjensen]

/-- **The approximate-identity estimate.**  If the `L²` increment of the field
under every translation of size below the radius of the mollifier is at most
`ε`, then the mollification differs from the field by at most `ε` in squared
`L²` norm. -/
theorem integral_normSq_mollify_sub_le (ρ : Mollifier d)
    {X : Ω → E} (hXm : StronglyMeasurable X) (hX : MemLp X 2 μ) {ε : ℝ}
    (hsmall : ∀ y : Vec d, ‖y‖ < ρ.radius →
      (∫ ω, ‖X ((-y) +ᵥ ω) - X ω‖ ^ 2 ∂μ) ≤ ε) :
    ∫ ω, ‖mollify ρ.toFun X ω - X ω‖ ^ 2 ∂μ ≤ ε := by
  have hprod := integrable_prod_weighted_normSq_sub (μ := μ) ρ.nonneg ρ.continuous ρ.integrable
    hXm hX
  have hdom : Integrable (fun ω => ∫ y, ρ.toFun y * ‖X ((-y) +ᵥ ω) - X ω‖ ^ 2) μ :=
    hprod.integral_prod_left
  have hswap : ∫ ω, (∫ y, ρ.toFun y * ‖X ((-y) +ᵥ ω) - X ω‖ ^ 2) ∂μ
      = ∫ y, ρ.toFun y * ∫ ω, ‖X ((-y) +ᵥ ω) - X ω‖ ^ 2 ∂μ := by
    rw [integral_integral_swap hprod]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    exact integral_const_mul (ρ.toFun y) fun ω => ‖X ((-y) +ᵥ ω) - X ω‖ ^ 2
  have hstep : ∫ ω, ‖mollify ρ.toFun X ω - X ω‖ ^ 2 ∂μ
      ≤ ∫ ω, (∫ y, ρ.toFun y * ‖X ((-y) +ᵥ ω) - X ω‖ ^ 2) ∂μ := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => by positivity) hdom ?_
    filter_upwards [normSq_mollify_sub_le (μ := μ) ρ hXm hX] with ω hω using hω
  refine hstep.trans ?_
  rw [hswap]
  have hker : ∀ y : Vec d,
      ρ.toFun y * ∫ ω, ‖X ((-y) +ᵥ ω) - X ω‖ ^ 2 ∂μ ≤ ρ.toFun y * ε := by
    intro y
    by_cases hy : ‖y‖ < ρ.radius
    · exact mul_le_mul_of_nonneg_left (hsmall y hy) (ρ.nonneg y)
    · have hzero : ρ.toFun y = 0 := by
        by_contra hne
        have : y ∈ Metric.ball (0 : Vec d) ρ.radius := ρ.support_subset hne
        exact hy (by simpa [dist_eq_norm] using Metric.mem_ball.1 this)
      simp [hzero]
  have hintl : Integrable (fun y => ρ.toFun y * ∫ ω, ‖X ((-y) +ᵥ ω) - X ω‖ ^ 2 ∂μ) volume := by
    have h := hprod.integral_prod_right
    refine h.congr (Filter.Eventually.of_forall fun y => ?_)
    exact integral_const_mul (ρ.toFun y) fun ω => ‖X ((-y) +ᵥ ω) - X ω‖ ^ 2
  have hintr : Integrable (fun y => ρ.toFun y * ε) volume := ρ.integrable.mul_const ε
  calc ∫ y, ρ.toFun y * ∫ ω, ‖X ((-y) +ᵥ ω) - X ω‖ ^ 2 ∂μ
      ≤ ∫ y, ρ.toFun y * ε := integral_mono hintl hintr hker
    _ = ε := by rw [integral_mul_const, ρ.integral_eq_one, one_mul]

end ApproximateIdentity

/-! ### `L²` continuity of the translation action -/

section Continuity

open Algsuperdiff.Probability.Stationary

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] [AddAction (Vec d) Ω]
variable {μ : Measure Ω} [SFinite μ]
variable [MeasurableConstVAdd (Vec d) Ω] [MeasurableVAdd₂ (Vec d) Ω]
variable [VAddInvariantMeasure (Vec d) Ω μ]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [SFinite μ] [MeasurableVAdd₂ (Vec d) Ω] in
/-- The Koopman translate of an `L²` class is represented by the translated
representative. -/
theorem coeFn_koopman_toLp {X : Ω → E} (hX : MemLp X 2 μ) (x : Vec d) :
    ∀ᵐ ω ∂μ, (koopman (μ := μ) x (hX.toLp X)) ω = X (x +ᵥ ω) := by
  have hshift : ∀ᵐ ω ∂μ, (hX.toLp X) (x +ᵥ ω) = X (x +ᵥ ω) :=
    (measurePreserving_const_vadd (μ := μ) x).quasiMeasurePreserving.ae hX.coeFn_toLp
  filter_upwards [Lp.coeFn_compMeasurePreserving (E := E) (p := 2) (hX.toLp X)
    (measurePreserving_const_vadd (μ := μ) x), hshift] with ω h1 h2
  exact h1.trans h2

omit [SFinite μ] [MeasurableVAdd₂ (Vec d) Ω] in
/-- The `L²` increment of a stationary field under a translation is the squared
distance travelled by the Koopman orbit. -/
theorem integral_normSq_translate_eq {X : Ω → E} (hX : MemLp X 2 μ) (y : Vec d) :
    ∫ ω, ‖X ((-y) +ᵥ ω) - X ω‖ ^ 2 ∂μ
      = ‖koopman (μ := μ) (-y) (hX.toLp X) - hX.toLp X‖ ^ 2 := by
  rw [norm_sq_eq_integral_normSq]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_sub (koopman (μ := μ) (-y) (hX.toLp X)) (hX.toLp X),
    coeFn_koopman_toLp hX (-y), hX.coeFn_toLp] with ω h1 h2 h3
  rw [h1]
  simp only [Pi.sub_apply]
  rw [h2, h3]

section ContinuousAction

variable [TopologicalSpace Ω] [R1Space Ω] [BorelSpace Ω] [ContinuousVAdd (Vec d) Ω]
variable [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop]

omit [SFinite μ] [MeasurableVAdd₂ (Vec d) Ω] in
/-- **The `L²` modulus of continuity of the translation action is continuous.**
This is the only place where the `ContinuousAction`-style carrier hypotheses of
`Algsuperdiff/Probability/StationaryProjection.lean` are used. -/
theorem continuous_integral_normSq_translate {X : Ω → E} (hX : MemLp X 2 μ) :
    Continuous fun y : Vec d => ∫ ω, ‖X ((-y) +ᵥ ω) - X ω‖ ^ 2 ∂μ := by
  have hcont : Continuous fun y : Vec d => koopman (μ := μ) (-y) (hX.toLp X) :=
    (continuous_koopman_orbit (μ := μ) (hX.toLp X)).comp continuous_neg
  have h : Continuous fun y : Vec d =>
      ‖koopman (μ := μ) (-y) (hX.toLp X) - hX.toLp X‖ ^ 2 :=
    ((hcont.sub continuous_const).norm).pow 2
  refine h.congr fun y => ?_
  exact (integral_normSq_translate_eq hX y).symm

variable [CompleteSpace E]

/-- **Mollification is an approximate identity on `L²(Ω)`.**  For every
tolerance there is a radius at which the mollification of a stationary `L²`
field differs from it by at most that tolerance in squared `L²` norm. -/
theorem exists_radius_integral_normSq_mollify_sub_le
    {X : Ω → E} (hXm : StronglyMeasurable X) (hX : MemLp X 2 μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, ∃ hr : 0 < r,
      ∫ ω, ‖mollify (Mollifier.ofRadius d hr).toFun X ω - X ω‖ ^ 2 ∂μ ≤ ε := by
  have hcont : ContinuousAt (fun y : Vec d => ∫ ω, ‖X ((-y) +ᵥ ω) - X ω‖ ^ 2 ∂μ) 0 :=
    (continuous_integral_normSq_translate (μ := μ) hX).continuousAt
  have hzero : (∫ ω, ‖X ((-(0 : Vec d)) +ᵥ ω) - X ω‖ ^ 2 ∂μ) = 0 := by simp
  rw [Metric.continuousAt_iff] at hcont
  rw [hzero] at hcont
  obtain ⟨r, hr, hball⟩ := hcont ε hε
  refine ⟨r, hr, ?_⟩
  refine integral_normSq_mollify_sub_le (μ := μ) (Mollifier.ofRadius d hr) hXm hX ?_
  intro y hy
  have hy' : dist y (0 : Vec d) < r := by
    rw [dist_eq_norm, sub_zero]
    exact hy
  have := hball hy'
  rw [Real.dist_eq, sub_zero] at this
  exact (le_abs_self _).trans this.le

end ContinuousAction

end Continuity

end

end Algsuperdiff.Section3.Provider.Corrector
