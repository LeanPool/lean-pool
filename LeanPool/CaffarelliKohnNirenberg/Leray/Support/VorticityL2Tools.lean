/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.VorticityMollifiedIdentities
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Vec3Norm

/-!
# `L²` bookkeeping for the vorticity bootstrap

Conversions between `L²` seminorms and integrals of squares, convergence of integrals of squares,
Fubini in the time-outer order on space-time boxes, integrability of smooth functions on bounded
sets, the linearity of the coordinate derivatives on smooth functions, and the geometry of the
backward kernel balls used in `thm:vorticity-regularity` of the Escauriaza–Seregin–Šverák manuscript.
-/

public section

open Filter Function MeasureTheory Set Topology
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN

/-- The `L²` seminorm of a square-integrable function is the square root of the integral of its
square. -/
theorem vorticity_eLpNorm_two_eq_sqrt {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (hf : MemLp f 2 μ) :
    eLpNorm f 2 μ = ENNReal.ofReal (Real.sqrt (∫ x, f x ^ 2 ∂μ)) := by
  rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  congr 1
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [h2, Real.sqrt_eq_rpow, show (2 : ℝ)⁻¹ = 1 / 2 by norm_num]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  rw [Real.norm_eq_abs, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]

/-- The integral of the square of a square-integrable function is the square of its norm. -/
theorem vorticity_integral_sq_eq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (hf : MemLp f 2 μ) :
    ∫ x, f x ^ 2 ∂μ = (eLpNorm f 2 μ).toReal ^ 2 := by
  rw [vorticity_eLpNorm_two_eq_sqrt hf, ENNReal.toReal_ofReal (Real.sqrt_nonneg _),
    Real.sq_sqrt (integral_nonneg fun x => sq_nonneg (f x))]

/-- Integrals of squares tending to zero give `L²` convergence to zero. -/
theorem vorticity_tendsto_eLpNorm_of_integral_sq {α ι : Type*} [MeasurableSpace α]
    {μ : Measure α} {l : Filter ι} {f : ι → α → ℝ} (hf : ∀ i, MemLp (f i) 2 μ)
    (h : Tendsto (fun i => ∫ x, f i x ^ 2 ∂μ) l (𝓝 0)) :
    Tendsto (fun i => eLpNorm (f i) 2 μ) l (𝓝 0) := by
  have hcont : Tendsto (fun i => ENNReal.ofReal (Real.sqrt (∫ x, f i x ^ 2 ∂μ))) l
      (𝓝 (ENNReal.ofReal (Real.sqrt 0))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp ((Real.continuous_sqrt.tendsto 0).comp h)
  rw [Real.sqrt_zero, ENNReal.ofReal_zero] at hcont
  exact hcont.congr fun i => (vorticity_eLpNorm_two_eq_sqrt (hf i)).symm

/-- `L²` convergence to zero gives integrals of squares tending to zero. -/
theorem vorticity_integral_sq_tendsto_zero {α ι : Type*} [MeasurableSpace α]
    {μ : Measure α} {l : Filter ι} {f : ι → α → ℝ} (hf : ∀ i, MemLp (f i) 2 μ)
    (h : Tendsto (fun i => eLpNorm (f i) 2 μ) l (𝓝 0)) :
    Tendsto (fun i => ∫ x, f i x ^ 2 ∂μ) l (𝓝 0) := by
  have hreal := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h)
  have hsq := (continuous_pow 2).tendsto _ |>.comp hreal
  simp only [ENNReal.toReal_zero, Function.comp_def] at hsq
  rw [show ((0 : ℝ) ^ 2) = 0 by norm_num] at hsq
  exact hsq.congr fun i => (vorticity_integral_sq_eq (hf i)).symm

/-- Integrals of squares are continuous along `L²` convergence. -/
theorem vorticity_tendsto_integral_sq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : ℕ → α → ℝ} {g : α → ℝ} (hf : ∀ n, MemLp (f n) 2 μ) (hg : MemLp g 2 μ)
    (h : Tendsto (fun n => eLpNorm (f n - g) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, f n x ^ 2 ∂μ) atTop (𝓝 (∫ x, g x ^ 2 ∂μ)) := by
  have : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  have hLp : Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hg.toLp g)) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf g hg).2 h
  have hnorm := (continuous_norm.tendsto _).comp hLp
  have hsq := (continuous_pow 2).tendsto _ |>.comp hnorm
  simp only [Function.comp_def, Lp.norm_toLp] at hsq
  rw [vorticity_integral_sq_eq hg]
  exact hsq.congr fun n => (vorticity_integral_sq_eq (hf n)).symm

/-- The integral of the square of a difference is controlled by two nearby approximations. -/
theorem vorticity_integral_sq_sub_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g h : α → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (hh : MemLp h 2 μ) :
    ∫ x, (f x - g x) ^ 2 ∂μ ≤ 2 * ∫ x, (f x - h x) ^ 2 ∂μ + 2 * ∫ x, (g x - h x) ^ 2 ∂μ := by
  have hi (u v : α → ℝ) (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) :
      Integrable (fun x => (u x - v x) ^ 2) μ :=
    (memLp_two_iff_integrable_sq (hu.aestronglyMeasurable.sub hv.aestronglyMeasurable)).1
      (hu.sub hv)
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add
    ((hi f h hf hh).const_mul 2) ((hi g h hg hh).const_mul 2)]
  apply integral_mono (hi f g hf hg) (((hi f h hf hh).const_mul 2).add
    ((hi g h hg hh).const_mul 2))
  intro x
  simp only [Pi.add_apply]
  nlinarith only [sq_nonneg (f x - h x + (g x - h x))]

/-- A continuous function is integrable on a bounded measurable set. -/
theorem vorticity_integrableOn_of_continuous_bounded {S : Set (Vec3 × ℝ)}
    {g : Vec3 × ℝ → ℝ} (hg : Continuous g) (hS : Bornology.IsBounded S) :
    IntegrableOn g S :=
  (hg.continuousOn.integrableOn_compact hS.isCompact_closure).mono_set subset_closure

/-- A continuous function is square integrable on a bounded set. -/
theorem vorticity_memLp_two_of_continuous_bounded {S : Set (Vec3 × ℝ)}
    {g : Vec3 × ℝ → ℝ} (hg : Continuous g) (hS : Bornology.IsBounded S) :
    MemLp g 2 (volume.restrict S) :=
  (memLp_two_iff_integrable_sq hg.aestronglyMeasurable).2
    (vorticity_integrableOn_of_continuous_bounded (hg.pow 2) hS)

/-- On a space-time box, the set integral is the iterated integral with time outside. -/
theorem vorticity_setIntegral_prod_time {B : Set Vec3} {I : Set ℝ}
    {f : Vec3 × ℝ → ℝ} (hf : IntegrableOn f (B ×ˢ I)) :
    ∫ z in B ×ˢ I, f z = ∫ t in I, ∫ x in B, f (x, t) := by
  have hf' : Integrable f ((volume.restrict B).prod (volume.restrict I)) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact hf
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict,
    integral_prod f hf']
  exact integral_integral_swap (f := fun x t => f (x, t)) hf'

/-- A spatial coordinate derivative of a difference of smooth functions. -/
theorem vorticity_spatialPartial_sub {f g : Vec3 × ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (j : Fin 3) (z : Vec3 × ℝ) :
    spatialPartial (fun y : Vec3 × ℝ => f y - g y) j z =
      spatialPartial f j z - spatialPartial g j z := by
  rw [spatialPartial_eq_product_fderiv ((hf.sub hg).differentiable (by simp) z),
    spatialPartial_eq_product_fderiv (hf.differentiable (by simp) z),
    spatialPartial_eq_product_fderiv (hg.differentiable (by simp) z),
    fderiv_fun_sub (hf.differentiable (by simp) z) (hg.differentiable (by simp) z)]
  rfl

/-- The time derivative of a difference of smooth functions. -/
theorem vorticity_timePartial_sub {f g : Vec3 × ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (z : Vec3 × ℝ) :
    timePartial (fun y : Vec3 × ℝ => f y - g y) z = timePartial f z - timePartial g z := by
  rw [timePartial_eq_product_fderiv ((hf.sub hg).differentiable (by simp) z),
    timePartial_eq_product_fderiv (hf.differentiable (by simp) z),
    timePartial_eq_product_fderiv (hg.differentiable (by simp) z),
    fderiv_fun_sub (hf.differentiable (by simp) z) (hg.differentiable (by simp) z)]
  rfl

/-- A second spatial coordinate derivative of a difference of smooth functions. -/
theorem vorticity_spatialSecondPartial_sub {f g : Vec3 × ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (j k : Fin 3)
    (z : Vec3 × ℝ) :
    spatialSecondPartial (fun y : Vec3 × ℝ => f y - g y) j k z =
      spatialSecondPartial f j k z - spatialSecondPartial g j k z := by
  have hfirst : (fun y : ParabolicPoint => spatialPartial (fun y : Vec3 × ℝ => f y - g y) j y) =
      fun y : Vec3 × ℝ => spatialPartial f j y - spatialPartial g j y := by
    funext y
    exact vorticity_spatialPartial_sub hf hg j y
  unfold spatialSecondPartial
  rw [hfirst]
  exact vorticity_spatialPartial_sub (CKN.spatialPartial_contDiff hf j)
    (CKN.spatialPartial_contDiff hg j) k z

/-- The backward kernel ball of a point of a slightly smaller box lies in the box. -/
theorem vorticityBackBall_subset {x₀ : Vec3} {ρ R a b κ ε : ℝ} (hε : 0 < ε)
    (hεR : 2 * ε ≤ R - ρ) (hεκ : 6 * ε ≤ κ) {z : Vec3 × ℝ}
    (hz : z ∈ vec3Ball x₀ ρ ×ˢ Ioc (a + κ) b) :
    Metric.closedBall (z - vorticityBackShift ε) ε ⊆ vec3Ball x₀ R ×ˢ Ioo a b := by
  intro y hy
  rw [Metric.mem_closedBall, Prod.dist_eq, max_le_iff] at hy
  rcases hy with ⟨hy1, hy2⟩
  rcases hz with ⟨hz1, hz2⟩
  simp only [vorticityBackShift, Prod.fst_sub, Prod.snd_sub, sub_zero] at hy1 hy2
  refine ⟨?_, ?_, ?_⟩
  · change vec3EuclideanNorm (y.1 - x₀) < R
    have hsplit : y.1 - x₀ = (y.1 - z.1) + (z.1 - x₀) := by abel
    have htri : vec3EuclideanNorm (y.1 - x₀) ≤
        vec3EuclideanNorm (y.1 - z.1) + vec3EuclideanNorm (z.1 - x₀) := by
      rw [hsplit, vec3EuclideanNorm_eq_l2, vec3EuclideanNorm_eq_l2, vec3EuclideanNorm_eq_l2,
        WithLp.toLp_add]
      exact norm_add_le _ _
    have hsmall : vec3EuclideanNorm (y.1 - z.1) ≤ Real.sqrt 3 * ε := by
      refine (vec3EuclideanNorm_le_sqrt_three_mul_norm _).trans ?_
      rw [← dist_eq_norm]
      exact mul_le_mul_of_nonneg_left hy1 (Real.sqrt_nonneg 3)
    have hsqrt : Real.sqrt 3 < 2 := by
      rw [Real.sqrt_lt' (by norm_num)]
      norm_num
    have hz1' : vec3EuclideanNorm (z.1 - x₀) < ρ := hz1
    nlinarith only [htri, hsmall, hsqrt, hz1', hεR, hε]
  · rw [Real.dist_eq, abs_le] at hy2
    rcases hz2 with ⟨hz2a, _⟩
    linarith only [hy2.1, hz2a, hεκ]
  · rw [Real.dist_eq, abs_le] at hy2
    rcases hz2 with ⟨_, hz2b⟩
    linarith only [hy2.2, hz2b, hε]

/-- Backward mollifications converge in `L²` on every subset of the domain. -/
theorem vorticityBackMollify_tendsto_restrict {W S : Set (Vec3 × ℝ)} (hW : MeasurableSet W)
    (hS : MeasurableSet S) (hSW : S ⊆ W) {f : Vec3 × ℝ → ℝ} (hf : MemLp f 2 (volume.restrict W))
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) (hεpos : ∀ n, 0 < ε n) :
    Tendsto (fun n => eLpNorm (vorticityBackMollify W f (ε n) (hεpos n) - f) 2
      (volume.restrict S)) atTop (𝓝 0) := by
  have hglob : MemLp (W.indicator f) 2 (volume : Measure (Vec3 × ℝ)) :=
    (memLp_indicator_iff_restrict hW).2 hf
  have hconv := vorticityBackMollify_tendsto hglob hε hεpos
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hconv
    (fun _ => bot_le) (fun n => ?_)
  calc
    eLpNorm (vorticityBackMollify W f (ε n) (hεpos n) - f) 2 (volume.restrict S) =
        eLpNorm (fun z => vorticityBackMollify W f (ε n) (hεpos n) z - W.indicator f z) 2
          (volume.restrict S) := by
      apply eLpNorm_congr_ae
      filter_upwards [ae_restrict_mem hS] with z hz
      simp only [Pi.sub_apply, Set.indicator_of_mem (hSW hz)]
    _ ≤ _ := eLpNorm_mono_measure _ Measure.restrict_le_self

end CKN
