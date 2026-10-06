/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Space-time mollification on `ℝ³ × ℝ`

A normalized smooth bump kernel on `Vec3 × ℝ`, convolution with it, and its
basic properties: smoothness of the mollified function, control of its
support, the `L²` contraction bound, and `L²` convergence as the radius
tends to zero. These are used to extend the Carleman inequalities from
smooth compactly supported fields to Sobolev fields (`lem:carleman-sobolev`
of the Escauriaza–Seregin–Šverák manuscript).
-/

public section

open Function Filter MeasureTheory Set Topology
open scoped ENNReal Convolution Pointwise
open CKN.Foundation.Parabolic

namespace CKN

noncomputable section

local instance spaceTimeVolumeIsAddHaarMeasure :
    Measure.IsAddHaarMeasure (volume : Measure (Vec3 × ℝ)) := by
  rw [Measure.volume_eq_prod]
  exact Measure.prod.instIsAddHaarMeasure (volume : Measure Vec3) (volume : Measure ℝ)

local instance spaceTimeVolumeIsAddLeftInvariant :
    Measure.IsAddLeftInvariant (volume : Measure (Vec3 × ℝ)) :=
  spaceTimeVolumeIsAddHaarMeasure.toIsAddLeftInvariant

local instance spaceTimeVolumeIsAddRightInvariant :
    Measure.IsAddRightInvariant (volume : Measure (Vec3 × ℝ)) := by
  constructor
  intro t
  rw [show (fun x : Vec3 × ℝ => x + t) = fun x => t + x by
    funext x
    exact add_comm x t]
  exact MeasureTheory.map_add_left_eq_self (μ := (volume : Measure (Vec3 × ℝ))) t

/-- The normalized bump of radius `δ` on space-time. -/
@[expose]
noncomputable def spaceTimeStandardBump (δ : ℝ) (hδ : 0 < δ) :
    ContDiffBump (0 : Vec3 × ℝ) :=
  { rIn := δ / 2
    rOut := δ
    rIn_pos := by positivity
    rIn_lt_rOut := by linarith only [hδ] }

/-- The nonnegative normalized space-time kernel with outer radius `δ`. -/
@[expose]
noncomputable def spaceTimeMollifier (δ : ℝ) (hδ : 0 < δ) :
    Vec3 × ℝ → ℝ :=
  (spaceTimeStandardBump δ hδ).normed (volume : Measure (Vec3 × ℝ))

/-- Convolution with the normalized space-time kernel of radius `δ`. -/
@[expose]
noncomputable def spaceTimeMollify (f : Vec3 × ℝ → ℝ) (δ : ℝ) (hδ : 0 < δ) :
    Vec3 × ℝ → ℝ :=
  MeasureTheory.convolution (spaceTimeMollifier δ hδ) f
    (ContinuousLinearMap.lsmul ℝ ℝ) (volume : Measure (Vec3 × ℝ))

/-- The space-time kernel is pointwise nonnegative. -/
theorem spaceTimeMollifier_nonneg {δ : ℝ} (hδ : 0 < δ) (z : Vec3 × ℝ) :
    0 ≤ spaceTimeMollifier δ hδ z := by
  exact (spaceTimeStandardBump δ hδ).nonneg_normed z

/-- The space-time kernel has integral one. -/
theorem spaceTimeMollifier_integral_one {δ : ℝ} (hδ : 0 < δ) :
    ∫ z : Vec3 × ℝ, spaceTimeMollifier δ hδ z ∂(volume : Measure (Vec3 × ℝ)) = 1 := by
  exact (spaceTimeStandardBump δ hδ).integral_normed

/-- The space-time kernel has compact support. -/
theorem spaceTimeMollifier_hasCompactSupport {δ : ℝ} (hδ : 0 < δ) :
    HasCompactSupport (spaceTimeMollifier δ hδ) := by
  exact (spaceTimeStandardBump δ hδ).hasCompactSupport_normed

/-- The support of the kernel lies in the open ball of radius `δ`. -/
theorem spaceTimeMollifier_support {δ : ℝ} (hδ : 0 < δ) :
    Function.support (spaceTimeMollifier δ hδ) = Metric.ball (0 : Vec3 × ℝ) δ := by
  exact (spaceTimeStandardBump δ hδ).support_normed_eq

/-- The space-time kernel is smooth to every finite or infinite order. -/
theorem spaceTimeMollifier_contDiff {δ : ℝ} (hδ : 0 < δ) {n : ℕ∞} :
    ContDiff ℝ n (spaceTimeMollifier δ hδ) := by
  exact (spaceTimeStandardBump δ hδ).contDiff_normed

/-- Convolution with the space-time kernel is smooth for locally integrable data. -/
theorem spaceTimeMollify_contDiff {f : Vec3 × ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    {n : ℕ∞} (hf : LocallyIntegrable f (volume : Measure (Vec3 × ℝ))) :
    ContDiff ℝ n (spaceTimeMollify f δ hδ) := by
  exact (spaceTimeMollifier_hasCompactSupport hδ).contDiff_convolution_left
    (L := ContinuousLinearMap.lsmul ℝ ℝ) (spaceTimeMollifier_contDiff hδ) hf

/-- Convolution with the space-time kernel preserves compact support. -/
theorem spaceTimeMollify_hasCompactSupport {f : Vec3 × ℝ → ℝ} {δ : ℝ}
    (hδ : 0 < δ) (hf : HasCompactSupport f) :
    HasCompactSupport (spaceTimeMollify f δ hδ) := by
  exact (spaceTimeMollifier_hasCompactSupport hδ).convolution
    (ContinuousLinearMap.lsmul ℝ ℝ) hf

/-- The support after mollification lies within distance `δ` of the original support. -/
theorem spaceTimeMollify_support_subset {f : Vec3 × ℝ → ℝ} {δ : ℝ}
    (hδ : 0 < δ) :
    Function.support (spaceTimeMollify f δ hδ) ⊆
      Metric.ball (0 : Vec3 × ℝ) δ + Function.support f := by
  calc
    Function.support (spaceTimeMollify f δ hδ) ⊆
        Function.support (spaceTimeMollifier δ hδ) + Function.support f := by
      simpa [spaceTimeMollify] using
        (MeasureTheory.support_convolution_subset
          (L := ContinuousLinearMap.lsmul ℝ ℝ)
          (f := spaceTimeMollifier δ hδ) (g := f))
    _ = Metric.ball (0 : Vec3 × ℝ) δ + Function.support f := by
      rw [spaceTimeMollifier_support hδ]

/-- Componentwise mollification for fields with a finite scalar index. This includes Vec3 values
and fields with values `Fin 3 → Vec3`. -/
@[expose]
noncomputable def spaceTimeMollifyPi {ι : Type*} [Fintype ι]
    (f : Vec3 × ℝ → ι → ℝ) (δ : ℝ) (hδ : 0 < δ) : Vec3 × ℝ → ι → ℝ :=
  fun x i => spaceTimeMollify (fun y => f y i) δ hδ x

/-- Componentwise mollification preserves smoothness. -/
theorem spaceTimeMollifyPi_contDiff {ι : Type*} [Fintype ι]
    {f : Vec3 × ℝ → ι → ℝ} {δ : ℝ} (hδ : 0 < δ) {n : ℕ∞}
    (hf : ∀ i, LocallyIntegrable (fun y => f y i) (volume : Measure (Vec3 × ℝ))) :
    ContDiff ℝ n (spaceTimeMollifyPi f δ hδ) := by
  rw [contDiff_pi]
  intro i
  exact spaceTimeMollify_contDiff hδ (hf i)

/-- The support of a componentwise mollification lies within distance `δ` of the field support. -/
theorem spaceTimeMollifyPi_support_subset {ι : Type*} [Fintype ι]
    {f : Vec3 × ℝ → ι → ℝ} {δ : ℝ} (hδ : 0 < δ) :
    Function.support (spaceTimeMollifyPi f δ hδ) ⊆
      Metric.ball (0 : Vec3 × ℝ) δ + Function.support f := by
  classical
  intro x hx
  have hxne : spaceTimeMollifyPi f δ hδ x ≠ 0 := by
    simpa only [Function.mem_support] using hx
  obtain ⟨i, hi⟩ : ∃ i, spaceTimeMollifyPi f δ hδ x i ≠ 0 := by
    by_contra h
    apply hxne
    funext j
    by_contra hj
    exact h ⟨j, hj⟩
  have hcomponent : x ∈ Function.support
      (fun y => spaceTimeMollify (fun z => f z i) δ hδ y) := by
    rw [Function.mem_support]
    intro hzero
    apply hi
    simpa only [spaceTimeMollifyPi] using hzero
  have hscalar := spaceTimeMollify_support_subset
    (f := fun y => f y i) hδ hcomponent
  rcases hscalar with ⟨z, hz, y, hy, hxy⟩
  refine ⟨z, hz, y, ?_, hxy⟩
  rw [Function.mem_support]
  intro hzero
  apply hy
  exact congrFun hzero i

/-- Componentwise mollification has compact support when the input field does. -/
theorem spaceTimeMollifyPi_hasCompactSupport {ι : Type*} [Fintype ι]
    {f : Vec3 × ℝ → ι → ℝ} {δ : ℝ} (hδ : 0 < δ) (hf : HasCompactSupport f) :
    HasCompactSupport (spaceTimeMollifyPi f δ hδ) := by
  apply HasCompactSupport.of_support_subset_isCompact
    ((isCompact_closedBall (0 : Vec3 × ℝ) δ).add hf.isCompact)
  calc
    Function.support (spaceTimeMollifyPi f δ hδ) ⊆
        Metric.ball (0 : Vec3 × ℝ) δ + Function.support f :=
      spaceTimeMollifyPi_support_subset hδ
    _ ⊆ Metric.closedBall 0 δ + tsupport f := by
      apply add_subset_add
      · exact Metric.ball_subset_closedBall
      · exact subset_tsupport _

end

local instance spaceTimeVolumeIsAddHaarMeasure' :
    Measure.IsAddHaarMeasure (volume : Measure (Vec3 × ℝ)) := by
  rw [Measure.volume_eq_prod]
  exact Measure.prod.instIsAddHaarMeasure (volume : Measure Vec3) (volume : Measure ℝ)

local instance spaceTimeVolumeIsAddLeftInvariant' :
    Measure.IsAddLeftInvariant (volume : Measure (Vec3 × ℝ)) :=
  spaceTimeVolumeIsAddHaarMeasure'.toIsAddLeftInvariant

private lemma convexOn_abs_rpow {p : ℝ} (hp : 1 ≤ p) :
    ConvexOn ℝ Set.univ (fun x : ℝ => |x| ^ p) := by
  have h1 : ConvexOn ℝ Set.univ (fun x : ℝ => |x|) := by
    convert (convexOn_univ_norm : ConvexOn ℝ Set.univ (fun x : ℝ => ‖x‖)) using 1
  have h2 : ConvexOn ℝ (Set.Ici 0) (fun t : ℝ => t ^ p) := convexOn_rpow hp
  have h3 : MonotoneOn (fun t : ℝ => t ^ p) (Set.Ici 0) := by
    intro a ha b hb hab
    exact Real.rpow_le_rpow ha hab (le_trans zero_le_one hp)
  have himg : (fun x : ℝ => |x|) '' Set.univ ⊆ Set.Ici 0 := by
    rintro _ ⟨x, -, rfl⟩
    exact abs_nonneg x
  have himg_convex : Convex ℝ ((fun x : ℝ => |x|) '' Set.univ) := by
    have heq : (fun x : ℝ => |x|) '' Set.univ = Set.Ici 0 := by
      ext y
      simp only [Set.mem_image, Set.mem_univ, true_and, Set.mem_Ici]
      constructor
      · rintro ⟨x, rfl⟩
        exact abs_nonneg x
      · intro hy
        exact ⟨y, abs_of_nonneg hy⟩
    rw [heq]
    exact convex_Ici 0
  exact (h2.subset himg himg_convex).comp h1 (h3.mono himg)

private lemma jensen_abs_rpow_integral
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {f : α → ℝ} {p : ℝ} (hp : 1 ≤ p)
    (hf : Integrable f μ) (hfpow : Integrable (fun x => |f x| ^ p) μ) :
    |∫ x, f x ∂μ| ^ p ≤ ∫ x, |f x| ^ p ∂μ := by
  have hconv : ConvexOn ℝ Set.univ (fun x : ℝ => |x| ^ p) := convexOn_abs_rpow hp
  have hcont : ContinuousOn (fun x : ℝ => |x| ^ p) Set.univ := by
    exact (continuous_abs.rpow_const fun _ => Or.inr (le_trans zero_le_one hp)).continuousOn
  exact hconv.map_integral_le hcont isClosed_univ
    (Filter.Eventually.of_forall (fun _ => Set.mem_univ _)) hf hfpow

private lemma lintegral_comp_sub_right (f : Vec3 × ℝ → ℝ≥0∞) (hf : Measurable f)
    (t : Vec3 × ℝ) :
    ∫⁻ x, f (x - t) ∂(volume : Measure (Vec3 × ℝ)) = ∫⁻ x, f x ∂volume := by
  have heq : (fun x => f (x - t)) = f ∘ ((· + (-t)) : Vec3 × ℝ → Vec3 × ℝ) := by
    funext x
    simp [sub_eq_add_neg]
  rw [heq, lintegral_comp hf (measurable_add_const (-t))]
  have hmap : Measure.map (fun x : Vec3 × ℝ => x + (-t))
      (volume : Measure (Vec3 × ℝ)) = volume := by
    rw [show (fun x : Vec3 × ℝ => x + (-t)) = fun x => (-t) + x by
      funext x
      exact add_comm x (-t)]
    exact spaceTimeVolumeIsAddHaarMeasure.toIsAddLeftInvariant.map_add_left_eq_self (-t)
  rw [hmap]

private lemma fubini_translation_key (ρ : Vec3 × ℝ → ℝ≥0∞) (g : Vec3 × ℝ → ℝ) (p : ℝ)
    (hρ : Measurable ρ) (hg : Measurable g) :
    ∫⁻ x, ∫⁻ t, ρ t * (ENNReal.ofReal |g (x - t)|) ^ p ∂volume ∂volume =
      (∫⁻ t, ρ t ∂volume) * (∫⁻ x, (ENNReal.ofReal |g x|) ^ p ∂volume) := by
  have hswap :
      ∫⁻ x, ∫⁻ t, ρ t * (ENNReal.ofReal |g (x - t)|) ^ p ∂volume ∂volume =
        ∫⁻ t, ∫⁻ x, ρ t * (ENNReal.ofReal |g (x - t)|) ^ p ∂volume ∂volume := by
    apply lintegral_lintegral_swap
    apply AEMeasurable.mul
    · exact (hρ.comp measurable_snd).aemeasurable
    · have hpow : Measurable (fun z : (Vec3 × ℝ) × (Vec3 × ℝ) =>
          (ENNReal.ofReal |g (z.1 - z.2)|) ^ p) := by
        have hbase : Measurable (fun z : (Vec3 × ℝ) × (Vec3 × ℝ) =>
            ENNReal.ofReal |g (z.1 - z.2)|) := by
          exact ENNReal.measurable_ofReal.comp
            (continuous_abs.measurable.comp (hg.comp (measurable_fst.sub measurable_snd)))
        exact Measurable.pow_const hbase p
      exact hpow.aemeasurable
  rw [hswap]
  have hfactor :
      ∫⁻ t, ∫⁻ x, ρ t * (ENNReal.ofReal |g (x - t)|) ^ p ∂volume ∂volume =
        ∫⁻ t, ρ t * ∫⁻ x, (ENNReal.ofReal |g (x - t)|) ^ p ∂volume ∂volume := by
    congr 1
    ext t
    have hsub : Measurable (fun x : Vec3 × ℝ => x - t) := measurable_id.sub measurable_const
    exact lintegral_const_mul _ (Measurable.pow_const
      (ENNReal.measurable_ofReal.comp
        (continuous_abs.measurable.comp (hg.comp hsub))) p)
  rw [hfactor]
  have htrans : ∀ t, ∫⁻ x, (ENNReal.ofReal |g (x - t)|) ^ p ∂(volume : Measure (Vec3 × ℝ)) =
      ∫⁻ x, (ENNReal.ofReal |g x|) ^ p ∂volume := by
    intro t
    exact lintegral_comp_sub_right _ (Measurable.pow_const
      (ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp hg)) p) t
  simp_rw [htrans]
  rw [lintegral_mul_const _ hρ, mul_comm]

private lemma integral_withDensity_ofReal_eq_integral_mul
    {f g : Vec3 × ℝ → ℝ} (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_meas : AEMeasurable f volume) :
    ∫ x, g x ∂(volume.withDensity fun x => ENNReal.ofReal (f x)) =
      ∫ x, f x * g x := by
  have heq : (fun x => ENNReal.ofReal (f x)) =
      fun x => (Real.toNNReal (f x) : ℝ≥0∞) := by
    funext x
    rw [ENNReal.ofReal_eq_coe_nnreal (hf_nonneg x),
      Real.toNNReal_of_nonneg (hf_nonneg x)]
  rw [heq, integral_withDensity_eq_integral_smul₀ (hf_meas.real_toNNReal)]
  congr 1
  funext x
  simp [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (hf_nonneg x)]

private theorem young_convolution_nonneg_integral_one
    {ρ g : Vec3 × ℝ → ℝ} {p : ENNReal} (hp : 1 ≤ p) (hp_top : p ≠ ∞)
    (hρ_nonneg : ∀ x, 0 ≤ ρ x) (hρ_int : Integrable ρ volume)
    (hρ_one : ∫ x, ρ x = 1) (hρ_meas : Measurable ρ) (hg_meas : Measurable g)
    (hconv_aestrong : AEStronglyMeasurable
      (convolution ρ g (ContinuousLinearMap.lsmul ℝ ℝ) volume) volume) :
    eLpNorm (convolution ρ g (ContinuousLinearMap.lsmul ℝ ℝ) volume) p volume ≤
      eLpNorm g p volume := by
  have hp_ne_zero : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp_ne_zero hp_top
  have hp_ge_one : 1 ≤ p.toReal := by
    rw [← ENNReal.toReal_one]
    exact (ENNReal.toReal_le_toReal ENNReal.one_ne_top hp_top).mpr hp
  let μ : Measure (Vec3 × ℝ) := volume.withDensity fun t => ENNReal.ofReal (ρ t)
  let _ : IsProbabilityMeasure μ := by
    constructor
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    rw [← ofReal_integral_eq_lintegral_ofReal hρ_int (ae_of_all _ hρ_nonneg), hρ_one]
    simp
  have hg_aestrong : AEStronglyMeasurable g volume := hg_meas.aestronglyMeasurable
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp_ne_zero hp_top hconv_aestrong]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp_ne_zero hp_top hg_aestrong]
  apply ENNReal.rpow_le_rpow _ (by positivity : 0 ≤ 1 / p.toReal)
  have hfubini := fubini_translation_key (fun t => ENNReal.ofReal (ρ t)) g
    p.toReal hρ_meas.ennreal_ofReal hg_meas
  have hρ_lint_one : ∫⁻ t, ENNReal.ofReal (ρ t) ∂volume = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hρ_int (ae_of_all _ hρ_nonneg), hρ_one]
    simp
  have hpointwise : ∀ x, ‖convolution ρ g (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ₑ ^ p.toReal ≤
      ∫⁻ t, ENNReal.ofReal (ρ t) * (ENNReal.ofReal |g (x - t)|) ^ p.toReal ∂volume := by
    intro x
    rw [convolution_def]
    simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
    rw [Real.enorm_eq_ofReal_abs]
    have heq_int : ∫ t, ρ t * g (x - t) = ∫ t, g (x - t) ∂μ := by
      symm
      exact integral_withDensity_ofReal_eq_integral_mul hρ_nonneg hρ_meas.aemeasurable
    rw [heq_int]
    by_cases hg_int_μ : Integrable (fun t => g (x - t)) μ
    · by_cases hgpow_int_μ : Integrable (fun t => |g (x - t)| ^ p.toReal) μ
      · have hJensen := jensen_abs_rpow_integral μ hp_ge_one hg_int_μ hgpow_int_μ
        have heq_pow : ∫ t, |g (x - t)| ^ p.toReal ∂μ =
            (∫⁻ t, ENNReal.ofReal (ρ t) * (ENNReal.ofReal |g (x - t)|) ^ p.toReal
              ∂volume).toReal := by
          rw [integral_withDensity_ofReal_eq_integral_mul hρ_nonneg hρ_meas.aemeasurable]
          rw [integral_eq_lintegral_of_nonneg_ae]
          · congr 1
            apply lintegral_congr
            intro t
            rw [ENNReal.ofReal_mul (hρ_nonneg t)]
            congr 1
            rw [← ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp_pos.le]
          · exact ae_of_all _ (fun t => mul_nonneg (hρ_nonneg t)
              (Real.rpow_nonneg (abs_nonneg _) _))
          · have habs_rpow_meas : Measurable (fun t => |g (x - t)| ^ p.toReal) := by
              have hcont : Continuous (fun y : ℝ => |y| ^ p.toReal) :=
                continuous_abs.rpow_const (fun _ => Or.inr hp_pos.le)
              exact hcont.measurable.comp (hg_meas.comp (measurable_const.sub measurable_id))
            exact (hρ_meas.mul habs_rpow_meas).aestronglyMeasurable
        calc
          ENNReal.ofReal |∫ t, g (x - t) ∂μ| ^ p.toReal =
              ENNReal.ofReal (|∫ t, g (x - t) ∂μ| ^ p.toReal) := by
                rw [← ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp_pos.le]
          _ ≤ ENNReal.ofReal (∫ t, |g (x - t)| ^ p.toReal ∂μ) :=
            ENNReal.ofReal_le_ofReal hJensen
          _ = ENNReal.ofReal ((∫⁻ t, ENNReal.ofReal (ρ t) *
              (ENNReal.ofReal |g (x - t)|) ^ p.toReal ∂volume).toReal) := by
            rw [heq_pow]
          _ ≤ ∫⁻ t, ENNReal.ofReal (ρ t) *
              (ENNReal.ofReal |g (x - t)|) ^ p.toReal ∂volume :=
            ENNReal.ofReal_toReal_le
      · have hnot_finite : ∫⁻ t, ENNReal.ofReal (ρ t) *
            (ENNReal.ofReal |g (x - t)|) ^ p.toReal ∂volume = ⊤ := by
          have h_eq : ∫⁻ t, ENNReal.ofReal (ρ t) *
              (ENNReal.ofReal |g (x - t)|) ^ p.toReal ∂volume =
              ∫⁻ t, (ENNReal.ofReal |g (x - t)|) ^ p.toReal ∂μ := by
            have hsub : Measurable (fun t : Vec3 × ℝ => x - t) := measurable_const.sub measurable_id
            have h_abs_meas : Measurable (fun t => |g (x - t)|) :=
              continuous_abs.measurable.comp (hg_meas.comp hsub)
            have h_meas_pow : Measurable
                (fun t => (ENNReal.ofReal |g (x - t)|) ^ p.toReal) :=
              Measurable.pow_const h_abs_meas.ennreal_ofReal p.toReal
            symm
            convert lintegral_withDensity_eq_lintegral_mul volume
              hρ_meas.ennreal_ofReal h_meas_pow using 2
          rw [h_eq]
          have habs_rpow_nonneg : ∀ t, 0 ≤ |g (x - t)| ^ p.toReal :=
            fun t => Real.rpow_nonneg (abs_nonneg _) _
          have habs_rpow_meas : Measurable (fun t => |g (x - t)| ^ p.toReal) := by
            have hcont : Continuous (fun y : ℝ => |y| ^ p.toReal) :=
              continuous_abs.rpow_const (fun _ => Or.inr hp_pos.le)
            have hsub : Measurable (fun t : Vec3 × ℝ => x - t) := measurable_const.sub measurable_id
            exact hcont.measurable.comp (hg_meas.comp hsub)
          have htop : ∫⁻ t, (ENNReal.ofReal |g (x - t)|) ^ p.toReal ∂μ = ⊤ := by
            rw [← lintegral_ofReal_ne_top_iff_integrable habs_rpow_meas.aestronglyMeasurable
                (ae_of_all _ habs_rpow_nonneg)] at hgpow_int_μ
            have htop' : ∫⁻ t, ENNReal.ofReal (|g (x - t)| ^ p.toReal) ∂μ = ⊤ := by
              exact not_ne_iff.mp hgpow_int_μ
            convert htop' using 1
            congr 1
            ext t
            rw [← ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp_pos.le]
          rw [htop]
        simp [hnot_finite]
    · rw [integral_undef hg_int_μ]
      simp only [abs_zero, ENNReal.ofReal_zero]
      rw [ENNReal.zero_rpow_of_pos hp_pos]
      exact zero_le
  calc
    ∫⁻ x, ‖convolution ρ g (ContinuousLinearMap.lsmul ℝ ℝ) volume x‖ₑ ^ p.toReal ∂volume ≤
        ∫⁻ x, ∫⁻ t, ENNReal.ofReal (ρ t) *
          (ENNReal.ofReal |g (x - t)|) ^ p.toReal ∂volume ∂volume :=
      lintegral_mono hpointwise
    _ = (∫⁻ t, ENNReal.ofReal (ρ t) ∂volume) *
          (∫⁻ x, (ENNReal.ofReal |g x|) ^ p.toReal ∂volume) := hfubini
    _ = 1 * (∫⁻ x, (ENNReal.ofReal |g x|) ^ p.toReal ∂volume) := by rw [hρ_lint_one]
    _ = ∫⁻ x, (ENNReal.ofReal |g x|) ^ p.toReal ∂volume := one_mul _
    _ = ∫⁻ x, ‖g x‖ₑ ^ p.toReal ∂volume := by
      congr 1
      ext x
      rw [Real.enorm_eq_ofReal_abs]

private theorem tendsto_eLpNorm_sub_zero_spaceTimeMollify_of_continuous
    {f : Vec3 × ℝ → ℝ} {p : ENNReal}
    (hp_top : p ≠ ∞) (hf_cont : Continuous f) (hf_supp : HasCompactSupport f)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (nhds 0))
    (hε_pos : ∀ n, 0 < ε n) :
    Tendsto
      (fun n => eLpNorm (fun x => spaceTimeMollify f (ε n) (hε_pos n) x - f x) p volume)
      atTop (nhds 0) := by
  let K : Set (Vec3 × ℝ) := Metric.closedBall 0 1 + tsupport f
  have hK_compact : IsCompact K :=
    (isCompact_closedBall (0 : Vec3 × ℝ) 1).add hf_supp.isCompact
  have hK_meas : MeasurableSet K := hK_compact.measurableSet
  have hK_ne_top : volume K ≠ ⊤ := hK_compact.measure_lt_top.ne
  have hpow_ne_top : volume K ^ (1 / p.toReal) ≠ ⊤ := by
    exact (ENNReal.rpow_lt_top_of_nonneg (by positivity) hK_ne_top).ne
  let cK : ℝ := (volume K ^ (1 / p.toReal)).toReal
  have hcK_nonneg : 0 ≤ cK := ENNReal.toReal_nonneg
  have hpow_eq : ENNReal.ofReal cK = volume K ^ (1 / p.toReal) := by
    dsimp [cK]
    exact ENNReal.ofReal_toReal hpow_ne_top
  apply ENNReal.tendsto_nhds_zero.2
  intro η hη
  by_cases hη_top : η = ⊤
  · exact Eventually.of_forall (fun n => by simp only [hη_top, le_top])
  let δ : ℝ := η.toReal / (cK + 1)
  have hη_real : 0 < η.toReal := ENNReal.toReal_pos hη.ne' hη_top
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    positivity
  obtain ⟨γ, hγ_pos, hγ⟩ :=
    Metric.uniformContinuous_iff.mp (hf_supp.uniformContinuous_of_continuous hf_cont) δ hδ_pos
  have hε_small : ∀ᶠ n in atTop, ε n < γ / 2 :=
    (tendsto_order.1 hε).2 _ (by positivity)
  have hε_le_one : ∀ᶠ n in atTop, ε n ≤ 1 :=
    ((tendsto_order.1 hε).2 _ zero_lt_one).mono (fun _ hn => le_of_lt hn)
  filter_upwards [hε_small, hε_le_one] with n hn_small hn_one
  have hkernel_support :
      support (spaceTimeMollifier (ε n) (hε_pos n)) ⊆ Metric.ball 0 (2 * ε n) := by
    rw [spaceTimeMollifier_support (hε_pos n)]
    exact Metric.ball_subset_ball (by linarith only [hε_pos n])
  have hdist : ∀ x,
      dist (spaceTimeMollify f (ε n) (hε_pos n) x) (f x) ≤ δ := by
    intro x
    exact @MeasureTheory.dist_convolution_le
      (Vec3 × ℝ) ℝ _ f _ (volume : Measure (Vec3 × ℝ)) _ _ _
      spaceTimeVolumeIsAddLeftInvariant _ _ _
      (spaceTimeMollifier (ε n) (hε_pos n)) x (2 * ε n) δ (f x)
      (le_of_lt hδ_pos) hkernel_support
      (spaceTimeMollifier_nonneg (hε_pos n))
      (spaceTimeMollifier_integral_one (hε_pos n))
      hf_cont.aestronglyMeasurable (by
        intro y hy
        rw [Metric.mem_ball, dist_eq_norm_sub] at hy
        apply (hγ ?_).le
        rw [dist_eq_norm_sub]
        exact hy.trans (by linarith only [hn_small]))
  have hconv_support :
      support (spaceTimeMollify f (ε n) (hε_pos n)) ⊆ K := by
    calc
      support (spaceTimeMollify f (ε n) (hε_pos n)) ⊆
          Metric.ball 0 (ε n) + support f :=
        spaceTimeMollify_support_subset (hε_pos n)
      _ ⊆ Metric.closedBall 0 1 + tsupport f := by
        apply add_subset_add
        · intro z hz
          exact (Metric.mem_ball.mp hz).le.trans hn_one
        · exact subset_tsupport _
  have hf_support : support f ⊆ K := by
    intro x hx
    refine ⟨0, ?_, x, subset_tsupport f hx, by simp only [zero_add]⟩
    simp only [Metric.mem_closedBall, dist_zero_right, norm_zero]
    exact zero_le_one
  have hbound :
      eLpNorm (fun x => spaceTimeMollify f (ε n) (hε_pos n) x - f x) p volume ≤
        ENNReal.ofReal δ * volume K ^ (1 / p.toReal) := by
    have hmeas : AEStronglyMeasurable
        (fun x => spaceTimeMollify f (ε n) (hε_pos n) x - f x) volume :=
      (((spaceTimeMollify_contDiff (f := f) (δ := ε n) (hε_pos n) (n := 0)
        (hf_cont.integrable_of_hasCompactSupport hf_supp).locallyIntegrable).continuous).sub
          hf_cont)
        |>.aestronglyMeasurable
    exact eLpNorm_sub_le_of_dist_bdd volume hp_top hK_meas.nullMeasurableSet hδ_pos.le
      hmeas hdist
      hconv_support hf_support
  have hδmul : δ * cK ≤ η.toReal := by
    have hfrac_le : cK / (cK + 1) ≤ 1 := by
      exact div_le_one_of_le₀ (by linarith only [hcK_nonneg]) (by linarith only [hcK_nonneg])
    calc
      δ * cK = η.toReal * (cK / (cK + 1)) := by
        dsimp [δ]
        rw [div_eq_mul_inv, div_eq_mul_inv]
        ring_nf
      _ ≤ η.toReal * 1 := mul_le_mul_of_nonneg_left hfrac_le hη_real.le
      _ = η.toReal := mul_one _
  calc
    eLpNorm (fun x => spaceTimeMollify f (ε n) (hε_pos n) x - f x) p volume ≤
        ENNReal.ofReal δ * volume K ^ (1 / p.toReal) := hbound
    _ = ENNReal.ofReal (δ * cK) := by
      rw [← hpow_eq, ← ENNReal.ofReal_mul]
      positivity
    _ ≤ η := by
      rw [← ENNReal.ofReal_toReal hη_top]
      exact ENNReal.ofReal_le_ofReal hδmul


/-- Convolution by the space-time kernel is a contraction on `L²`. -/
theorem spaceTimeMollify_eLpNorm_le {f : Vec3 × ℝ → ℝ} {δ : ℝ}
    (hδ : 0 < δ) (hf : MemLp f (2 : ℝ≥0∞) (volume : Measure (Vec3 × ℝ))) :
    eLpNorm (spaceTimeMollify f δ hδ) 2 (volume : Measure (Vec3 × ℝ)) ≤
      eLpNorm f 2 (volume : Measure (Vec3 × ℝ)) := by
  let ρ := spaceTimeMollifier δ hδ
  let g' := hf.aestronglyMeasurable.mk f
  have hg'meas : Measurable g' := hf.aestronglyMeasurable.measurable_mk
  have hfg : f =ᵐ[volume] g' := hf.aestronglyMeasurable.ae_eq_mk
  have hg'mem : MemLp g' (2 : ℝ≥0∞) volume := MemLp.ae_eq hfg hf
  have hkcont : Continuous ρ := (spaceTimeMollifier_contDiff hδ (n := 0)).continuous
  have hkcompact : HasCompactSupport ρ := spaceTimeMollifier_hasCompactSupport hδ
  have hkint : Integrable ρ volume := hkcont.integrable_of_hasCompactSupport hkcompact
  let hRight : Measure.IsAddRightInvariant (volume : Measure (Vec3 × ℝ)) :=
    spaceTimeVolumeIsAddRightInvariant
  have hconvEq : convolution ρ f (ContinuousLinearMap.lsmul ℝ ℝ) volume =
      convolution ρ g' (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
    exact MeasureTheory.convolution_congr (L := ContinuousLinearMap.lsmul ℝ ℝ)
      (μ := (volume : Measure (Vec3 × ℝ))) EventuallyEq.rfl hfg
  have hconvCont : Continuous
      (convolution ρ g' (ContinuousLinearMap.lsmul ℝ ℝ) volume) := by
    have hloc : LocallyIntegrable g' (volume : Measure (Vec3 × ℝ)) :=
      hg'mem.locallyIntegrable (by norm_num : 1 ≤ (2 : ℝ≥0∞))
    have hsmooth : ContDiff ℝ (0 : ℕ∞) (spaceTimeMollify g' δ hδ) :=
      spaceTimeMollify_contDiff hδ hloc
    exact hsmooth.continuous
  have hbound := young_convolution_nonneg_integral_one
    (ρ := ρ) (g := g') (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)
    (fun z => spaceTimeMollifier_nonneg hδ z) hkint
    (spaceTimeMollifier_integral_one hδ) hkcont.measurable hg'meas
    hconvCont.aestronglyMeasurable
  change eLpNorm (convolution ρ f (ContinuousLinearMap.lsmul ℝ ℝ) volume) 2 volume ≤ _
  rw [hconvEq]
  exact hbound.trans_eq (eLpNorm_congr_ae hfg.symm)

private theorem spaceTimeConvolutionExists_left {f g : Vec3 × ℝ → ℝ}
    (hf_compact : HasCompactSupport f) (hf_cont : Continuous f)
    (hg_loc : LocallyIntegrable g (volume : Measure (Vec3 × ℝ))) :
    ConvolutionExists f g (ContinuousLinearMap.lsmul ℝ ℝ)
      (volume : Measure (Vec3 × ℝ)) :=
  hf_compact.convolutionExists_left (L := ContinuousLinearMap.lsmul ℝ ℝ) hf_cont hg_loc

/-- Mollification converges in `L²` for every square-integrable space-time function. -/
theorem tendsto_eLpNorm_sub_zero_spaceTimeMollify
    {g : Vec3 × ℝ → ℝ}
    (hg : MemLp g (2 : ℝ≥0∞) (volume : Measure (Vec3 × ℝ)))
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (nhds 0))
    (hε_pos : ∀ n, 0 < ε n) :
    Tendsto
      (fun n => eLpNorm
        (fun x => spaceTimeMollify g (ε n) (hε_pos n) x - g x)
        2 (volume : Measure (Vec3 × ℝ))) atTop (nhds 0) := by
  apply ENNReal.tendsto_nhds_zero.2
  intro η hη
  obtain ⟨η₁, hη₁_pos, hη₁⟩ :=
    MeasureTheory.exists_Lp_half (μ := (volume : Measure (Vec3 × ℝ)))
      (ε := ℝ) (p := (2 : ℝ≥0∞)) hη.ne'
  obtain ⟨η₂, hη₂_pos, hη₂⟩ :=
    MeasureTheory.exists_Lp_half (μ := (volume : Measure (Vec3 × ℝ)))
      (ε := ℝ) (p := (2 : ℝ≥0∞)) hη₁_pos.ne'
  let δ : ℝ≥0∞ := min η₁ η₂
  have hδ_pos : 0 < δ := lt_min hη₁_pos hη₂_pos
  obtain ⟨f', hf'_supp, happrox', hf'_cont, hf'_mem⟩ :=
    hg.exists_hasCompactSupport_eLpNorm_sub_le (by norm_num) hδ_pos.ne'
  have hdiff_mem : MemLp (fun x => g x - f' x) (2 : ℝ≥0∞)
      (volume : Measure (Vec3 × ℝ)) := hg.sub hf'_mem
  have hthird_norm :
      eLpNorm (fun x => f' x - g x) 2 (volume : Measure (Vec3 × ℝ)) ≤ η₁ := by
    have hneg : (fun x => f' x - g x) = -(fun x => g x - f' x) := by
      ext x
      change f' x - g x = -(g x - f' x)
      abel_nf
    rw [hneg, eLpNorm_neg]
    exact happrox'.trans (min_le_left _ _)
  have hmid_eventually : ∀ᶠ n in atTop,
      eLpNorm
        (fun x => spaceTimeMollify f' (ε n) (hε_pos n) x - f' x)
        2 (volume : Measure (Vec3 × ℝ)) ≤ η₂ :=
    ENNReal.tendsto_nhds_zero.1
      (tendsto_eLpNorm_sub_zero_spaceTimeMollify_of_continuous
        (by norm_num) hf'_cont hf'_supp hε hε_pos) η₂ hη₂_pos
  filter_upwards [hmid_eventually] with n hmid
  let k : Vec3 × ℝ → ℝ := spaceTimeMollifier (ε n) (hε_pos n)
  have hk_compact : HasCompactSupport k := spaceTimeMollifier_hasCompactSupport (hε_pos n)
  have hk_cont : Continuous k := (spaceTimeMollifier_contDiff (hε_pos n) (n := 0)).continuous
  have hg_loc : LocallyIntegrable g (volume : Measure (Vec3 × ℝ)) :=
    hg.locallyIntegrable (by norm_num)
  have hf'_loc : LocallyIntegrable f' (volume : Measure (Vec3 × ℝ)) :=
    hf'_mem.locallyIntegrable (by norm_num)
  have hdiff_loc : LocallyIntegrable (fun x => g x - f' x)
      (volume : Measure (Vec3 × ℝ)) := hg_loc.sub hf'_loc
  have hconv_g : ConvolutionExists k g (ContinuousLinearMap.lsmul ℝ ℝ)
      (volume : Measure (Vec3 × ℝ)) :=
    spaceTimeConvolutionExists_left hk_compact hk_cont hg_loc
  have hconv_f : ConvolutionExists k f' (ContinuousLinearMap.lsmul ℝ ℝ)
      (volume : Measure (Vec3 × ℝ)) :=
    spaceTimeConvolutionExists_left hk_compact hk_cont hf'_loc
  have hconv_diff : ConvolutionExists k (fun x => g x - f' x)
      (ContinuousLinearMap.lsmul ℝ ℝ) (volume : Measure (Vec3 × ℝ)) :=
    spaceTimeConvolutionExists_left hk_compact hk_cont hdiff_loc
  have hsplit : g = (fun x => g x - f' x) + f' := by
    ext x
    change g x = (g x - f' x) + f' x
    abel_nf
  have hconv_split :
      k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g =
        (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun x => g x - f' x) +
          k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f' := by
    calc
      k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g =
          k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ((fun x => g x - f' x) + f') := by
            exact congrArg (fun v => k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] v) hsplit
      _ = (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun x => g x - f' x) +
          k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f' := hconv_diff.distrib_add hconv_f
  have hfirst_norm :
      eLpNorm (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun x => g x - f' x)
        2 (volume : Measure (Vec3 × ℝ)) ≤ η₂ := by
    calc
      eLpNorm (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun x => g x - f' x)
          2 (volume : Measure (Vec3 × ℝ)) ≤
        eLpNorm (fun x => g x - f' x) 2 (volume : Measure (Vec3 × ℝ)) := by
          simpa only [spaceTimeMollify, k] using
            (spaceTimeMollify_eLpNorm_le (hε_pos n) hdiff_mem)
      _ ≤ η₂ := happrox'.trans (min_le_right _ _)
  have hfirst_middle :
      eLpNorm
        ((k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun x => g x - f' x) +
          fun x => (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f') x - f' x)
        2 (volume : Measure (Vec3 × ℝ)) < η₁ := by
    exact hη₂ _ _ hfirst_norm (by simpa only [spaceTimeMollify, k] using hmid)
  have hsum :
      eLpNorm
        (((k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun x => g x - f' x) +
          fun x => (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f') x - f' x) +
          fun x => f' x - g x)
        2 (volume : Measure (Vec3 × ℝ)) < η :=
    hη₁ _ _ hfirst_middle.le hthird_norm
  have hdecomp :
      eLpNorm
        (fun x => spaceTimeMollify g (ε n) (hε_pos n) x - g x)
        2 (volume : Measure (Vec3 × ℝ)) =
      eLpNorm
        (((k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun x => g x - f' x) +
          fun x => (k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f') x - f' x) +
          fun x => f' x - g x)
        2 (volume : Measure (Vec3 × ℝ)) := by
    rw [show spaceTimeMollify g (ε n) (hε_pos n) =
        k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g by rfl, hconv_split]
    congr 1
    ext x
    simp only [Pi.add_apply]
    abel_nf
  exact hdecomp ▸ hsum.le


end CKN
