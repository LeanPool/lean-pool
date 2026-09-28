/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Complex.MeanValue
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Convex.Gauge
public import Mathlib.Analysis.Convex.GaugeRescale
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Affine.ContinuousAffineMap
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.List.MinMax
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.Tactic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Separation.Lemmas

/-!
# Moving sofa: related mathematical developments

* `ForMathlib.Analysis.Calculus.Deriv.Shift`.
* `ForMathlib.Analysis.Calculus.FirstReturn`.
* `ForMathlib.Analysis.Calculus.Interval`.
* `ForMathlib.Analysis.Calculus.LocalExtr.OneSided`.
* `ForMathlib.Analysis.Complex.DiskIntegral`.
* `ForMathlib.Analysis.Convex.Basic`.
* `ForMathlib.Analysis.Convex.Deriv`.
* `ForMathlib.Analysis.Convex.Gauge`.
* `ForMathlib.Analysis.Convex.GaugeRescale`.
* `ForMathlib.Analysis.Convex.Radial`.
* `ForMathlib.Analysis.FiniteEnvelope`.
* `ForMathlib.Analysis.InnerProductSpace.Box`.
* `ForMathlib.Analysis.InnerProductSpace.Linear`.
* `ForMathlib.Analysis.Normed.Affine.ContinuousAffineMap`.
* `ForMathlib.Analysis.SpecialFunctions.Angle`.
* `ForMathlib.Analysis.SpecialFunctions.AngleLift`.
* `ForMathlib.Analysis.SpecialFunctions.Arctan`.
* `ForMathlib.Analysis.SpecificLimits.AlternatingBracket`.
* `ForMathlib.Analysis.SpecialFunctions.Trigonometric`.
-/

@[expose] public section

noncomputable section


section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Shifting the base point of a derivative

`HasDerivAt.comp_add_const` transports a derivative at a shifted base point to the shifted
function; this file records the converse implication, packaged as an `Iff`.
-/

@[expose] public section

/-- A derivative at a shifted base point is the derivative of the shifted function. -/
theorem hasDerivAt_comp_add_const_iff {𝕜 : Type*} [NontriviallyNormedField 𝕜] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : 𝕜 → F} {f' : F} (x a : 𝕜) :
    HasDerivAt (fun u ↦ f (u + a)) f' x ↔ HasDerivAt f f' (x + a) := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.comp_add_const x a⟩
  have h' : HasDerivAt (fun u ↦ f (u + a)) f' (x + a + -a) := by simpa using h
  simpa using h'.comp_add_const (x + a) (-a)

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# First return to a level

A continuous real function that starts strictly below a level and reaches it has a smallest
time at which it attains that level, and its derivative there is nonnegative.
-/

@[expose] public section

/-- A continuous function below a level at the left end has a first return to that level. -/
theorem exists_first_return {g : ℝ → ℝ} {a b c : ℝ} (hab : a < b)
    (hcont : ContinuousOn g (Set.Icc a b)) (hga : g a < c) (hgb : c ≤ g b) :
    ∃ t ∈ Set.Ioc a b, g t = c ∧ ∀ u ∈ Set.Ico a t, g u < c := by
  set E : Set ℝ := Set.Icc a b ∩ g ⁻¹' Set.Ici c with hE
  have hEcl : IsClosed E := hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hEne : E.Nonempty := ⟨b, ⟨hab.le, le_refl b⟩, hgb⟩
  have hEbdd : BddBelow E := ⟨a, fun u hu => hu.1.1⟩
  set t : ℝ := sInf E with ht
  have htE : t ∈ E := hEcl.csInf_mem hEne hEbdd
  have htlb : ∀ u ∈ E, t ≤ u := fun u hu => csInf_le hEbdd hu
  have hta : a < t := by
    rcases eq_or_lt_of_le htE.1.1 with h | h
    · exact absurd htE.2 (by rw [← h]; exact not_le.mpr hga)
    · exact h
  have hleft : ∀ u ∈ Set.Ico a t, g u < c := by
    intro u hu
    by_contra hcc
    push Not at hcc
    exact absurd (htlb u ⟨⟨hu.1, le_trans hu.2.le htE.1.2⟩, hcc⟩) (not_le.mpr hu.2)
  have hIco : Set.Ico a t ∈ nhdsWithin t (Set.Iio t) := Ico_mem_nhdsLT hta
  have hsub : Set.Ico a t ⊆ Set.Icc a b := fun u hu => ⟨hu.1, le_trans hu.2.le htE.1.2⟩
  have htend : Filter.Tendsto g (nhdsWithin t (Set.Iio t)) (nhds (g t)) :=
    ((hcont t htE.1).mono hsub).tendsto.mono_left (nhdsWithin_le_of_mem hIco)
  refine ⟨t, ⟨hta, htE.1.2⟩, le_antisymm ?_ htE.2, hleft⟩
  exact le_of_tendsto htend (Filter.eventually_of_mem hIco fun u hu => (hleft u hu).le)

/-- At a first return from below, the derivative is nonnegative. -/
theorem nonneg_of_first_return {g : ℝ → ℝ} {a t c d : ℝ} (hat : a < t)
    (hd : HasDerivAt g d t) (hgt : g t = c) (hleft : ∀ u ∈ Set.Ico a t, g u < c) :
    0 ≤ d := by
  have hIco : Set.Ico a t ∈ nhdsWithin t (Set.Iio t) := Ico_mem_nhdsLT hat
  have hsl := (hasDerivAt_iff_tendsto_slope.mp hd).mono_left
    (nhdsWithin_mono t (fun x hx => ne_of_lt hx) :
      nhdsWithin t (Set.Iio t) ≤ nhdsWithin t {t}ᶜ)
  refine ge_of_tendsto hsl (Filter.eventually_of_mem hIco fun u hu => ?_)
  rw [slope_def_field, hgt]
  exact le_of_lt (div_pos_of_neg_of_neg (by linarith only [hleft u hu])
    (by linarith only [hu.2]))

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Analysis / Calculus / Interval
-/

@[expose] public section

open Set

/-- Glue one-sided derivatives on a closed interval, including its endpoints. -/
theorem hasDerivWithinAt_Icc_of_oneSided {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {a b t : ℝ} (hab : a < b)
    (ht : t ∈ Icc a b) {f : ℝ → E} {d : E}
    (hr : t < b → HasDerivWithinAt f d (Ici t) t)
    (hl : a < t → HasDerivWithinAt f d (Iic t) t) :
    HasDerivWithinAt f d (Icc a b) t := by
  rcases eq_or_lt_of_le ht.1 with rfl | hat
  · exact (hr hab).mono Icc_subset_Ici_self
  · rcases lt_or_eq_of_le ht.2 with htb | rfl
    · have h := (hl hat).union (hr htb)
      rw [Iic_union_Ici] at h
      exact h.mono (subset_univ _)
    · exact (hl hat).mono Icc_subset_Iic_self

/-- A continuous derivative field on a uniquely differentiable set gives order-one regularity. -/
theorem contDiffOn_one_of_continuous_derivative {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set ℝ}
    (hs : UniqueDiffOn ℝ s) (f : ℝ → E) (d : s → E) (hd : Continuous d)
    (hf : ∀ t : s, HasDerivWithinAt f (d t) s t) : ContDiffOn ℝ 1 f s := by
  apply (contDiffOn_one_iff_derivWithin hs).mpr
  refine ⟨fun t ht ↦ (hf ⟨t, ht⟩).differentiableWithinAt, ?_⟩
  apply continuousOn_iff_continuous_domRestrict.mpr
  apply hd.congr
  intro t
  exact ((hf t).derivWithin (hs t t.property)).symm

/-- Glue two everywhere differentiable functions along the switch `{s ≤ c}`.  If the values
and the derivatives agree at `c`, the glued function is differentiable everywhere and its
derivative is the analogous glue of the two derivative fields.  At `c` itself the statement
is genuine two-sided differentiability, obtained from the two one-sided derivatives. -/
theorem hasDerivAt_if_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g f' g' : ℝ → E} {c : ℝ}
    (hf : ∀ t, HasDerivAt f (f' t) t) (hg : ∀ t, HasDerivAt g (g' t) t)
    (hfg : f c = g c) (hfg' : f' c = g' c) (t : ℝ) :
    HasDerivAt (fun s => if s ≤ c then f s else g s) (if t ≤ c then f' t else g' t) t := by
  rcases lt_trichotomy t c with ht | ht | ht
  · rw [ite_eq_left ht.le]
    refine (hf t).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds ht] with s hs
    exact ite_eq_left (le_of_lt hs)
  · subst ht
    rw [ite_eq_left le_rfl]
    have hl : HasDerivWithinAt (fun s => if s ≤ t then f s else g s) (f' t) (Iic t) t :=
      (hf t).hasDerivWithinAt.congr (fun _ hs => ite_eq_left hs) (ite_eq_left le_rfl)
    have hr : HasDerivWithinAt (fun s => if s ≤ t then f s else g s) (f' t) (Ici t) t := by
      rw [hfg']
      refine (hg t).hasDerivWithinAt.congr (fun s hs => ?_) (by rw [ite_eq_left le_rfl, hfg])
      rcases eq_or_lt_of_le (mem_Ici.mp hs) with rfl | hlt
      · rw [ite_eq_left le_rfl, hfg]
      · rw [ite_eq_right (not_le.mpr hlt)]
    have hu := hl.union hr
    rw [Iic_union_Ici] at hu
    exact hasDerivWithinAt_univ.mp hu
  · rw [ite_eq_right (not_le.mpr ht)]
    refine (hg t).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact ite_eq_right (not_le.mpr hs)

/-- A globally defined continuous derivative field witnesses continuous differentiability. -/
theorem contDiff_one_of_hasDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f f' : ℝ → E} (hf : ∀ t, HasDerivAt f (f' t) t) (hf' : Continuous f') :
    ContDiff ℝ 1 f :=
  contDiff_one_iff_deriv.2 ⟨fun t => (hf t).differentiableAt, deriv_eq hf ▸ hf'⟩

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Fermat's theorem for one-sided derivatives on the real line

`IsLocalMinOn.hasFDerivWithinAt_nonneg` signs a derivative within a set against the positive
tangent cone of that set.  On the real line the positive tangent cones of the two half-lines
at `a` are generated by `1` and by `-1`, which turns that statement into the two familiar
one-sided derivative tests at a one-sided minimum.
-/

@[expose] public section

/-- The forward direction belongs to the positive tangent cone of a right half-line. -/
theorem one_mem_posTangentConeAt_Ici (a : ℝ) : (1 : ℝ) ∈ posTangentConeAt (Set.Ici a) a :=
  mem_posTangentConeAt_of_segment_subset
    ((convex_Ici a).segment_subset (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 (by linarith)))

/-- The backward direction belongs to the positive tangent cone of a left half-line. -/
theorem neg_one_mem_posTangentConeAt_Iic (a : ℝ) :
    (-1 : ℝ) ∈ posTangentConeAt (Set.Iic a) a :=
  mem_posTangentConeAt_of_segment_subset
    ((convex_Iic a).segment_subset (Set.mem_Iic.2 le_rfl) (Set.mem_Iic.2 (by linarith)))

/-- A right derivative at a minimum over a right half-line is nonnegative. -/
theorem IsLocalMinOn.hasDerivWithinAt_Ici_nonneg {f : ℝ → ℝ} {f' a : ℝ}
    (h : IsLocalMinOn f (Set.Ici a) a) (hf : HasDerivWithinAt f f' (Set.Ici a) a) : 0 ≤ f' := by
  simpa using h.hasFDerivWithinAt_nonneg hf (one_mem_posTangentConeAt_Ici a)

/-- A left derivative at a minimum over a left half-line is nonpositive. -/
theorem IsLocalMinOn.hasDerivWithinAt_Iic_nonpos {f : ℝ → ℝ} {f' a : ℝ}
    (h : IsLocalMinOn f (Set.Iic a) a) (hf : HasDerivWithinAt f f' (Set.Iic a) a) : f' ≤ 0 :=
  neg_nonneg.1 <| by
    simpa using h.hasFDerivWithinAt_nonneg hf (neg_one_mem_posTangentConeAt_Iic a)

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Analysis / Complex / Disk Integral
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Complex

private theorem integrableOn_polarCoord_target
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : ℝ × ℝ → F) (hg : Integrable g) :
    IntegrableOn (fun p : ℝ × ℝ ↦ p.1 • g (polarCoord.symm p))
      polarCoord.target := by
  have hinj : Set.InjOn (polarCoord.symm : ℝ × ℝ → ℝ × ℝ)
      polarCoord.target := by
    rw [← polarCoord.symm_source]
    exact polarCoord.symm.injOn
  have himage : polarCoord.symm '' polarCoord.target =
      polarCoord.source := by
    rw [← polarCoord.symm_source, ← polarCoord.symm_target]
    exact polarCoord.symm.image_source_eq_target
  have hj := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul
    (s := polarCoord.target) volume polarCoord.open_target.measurableSet
    (fun p _ ↦ (hasFDerivAt_polarCoord_symm p).hasFDerivWithinAt)
    hinj g).mp (by
      rw [himage]
      exact hg.integrableOn)
  refine hj.congr_fun ?_ polarCoord.open_target.measurableSet
  intro p hp
  dsimp only
  rw [det_fderivPolarCoordSymm, abs_of_pos hp.1]

private theorem integrableOn_complex_polarCoord_target
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℂ → F) (hf : Integrable f) :
    IntegrableOn (fun p : ℝ × ℝ ↦ p.1 • f (Complex.polarCoord.symm p))
      Complex.polarCoord.target := by
  rw [Complex.polarCoord_target]
  let g : ℝ × ℝ → F := f ∘ Complex.measurableEquivRealProd.symm
  have hg : Integrable g :=
    ((Complex.volume_preserving_equiv_real_prod.symm).integrable_comp_emb
      Complex.measurableEquivRealProd.symm.measurableEmbedding).mpr hf
  have h := integrableOn_polarCoord_target g hg
  change IntegrableOn
    (fun p ↦ p.1 • (f ∘ Complex.measurableEquivRealProd.symm)
      (polarCoord.symm p)) (Set.Ioi 0 ×ˢ Set.Ioo (-Real.pi) Real.pi) at h
  simpa only [Function.comp_apply,
    Complex.measurableEquivRealProd_symm_polarCoord_symm_apply] using h

private theorem integral_circleMap_Ioo_eq_circleAverage
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℂ → E) (r : ℝ) :
    (∫ θ in Set.Ioo (-Real.pi) Real.pi, f (circleMap 0 r θ)) =
      (2 * Real.pi) • Real.circleAverage f 0 r := by
  rw [Real.circleAverage_eq_integral_add (-Real.pi), smul_smul]
  have hp : (2 * Real.pi) * (2 * Real.pi)⁻¹ = 1 := by
    field_simp [Real.pi_ne_zero]
  rw [hp, one_smul, ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (le_of_lt (neg_lt_self Real.pi_pos))]
  have hshift := intervalIntegral.integral_comp_add_right
    (f := fun θ ↦ f (circleMap 0 r θ)) (a := 0) (b := 2 * Real.pi) (-Real.pi)
  simpa [two_mul] using hshift.symm

/-- The radial profile of the inverse distance truncated to a disk of radius `S`. -/
private def invNormCutoff (S r : ℝ) : ℝ := if r < S then r⁻¹ else 0

private theorem indicator_ball_inv_norm_eq (S : ℝ) :
    (fun p : ℂ ↦ (Metric.ball 0 S).indicator (fun p ↦ ‖p‖⁻¹) p) =
      fun p ↦ invNormCutoff S ‖p‖ := by
  funext p
  rw [Set.indicator]
  simp only [Metric.mem_ball, dist_zero_right, invNormCutoff]

private theorem radial_invNormCutoff_ae (S : ℝ) :
    (fun y : ℝ ↦ y ^ (Module.finrank ℝ ℂ - 1) • invNormCutoff S y)
      =ᵐ[volume.restrict (Set.Ioi 0)]
      (Set.Iio S).indicator (fun _ ↦ (1 : ℝ)) := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  have hy0 : y ≠ 0 := ne_of_gt hy
  simp [invNormCutoff, Set.indicator, smul_eq_mul, hy0]

/-- Inverse distance from zero is integrable on a complex disk centred at zero. -/
theorem integrableOn_inv_norm_ball (S : ℝ) :
    IntegrableOn (fun p : ℂ ↦ ‖p‖⁻¹) (Metric.ball 0 S) := by
  rw [← integrable_indicator_iff measurableSet_ball]
  change Integrable (fun p : ℂ ↦ (Metric.ball 0 S).indicator (fun p ↦ ‖p‖⁻¹) p)
  rw [indicator_ball_inv_norm_eq,
    MeasureTheory.integrable_fun_norm_addHaar volume (f := invNormCutoff S)]
  refine IntegrableOn.congr_fun_ae ?_ (radial_invNormCutoff_ae S).symm
  rw [integrableOn_indicator_iff measurableSet_Iio, Set.Iio_inter_Ioi]
  exact integrableOn_const (by simp)

/-- The integral of inverse distance from zero over a complex disk centred at zero. -/
theorem setIntegral_inv_norm_ball (S : ℝ) (hS : 0 < S) :
    (∫ p : ℂ in Metric.ball 0 S, ‖p‖⁻¹) = 2 * Real.pi * S := by
  rw [← integral_indicator (f := fun p : ℂ ↦ ‖p‖⁻¹) measurableSet_ball,
    indicator_ball_inv_norm_eq,
    MeasureTheory.integral_fun_norm_addHaar volume (invNormCutoff S),
    integral_congr_ae (radial_invNormCutoff_ae S),
    setIntegral_indicator measurableSet_Iio, Set.Ioi_inter_Iio]
  simp [hS.le, Measure.real, Complex.volume_ball, mul_assoc]

private theorem integrableOn_inv_sub_ball (R : ℝ) (a : ℂ) (ha : ‖a‖ < R) :
    IntegrableOn (fun q : ℂ ↦ (a - q)⁻¹) (Metric.ball 0 R) := by
  rw [← integrable_indicator_iff measurableSet_ball]
  let g : ℂ → ℝ :=
    (Metric.ball a (2 * R)).indicator (fun q ↦ ‖a - q‖⁻¹)
  have hg : Integrable g := by
    have hcenter : (fun q : ℂ ↦
        (Metric.ball a (2 * R)).indicator (fun q ↦ ‖a - q‖⁻¹) q) =
        fun q ↦ (Metric.ball 0 (2 * R)).indicator (fun w ↦ ‖w‖⁻¹) (a - q) := by
      funext q
      have hm : q ∈ Metric.ball a (2 * R) ↔ a - q ∈ Metric.ball 0 (2 * R) := by
        simp only [Metric.mem_ball, dist_eq_norm]
        simp [sub_zero, norm_sub_rev]
      by_cases hq : q ∈ Metric.ball a (2 * R)
      · simp [hq, hm.mp hq]
      · simp [hq, mt hm.mpr hq]
    change Integrable (fun q : ℂ ↦
      (Metric.ball a (2 * R)).indicator (fun q ↦ ‖a - q‖⁻¹) q)
    rw [hcenter, MeasureTheory.integrable_comp_sub_left]
    exact (integrable_indicator_iff measurableSet_ball).mpr
      (integrableOn_inv_norm_ball (2 * R))
  refine Integrable.mono' hg ?_ ?_
  · exact ((measurable_const.sub measurable_id).inv.indicator
      measurableSet_ball).aestronglyMeasurable
  · filter_upwards with q
    by_cases hq : q ∈ Metric.ball (0 : ℂ) R
    · have hqa : q ∈ Metric.ball a (2 * R) := by
        rw [Metric.mem_ball, dist_eq_norm]
        have hqR : ‖q‖ < R := by simpa [Metric.mem_ball, dist_eq_norm] using hq
        calc
          ‖q - a‖ ≤ ‖q‖ + ‖a‖ := norm_sub_le q a
          _ < R + R := add_lt_add hqR ha
          _ = 2 * R := by ring
      simp only [Set.indicator_of_mem hq, norm_inv]
      simp [g, hqa]
    · simp only [Set.indicator, hq, ↓reduceIte, norm_zero]
      exact Set.indicator_apply_nonneg fun _ ↦ by positivity

private theorem circleAverage_inv_sub_eq_inv_of_radius_lt_norm
    (a : ℂ) (r : ℝ) (hr : 0 ≤ r) (hout : r < ‖a‖) :
    Real.circleAverage (fun w ↦ (a - w)⁻¹) 0 r = a⁻¹ := by
  have hne : ∀ w ∈ Metric.closedBall (0 : ℂ) |r|, a - w ≠ 0 := by
    intro w hw hwa
    have hwa' : w = a := (sub_eq_zero.mp hwa).symm
    subst a
    have : ‖w‖ ≤ r := by simpa [abs_of_nonneg hr, dist_eq_norm] using hw
    linarith
  have hcont : ContinuousOn (fun w : ℂ ↦ (a - w)⁻¹) (Metric.closedBall 0 |r|) :=
    ((continuous_const.sub continuous_id).continuousOn).inv₀ hne
  have hdiff : DiffContOnCl ℂ (fun w : ℂ ↦ (a - w)⁻¹) (Metric.ball 0 |r|) :=
    DiffContOnCl.mk_ball
      (fun w hw ↦ (((differentiableAt_const a).sub differentiableAt_id).inv
        (hne w (Metric.ball_subset_closedBall hw))).differentiableWithinAt) hcont
  simpa using hdiff.circleAverage

private theorem partialFraction_circleIntegral_congr (a : ℂ) (r : ℝ) (hr : 0 < r)
    (ha : a ≠ 0) (hra : ‖a‖ ≠ r) :
    (∮ w in C(0, r), (w - 0)⁻¹ * (a - w)⁻¹) =
      ∮ w in C(0, r), a⁻¹ * ((w - 0)⁻¹ - (w - a)⁻¹) := by
  refine circleIntegral.integral_congr hr.le fun w hw ↦ ?_
  have hw0 : w ≠ 0 := by
    intro h
    subst w
    have hz : (0 : ℝ) = r := by simpa using (Metric.mem_sphere.mp hw)
    linarith
  have hwa : w ≠ a := by
    intro h
    subst w
    exact hra (by simpa [dist_eq_norm] using (Metric.mem_sphere.mp hw))
  field_simp
  ring

private theorem circleIntegrable_sub_inv_of_norm_ne (a : ℂ) (r : ℝ) (hr : 0 < r)
    (hra : ‖a‖ ≠ r) : CircleIntegrable (fun w : ℂ ↦ (w - a)⁻¹) 0 r :=
  circleIntegrable_sub_inv_iff.mpr (Or.inr fun h ↦
    hra (by simpa [dist_eq_norm, abs_of_pos hr] using (Metric.mem_sphere.mp h)))

private theorem circleAverage_inv_sub_eq_zero_of_norm_lt_radius
    (a : ℂ) (r : ℝ) (hr : 0 < r) (ha : a ≠ 0) (hinner : ‖a‖ < r) :
    Real.circleAverage (fun w ↦ (a - w)⁻¹) 0 r = 0 := by
  rw [Real.circleAverage_eq_circleIntegral hr.ne']
  change (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
      (∮ z in C(0, r), (z - 0)⁻¹ * (a - z)⁻¹) = 0
  have hmem : a ∈ Metric.ball (0 : ℂ) r := by
    simpa [Metric.mem_ball, dist_eq_norm] using hinner
  rw [partialFraction_circleIntegral_congr a r hr ha hinner.ne,
    circleIntegral.integral_const_mul,
    circleIntegral.integral_sub
      (circleIntegrable_sub_inv_of_norm_ne 0 r hr (by simpa using hr.ne))
      (circleIntegrable_sub_inv_of_norm_ne a r hr hinner.ne),
    circleIntegral.integral_sub_center_inv 0 hr.ne',
    circleIntegral.integral_sub_inv_of_mem_ball hmem]
  simp

private theorem setIntegral_inv_sub_ball_of_ne_zero (R : ℝ) (a : ℂ) (ha0 : a ≠ 0)
    (ha : ‖a‖ < R) :
    (∫ q in Metric.ball 0 R, (a - q)⁻¹) = Real.pi * starRingEnd ℂ a := by
  let f : ℂ → ℂ := (Metric.ball 0 R).indicator (fun q ↦ (a - q)⁻¹)
  have hf : Integrable f :=
    (integrable_indicator_iff measurableSet_ball).mpr (integrableOn_inv_sub_ball R a ha)
  have hpInt := integrableOn_complex_polarCoord_target f hf
  have hpolar := Complex.integral_comp_polarCoord_symm f
  have hprod :
      (∫ p in polarCoord.target,
        p.1 • f (Complex.polarCoord.symm p)) =
        ∫ r in Set.Ioi (0 : ℝ), ∫ θ in Set.Ioo (-Real.pi) Real.pi,
          r • f (Complex.polarCoord.symm (r, θ)) := by
    change (∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
      p.1 • f (Complex.polarCoord.symm p)) = _
    exact setIntegral_prod _ (by
      rw [← Measure.volume_eq_prod ℝ ℝ]
      simpa only [Complex.polarCoord_target] using hpInt)
  rw [← integral_indicator measurableSet_ball]
  change (∫ q, f q) = _
  rw [← hpolar, hprod]
  have hinner : ∀ r ∈ Set.Ioi (0 : ℝ),
      (∫ θ in Set.Ioo (-Real.pi) Real.pi,
          r • f (Complex.polarCoord.symm (r, θ))) =
        if r < R then r • ((2 * Real.pi) •
          Real.circleAverage (fun q ↦ (a - q)⁻¹) 0 r) else 0 := by
    intro r hr
    have hr0 : 0 < r := hr
    have hpoint : ∀ θ, Complex.polarCoord.symm (r, θ) = circleMap 0 r θ := by
      intro θ
      rw [Complex.polarCoord_symm_apply, circleMap_zero, Complex.exp_mul_I]
      simp
    by_cases hrR : r < R
    · simp only [hrR, ↓reduceIte]
      have hmem : ∀ θ, Complex.polarCoord.symm (r, θ) ∈ Metric.ball (0 : ℂ) R := by
        intro θ
        rw [hpoint]
        simpa [Metric.mem_ball, dist_eq_norm, abs_of_pos hr0] using hrR
      simp_rw [f, Set.indicator_of_mem (hmem _), hpoint]
      rw [integral_smul]
      rw [integral_circleMap_Ioo_eq_circleAverage (fun q ↦ (a - q)⁻¹) r]
    · simp only [hrR, ↓reduceIte]
      have hnotmem : ∀ θ, Complex.polarCoord.symm (r, θ) ∉ Metric.ball (0 : ℂ) R := by
        intro θ hθ
        rw [hpoint] at hθ
        have : r < R := by
          simpa [Metric.mem_ball, dist_eq_norm, abs_of_pos hr0] using hθ
        exact hrR this
      simp_rw [f, Set.indicator, hnotmem]
      simp
  rw [setIntegral_congr_fun measurableSet_Ioi hinner]
  have hradial :
      (fun r : ℝ ↦ if r < R then r • ((2 * Real.pi) •
        Real.circleAverage (fun q ↦ (a - q)⁻¹) 0 r) else 0)
        =ᵐ[volume.restrict (Set.Ioi 0)]
      fun r ↦ if r < ‖a‖ then r • ((2 * Real.pi) • a⁻¹) else 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi,
      ae_restrict_of_ae (Measure.ae_ne volume ‖a‖)] with r hr hra
    have hr0 : 0 < r := hr
    by_cases hra' : r < ‖a‖
    · have hrR : r < R := hra'.trans ha
      simp only [hrR, hra', ↓reduceIte]
      rw [circleAverage_inv_sub_eq_inv_of_radius_lt_norm a r hr0.le hra']
    · have har : ‖a‖ < r := lt_of_le_of_ne (le_of_not_gt hra') (Ne.symm hra)
      by_cases hrR : r < R
      · simp only [hrR, hra', ↓reduceIte]
        rw [circleAverage_inv_sub_eq_zero_of_norm_lt_radius a r hr0 ha0 har, smul_zero]
        simp
      · simp only [hrR, hra', ↓reduceIte]
  rw [integral_congr_ae hradial]
  rw [show (fun r : ℝ ↦ if r < ‖a‖ then r • ((2 * Real.pi) • a⁻¹) else 0) =
      (Set.Iio ‖a‖).indicator (fun r ↦ r • ((2 * Real.pi) • a⁻¹)) by
    funext r
    simp [Set.indicator]]
  rw [setIntegral_indicator measurableSet_Iio, Set.Ioi_inter_Iio]
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (norm_nonneg a)]
  rw [intervalIntegral.integral_smul_const]
  rw [integral_id]
  rw [Complex.inv_def]
  simp only [starRingEnd_apply, Complex.normSq_eq_norm_sq, Complex.real_smul]
  have hnorm : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha0
  have hnormc : (‖a‖ : ℂ) ≠ 0 := by exact_mod_cast hnorm
  push_cast
  field_simp [hnormc]
  ring

private theorem setIntegral_inv_sub_ball_zero (R : ℝ) :
    (∫ q in Metric.ball 0 R, ((0 : ℂ) - q)⁻¹) = 0 := by
  rw [← integral_indicator (f := fun q : ℂ ↦ ((0 : ℂ) - q)⁻¹) measurableSet_ball]
  let f : ℂ → ℂ := (Metric.ball 0 R).indicator (fun q ↦ ((0 : ℂ) - q)⁻¹)
  have hodd : ∀ q, f (-q) = -f q := by
    intro q
    have hm : -q ∈ Metric.ball (0 : ℂ) R ↔ q ∈ Metric.ball 0 R := by
      simp [Metric.mem_ball, dist_eq_norm]
    by_cases hq : q ∈ Metric.ball (0 : ℂ) R
    · simp [f, hq, hm.mpr hq]
    · simp [f, hq, mt hm.mp hq]
  have hneg : (∫ q, f (-q)) = -(∫ q, f q) := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hodd), integral_neg]
  have hself : (∫ q, f q) = -(∫ q, f q) :=
    (MeasureTheory.integral_neg_eq_self f volume).symm.trans hneg
  have ht : (2 : ℝ) • (∫ q, f q) = 0 := by
    rw [two_smul]
    calc
      (∫ q, f q) + ∫ q, f q = -(∫ q, f q) + ∫ q, f q :=
        congrArg (fun x ↦ x + ∫ q, f q) hself
      _ = 0 := neg_add_cancel _
  exact (smul_eq_zero.mp ht).resolve_left (by norm_num)

/-- The integral of `q ↦ (a - q)⁻¹` over a disk centred at zero containing `a`. -/
theorem setIntegral_inv_sub_ball (R : ℝ) (a : ℂ) (ha : ‖a‖ < R) :
    (∫ q in Metric.ball 0 R, (a - q)⁻¹) = Real.pi * starRingEnd ℂ a := by
  by_cases ha0 : a = 0
  · subst a
    simpa using setIntegral_inv_sub_ball_zero R
  · exact setIntegral_inv_sub_ball_of_ne_zero R a ha0 ha

end Complex

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Analysis / Convex / Basic
-/

@[expose] public section

namespace Convex

/-- Every nonnegative scalar between zero and a known scalar multiple stays in a convex set. -/
theorem smul_mem_of_nonneg_of_le {E : Type*} [AddCommGroup E] [Module ℝ E]
    {s : Set E} (hs : Convex ℝ s) {v : E} {x a : ℝ}
    (hzero : (0 : E) ∈ s) (ha : a • v ∈ s) (hx : 0 ≤ x) (hxa : x ≤ a) :
    x • v ∈ s := by
  by_cases ha0 : a = 0
  · have hx0 : x = 0 := by linarith
    simpa [hx0] using hzero
  · have hapos : 0 < a := lt_of_le_of_ne (hx.trans hxa) (Ne.symm ha0)
    have hratio : x / a ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨div_nonneg hx hapos.le, (div_le_one hapos).2 hxa⟩
    have hmem := hs.smul_mem_of_zero_mem hzero ha hratio
    simpa only [smul_smul, div_mul_cancel₀ x ha0] using hmem

end Convex

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Analysis / Convex / Deriv
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace ConcaveOn

/-- A differentiable concave real function lies below its tangent line. -/
theorem le_add_deriv_mul_sub {s : Set ℝ} {g : ℝ → ℝ}
    (hg : ConcaveOn ℝ s g) {x : ℝ} (hx : x ∈ s)
    (hdiff : DifferentiableAt ℝ g x) {y : ℝ} (hy : y ∈ s) :
    g y ≤ g x + deriv g x * (y - x) := by
  rcases lt_trichotomy y x with hyx | rfl | hxy
  · have hslope := hg.deriv_le_slope hy hx hyx hdiff
    rw [slope] at hslope
    have hpos : 0 < x - y := sub_pos.mpr hyx
    have hs : deriv g x * (x - y) ≤ g x - g y := by
      apply (le_div_iff₀ hpos).mp
      simpa [smul_eq_mul, inv_mul_eq_div] using hslope
    nlinarith
  · simp
  · have hslope := hg.slope_le_of_hasDerivAt hx hy hxy hdiff.hasDerivAt
    rw [slope] at hslope
    have hpos : 0 < y - x := sub_pos.mpr hxy
    have hs : g y - g x ≤ deriv g x * (y - x) := by
      apply (div_le_iff₀ hpos).mp
      simpa [smul_eq_mul, inv_mul_eq_div] using hslope
    linarith

/-- Pointwise convergence of concave functions forces derivative convergence at a common
differentiability point in the interior of an interval. -/
theorem tendsto_deriv_of_tendsto_Ioo {ι : Type*} {F : Filter ι}
    {f : ι → ℝ → ℝ} {g : ℝ → ℝ}
    {a b x : ℝ} (hx : x ∈ Ioo a b)
    (hf : ∀ᶠ n in F, ConcaveOn ℝ (Ioo a b) (f n))
    (hlim : ∀ y ∈ Ioo a b, Tendsto (fun n ↦ f n y) F (𝓝 (g y)))
    (hdf : ∀ᶠ n in F, DifferentiableAt ℝ (f n) x)
    (hdg : DifferentiableAt ℝ g x) :
    Tendsto (fun n ↦ deriv (f n) x) F (𝓝 (deriv g x)) := by
  have hslope (y : ℝ) (hy : y ∈ Ioo a b) :
      Tendsto (fun n ↦ slope (f n) x y) F (𝓝 (slope g x y)) := by
    simpa only [slope, smul_eq_mul, vsub_eq_sub] using
      ((hlim y hy).sub (hlim x hx)).const_mul (y - x)⁻¹
  have hnear : ∀ᶠ y in 𝓝 x, y ∈ Ioo a b := isOpen_Ioo.mem_nhds hx
  apply tendsto_order.mpr
  constructor
  · intro l hl
    have hright := hdg.hasDerivAt.tendsto_slope.mono_left (nhdsGT_le_nhdsNE x)
    have hgood : ∀ᶠ y in 𝓝[>] x, y ∈ Ioo a b ∧ x < y ∧ l < slope g x y := by
      filter_upwards [hnear.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin,
        hright.eventually (lt_mem_nhds hl)] with y hy hxy hsy
      exact ⟨hy, hxy, hsy⟩
    obtain ⟨y, hy, hxy, hly⟩ := hgood.exists
    filter_upwards [hf, hdf, (hslope y hy).eventually (lt_mem_nhds hly)] with n hfn hdn hn
    exact hn.trans_le (hfn.slope_le_of_hasDerivAt hx hy hxy hdn.hasDerivAt)
  · intro u hu
    have hleft := hdg.hasDerivAt.tendsto_slope.mono_left (nhdsLT_le_nhdsNE x)
    have hgood : ∀ᶠ y in 𝓝[<] x, y ∈ Ioo a b ∧ y < x ∧ slope g x y < u := by
      filter_upwards [hnear.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin,
        hleft.eventually (gt_mem_nhds hu)] with y hy hyx hsy
      exact ⟨hy, hyx, hsy⟩
    obtain ⟨y, hy, hyx, hyu⟩ := hgood.exists
    filter_upwards [hf, hdf, (hslope y hy).eventually (gt_mem_nhds hyu)] with n hfn hdn hn
    have hle := hfn.deriv_le_slope hy hx hyx hdn
    rw [slope_comm] at hle
    exact hle.trans_lt hn

end ConcaveOn

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Analysis / Convex / Gauge
-/

@[expose] public section

open Set
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A direction of positive gauge has a unique positive multiple on the frontier. -/
lemma Convex.existsUnique_pos_smul_mem_frontier_of_gauge_pos {s : Set E}
    (hs : Convex ℝ s) (h₀ : s ∈ nhds (0 : E)) {u : E} (hu : 0 < gauge s u) :
    ∃! r : ℝ, 0 < r ∧ r • u ∈ frontier s := by
  refine ⟨(gauge s u)⁻¹, ⟨inv_pos.mpr hu, ?_⟩, ?_⟩
  · apply (gauge_eq_one_iff_mem_frontier hs h₀).mp
    rw [gauge_smul_of_nonneg (inv_nonneg.mpr hu.le), smul_eq_mul, inv_mul_cancel₀ hu.ne']
  · intro r hr
    have h := (gauge_eq_one_iff_mem_frontier hs h₀).mpr hr.2
    rw [gauge_smul_of_nonneg hr.1.le, smul_eq_mul] at h
    simpa only [one_div] using (eq_div_iff hu.ne').mpr h

/-- Every nonzero direction has a unique positive multiple on the frontier of a bounded convex
neighborhood of zero. -/
lemma Convex.existsUnique_pos_smul_mem_frontier {s : Set E}
    (hs : Convex ℝ s) (h₀ : s ∈ nhds (0 : E))
    (hb : Bornology.IsVonNBounded ℝ s) {u : E} (hu : u ≠ 0) :
    ∃! r : ℝ, 0 < r ∧ r • u ∈ frontier s :=
  hs.existsUnique_pos_smul_mem_frontier_of_gauge_pos h₀
    ((gauge_pos (absorbent_nhds_zero h₀) hb).mpr hu)

/-- Reciprocation is Lipschitz on real numbers bounded below by a positive constant. -/
lemma Real.dist_inv_le_of_pos_lower_bound {a b c : ℝ} (hc : 0 < c)
    (ha : c ≤ a) (hb : c ≤ b) :
    dist a⁻¹ b⁻¹ ≤ c⁻¹ ^ 2 * dist a b := by
  have ha₀ := hc.trans_le ha
  have hb₀ := hc.trans_le hb
  rw [dist_inv_inv₀ ha₀.ne' hb₀.ne', Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos ha₀, abs_of_pos hb₀]
  calc
    dist a b / (a * b) ≤ dist a b / (c * c) := by gcongr
    _ = c⁻¹ ^ 2 * dist a b := by ring

/-- The reciprocal of a positive uniformly bounded-below Lipschitz function is Lipschitz. -/
lemma LipschitzWith.inv_of_pos_lower_bound {X : Type*} [PseudoMetricSpace X]
    {f : X → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) {c : ℝ}
    (hc : 0 < c) (hbound : ∀ x, c ≤ f x) :
    LipschitzWith (Real.toNNReal (c⁻¹ ^ 2) * K) (fun x ↦ (f x)⁻¹) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  calc
    dist (f x)⁻¹ (f y)⁻¹ ≤ c⁻¹ ^ 2 * dist (f x) (f y) :=
      Real.dist_inv_le_of_pos_lower_bound hc (hbound x) (hbound y)
    _ ≤ c⁻¹ ^ 2 * ((K : ℝ) * dist x y) :=
      mul_le_mul_of_nonneg_left (hf.dist_le_mul x y) (sq_nonneg _)
    _ = _ := by
      rw [NNReal.coe_mul, Real.coe_toNNReal _ (sq_nonneg _)]
      ring

/-- The reciprocal gauge is Lipschitz on the unit sphere of a bounded convex neighborhood of zero.
-/
lemma Convex.exists_lipschitzWith_inv_gauge_sphere {s : Set E}
    (hs : Convex ℝ s) (h₀ : s ∈ nhds (0 : E)) {R : ℝ} (hR : 0 < R)
    (hbound : s ⊆ Metric.closedBall 0 R) :
    ∃ C, LipschitzWith C (fun u : {u : E | ‖u‖ = 1} ↦ (gauge s u.val)⁻¹) := by
  obtain ⟨K, hK⟩ := hs.lipschitz_gauge h₀
  have hf : LipschitzWith K (fun u : {u : E | ‖u‖ = 1} ↦ gauge s u.val) :=
    by
      apply LipschitzWith.of_dist_le_mul
      intro u v
      exact hK.dist_le_mul u.val v.val
  have hlower (u : {u : E | ‖u‖ = 1}) : 1 / R ≤ gauge s u.val := by
    have hu : ‖(u : E)‖ = 1 := u.property
    calc
      1 / R = ‖u.val‖ / R := congrArg (fun r ↦ r / R) hu.symm
      _ ≤ gauge s u.val :=
        le_gauge_of_subset_closedBall (absorbent_nhds_zero h₀) hR.le hbound
  exact ⟨_, hf.inv_of_pos_lower_bound (one_div_pos.mpr hR) hlower⟩

/-- Radial gauge rescaling is Lipschitz on the unit sphere. -/
lemma Convex.exists_lipschitzWith_radial_gauge_sphere {s : Set E}
    (hs : Convex ℝ s) (h₀ : s ∈ nhds (0 : E)) {R : ℝ} (hR : 0 < R)
    (hbound : s ⊆ Metric.closedBall 0 R) :
    ∃ C, LipschitzWith C
      (fun u : {u : E | ‖u‖ = 1} ↦ (gauge s u.val)⁻¹ • u.val) := by
  obtain ⟨C, hC⟩ := hs.exists_lipschitzWith_inv_gauge_sphere h₀ hR hbound
  have hr (u : {u : E | ‖u‖ = 1}) : 0 ≤ (gauge s u.val)⁻¹ ∧
      (gauge s u.val)⁻¹ ≤ R := by
    have hu : ‖u.val‖ = 1 := u.property
    have hlower : 1 / R ≤ gauge s u.val := by
      calc
        1 / R = ‖u.val‖ / R := congrArg (fun r ↦ r / R) hu.symm
        _ ≤ _ := le_gauge_of_subset_closedBall (absorbent_nhds_zero h₀) hR.le hbound
    refine ⟨inv_nonneg.mpr (gauge_nonneg _), ?_⟩
    simpa only [one_div, inv_inv] using
      one_div_le_one_div_of_le (one_div_pos.mpr hR) hlower
  refine ⟨Real.toNNReal R + C, LipschitzWith.of_dist_le_mul fun u v ↦ ?_⟩
  have hv : ‖v.val‖ = 1 := v.property
  calc
    dist ((gauge s u.val)⁻¹ • u.val) ((gauge s v.val)⁻¹ • v.val) ≤
        dist ((gauge s u.val)⁻¹ • u.val) ((gauge s u.val)⁻¹ • v.val) +
        dist ((gauge s u.val)⁻¹ • v.val) ((gauge s v.val)⁻¹ • v.val) :=
      dist_triangle _ _ _
    _ = (gauge s u.val)⁻¹ * dist u v +
        dist (gauge s u.val)⁻¹ (gauge s v.val)⁻¹ := by
      rw [dist_smul₀, Real.norm_eq_abs, abs_of_nonneg (hr u).1]
      congr 1
      rw [dist_eq_norm, ← sub_smul, norm_smul, hv, mul_one, dist_eq_norm]
    _ ≤ R * dist u v + (C : ℝ) * dist u v :=
      add_le_add (mul_le_mul_of_nonneg_right (hr u).2 dist_nonneg) (hC.dist_le_mul u v)
    _ = _ := by rw [NNReal.coe_add, Real.coe_toNNReal _ hR.le]; ring

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Analysis / Convex / Gauge Rescale
-/

@[expose] public section

open Set
open scoped Topology NNReal Pointwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Gauge rescaling identifies the unit sphere with the frontier of a bounded convex neighborhood.
-/
noncomputable def radialGaugeHomeomorph {s : Set E}
    (hs : Convex ℝ s) (h₀ : s ∈ nhds (0 : E))
    (hb : Bornology.IsVonNBounded ℝ s) :
    {u : E | ‖u‖ = 1} ≃ₜ ↥(frontier s) := by
  let e := gaugeRescaleHomeomorph (Metric.ball (0 : E) 1) s
    (convex_ball 0 1) (Metric.ball_mem_nhds _ (by norm_num))
    (NormedSpace.isVonNBounded_ball ℝ E 1) hs h₀ hb
  have he : e '' frontier (Metric.ball (0 : E) 1) = frontier s := by
    rw [← closure_sdiff_interior, Set.image_sdiff e.injective]
    rw [image_gaugeRescaleHomeomorph_closure, image_gaugeRescaleHomeomorph_interior]
    exact closure_sdiff_interior s
  have hunit : {u : E | ‖u‖ = 1} = frontier (Metric.ball (0 : E) 1) := by
    rw [frontier_ball _ one_ne_zero]
    ext u
    simp
  exact (Homeomorph.setCongr hunit).trans ((e.image _).trans (Homeomorph.setCongr he))

/-- The radial gauge homeomorphism sends a unit vector to its reciprocal-gauge multiple. -/
lemma radialGaugeHomeomorph_apply {s : Set E}
    (hs : Convex ℝ s) (h₀ : s ∈ nhds (0 : E))
    (hb : Bornology.IsVonNBounded ℝ s) (u : {u : E | ‖u‖ = 1}) :
    (radialGaugeHomeomorph hs h₀ hb u : E) = (gauge s u.val)⁻¹ • u.val := by
  change (gauge (Metric.ball (0 : E) 1) u.val / gauge s u.val) • u.val = _
  rw [gauge_ball (by norm_num), div_one]
  have hu : ‖u.val‖ = 1 := u.property
  rw [hu, one_div]

open scoped Pointwise

/-- Translate the radial gauge homeomorphism by a fixed vector. -/
noncomputable def translatedRadialGaugeHomeomorph {s : Set E}
    (hs : Convex ℝ s) (h₀ : s ∈ nhds (0 : E))
    (hb : Bornology.IsVonNBounded ℝ s) (o : E) :
    {u : E | ‖u‖ = 1} ≃ₜ ↥(frontier (o +ᵥ s)) := by
  let e : E ≃ₜ E := Homeomorph.addLeft o
  have he : e '' frontier s = frontier (o +ᵥ s) := by
    rw [e.image_frontier]
    rfl
  exact (radialGaugeHomeomorph hs h₀ hb).trans
    ((e.image _).trans (Homeomorph.setCongr he))

/-- The translated radial gauge homeomorphism has the expected affine formula. -/
lemma translatedRadialGaugeHomeomorph_apply {s : Set E}
    (hs : Convex ℝ s) (h₀ : s ∈ nhds (0 : E))
    (hb : Bornology.IsVonNBounded ℝ s) (o : E) (u : {u : E | ‖u‖ = 1}) :
    (translatedRadialGaugeHomeomorph hs h₀ hb o u : E) =
      o + (gauge s u.val)⁻¹ • u.val := by
  change o + (radialGaugeHomeomorph hs h₀ hb u : E) = _
  rw [radialGaugeHomeomorph_apply]

/-- The translated radial gauge homeomorphism is Lipschitz on the unit sphere. -/
lemma exists_lipschitzWith_translatedRadialGaugeHomeomorph {s : Set E}
    (hs : Convex ℝ s) (h₀ : s ∈ nhds (0 : E))
    (hb : Bornology.IsVonNBounded ℝ s) (o : E) {R : ℝ} (hR : 0 < R)
    (hbound : s ⊆ Metric.closedBall 0 R) :
    ∃ C, LipschitzWith C (fun u ↦ (translatedRadialGaugeHomeomorph hs h₀ hb o u : E)) := by
  obtain ⟨C, hC⟩ := hs.exists_lipschitzWith_radial_gauge_sphere h₀ hR hbound
  refine ⟨C, LipschitzWith.of_dist_le_mul fun u v ↦ ?_⟩
  rw [translatedRadialGaugeHomeomorph_apply, translatedRadialGaugeHomeomorph_apply,
    dist_add_left]
  exact hC.dist_le_mul u v

/-- A bounded convex set with an interior basepoint admits a positive Lipschitz radial
parametrization of its frontier. -/
lemma exists_radial_homeomorph {s : Set E}
    (hs : Convex ℝ s) (hb : Bornology.IsBounded s) (o : E) (ho : o ∈ interior s) :
    ∃ (ρ : E → ℝ) (e : {u : E | ‖u‖ = 1} ≃ₜ ↥(frontier s)) (C : NNReal),
      (∀ u, ‖u‖ = 1 → 0 < ρ u ∧ o + ρ u • u ∈ frontier s ∧
        ∀ r : ℝ, 0 < r → o + r • u ∈ frontier s → r = ρ u) ∧
      (∀ u, (e u : E) = o + ρ u.val • u.val) ∧
      LipschitzWith C (fun u ↦ (e u : E)) := by
  let t : Set E := -o +ᵥ s
  have htconv : Convex ℝ t := hs.vadd (-o)
  have htzero : t ∈ nhds (0 : E) := by
    simpa [t, ← mem_interior_iff_mem_nhds, interior_vadd,
      mem_vadd_set_iff_neg_vadd_mem] using ho
  have htbound : Bornology.IsBounded t := hb.vadd (-o)
  have htbounded := NormedSpace.isVonNBounded_of_isBounded ℝ htbound
  have htranslate : o +ᵥ t = s := by simp [t]
  let e := (translatedRadialGaugeHomeomorph htconv htzero htbounded o).trans
    (Homeomorph.setCongr (congrArg frontier htranslate))
  obtain ⟨R, hR, hnorm⟩ := htbound.exists_pos_norm_le
  have hball : t ⊆ Metric.closedBall 0 R := by
    intro x hx
    simpa using hnorm x hx
  obtain ⟨C, hC⟩ := exists_lipschitzWith_translatedRadialGaugeHomeomorph
    htconv htzero htbounded o hR hball
  refine ⟨fun u ↦ (gauge t u)⁻¹, e, C, ?_, ?_, ?_⟩
  · intro u hu
    have hune : u ≠ 0 := by intro h; simp [h] at hu
    have hg := (gauge_pos (absorbent_nhds_zero htzero) htbounded).mpr hune
    refine ⟨inv_pos.mpr hg, ?_, ?_⟩
    · have hm := (e ⟨u, hu⟩).property
      change (translatedRadialGaugeHomeomorph htconv htzero htbounded o ⟨u, hu⟩ : E)
        ∈ frontier s at hm
      rwa [translatedRadialGaugeHomeomorph_apply] at hm
    · intro r hr hru
      have hz : r • u ∈ frontier t := by
        change r • u ∈ frontier (-o +ᵥ s)
        rw [frontier, closure_vadd, interior_vadd]
        simpa only [frontier, Set.mem_sdiff, mem_vadd_set_iff_neg_vadd_mem, neg_neg, vadd_eq_add]
          using hru
      have hgauge := (gauge_eq_one_iff_mem_frontier htconv htzero).mpr hz
      rw [gauge_smul_of_nonneg hr.le, smul_eq_mul] at hgauge
      simpa only [one_div] using (eq_div_iff hg.ne').mpr hgauge
  · intro u
    exact translatedRadialGaugeHomeomorph_apply htconv htzero htbounded o u
  · exact hC

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Radial exit points of a convex set

From an interior base point of a compact convex set, every point of the set lies on a segment
ending at a boundary point, and that boundary point is unique. These are the facts behind a
radial decomposition of a convex body into cones over its boundary.
-/

@[expose] public section

open Set
open scoped Topology Pointwise

open Set
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A point lying a fixed fraction of the way, less than all of it, from an interior point of a
convex set towards a point of the set is itself an interior point. -/
theorem Convex.mem_interior_of_sub_eq_smul_sub {s : Set E} (hs : Convex ℝ s) {o w z : E}
    {γ : ℝ} (ho : o ∈ interior s) (hw : w ∈ s) (hγ₀ : 0 ≤ γ) (hγ₁ : γ < 1)
    (h : z - o = γ • (w - o)) : z ∈ interior s := by
  have hz : z = (1 - γ) • o + γ • w := by
    have hzo : z = o + γ • (w - o) := by rw [← h]; abel
    rw [hzo, smul_sub, sub_smul, one_smul]
    abel
  rw [hz]
  exact hs.combo_interior_closure_mem_interior ho (subset_closure hw) (by linarith) hγ₀ (by ring)

/-- From an interior base point, every point of a compact convex set lies on a segment ending at
a boundary point: the radial exit point of its direction. -/
theorem Convex.exists_mem_frontier_mem_segment [Nontrivial E] {s : Set E} (hs : Convex ℝ s)
    (hcomp : IsCompact s) {o : E} (ho : o ∈ interior s) {x : E} (hx : x ∈ s) :
    ∃ p ∈ frontier s, x ∈ segment ℝ o p := by
  have himage : ((-o) +ᵥ s) = (fun z : E ↦ -o + z) '' s := (Set.image_vadd).symm
  have hsconv : Convex ℝ ((-o) +ᵥ s) := by
    rw [himage]; exact hs.translate (-o)
  have hscompact : IsCompact ((-o) +ᵥ s) := by
    rw [himage]; exact hcomp.image (continuous_const.add continuous_id)
  have h0 : (0 : E) ∈ interior ((-o) +ᵥ s) := by
    rw [interior_vadd]
    exact ⟨o, ho, by simp only [vadd_eq_add]; abel⟩
  have hnhds : ((-o) +ᵥ s) ∈ 𝓝 (0 : E) := mem_interior_iff_mem_nhds.mp h0
  have hgbound := NormedSpace.isVonNBounded_of_isBounded ℝ hscompact.isBounded
  have hfrontier : ∀ {z : E}, z ∈ frontier ((-o) +ᵥ s) → o + z ∈ frontier s := by
    intro z hz
    have hzs : z ∈ ((-o) +ᵥ s) := by
      have h := frontier_subset_closure hz
      rwa [hscompact.isClosed.closure_eq] at h
    obtain ⟨k, hk, hkeq⟩ := hzs
    have hok : o + z = k := by rw [← hkeq]; simp only [vadd_eq_add]; abel
    rw [hok, mem_frontier_iff_notMem_interior hk]
    intro hkint
    exact hz.2 (by rw [interior_vadd]; exact ⟨k, hkint, hkeq⟩)
  by_cases hxo : x = o
  · obtain ⟨u, hu⟩ := exists_ne (0 : E)
    obtain ⟨r, hr, -⟩ := hsconv.existsUnique_pos_smul_mem_frontier hnhds hgbound hu
    exact ⟨o + r • u, hfrontier hr.2, hxo ▸ left_mem_segment ℝ o _⟩
  have hxs : x - o ∈ ((-o) +ᵥ s) := ⟨x, hx, by simp only [vadd_eq_add]; abel⟩
  have hgpos : 0 < gauge ((-o) +ᵥ s) (x - o) :=
    (gauge_pos (absorbent_nhds_zero hnhds) hgbound).mpr (sub_ne_zero.mpr hxo)
  have hgle : gauge ((-o) +ᵥ s) (x - o) ≤ 1 := gauge_le_one_of_mem hxs
  have hfr : (gauge ((-o) +ᵥ s) (x - o))⁻¹ • (x - o) ∈ frontier ((-o) +ᵥ s) := by
    apply (gauge_eq_one_iff_mem_frontier hsconv hnhds).mp
    rw [gauge_smul_of_nonneg (inv_nonneg.mpr hgpos.le), smul_eq_mul, inv_mul_cancel₀ hgpos.ne']
  refine ⟨o + (gauge ((-o) +ᵥ s) (x - o))⁻¹ • (x - o), hfrontier hfr, ?_⟩
  rw [segment_eq_image']
  refine ⟨gauge ((-o) +ᵥ s) (x - o), ⟨hgpos.le, hgle⟩, ?_⟩
  change o + gauge ((-o) +ᵥ s) (x - o) • (o + (gauge ((-o) +ᵥ s) (x - o))⁻¹ • (x - o) - o) = x
  rw [add_sub_cancel_left, smul_smul, mul_inv_cancel₀ hgpos.ne', one_smul]
  abel

/-- The radial exit point from an interior base point is unique. -/
theorem Convex.eq_of_mem_frontier_of_mem_segment {s : Set E} (hs : Convex ℝ s)
    (hclosed : IsClosed s) {o x z w : E} (ho : o ∈ interior s) (hxo : x ≠ o)
    (hz : z ∈ frontier s) (hw : w ∈ frontier s) (hxz : x ∈ segment ℝ o z)
    (hxw : x ∈ segment ℝ o w) : z = w := by
  have hzs : z ∈ s := hclosed.frontier_subset hz
  have hws : w ∈ s := hclosed.frontier_subset hw
  have hzint : z ∉ interior s := (mem_frontier_iff_notMem_interior hzs).mp hz
  have hwint : w ∉ interior s := (mem_frontier_iff_notMem_interior hws).mp hw
  rw [segment_eq_image'] at hxz hxw
  obtain ⟨α, hα, hxα⟩ := hxz
  obtain ⟨β, hβ, hxβ⟩ := hxw
  have hxα' : o + α • (z - o) = x := hxα
  have hxβ' : o + β • (w - o) = x := hxβ
  have hαpos : 0 < α := hα.1.lt_or_eq.resolve_right fun h ↦ hxo (by rw [← hxα', ← h]; simp)
  have hβpos : 0 < β := hβ.1.lt_or_eq.resolve_right fun h ↦ hxo (by rw [← hxβ', ← h]; simp)
  have hkey : α • (z - o) = β • (w - o) := add_left_cancel (hxα'.trans hxβ'.symm)
  have hzw : z - o = (α⁻¹ * β) • (w - o) := by
    rw [mul_smul, ← hkey, smul_smul, inv_mul_cancel₀ hαpos.ne', one_smul]
  have hwz : w - o = (α⁻¹ * β)⁻¹ • (z - o) := by
    rw [hzw, smul_smul, inv_mul_cancel₀ (by positivity), one_smul]
  rcases lt_trichotomy (α⁻¹ * β) 1 with hlt | heq | hgt
  · exact absurd (hs.mem_interior_of_sub_eq_smul_sub ho hws (by positivity) hlt hzw) hzint
  · have hzo : z - o = w - o := by rw [hzw, heq, one_smul]
    simpa using congrArg (fun p : E ↦ p + o) hzo
  · refine absurd (hs.mem_interior_of_sub_eq_smul_sub ho hzs (by positivity) ?_ hwz) hwint
    rw [inv_lt_one_iff₀]
    exact Or.inr hgt

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Analysis / Finite Envelope
-/

@[expose] public section

noncomputable section

namespace List

open Filter Topology

lemma abs_foldr_min_apply_sub_le (l : List (ℝ → ℝ)) (r L x z : ℝ) (hL : 0 ≤ L)
    (hl : ∀ f ∈ l, |f x - f z| ≤ L * |x - z|) :
    |l.foldr (fun f s ↦ min (f x) s) r -
        l.foldr (fun f s ↦ min (f z) s) r| ≤ L * |x - z| := by
  induction l with
  | nil => simpa using mul_nonneg hL (abs_nonneg (x - z))
  | cons f l ih =>
      simp only [List.foldr_cons]
      refine (abs_min_sub_min_le_max _ _ _ _).trans (max_le ?_ ?_)
      · exact hl f (by simp)
      · exact ih (fun g hg ↦ hl g (by simp [hg]))

lemma abs_foldr_max_apply_sub_le (l : List (ℝ → ℝ)) (r L x z : ℝ) (hL : 0 ≤ L)
    (hl : ∀ f ∈ l, |f x - f z| ≤ L * |x - z|) :
    |l.foldr (fun f s ↦ max (f x) s) r -
        l.foldr (fun f s ↦ max (f z) s) r| ≤ L * |x - z| := by
  induction l with
  | nil => simpa using mul_nonneg hL (abs_nonneg (x - z))
  | cons f l ih =>
      simp only [List.foldr_cons]
      refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le ?_ ?_)
      · exact hl f (by simp)
      · exact ih (fun g hg ↦ hl g (by simp [hg]))

lemma le_foldr_min_apply_iff (l : List (ℝ → ℝ)) (r x y : ℝ) :
    y ≤ l.foldr (fun f s ↦ min (f x) s) r ↔ y ≤ r ∧ ∀ f ∈ l, y ≤ f x := by
  induction l with
  | nil => simp
  | cons f l ih => simp [ih, and_left_comm]

lemma foldr_max_apply_le_iff (l : List (ℝ → ℝ)) (r x y : ℝ) :
    l.foldr (fun f s ↦ max (f x) s) r ≤ y ↔ r ≤ y ∧ ∀ f ∈ l, f x ≤ y := by
  induction l with
  | nil => simp
  | cons f l ih => simp [ih, and_left_comm]

end List

end

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Analysis / Inner Product Space / Box
-/

@[expose] public section

namespace EuclideanSpace

/-- A rectangle with finite coordinate bounds is bounded in the Euclidean plane. -/
theorem isBounded_coordinate_rectangle (l r a b : ℝ) :
    Bornology.IsBounded {p : EuclideanSpace ℝ (Fin 2) | l ≤ p 0 ∧ p 0 ≤ r ∧ a ≤ p 1 ∧ p 1 ≤ b} := by
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨(|l| + |r|) + (|a| + |b|), ?_⟩
  rintro p ⟨hl, hr, ha, hb⟩
  have hx : |p 0| ≤ |l| + |r| := abs_le.mpr
    ⟨by linarith [neg_abs_le l, abs_nonneg r],
      by linarith [le_abs_self r, abs_nonneg l]⟩
  have hy : |p 1| ≤ |a| + |b| := abs_le.mpr
    ⟨by linarith [neg_abs_le a, abs_nonneg b],
      by linarith [le_abs_self b, abs_nonneg a]⟩
  have hx2 := (sq_le_sq₀ (abs_nonneg (p 0)) (by positivity)).mpr hx
  have hy2 := (sq_le_sq₀ (abs_nonneg (p 1)) (by positivity)).mpr hy
  have hn := EuclideanSpace.norm_sq_eq p
  simp only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs] at hn hx2 hy2
  nlinarith [mul_nonneg (by positivity : 0 ≤ |l| + |r|)
    (by positivity : 0 ≤ |a| + |b|), norm_nonneg p,
    abs_nonneg l, abs_nonneg r, abs_nonneg a, abs_nonneg b]

end EuclideanSpace

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Linearity of a real inner product in its left argument

`Mathlib.Analysis.InnerProductSpace.Basic` provides the continuous linear map
`innerSL ℝ v = fun x ↦ ⟪v, x⟫`; the bundled form of the symmetric slot is what the
half-space convexity lemmas `convex_halfSpace_le` and `convex_halfSpace_ge` consume.
-/

@[expose] public section

/-- `x ↦ ⟪x, v⟫` is a linear map of a real inner product space. -/
theorem isLinearMap_inner_left {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : E) : IsLinearMap ℝ fun x : E ↦ inner ℝ x v :=
  ⟨fun a b ↦ inner_add_left a b v, fun c a ↦ real_inner_smul_left a v c⟩

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Analysis / Normed / Affine / Continuous Affine Map
-/

@[expose] public section

namespace ContinuousAffineMap

variable {E F G : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedAddCommGroup G] [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace ℝ G]

/-- Precomposition by a fixed continuous affine map is continuous. -/
theorem continuous_comp_right (g : E →ᴬ[ℝ] F) :
    Continuous (fun f : F →ᴬ[ℝ] G ↦ f.comp g) := by
  let C : NNReal := ⟨‖g‖ + 1, by positivity⟩
  apply (LipschitzWith.of_dist_le_mul (K := C) fun f h ↦ ?_).continuous
  rw [dist_eq_norm, dist_eq_norm]
  have heq : f.comp g - h.comp g = (f - h).comp g := by
    ext x
    simp
  rw [heq]
  calc
    ‖(f - h).comp g‖ ≤ ‖f - h‖ * ‖g‖ + ‖(f - h) 0‖ :=
      ContinuousAffineMap.norm_comp_le _ _
    _ ≤ ‖f - h‖ * ‖g‖ + ‖f - h‖ := by
      gcongr
      exact ContinuousAffineMap.norm_image_zero_le _
    _ = (C : ℝ) * ‖f - h‖ := by
      change _ = (‖g‖ + 1) * ‖f - h‖
      ring

end ContinuousAffineMap

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Analysis / Special Functions / Angle
-/

@[expose] public section

namespace Real.Angle

/-- Distinct reals at distance less than a full turn have distinct angles. -/
theorem coe_ne_coe_of_abs_sub_lt {x y : ℝ} (hne : x ≠ y) (h : |x - y| < 2 * Real.pi) :
    ((x : ℝ) : Real.Angle) ≠ ((y : ℝ) : Real.Angle) := by
  intro he
  rw [Real.Angle.angle_eq_iff_two_pi_dvd_sub] at he
  obtain ⟨k, hk⟩ := he
  have hpi := Real.pi_pos
  rw [abs_lt] at h
  rcases lt_trichotomy k 0 with hk0 | rfl | hk0
  · have hk' : (k : ℝ) ≤ -1 := by exact_mod_cast (by omega : k ≤ -1)
    nlinarith [h.1]
  · simp only [Int.cast_zero, mul_zero] at hk
    exact hne (by linarith)
  · have hk' : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : (1 : ℤ) ≤ k)
    nlinarith [h.2]

end Real.Angle

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Analysis / Special Functions / Angle Lift
-/

@[expose] public section

namespace Real

/-- Continuous real angle lifts of the same circle-valued map differ by a constant. -/
theorem sub_eq_sub_of_cos_eq_cos_of_sin_eq_sin {X : Type*} [TopologicalSpace X] [PreconnectedSpace
  X]
    {θ ψ : X → ℝ} (hθ : Continuous θ) (hψ : Continuous ψ)
    (hcos : ∀ x, Real.cos (θ x) = Real.cos (ψ x))
    (hsin : ∀ x, Real.sin (θ x) = Real.sin (ψ x)) (x y : X) :
    θ x - ψ x = θ y - ψ y := by
  have hsub : Set.range (fun z ↦ θ z - ψ z) ⊆ Set.range (fun n : ℤ ↦ 2 * Real.pi * n) := by
    rintro _ ⟨z, rfl⟩
    obtain ⟨n, hn⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.mp
      (Real.Angle.cos_sin_inj (hcos z) (hsin z))
    exact ⟨n, hn.symm⟩
  have hconst := (Set.countable_range (fun n : ℤ ↦ 2 * Real.pi * n)).isTotallyDisconnected
    _ hsub (isPreconnected_range (hθ.sub hψ))
  exact hconst (Set.mem_range_self x) (Set.mem_range_self y)

end Real

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# A cubic remainder bound for the arctangent

`Real.abs_arctan_sub_self_le` complements `Real.abs_arctan_le_abs` by quantifying the
first-order approximation `arctan s ≈ s` near the origin.
-/

@[expose] public section

namespace Real

/-- The arctangent differs from the identity by at most a cubic error. -/
theorem abs_arctan_sub_self_le (s : ℝ) : |arctan s - s| ≤ |s| ^ 3 := by
  have hderiv : ∀ u ∈ Set.uIcc (0 : ℝ) s,
      HasDerivWithinAt (fun u : ℝ ↦ arctan u - u) (1 / (1 + u ^ 2) - 1)
        (Set.uIcc (0 : ℝ) s) u := fun u _ ↦
    ((hasDerivAt_arctan u).sub (hasDerivAt_id u)).hasDerivWithinAt
  have hbound : ∀ u ∈ Set.uIcc (0 : ℝ) s, ‖1 / (1 + u ^ 2) - 1‖ ≤ s ^ 2 := by
    intro u hu
    have hu' : |u| ≤ |s| := by
      rcases Set.mem_uIcc.mp hu with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
        rcases abs_cases u with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;>
          rcases abs_cases s with ⟨f1, f2⟩ | ⟨f1, f2⟩ <;> linarith
    have hpos : (0 : ℝ) < 1 + u ^ 2 := by positivity
    have heq : 1 / (1 + u ^ 2) - 1 = -(u ^ 2 / (1 + u ^ 2)) := by field_simp; ring
    rw [heq, norm_neg, Real.norm_eq_abs, abs_of_nonneg (by positivity), div_le_iff₀ hpos]
    nlinarith [sq_abs u, sq_abs s, abs_nonneg u, abs_nonneg s, sq_nonneg u]
  have hmain := (convex_uIcc (0 : ℝ) s).norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv hbound Set.left_mem_uIcc Set.right_mem_uIcc
  have hmain' : |arctan s - s| ≤ s ^ 2 * |s| := by simpa using hmain
  calc |arctan s - s| ≤ s ^ 2 * |s| := hmain'
    _ = |s| ^ 3 := by rw [← sq_abs s]; ring

/-- First-order angle estimate. If `W = (w0, w1)` has norm `nw > 0` and the displacement
`d = (d0, d1)` has norm `nd` with `2 * nd ≤ nw`, then the principal angle between `W` and
`W + d`, in the arctangent form given by their cross and dot products, differs from its
linearization `(w0 * d1 - w1 * d0) / nw ^ 2` by at most `6 * nd ^ 2 / nw ^ 2`. -/
theorem abs_arctan_div_sub_le_of_small {w0 w1 d0 d1 nw nd : ℝ}
    (hnw : 0 < nw) (hnw2 : nw ^ 2 = w0 ^ 2 + w1 ^ 2)
    (hnd : 0 ≤ nd) (hnd2 : nd ^ 2 = d0 ^ 2 + d1 ^ 2)
    (hsmall : 2 * nd ≤ nw) :
    |arctan ((w0 * d1 - w1 * d0) / (nw ^ 2 + (w0 * d0 + w1 * d1))) -
        (w0 * d1 - w1 * d0) / nw ^ 2| ≤ 6 * nd ^ 2 / nw ^ 2 := by
  set N := w0 * d1 - w1 * d0 with hN
  set P := w0 * d0 + w1 * d1 with hP
  have hlag : N ^ 2 + P ^ 2 = nw ^ 2 * nd ^ 2 := by
    rw [hN, hP, hnw2, hnd2]; ring
  have hprod : 0 ≤ nw * nd := mul_nonneg hnw.le hnd
  have hCS : |N| ≤ nw * nd := by
    nlinarith [sq_abs N, abs_nonneg N, sq_nonneg P]
  have hCS' : |P| ≤ nw * nd := by
    nlinarith [sq_abs P, abs_nonneg P, sq_nonneg N]
  set D := nw ^ 2 + P with hD
  have hPlow : -(nw * nd) ≤ P := neg_le_of_abs_le hCS'
  have hDlow : nw ^ 2 / 2 ≤ D := by nlinarith
  have hD0 : 0 < D := lt_of_lt_of_le (by positivity) hDlow
  set s := N / D with hs
  have hsle : |s| ≤ 2 * nd / nw := by
    rw [hs, abs_div, abs_of_pos hD0, div_le_div_iff₀ hD0 hnw]
    nlinarith [abs_nonneg N]
  have hs1 : |s| ≤ 1 := by
    refine hsle.trans ?_
    rw [div_le_one hnw]
    linarith
  have h1 : |arctan s - s| ≤ 4 * nd ^ 2 / nw ^ 2 := by
    refine (abs_arctan_sub_self_le s).trans ?_
    have hstep : |s| ^ 3 ≤ (2 * nd / nw) ^ 2 := by
      nlinarith [abs_nonneg s, hsle, hs1, sq_nonneg (|s|)]
    refine hstep.trans_eq ?_
    field_simp
    ring
  have h2 : |s - N / nw ^ 2| ≤ 2 * nd ^ 2 / nw ^ 2 := by
    have heq : s - N / nw ^ 2 = -(N * P) / (D * nw ^ 2) := by
      rw [hs, hD]
      rw [div_sub_div _ _ (ne_of_gt hD0) (by positivity : (nw : ℝ) ^ 2 ≠ 0)]
      rw [hD]
      ring_nf
    rw [heq, abs_div, abs_neg, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < D * nw ^ 2),
      div_le_div_iff₀ (by positivity) (by positivity : (0 : ℝ) < nw ^ 2)]
    nlinarith [mul_le_mul hCS hCS' (abs_nonneg P) hprod, abs_nonneg N, abs_nonneg P,
      mul_nonneg (abs_nonneg N) (abs_nonneg P), sq_nonneg nd, sq_nonneg nw]
  calc |arctan s - N / nw ^ 2| ≤ |arctan s - s| + |s - N / nw ^ 2| :=
        abs_sub_le _ _ _
    _ ≤ 4 * nd ^ 2 / nw ^ 2 + 2 * nd ^ 2 / nw ^ 2 := add_le_add h1 h2
    _ = 6 * nd ^ 2 / nw ^ 2 := by ring

end Real

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# Two-sided bracketing of an alternating series with an antitone tail

`alternating_series_bracket_of_antitone_shift` upgrades the one-sided Leibniz estimates
`Antitone.alternating_series_le_tendsto` and `Antitone.tendsto_le_alternating_series` to a
two-sided bracket for an alternating series whose term magnitudes are antitone only from an
even index `2 * N` onwards: the sum then lies between the partial sums of `2 * N` and of
`2 * N + 1` terms.  `antitone_pow_div_factorial_two_mul_add` is the antitonicity criterion
for the stride-two factorial quotients `x ^ (2 * n + a) / (2 * n + a)!` that the Taylor
series of the trigonometric functions produce.
-/

@[expose] public section

/-- The stride-two factorial quotients `x ^ (2 * n + a) / (2 * n + a)!` are antitone as soon
as `x ^ 2 ≤ (a + 1) * (a + 2)`, i.e. as soon as the first term ratio is at most one. -/
theorem antitone_pow_div_factorial_two_mul_add {x : ℝ} (hx0 : 0 ≤ x) {a : ℕ}
    (hx : x ^ 2 ≤ ((a + 1) * (a + 2) : ℕ)) :
    Antitone fun n : ℕ ↦ x ^ (2 * n + a) / (Nat.factorial (2 * n + a) : ℝ) := by
  refine antitone_nat_of_succ_le fun n ↦ ?_
  set m := 2 * n + a with hm
  have ham : a ≤ m := by omega
  have hstep : 2 * (n + 1) + a = m + 1 + 1 := by omega
  have hfac : (0 : ℝ) < (Nat.factorial m : ℝ) := by positivity
  have hle : x ^ 2 ≤ ((m : ℝ) + 1) * ((m : ℝ) + 2) := by
    refine hx.trans ?_
    have hcast : (a : ℝ) ≤ (m : ℝ) := by exact_mod_cast ham
    have h0 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
    push_cast
    nlinarith
  have hpow : x ^ (m + 1 + 1) = x ^ m * x * x := by ring
  rw [hstep, Nat.factorial_succ, Nat.factorial_succ, hpow,
    div_le_div_iff₀ (by positivity) hfac]
  push_cast
  nlinarith [mul_nonneg (mul_nonneg (pow_nonneg hx0 m) hfac.le) (sub_nonneg.2 hle)]

/-- Leibniz bracketing for an alternating series whose term magnitudes are antitone only
from index `2 * N` onwards: the limit lies between the partial sums of `2 * N` and of
`2 * N + 1` terms. -/
theorem alternating_series_bracket_of_antitone_shift {f : ℕ → ℝ} {l : ℝ} (N : ℕ)
    (hfl : Filter.Tendsto (fun n ↦ ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * f i)
      Filter.atTop (nhds l))
    (hfa : Antitone fun n ↦ f (2 * N + n)) :
    (∑ i ∈ Finset.range (2 * N), (-1 : ℝ) ^ i * f i) ≤ l ∧
      l ≤ ∑ i ∈ Finset.range (2 * N + 1), (-1 : ℝ) ^ i * f i := by
  set S := ∑ i ∈ Finset.range (2 * N), (-1 : ℝ) ^ i * f i with hS
  have key : ∀ n : ℕ, (∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * f (2 * N + i))
      = (∑ i ∈ Finset.range (2 * N + n), (-1 : ℝ) ^ i * f i) - S := by
    intro n
    rw [hS, Finset.sum_range_add]
    simp [pow_add, pow_mul]
  have hshift : Filter.Tendsto
      (fun n ↦ ∑ i ∈ Finset.range (2 * N + n), (-1 : ℝ) ^ i * f i)
      Filter.atTop (nhds l) := by
    have h := hfl.comp (Filter.tendsto_add_atTop_nat (2 * N))
    simpa [Function.comp_def, Nat.add_comm] using h
  have htend : Filter.Tendsto
      (fun n ↦ ∑ i ∈ Finset.range n, (-1 : ℝ) ^ i * f (2 * N + i))
      Filter.atTop (nhds (l - S)) := by
    simp only [key]
    exact hshift.sub_const S
  have hlow := Antitone.alternating_series_le_tendsto htend hfa 0
  have hhigh := Antitone.tendsto_le_alternating_series htend hfa 0
  simp only [Nat.mul_zero, Finset.range_zero, Finset.sum_empty, Nat.zero_add,
    Finset.sum_range_one, pow_zero, one_mul, Nat.add_zero] at hlow hhigh
  refine ⟨by linarith, ?_⟩
  rw [Finset.sum_range_succ, ← hS, pow_mul]
  simp only [neg_one_sq, one_pow, one_mul]
  linarith

end

end

section

/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
/-!
# For Mathlib / Analysis / Special Functions / Trigonometric
-/

@[expose] public section

/-- The tangent of half a complementary angle is secant minus tangent on the first quadrant. -/
theorem Real.tan_pi_div_two_sub_div_two (ω : ℝ) (hω : ω ∈ Set.Ico 0 (Real.pi / 2)) :
    Real.tan ((Real.pi / 2 - ω) / 2) = (Real.cos ω)⁻¹ - Real.tan ω := by
  let u := (Real.pi / 2 - ω) / 2
  have hu : 0 < Real.cos u := Real.cos_pos_of_mem_Ioo ⟨by
    dsimp [u]
    linarith [Real.pi_pos, hω.1, hω.2], by
    dsimp [u]
    linarith [Real.pi_pos, hω.1, hω.2]⟩
  have hw : 0 < Real.cos ω :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hω.1, hω.2], hω.2⟩
  have h2 : 2 * u = Real.pi / 2 - ω := by
    dsimp [u]
    ring
  have hs : 2 * Real.sin u * Real.cos u = Real.cos ω := by
    rw [← Real.sin_two_mul, h2, Real.sin_pi_div_two_sub]
  have hc : 2 * Real.cos u ^ 2 - 1 = Real.sin ω := by
    rw [← Real.cos_two_mul, h2, Real.cos_pi_div_two_sub]
  change Real.tan u = _
  rw [Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos]
  field_simp [hu.ne', hw.ne']
  nlinarith [Real.sin_sq_add_cos_sq u]

/-- Cotangent is antitone between its consecutive poles at negative pi and zero. -/
theorem Real.antitoneOn_cos_div_sin_Ioo_neg_pi_zero :
    AntitoneOn (fun x : ℝ ↦ Real.cos x / Real.sin x) (Set.Ioo (-Real.pi) 0) := by
  intro x hx y hy hxy
  have hxsin := Real.sin_neg_of_neg_of_neg_pi_lt hx.2 hx.1
  have hysin := Real.sin_neg_of_neg_of_neg_pi_lt hy.2 hy.1
  change Real.cos y / Real.sin y ≤ Real.cos x / Real.sin x
  rw [← neg_div_neg_eq (Real.cos y) (Real.sin y),
    ← neg_div_neg_eq (Real.cos x) (Real.sin x)]
  apply (div_le_div_iff₀ (neg_pos.mpr hysin) (neg_pos.mpr hxsin)).mpr
  have hsin : 0 ≤ Real.sin (y - x) := Real.sin_nonneg_of_nonneg_of_le_pi
    (by linarith) (by linarith [hx.1, hy.2])
  rw [Real.sin_sub] at hsin
  nlinarith

/-- A cubic upper bound for the tangent on `[0, 1]`, companion to `Real.sin_gt_sub_cube`. -/
theorem Real.tan_le_self_add_cube {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.tan x ≤ x + 4 / 3 * x ^ 3 := by
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hcos : 0 < Real.cos x :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hcl : 1 - x ^ 2 / 2 ≤ Real.cos x := Real.one_sub_sq_div_two_le_cos
  have hs : Real.sin x ≤ x := Real.sin_le hx
  rw [Real.tan_eq_sin_div_cos, div_le_iff₀ hcos]
  have h1 : (0 : ℝ) ≤ x + 4 / 3 * x ^ 3 := by positivity
  have h2 : (x + 4 / 3 * x ^ 3) * (1 - x ^ 2 / 2) ≤ (x + 4 / 3 * x ^ 3) * Real.cos x :=
    mul_le_mul_of_nonneg_left hcl h1
  have h3 : x ≤ (x + 4 / 3 * x ^ 3) * (1 - x ^ 2 / 2) := by
    nlinarith [mul_nonneg (pow_nonneg hx 3) (show (0 : ℝ) ≤ 5 / 6 - 2 / 3 * x ^ 2 by nlinarith)]
  linarith

/-- Leibniz bracketing of the sine by its Maclaurin partial sums: for `0 ≤ x` with
`x ^ 2 ≤ (4 * N + 2) * (4 * N + 3)` the value `Real.sin x` lies between the partial sums of
`2 * N` and of `2 * N + 1` terms, the first of which undershoots and the second overshoots. -/
theorem Real.sin_mem_Icc_taylor_sums (N : ℕ) {x : ℝ} (hx0 : 0 ≤ x)
    (hx : x ^ 2 ≤ ((4 * N + 2) * (4 * N + 3) : ℕ)) :
    Real.sin x ∈ Set.Icc
      (∑ k ∈ Finset.range (2 * N),
        (-1 : ℝ) ^ k * x ^ (2 * k + 1) / (Nat.factorial (2 * k + 1) : ℝ))
      (∑ k ∈ Finset.range (2 * N + 1),
        (-1 : ℝ) ^ k * x ^ (2 * k + 1) / (Nat.factorial (2 * k + 1) : ℝ)) := by
  have hsum : ∀ n : ℕ, (∑ i ∈ Finset.range n,
        (-1 : ℝ) ^ i * (x ^ (2 * i + 1) / (Nat.factorial (2 * i + 1) : ℝ)))
      = ∑ k ∈ Finset.range n,
        (-1 : ℝ) ^ k * x ^ (2 * k + 1) / (Nat.factorial (2 * k + 1) : ℝ) :=
    fun n ↦ Finset.sum_congr rfl fun k _ ↦ (mul_div_assoc _ _ _).symm
  have htend : Filter.Tendsto (fun n ↦ ∑ i ∈ Finset.range n,
      (-1 : ℝ) ^ i * (x ^ (2 * i + 1) / (Nat.factorial (2 * i + 1) : ℝ)))
      Filter.atTop (nhds (Real.sin x)) := by
    have h := (Real.hasSum_sin x).tendsto_sum_nat
    simpa only [mul_div_assoc] using h
  have hfa : Antitone fun n : ℕ ↦
      x ^ (2 * (2 * N + n) + 1) / (Nat.factorial (2 * (2 * N + n) + 1) : ℝ) := by
    have e : ∀ n : ℕ, 2 * (2 * N + n) + 1 = 2 * n + (4 * N + 1) := fun n ↦ by omega
    simp only [e]
    refine antitone_pow_div_factorial_two_mul_add (a := 4 * N + 1) hx0 ?_
    refine hx.trans (le_of_eq ?_)
    push_cast
    ring
  obtain ⟨hlow, hhigh⟩ :=
    alternating_series_bracket_of_antitone_shift
      (f := fun k : ℕ ↦ x ^ (2 * k + 1) / (Nat.factorial (2 * k + 1) : ℝ)) N htend hfa
  rw [hsum] at hlow hhigh
  exact ⟨hlow, hhigh⟩

/-- Leibniz bracketing of the cosine by its Maclaurin partial sums: for `0 ≤ x` with
`x ^ 2 ≤ (4 * N + 1) * (4 * N + 2)` the value `Real.cos x` lies between the partial sums of
`2 * N` and of `2 * N + 1` terms, the first of which undershoots and the second overshoots. -/
theorem Real.cos_mem_Icc_taylor_sums (N : ℕ) {x : ℝ} (hx0 : 0 ≤ x)
    (hx : x ^ 2 ≤ ((4 * N + 1) * (4 * N + 2) : ℕ)) :
    Real.cos x ∈ Set.Icc
      (∑ k ∈ Finset.range (2 * N),
        (-1 : ℝ) ^ k * x ^ (2 * k) / (Nat.factorial (2 * k) : ℝ))
      (∑ k ∈ Finset.range (2 * N + 1),
        (-1 : ℝ) ^ k * x ^ (2 * k) / (Nat.factorial (2 * k) : ℝ)) := by
  have hsum : ∀ n : ℕ, (∑ i ∈ Finset.range n,
        (-1 : ℝ) ^ i * (x ^ (2 * i) / (Nat.factorial (2 * i) : ℝ)))
      = ∑ k ∈ Finset.range n,
        (-1 : ℝ) ^ k * x ^ (2 * k) / (Nat.factorial (2 * k) : ℝ) :=
    fun n ↦ Finset.sum_congr rfl fun k _ ↦ (mul_div_assoc _ _ _).symm
  have htend : Filter.Tendsto (fun n ↦ ∑ i ∈ Finset.range n,
      (-1 : ℝ) ^ i * (x ^ (2 * i) / (Nat.factorial (2 * i) : ℝ)))
      Filter.atTop (nhds (Real.cos x)) := by
    have h := (Real.hasSum_cos x).tendsto_sum_nat
    simpa only [mul_div_assoc] using h
  have hfa : Antitone fun n : ℕ ↦
      x ^ (2 * (2 * N + n)) / (Nat.factorial (2 * (2 * N + n)) : ℝ) := by
    have e : ∀ n : ℕ, 2 * (2 * N + n) = 2 * n + 4 * N := fun n ↦ by omega
    simp only [e]
    refine antitone_pow_div_factorial_two_mul_add (a := 4 * N) hx0 ?_
    refine hx.trans (le_of_eq ?_)
    push_cast
    ring
  obtain ⟨hlow, hhigh⟩ :=
    alternating_series_bracket_of_antitone_shift
      (f := fun k : ℕ ↦ x ^ (2 * k) / (Nat.factorial (2 * k) : ℝ)) N htend hfa
  rw [hsum] at hlow hhigh
  exact ⟨hlow, hhigh⟩

end

end
