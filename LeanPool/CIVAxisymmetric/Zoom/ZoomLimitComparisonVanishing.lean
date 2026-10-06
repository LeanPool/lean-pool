/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Main.ComparisonAncient
public import LeanPool.CIVAxisymmetric.Zoom.FiniteAxisBounds
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# The comparison principle applied to the two ancient limits of `prop:aniso:small`

The last step of each branch of the zoom argument of `prop:aniso:small` applies the last
assertion of `lem:aniso:comparison` to the limiting scalar:

* in the finite-axis case, to the lifted limit `Ω_∞(X, Z, τ) = Ω(|X|, Z, τ)` of the rescaled
  potential vorticities on `ℝ⁴ × ℝ × (-∞, -1)`, with `(m, d) = (5, 4)` and `κ = 3/2 + h`
  (the paragraph after `eq:aniso:zoom:finite:limit`);
* in the receding-axis case, to the limit `Θ` of the rescaled azimuthal vorticities on
  `ℝ² × (-∞, -1)`, with `(m, d) = (2, 1)` and `κ = 1 + h` (the paragraph after
  `eq:aniso:zoom:receding:limit`).

In both cases the limit is continuous on the relevant open set up to the endpoint `τ = -1`
(it is a locally uniform limit) and obeys the decay bound inherited from
`eq:aniso:zoom:finite:bound` or `eq:aniso:zoom:receding:bound`. The two theorems below take
exactly these facts, together with the admissible drift and the distributional limit equation,
and conclude that the limit vanishes at every point of `{τ = -1}` (off the axis in the
finite-axis case). The local boundedness, the measurability and the decay premise of the
comparison lemma are derived here from the continuity and the pointwise bound; the axis
`{X = 0}` of the lifted variables is a null set.
-/

public section

open Set Filter Topology MeasureTheory
open CKN.Foundation.Parabolic CKN


noncomputable section

namespace CIV

/-! ### The axis of the lifted variables is a null set -/

/-- The axis `{X = 0}` of the lifted variables `Vec 5 × ℝ` is contained in the null
hyperplane `{X₀ = 0}`. -/
theorem volume_zoomLiftAxis_eq_zero :
    volume {z : Vec 5 × ℝ | zoomLiftRadius z.1 = 0} = 0 := by
  have hsub : {z : Vec 5 × ℝ | zoomLiftRadius z.1 = 0} ⊆
      {x : Vec 5 | x 0 = 0} ×ˢ (univ : Set ℝ) := by
    intro z hz
    refine ⟨?_, trivial⟩
    have h0 : z.1 0 ^ 2 + z.1 1 ^ 2 + z.1 2 ^ 2 + z.1 3 ^ 2 = 0 := by
      have hz' : Real.sqrt (z.1 0 ^ 2 + z.1 1 ^ 2 + z.1 2 ^ 2 + z.1 3 ^ 2) = 0 := hz
      rwa [Real.sqrt_eq_zero (by positivity)] at hz'
    have hsq : z.1 0 ^ 2 = 0 := by
      nlinarith only [h0, sq_nonneg (z.1 0), sq_nonneg (z.1 1), sq_nonneg (z.1 2),
        sq_nonneg (z.1 3)]
    exact pow_eq_zero_iff (two_ne_zero) |>.mp hsq
  have hplane : volume {x : Vec 5 | x 0 = 0} = 0 := by
    have := Measure.pi_hyperplane (fun _ : Fin 5 => (volume : Measure ℝ)) 0 (0 : ℝ)
    simpa [← MeasureTheory.volume_pi] using this
  refine measure_mono_null hsub ?_
  rw [Measure.volume_eq_prod, Measure.prod_prod, hplane, zero_mul]

/-- Almost every lifted point lies off the axis. -/
theorem ae_zoomLiftRadius_pos (μ : Measure (Vec 5 × ℝ)) (hμ : μ ≪ volume) :
    ∀ᵐ z ∂μ, 0 < zoomLiftRadius z.1 := by
  have hnull : ∀ᵐ z ∂(volume : Measure (Vec 5 × ℝ)), zoomLiftRadius z.1 ≠ 0 := by
    rw [ae_iff]
    simpa using volume_zoomLiftAxis_eq_zero
  exact (hnull.filter_mono hμ.ae_le).mono fun z hz =>
    lt_of_le_of_ne (zoomLiftRadius_nonneg z.1) (Ne.symm hz)

/-- Almost every lifted spatial point lies off the axis. -/
theorem ae_zoomLiftRadius_pos_vec :
    ∀ᵐ x ∂(volume : Measure (Vec 5)), 0 < zoomLiftRadius x := by
  have hnull : ∀ᵐ x ∂(volume : Measure (Vec 5)), x 0 ≠ 0 := by
    have := Measure.ae_eval_ne (fun _ : Fin 5 => (volume : Measure ℝ)) 0 (0 : ℝ)
    simpa [← MeasureTheory.volume_pi] using this
  refine hnull.mono fun x hx => ?_
  refine lt_of_le_of_ne (zoomLiftRadius_nonneg x) (Ne.symm ?_)
  intro h0
  apply hx
  have h0' : x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 = 0 := by
    have hz' : Real.sqrt (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2) = 0 := h0
    rwa [Real.sqrt_eq_zero (by positivity)] at hz'
  have hsq : x 0 ^ 2 = 0 := by
    nlinarith only [h0', sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2), sq_nonneg (x 3)]
  exact pow_eq_zero_iff (two_ne_zero) |>.mp hsq

/-- `zoomLiftPoint` is continuous. -/
theorem continuous_zoomLiftPoint : Continuous zoomLiftPoint := by
  unfold zoomLiftPoint zoomLiftRadius
  fun_prop

/-! ### The finite-axis case, `(m, d) = (5, 4)` -/

/-- The point `(R, 0, 0, 0, Z)` of the lifted space lies at lifted radius `R ≥ 0` and height
`Z`. -/
theorem zoomLiftPoint_mk {R Z τ : ℝ} (hR : 0 ≤ R) :
    zoomLiftPoint ((![R, 0, 0, 0, Z] : Vec 5), τ) = ((R, Z), τ) := by
  simp [zoomLiftPoint, zoomLiftRadius, Real.sqrt_sq hR]

/-- The lift of a function continuous on `{R > 0, τ ≤ -1}` and bounded there by
`C |τ|^{-3/2-h}` is locally bounded on `ℝ⁵ × (-∞, -1)` (the axis is a null set). -/
theorem isLocallyBoundedOn_zoomLift {C h : ℝ} (hh : 0 < h)
    (Ω : (ℝ × ℝ) × ℝ → ℝ) (hΩc : ContinuousOn Ω {p | 0 < p.1.1 ∧ p.2 ≤ -1})
    (hΩb : ∀ p : (ℝ × ℝ) × ℝ, 0 < p.1.1 → p.2 ≤ -1 → |Ω p| ≤ C * (-p.2) ^ (-(3 / 2 : ℝ) - h)) :
    IsLocallyBoundedOn 5 (Iio (-1)) (fun z => Ω (zoomLiftPoint z)) := by
  set q : Vec 5 × ℝ → ℝ := fun z => Ω (zoomLiftPoint z) with hq_def
  set U : Set (Vec 5 × ℝ) := {z | 0 < zoomLiftRadius z.1} with hU_def
  have hUopen : IsOpen U := by
    have hc : Continuous fun z : Vec 5 × ℝ => zoomLiftRadius z.1 := by
      unfold zoomLiftRadius; fun_prop
    exact isOpen_lt continuous_const hc
  -- continuity of the lift off the axis, up to `τ = -1`
  have hqc : ContinuousOn q (U ∩ univ ×ˢ Iic (-1)) := by
    refine hΩc.comp continuous_zoomLiftPoint.continuousOn ?_
    intro z hz
    exact ⟨hz.1, hz.2.2⟩
  -- the pointwise bound off the axis
  have hbound : ∀ z : Vec 5 × ℝ, 0 < zoomLiftRadius z.1 → z.2 ≤ -1 →
      |q z| ≤ max C 0 := by
    intro z hz hτ
    have h1 := hΩb (zoomLiftPoint z) hz hτ
    have hτ1 : (1 : ℝ) ≤ -z.2 := by linarith only [hτ]
    have hr : (-z.2) ^ (-(3 / 2 : ℝ) - h) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hτ1 (by linarith only [hh])
    have hr0 : 0 ≤ (-z.2) ^ (-(3 / 2 : ℝ) - h) := Real.rpow_nonneg (by linarith only [hτ1]) _
    calc |q z| ≤ C * (-z.2) ^ (-(3 / 2 : ℝ) - h) := h1
      _ ≤ max C 0 * (-z.2) ^ (-(3 / 2 : ℝ) - h) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hr0
      _ ≤ max C 0 * 1 := mul_le_mul_of_nonneg_left hr (le_max_right _ _)
      _ = max C 0 := mul_one _
  -- local boundedness
  have hmeasU : MeasurableSet (U ∩ univ ×ˢ Iio (-1)) :=
    hUopen.measurableSet.inter (MeasurableSet.univ.prod measurableSet_Iio)
  have hae_set : (U ∩ univ ×ˢ Iio (-1) : Set (Vec 5 × ℝ)) =ᵐ[volume]
      (univ ×ˢ Iio (-1) : Set (Vec 5 × ℝ)) := by
    have hUc : volume Uᶜ = 0 := by
      refine measure_mono_null (fun z hz => ?_) volume_zoomLiftAxis_eq_zero
      have hz' : ¬ 0 < zoomLiftRadius z.1 := hz
      exact le_antisymm (not_lt.mp hz') (zoomLiftRadius_nonneg z.1)
    have h1 : (U ∩ univ ×ˢ Iio (-1) : Set (Vec 5 × ℝ)) =ᵐ[volume]
        (univ ∩ univ ×ˢ Iio (-1) : Set (Vec 5 × ℝ)) :=
      (ae_eq_univ.mpr hUc).inter (ae_eq_refl _)
    simpa using h1
  have hq : IsLocallyBoundedOn 5 (Iio (-1)) q := by
    refine ⟨?_, ?_⟩
    · have hcont : ContinuousOn q (U ∩ univ ×ˢ Iio (-1)) :=
        hqc.mono (inter_subset_inter_right _ (prod_mono subset_rfl Iio_subset_Iic_self))
      have := hcont.aestronglyMeasurable (μ := volume) hmeasU
      rwa [Measure.restrict_congr_set hae_set] at this
    · intro J hJ hJsub
      refine ⟨max C 0, ?_⟩
      have hrestr : volume.restrict (univ ×ˢ J) ≪ (volume : Measure (Vec 5 × ℝ)) :=
        Measure.restrict_le_self.absolutelyContinuous
      filter_upwards [ae_zoomLiftRadius_pos _ hrestr,
        ae_restrict_mem (MeasurableSet.univ.prod hJ.measurableSet)] with z hz hzJ
      exact hbound z hz (le_of_lt (hJsub hzJ.2))
  exact hq

/-- The comparison principle applied to the finite-axis limit (the paragraph after
`eq:aniso:zoom:finite:limit`): a function `Ω` of `((R, Z), τ)`, continuous on
`{R > 0, τ ≤ -1}` and bounded there by `C |τ|^{-3/2-h}`, whose lift to `ℝ⁴ × ℝ` solves the limit
equation `eq:aniso:zoom:finite:limit` in the sense of distributions on `(-∞, -1)` with an
admissible drift, vanishes at every point `(R, Z, -1)` with `R > 0`. This is the last
assertion of `lem:aniso:comparison` with `(m, d) = (5, 4)` and `κ = 3/2 + h`. -/
theorem zoomOmegaLimit_endpoint_eq_zero {C h : ℝ} (hh : 0 < h)
    (Ω : (ℝ × ℝ) × ℝ → ℝ) (hΩc : ContinuousOn Ω {p | 0 < p.1.1 ∧ p.2 ≤ -1})
    (hΩb : ∀ p : (ℝ × ℝ) × ℝ, 0 < p.1.1 → p.2 ≤ -1 → |Ω p| ≤ C * (-p.2) ^ (-(3 / 2 : ℝ) - h))
    (B : Vec 5 × ℝ → Vec 5) (divB : Vec 5 × ℝ → ℝ)
    (hB : IsAdmissibleDrift 5 (Iio (-1)) B divB)
    (heq : IsDistributionalDriftDiffusion 5 4 (Iio (-1)) B divB
      (fun z => Ω (zoomLiftPoint z))) :
    ∀ p : ℝ × ℝ, 0 < p.1 → Ω (p, -1) = 0 := by
  set q : Vec 5 × ℝ → ℝ := fun z => Ω (zoomLiftPoint z) with hq_def
  set U : Set (Vec 5 × ℝ) := {z | 0 < zoomLiftRadius z.1} with hU_def
  have hUopen : IsOpen U := by
    have hc : Continuous fun z : Vec 5 × ℝ => zoomLiftRadius z.1 := by
      unfold zoomLiftRadius; fun_prop
    exact isOpen_lt continuous_const hc
  -- continuity of the lift off the axis, up to `τ = -1`
  have hqc : ContinuousOn q (U ∩ univ ×ˢ Iic (-1)) := by
    refine hΩc.comp continuous_zoomLiftPoint.continuousOn ?_
    intro z hz
    exact ⟨hz.1, hz.2.2⟩
  have hq : IsLocallyBoundedOn 5 (Iio (-1)) q := isLocallyBoundedOn_zoomLift hh Ω hΩc hΩb
  -- the decay premise with `κ = 3/2 + h`
  have hdecay : ∀ᵐ τ ∂(volume.restrict (Iio (min (-1 : ℝ) (-1)))),
      eLpNorm (fun x => q (x, τ)) ⊤ volume ≤
        ENNReal.ofReal (max C 0 * |τ| ^ (-(3 / 2 + h))) := by
    filter_upwards [ae_restrict_mem measurableSet_Iio] with τ hτ
    have hτ' : τ < -1 := by simpa using hτ
    have habs : |τ| = -τ := abs_of_neg (by linarith only [hτ'])
    have hmeas : AEStronglyMeasurable (fun x : Vec 5 => q (x, τ)) volume := by
      have hU' : IsOpen {x : Vec 5 | 0 < zoomLiftRadius x} := by
        refine isOpen_lt continuous_const ?_
        unfold zoomLiftRadius; fun_prop
      have hc' : ContinuousOn (fun x : Vec 5 => q (x, τ)) {x : Vec 5 | 0 < zoomLiftRadius x} :=
        hΩc.comp (continuous_zoomLiftPoint.comp (Continuous.prodMk_left τ)).continuousOn
          (fun x hx => ⟨hx, hτ'.le⟩)
      have hm := hc'.aestronglyMeasurable (μ := volume) hU'.measurableSet
      have hset : ({x : Vec 5 | 0 < zoomLiftRadius x} : Set (Vec 5)) =ᵐ[volume] univ :=
        ae_eq_univ.mpr (ae_iff.mp ae_zoomLiftRadius_pos_vec)
      rwa [Measure.restrict_congr_set hset, Measure.restrict_univ] at hm
    rw [eLpNorm_exponent_top hmeas]
    refine eLpNormEssSup_le_of_ae_bound ?_
    filter_upwards [ae_zoomLiftRadius_pos_vec] with x hx
    have h1 := hΩb (zoomLiftPoint (x, τ)) hx hτ'.le
    rw [Real.norm_eq_abs]
    have hexp : -(3 / 2 + h) = -(3 / 2 : ℝ) - h := by ring
    rw [habs, hexp]
    have hr0 : 0 ≤ (-τ) ^ (-(3 / 2 : ℝ) - h) := Real.rpow_nonneg (by linarith only [hτ']) _
    exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hr0)
  have hκ : (0 : ℝ) < 3 / 2 + h := by linarith only [hh]
  obtain ⟨-, hcont⟩ := Main.comparisonAncient 5 4 ⟨by norm_num, by norm_num⟩ (-1) B divB hB q hq
    heq (max C 0) (3 / 2 + h) hκ hdecay
  intro p hp
  have hz : ((![p.1, 0, 0, 0, p.2] : Vec 5), (-1 : ℝ)) ∈ U ∩ univ ×ˢ Iic (-1) := by
    refine ⟨?_, trivial, by simp⟩
    change 0 < zoomLiftRadius ![p.1, 0, 0, 0, p.2]
    simp [zoomLiftRadius, Real.sqrt_sq hp.le, hp]
  have h0 := hcont U q hUopen hqc (ae_of_all _ fun _ => rfl) _ hz
  simpa [hq_def, zoomLiftPoint_mk hp.le] using h0

/-! ### The receding-axis case, `(m, d) = (2, 1)` -/

/-- The meridional point `((R, Z), τ)` read from a point of `Vec 2 × ℝ`. -/
@[expose] def planeLiftPoint (z : Vec 2 × ℝ) : (ℝ × ℝ) × ℝ := ((z.1 0, z.1 1), z.2)

/-- `planeLiftPoint` is continuous. -/
theorem continuous_planeLiftPoint : Continuous planeLiftPoint := by
  unfold planeLiftPoint
  fun_prop

/-- The comparison principle applied to the receding-axis limit (the paragraph after
`eq:aniso:zoom:receding:limit`): a function `Θ` of `((R, Z), τ)`, continuous on `{τ ≤ -1}` and
bounded there by `C |τ|^{-1-h}`, which solves the limit equation
`eq:aniso:zoom:receding:limit:a` in the sense of distributions on `ℝ² × (-∞, -1)` with an
admissible drift and diffusion in `R` alone, vanishes at every point `(R, Z, -1)`. This is the
last assertion of `lem:aniso:comparison` with `(m, d) = (2, 1)` and `κ = 1 + h`. -/
theorem zoomThetaLimit_endpoint_eq_zero {C h : ℝ} (hh : 0 < h)
    (Θ : (ℝ × ℝ) × ℝ → ℝ) (hΘc : ContinuousOn Θ {p | p.2 ≤ -1})
    (hΘb : ∀ p : (ℝ × ℝ) × ℝ, p.2 ≤ -1 → |Θ p| ≤ C * (-p.2) ^ (-1 - h))
    (B : Vec 2 × ℝ → Vec 2) (divB : Vec 2 × ℝ → ℝ)
    (hB : IsAdmissibleDrift 2 (Iio (-1)) B divB)
    (heq : IsDistributionalDriftDiffusion 2 1 (Iio (-1)) B divB
      (fun z => Θ (planeLiftPoint z))) :
    ∀ p : ℝ × ℝ, Θ (p, -1) = 0 := by
  set q : Vec 2 × ℝ → ℝ := fun z => Θ (planeLiftPoint z) with hq_def
  have hqc : ContinuousOn q (univ ∩ univ ×ˢ Iic (-1)) := by
    refine hΘc.comp continuous_planeLiftPoint.continuousOn ?_
    intro z hz
    exact hz.2.2
  have hbound : ∀ z : Vec 2 × ℝ, z.2 ≤ -1 → |q z| ≤ max C 0 := by
    intro z hτ
    have h1 := hΘb (planeLiftPoint z) hτ
    have hτ1 : (1 : ℝ) ≤ -z.2 := by linarith only [hτ]
    have hr : (-z.2) ^ (-1 - h) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hτ1 (by linarith only [hh])
    have hr0 : 0 ≤ (-z.2) ^ (-1 - h) := Real.rpow_nonneg (by linarith only [hτ1]) _
    calc |q z| ≤ C * (-z.2) ^ (-1 - h) := h1
      _ ≤ max C 0 * (-z.2) ^ (-1 - h) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hr0
      _ ≤ max C 0 * 1 := mul_le_mul_of_nonneg_left hr (le_max_right _ _)
      _ = max C 0 := mul_one _
  have hq : IsLocallyBoundedOn 2 (Iio (-1)) q := by
    refine ⟨?_, ?_⟩
    · have hcont : ContinuousOn q (univ ×ˢ Iio (-1)) :=
        hqc.mono (fun z hz => ⟨trivial, trivial, (show z.2 ≤ -1 from le_of_lt hz.2)⟩)
      exact hcont.aestronglyMeasurable (MeasurableSet.univ.prod measurableSet_Iio)
    · intro J hJ hJsub
      refine ⟨max C 0, ?_⟩
      filter_upwards [ae_restrict_mem (MeasurableSet.univ.prod hJ.measurableSet)] with z hzJ
      exact hbound z (le_of_lt (hJsub hzJ.2))
  have hdecay : ∀ᵐ τ ∂(volume.restrict (Iio (min (-1 : ℝ) (-1)))),
      eLpNorm (fun x => q (x, τ)) ⊤ volume ≤
        ENNReal.ofReal (max C 0 * |τ| ^ (-(1 + h))) := by
    filter_upwards [ae_restrict_mem measurableSet_Iio] with τ hτ
    have hτ' : τ < -1 := by simpa using hτ
    have habs : |τ| = -τ := abs_of_neg (by linarith only [hτ'])
    have hmeas : AEStronglyMeasurable (fun x : Vec 2 => q (x, τ)) volume := by
      have hc' : Continuous (fun x : Vec 2 => q (x, τ)) := by
        have := hqc.comp_continuous (continuous_id.prodMk continuous_const)
          (fun x => ⟨trivial, trivial, hτ'.le⟩)
        exact this
      exact hc'.aestronglyMeasurable
    rw [eLpNorm_exponent_top hmeas]
    refine eLpNormEssSup_le_of_ae_bound (ae_of_all _ fun x => ?_)
    have h1 := hΘb (planeLiftPoint (x, τ)) hτ'.le
    rw [Real.norm_eq_abs]
    have hexp : -(1 + h) = -1 - h := by ring
    rw [habs, hexp]
    have hr0 : 0 ≤ (-τ) ^ (-1 - h) := Real.rpow_nonneg (by linarith only [hτ']) _
    exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hr0)
  have hκ : (0 : ℝ) < 1 + h := by linarith only [hh]
  obtain ⟨-, hcont⟩ := Main.comparisonAncient 2 1 ⟨le_refl 1, by norm_num⟩ (-1) B divB hB q hq
    heq (max C 0) (1 + h) hκ hdecay
  intro p
  have hz : ((![p.1, p.2] : Vec 2), (-1 : ℝ)) ∈ (univ : Set (Vec 2 × ℝ)) ∩ univ ×ˢ Iic (-1) :=
    ⟨trivial, trivial, by simp⟩
  have h0 := hcont univ q isOpen_univ hqc (ae_of_all _ fun _ => rfl) _ hz
  simpa [hq_def, planeLiftPoint] using h0

end CIV
