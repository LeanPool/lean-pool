/-
Copyright (c) 2026 Dean Cureton and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton, The Moving Sofa contributors
-/
module

public import LeanPool.MovingSofa.Infrastructure.Analysis.Foundations.Development001
public import LeanPool.MovingSofa.Analysis.Foundations.Development005
public import LeanPool.MovingSofa.Infrastructure.MathlibExtensions.Foundations.Development001
public import LeanPool.MovingSofa.Polygon.Applications.Development002
/-!
# Moving sofa: related mathematical developments

* `Cap.DensityExistence`.
* `Cap.Interpolation`.
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
# Existence and uniqueness of the surface densities of a balanced maximum cap

A balanced maximum cap of rotation angle `π / 2` satisfies the density clause of the
injectivity condition: its surface area measure has nonnegative measurable densities on the
quarter arcs `[0, π / 2)` and `(π / 2, π]`, unique up to Lebesgue-null sets.

On the first arc the density comes from the limiting inequality
`balancedMaximumCap_surface_domination` together with the Radon–Nikodym construction
`exists_nnreal_density_of_domination`. On the second arc the mirror image of the cap is again a
balanced maximum cap, and the surface-measure identity of `cap_mirror_features` transports its
first-arc density back along the reflection `a ↦ π - a` of normal angles.

On the first arc the domination inequality also bounds the density: the real density produced by
`exists_capDensity_right_le_magicDensity` is at most `k₀` of the positive tangent arm length.
-/

/-! ### A continuous section of the angular projection -/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace MovingSofa

/-- A continuous left inverse of the angle coercion on `[-(π / 2), π / 2]`. -/
private def angleSection (a : Real.Angle) : ℝ := Real.arcsin a.sin

private theorem continuous_angleSection : Continuous angleSection :=
  Real.continuous_arcsin.comp Real.Angle.continuous_sin

private theorem angleSection_coe {t : ℝ} (ht : t ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) :
    angleSection (t : Real.Angle) = t := by
  rw [angleSection, Real.Angle.sin_coe, Real.arcsin_sin ht.1 ht.2]

/-- After a quarter-turn shift, `angleSection` inverts the angle coercion on `[0, π]`. -/
private theorem angleSection_sub_coe {t : ℝ} (ht : t ∈ Icc (-(Real.pi / 2)) (Real.pi / 2)) :
    angleSection (((t + Real.pi / 2 : ℝ) : Real.Angle) -
      ((Real.pi / 2 : ℝ) : Real.Angle)) = t := by
  rw [← Real.Angle.coe_sub, add_sub_cancel_right, angleSection_coe ht]

/-- The second quarter arc, parametrized from `0` by a quarter-turn shift. -/
private theorem image_coe_add_pi_div_two_Ioc :
    (fun t : ℝ ↦ ((t + Real.pi / 2 : ℝ) : Real.Angle)) '' Ioc 0 (Real.pi / 2) =
      (fun t : ℝ ↦ (t : Real.Angle)) '' Ioc (Real.pi / 2) Real.pi := by
  rw [show (fun t : ℝ ↦ ((t + Real.pi / 2 : ℝ) : Real.Angle)) =
      (fun u : ℝ ↦ (u : Real.Angle)) ∘ (fun t : ℝ ↦ t + Real.pi / 2) from rfl,
    Set.image_comp, Set.image_add_const_Ioc, zero_add, add_halves]

/-- If `ψ` inverts `φ` on `S`, then cutting a `ψ`-preimage down to the `φ`-image of `S` is the
same as taking the `φ`-image of the corresponding part of `S`. -/
private theorem preimage_inter_image_eq_image_inter {α β : Type*} {φ : α → β} {ψ : β → α}
    {S : Set α} (hsec : ∀ t ∈ S, ψ (φ t) = t) (E : Set α) :
    ψ ⁻¹' E ∩ φ '' S = φ '' (E ∩ S) := by
  ext a
  constructor
  · rintro ⟨haE, t, ht, rfl⟩
    rw [mem_preimage, hsec t ht] at haE
    exact ⟨t, ⟨haE, ht⟩, rfl⟩
  · rintro ⟨t, ⟨htE, ht⟩, rfl⟩
    exact ⟨by rw [mem_preimage, hsec t ht]; exact htE, t, ht, rfl⟩

/-! ### Densities on an arc from a domination inequality -/

/-- Transport of the bounded-density construction to an arc of normal angles. If the angular
parametrization `φ` has a measurable left inverse on a measurable set `S` that fills
`[0, π / 2]` up to a null set, and the mass that `μ₀` gives to `φ '' E` is dominated by the
integral of a bounded nonnegative function `f` over `E ⊆ S`, then `μ₀` restricted to the arc
`φ '' S` is the pushforward along `φ` of a weighted Lebesgue measure on `S`. -/
private theorem exists_arcDensity_of_domination (μ₀ : Measure Real.Angle) [IsFiniteMeasure μ₀]
    {φ : ℝ → Real.Angle} (hφ : Measurable φ) {ψ : Real.Angle → ℝ} (hψ : Measurable ψ)
    {S : Set ℝ} (hS : MeasurableSet S) (hSae : S =ᵐ[volume] Icc (0 : ℝ) (Real.pi / 2))
    (hSsub : S ⊆ Icc (0 : ℝ) (Real.pi / 2)) (hA : MeasurableSet (φ '' S))
    (hsec : ∀ t ∈ S, ψ (φ t) = t)
    (f : ℝ → ℝ) (hf : AEStronglyMeasurable f (volume.restrict (Icc (0 : ℝ) (Real.pi / 2))))
    (hf_nonneg : ∀ t ∈ Icc (0 : ℝ) (Real.pi / 2), 0 ≤ f t)
    {M : ℝ} (hf_bound : ∀ t ∈ Icc (0 : ℝ) (Real.pi / 2), f t ≤ M)
    (hdom : ∀ E : Set ℝ, MeasurableSet E → E ⊆ S →
      μ₀ (φ '' E) ≤ ENNReal.ofReal (∫ t in E, f t)) :
    ∃ r : ℝ → ℝ≥0, Measurable r ∧
      μ₀.restrict (φ '' S) =
        Measure.map φ ((volume.restrict S).withDensity fun t ↦ (r t : ℝ≥0∞)) := by
  classical
  set μ : Measure ℝ := Measure.map ψ (μ₀.restrict (φ '' S)) with hμ
  have hμ_apply : ∀ E : Set ℝ, MeasurableSet E → μ E = μ₀ (φ '' (E ∩ S)) := fun E hE ↦ by
    rw [hμ, Measure.map_apply hψ hE, Measure.restrict_apply (hψ hE),
      preimage_inter_image_eq_image_inter hsec E]
  have : IsFiniteMeasure μ := by
    refine ⟨?_⟩
    rw [hμ_apply univ MeasurableSet.univ]
    exact measure_lt_top _ _
  have hμ_compl : μ (Icc (0 : ℝ) (Real.pi / 2))ᶜ = 0 := by
    rw [hμ_apply _ measurableSet_Icc.compl,
      show (Icc (0 : ℝ) (Real.pi / 2))ᶜ ∩ S = ∅ from
        eq_empty_of_subset_empty fun x hx ↦ hx.1 (hSsub hx.2),
      Set.image_empty, measure_empty]
  have hdom' : ∀ E : Set ℝ, MeasurableSet E → E ⊆ Icc (0 : ℝ) (Real.pi / 2) →
      μ E ≤ ENNReal.ofReal (∫ t in E, f t) := by
    intro E hE hEsub
    have hES : E ∩ S =ᵐ[volume] E := by
      have h := Filter.EventuallyEqSet.inter (Filter.EventuallyEq.refl _ E) hSae
      rwa [inter_eq_left.mpr hEsub] at h
    rw [hμ_apply E hE]
    exact (hdom _ (hE.inter hS) inter_subset_right).trans
      (le_of_eq (congrArg ENNReal.ofReal (setIntegral_congr_set hES)))
  obtain ⟨r, hr, hreq⟩ :=
    exists_nnreal_density_of_domination μ hμ_compl f hf hf_nonneg hf_bound hdom'
  refine ⟨r, hr, ?_⟩
  have hmap : Measure.map φ μ = μ₀.restrict (φ '' S) := by
    rw [hμ]
    refine Measure.map_map_of_ae_leftInverse hψ hφ ?_
    filter_upwards [ae_restrict_mem hA] with a ha
    obtain ⟨t, ht, rfl⟩ := ha
    rw [hsec t ht]
  rw [← hmap, hreq, ← Measure.restrict_congr_set hSae]

/-! ### The density on the first arc -/

private theorem exists_capDensity_right (K : RightAngleCapSpace)
    (hK : IsBalancedMaximumCap K) :
    ∃ r : ℝ → ℝ≥0, Measurable r ∧
      (surfaceAreaMeasure K.1).restrict
          ((fun t : ℝ ↦ (t : Real.Angle)) '' Ico 0 (Real.pi / 2)) =
        Measure.map (fun t : ℝ ↦ (t : Real.Angle))
          ((volume.restrict (Ico 0 (Real.pi / 2))).withDensity
            (fun t ↦ (r t : ℝ≥0∞))) := by
  have hpi := Real.pi_pos
  have _ : IsFiniteMeasure (surfaceAreaMeasure K.val) :=
    (surfaceAreaMeasure_face_union K.val).1
  have hmeas : AEStronglyMeasurable (fun t ↦ magicDensity (tangentArmLengths K t).2.1)
      (volume.restrict (Icc (0 : ℝ) (Real.pi / 2))) := by
    rw [← Measure.restrict_congr_set Ioc_ae_eq_Icc]
    exact aestronglyMeasurable_magicDensity_tangentArm_fst K
  refine exists_arcDensity_of_domination (surfaceAreaMeasure K.val)
    Real.Angle.continuous_coe.measurable continuous_angleSection.measurable
    measurableSet_Ico Ico_ae_eq_Icc Ico_subset_Icc_self ?_
    (fun t ht ↦ angleSection_coe ⟨by linarith [ht.1], ht.2.le⟩)
    (fun t ↦ magicDensity (tangentArmLengths K t).2.1) hmeas
    (fun t _ ↦ magicDensity_nonneg _)
    (M := (surfaceAreaMeasure K.val).real univ + 1)
    (fun t ht ↦ (magicDensity_le_abs_add_one _).trans
      (by linarith [abs_tangentArm_fst_le K ht]))
    fun E hE hEsub ↦ balancedMaximumCap_surface_domination K hK E hE hEsub
  exact Real.Angle.measurableSet_image_of_subset_Ioc (a := -Real.pi) (b := Real.pi)
    (by linarith) measurableSet_Ico fun t ht ↦ ⟨by linarith [ht.1], by linarith [ht.2]⟩

/-- On the first quarter arc the surface area measure of a balanced maximum cap is the integral
of a real density on the rotation interval which is bounded by the magic density of the positive
tangent arm length. This refines `exists_capDensity_right`, which only records the existence of a
density, by the pointwise bound carried by the limiting inequality
`balancedMaximumCap_surface_domination`. -/
theorem exists_capDensity_right_le_magicDensity (K : RightAngleCapSpace)
    (hK : IsBalancedMaximumCap K) :
    ∃ ρ : ℝ → ℝ, IntegrableOn ρ (Icc 0 (Real.pi / 2)) volume ∧
      (∀ᵐ t ∂volume.restrict (Icc 0 (Real.pi / 2)),
        0 ≤ ρ t ∧ ρ t ≤ magicDensity (tangentArmLengths K t).2.1) ∧
      ∀ E : Set ℝ, MeasurableSet E → E ⊆ Ico 0 (Real.pi / 2) →
        (surfaceAreaMeasure K.val ((fun t : ℝ ↦ (t : Real.Angle)) '' E)).toReal =
          ∫ t in E, ρ t := by
  have hpi := Real.pi_pos
  have _ : IsFiniteMeasure (surfaceAreaMeasure K.val) :=
    (surfaceAreaMeasure_face_union K.val).1
  have hsec : ∀ t ∈ Ico (0 : ℝ) (Real.pi / 2), angleSection (t : Real.Angle) = t :=
    fun t ht ↦ angleSection_coe ⟨by linarith [ht.1], ht.2.le⟩
  set μ : Measure ℝ := Measure.map angleSection ((surfaceAreaMeasure K.val).restrict
    ((fun t : ℝ ↦ (t : Real.Angle)) '' Ico 0 (Real.pi / 2))) with hμdef
  have hμ_apply : ∀ E : Set ℝ, MeasurableSet E →
      μ E = surfaceAreaMeasure K.val
        ((fun t : ℝ ↦ (t : Real.Angle)) '' (E ∩ Ico 0 (Real.pi / 2))) := fun E hE ↦ by
    rw [hμdef, Measure.map_apply continuous_angleSection.measurable hE,
      Measure.restrict_apply (continuous_angleSection.measurable hE),
      preimage_inter_image_eq_image_inter hsec E]
  have _ : IsFiniteMeasure μ := by
    refine ⟨?_⟩
    rw [hμ_apply univ MeasurableSet.univ]
    exact measure_lt_top _ _
  have hμ_compl : μ (Icc (0 : ℝ) (Real.pi / 2))ᶜ = 0 := by
    rw [hμ_apply _ measurableSet_Icc.compl,
      show (Icc (0 : ℝ) (Real.pi / 2))ᶜ ∩ Ico 0 (Real.pi / 2) = ∅ from
        eq_empty_of_subset_empty fun x hx ↦ hx.1 (Ico_subset_Icc_self hx.2),
      Set.image_empty, measure_empty]
  have hmeas : AEStronglyMeasurable (fun t ↦ magicDensity (tangentArmLengths K t).2.1)
      (volume.restrict (Icc (0 : ℝ) (Real.pi / 2))) := by
    rw [← Measure.restrict_congr_set Ioc_ae_eq_Icc]
    exact aestronglyMeasurable_magicDensity_tangentArm_fst K
  have hdom : ∀ E : Set ℝ, MeasurableSet E → E ⊆ Icc 0 (Real.pi / 2) →
      μ E ≤ ENNReal.ofReal (∫ t in E, magicDensity (tangentArmLengths K t).2.1) := by
    intro E hE hEsub
    have hES : E ∩ Ico (0 : ℝ) (Real.pi / 2) =ᵐ[volume] E := by
      have h := Filter.EventuallyEqSet.inter (Filter.EventuallyEq.refl _ E)
        (Ico_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := Real.pi / 2))
      rwa [inter_eq_left.mpr hEsub] at h
    rw [hμ_apply E hE]
    exact (balancedMaximumCap_surface_domination K hK _ (hE.inter measurableSet_Ico)
      inter_subset_right).trans
      (le_of_eq (congrArg ENNReal.ofReal (setIntegral_congr_set hES)))
  obtain ⟨ρ, -, hρint, hρle, hρeq⟩ := exists_density_le_of_domination μ hμ_compl
    (fun t ↦ magicDensity (tangentArmLengths K t).2.1) hmeas (fun t _ ↦ magicDensity_nonneg _)
    (M := (surfaceAreaMeasure K.val).real univ + 1)
    (fun t ht ↦ (magicDensity_le_abs_add_one _).trans
      (by linarith [abs_tangentArm_fst_le K ht])) hdom
  refine ⟨ρ, hρint, hρle, fun E hE hEsub ↦ ?_⟩
  have hEIcc : E ⊆ Icc (0 : ℝ) (Real.pi / 2) := hEsub.trans Ico_subset_Icc_self
  have hEint : Integrable ρ (volume.restrict E) := hρint.mono_set hEIcc
  have hEnn : 0 ≤ᵐ[volume.restrict E] ρ :=
    (ae_restrict_of_ae_restrict_of_subset hEIcc hρle).mono fun t h ↦ h.1
  have hEμ : μ E = surfaceAreaMeasure K.val ((fun t : ℝ ↦ (t : Real.Angle)) '' E) := by
    rw [hμ_apply E hE, inter_eq_left.mpr hEsub]
  rw [← hEμ, hρeq, withDensity_apply _ hE, Measure.restrict_restrict_of_subset hEIcc,
    ← ofReal_integral_eq_lintegral_ofReal hEint hEnn]
  exact ENNReal.toReal_ofReal (integral_nonneg_of_ae hEnn)

/-! ### The mirrored cap and the density on the second arc -/

/-- The mirror image of a balanced maximum right-angle cap is again a balanced maximum cap, and
the surface area measure of the cap is obtained from that of its mirror image by reflecting
normal angles through `a ↦ π - a`. -/
private theorem exists_mirror_balancedMaximumCap (K : RightAngleCapSpace)
    (hK : IsBalancedMaximumCap K) :
    ∃ P : RightAngleCapSpace, IsBalancedMaximumCap P ∧
      ∀ E : Set Real.Angle, MeasurableSet E →
        surfaceAreaMeasure K.val E =
          surfaceAreaMeasure P.val
            ((fun a : Real.Angle ↦ ((Real.pi : ℝ) : Real.Angle) - a) '' E) := by
  obtain ⟨P, hPset, hPbal⟩ := balancedMaximumCap_mirror K hK
  obtain ⟨Q, hQset, -, -, -, -, hQmeas⟩ := cap_mirror_features K
  have hQP : Q = P := Subtype.ext (ConvexBody.ext (by rw [hQset, hPset]))
  have hF : Function.Involutive (fun a : Real.Angle ↦ ((Real.pi : ℝ) : Real.Angle) - a) :=
    fun a ↦ sub_sub_cancel _ _
  refine ⟨P, hPbal, fun E hE ↦ ?_⟩
  have hFEmeas : MeasurableSet
      ((fun a : Real.Angle ↦ ((Real.pi : ℝ) : Real.Angle) - a) '' E) := by
    rw [Set.image_eq_preimage_of_inverse hF hF]
    exact (continuous_const.sub continuous_id).measurable hE
  have himg : (fun a : Real.Angle ↦ ((Real.pi / 2 + Real.pi / 2 : ℝ) : Real.Angle) - a) ''
      ((fun a : Real.Angle ↦ ((Real.pi : ℝ) : Real.Angle) - a) '' E) = E := by
    rw [show ((Real.pi / 2 + Real.pi / 2 : ℝ) : Real.Angle) = ((Real.pi : ℝ) : Real.Angle) from
      by rw [add_halves], Set.image_image, show (fun a : Real.Angle ↦
        ((Real.pi : ℝ) : Real.Angle) - (((Real.pi : ℝ) : Real.Angle) - a)) = fun a ↦ a from
      funext hF, Set.image_id']
  have hkey := hQmeas _ hFEmeas
  rw [hQP, himg] at hkey
  exact hkey.symm

private theorem exists_capDensity_left (K : RightAngleCapSpace)
    (hK : IsBalancedMaximumCap K) :
    ∃ s : ℝ → ℝ≥0, Measurable s ∧
      (surfaceAreaMeasure K.1).restrict
          ((fun t : ℝ ↦ (t : Real.Angle)) '' Ioc (Real.pi / 2) Real.pi) =
        Measure.map (fun t : ℝ ↦ ((t + Real.pi / 2 : ℝ) : Real.Angle))
          ((volume.restrict (Ioc 0 (Real.pi / 2))).withDensity
            (fun t ↦ (s t : ℝ≥0∞))) := by
  obtain ⟨P, hPbal, hPmeas⟩ := exists_mirror_balancedMaximumCap K hK
  have hpi := Real.pi_pos
  have _ : IsFiniteMeasure (surfaceAreaMeasure K.val) :=
    (surfaceAreaMeasure_face_union K.val).1
  have hrefl : Function.Involutive (fun t : ℝ ↦ Real.pi / 2 - t) := fun t ↦ sub_sub_cancel _ _
  have hmp : MeasurePreserving (fun t : ℝ ↦ Real.pi / 2 - t)
      (volume.restrict (Icc (0 : ℝ) (Real.pi / 2)))
      (volume.restrict (Icc (0 : ℝ) (Real.pi / 2))) := by
    have h := (Measure.measurePreserving_sub_left volume (Real.pi / 2)).restrict_preimage
      (measurableSet_Icc (a := (0 : ℝ)) (b := Real.pi / 2))
    have hpre : (fun t : ℝ ↦ Real.pi / 2 - t) ⁻¹' Icc (0 : ℝ) (Real.pi / 2) =
        Icc (0 : ℝ) (Real.pi / 2) := by
      ext x
      simp only [mem_preimage, mem_Icc]
      constructor <;> intro hx <;> exact ⟨by linarith [hx.2], by linarith [hx.1]⟩
    rwa [hpre] at h
  have hmeas : AEStronglyMeasurable (fun u ↦ magicDensity (tangentArmLengths P u).2.1)
      (volume.restrict (Icc (0 : ℝ) (Real.pi / 2))) := by
    rw [← Measure.restrict_congr_set Ioc_ae_eq_Icc]
    exact aestronglyMeasurable_magicDensity_tangentArm_fst P
  have hbound : ∀ t ∈ Icc (0 : ℝ) (Real.pi / 2),
      magicDensity (tangentArmLengths P (Real.pi / 2 - t)).2.1 ≤
        (surfaceAreaMeasure P.val).real univ + 1 := by
    intro t ht
    refine (magicDensity_le_abs_add_one _).trans ?_
    have harm := abs_tangentArm_fst_le P
      (show Real.pi / 2 - t ∈ Icc (0 : ℝ) (Real.pi / 2) from
        ⟨by linarith [ht.2], by linarith [ht.1]⟩)
    linarith
  rw [← image_coe_add_pi_div_two_Ioc]
  refine exists_arcDensity_of_domination (surfaceAreaMeasure K.val)
    (φ := fun t : ℝ ↦ ((t + Real.pi / 2 : ℝ) : Real.Angle))
    (ψ := fun a : Real.Angle ↦ angleSection (a - ((Real.pi / 2 : ℝ) : Real.Angle)))
    (Real.Angle.continuous_coe.comp (continuous_id.add continuous_const)).measurable
    (continuous_angleSection.comp (continuous_id.sub continuous_const)).measurable
    measurableSet_Ioc Ioc_ae_eq_Icc Ioc_subset_Icc_self ?_
    (fun t ht ↦ angleSection_sub_coe ⟨by linarith [ht.1], ht.2⟩)
    (fun t ↦ magicDensity (tangentArmLengths P (Real.pi / 2 - t)).2.1)
    (hmeas.comp_measurePreserving hmp) (fun t _ ↦ magicDensity_nonneg _) hbound ?_
  · rw [image_coe_add_pi_div_two_Ioc]
    exact Real.Angle.measurableSet_image_of_subset_Ioc (a := -Real.pi) (b := Real.pi)
      (by linarith) measurableSet_Ioc fun t ht ↦ ⟨by linarith [ht.1], ht.2⟩
  · intro E hE hEsub
    have hgmeas : MeasurableSet ((fun t : ℝ ↦ Real.pi / 2 - t) '' E) := by
      rw [Set.image_eq_preimage_of_inverse hrefl hrefl]
      exact (measurable_const.sub measurable_id) hE
    have hgsub : (fun t : ℝ ↦ Real.pi / 2 - t) '' E ⊆ Ico 0 (Real.pi / 2) := by
      rintro u ⟨t, ht, rfl⟩
      exact ⟨by linarith [(hEsub ht).2], by linarith [(hEsub ht).1]⟩
    have hEarc : MeasurableSet
        ((fun t : ℝ ↦ ((t + Real.pi / 2 : ℝ) : Real.Angle)) '' E) := by
      rw [show (fun t : ℝ ↦ ((t + Real.pi / 2 : ℝ) : Real.Angle)) =
          (fun u : ℝ ↦ (u : Real.Angle)) ∘ (fun t : ℝ ↦ t + Real.pi / 2) from rfl,
        Set.image_comp]
      refine Real.Angle.measurableSet_image_of_subset_Ioc (a := -Real.pi) (b := Real.pi)
        (by linarith) ?_ ?_
      · rw [Set.image_add_right]
        exact (measurable_id.add_const _) hE
      · rintro u ⟨t, ht, rfl⟩
        exact ⟨by linarith [(hEsub ht).1], by linarith [(hEsub ht).2]⟩
    have hmirror : (fun a : Real.Angle ↦ ((Real.pi : ℝ) : Real.Angle) - a) ''
        ((fun t : ℝ ↦ ((t + Real.pi / 2 : ℝ) : Real.Angle)) '' E) =
        (fun u : ℝ ↦ (u : Real.Angle)) '' ((fun t : ℝ ↦ Real.pi / 2 - t) '' E) := by
      rw [Set.image_image, Set.image_image]
      refine Set.image_congr' fun t ↦ ?_
      show ((Real.pi : ℝ) : Real.Angle) - ((t + Real.pi / 2 : ℝ) : Real.Angle) =
        ((Real.pi / 2 - t : ℝ) : Real.Angle)
      rw [← Real.Angle.coe_sub]
      congr 1
      ring
    calc surfaceAreaMeasure K.val
          ((fun t : ℝ ↦ ((t + Real.pi / 2 : ℝ) : Real.Angle)) '' E)
        = surfaceAreaMeasure P.val ((fun u : ℝ ↦ (u : Real.Angle)) ''
            ((fun t : ℝ ↦ Real.pi / 2 - t) '' E)) := by rw [hPmeas _ hEarc, hmirror]
      _ ≤ ENNReal.ofReal (∫ t in (fun t : ℝ ↦ Real.pi / 2 - t) '' E,
            magicDensity (tangentArmLengths P t).2.1) :=
          balancedMaximumCap_surface_domination P hPbal _ hgmeas hgsub
      _ = ENNReal.ofReal
            (∫ t in E, magicDensity (tangentArmLengths P (Real.pi / 2 - t)).2.1) :=
          congrArg ENNReal.ofReal
            ((Measure.measurePreserving_sub_left volume (Real.pi / 2)).setIntegral_image_emb
              (measurableEmbedding_subLeft _) _ E)

/-! ### Uniqueness of the densities -/

/-- Two measurable weights on `S` whose pushforwards along `φ` agree are almost everywhere
equal, provided `φ` has a measurable left inverse on `S`. -/
private theorem ae_eq_of_map_withDensity_eq {S : Set ℝ} (hS : MeasurableSet S)
    {φ : ℝ → Real.Angle} (hφ : Measurable φ) {ψ : Real.Angle → ℝ} (hψ : Measurable ψ)
    (hsec : ∀ t ∈ S, ψ (φ t) = t) {w₁ w₂ : ℝ → ℝ≥0}
    (h₁ : Measurable w₁) (h₂ : Measurable w₂)
    (h : Measure.map φ ((volume.restrict S).withDensity (fun t ↦ (w₁ t : ℝ≥0∞))) =
      Measure.map φ ((volume.restrict S).withDensity (fun t ↦ (w₂ t : ℝ≥0∞)))) :
    w₁ =ᵐ[volume.restrict S] w₂ := by
  have key : ∀ w : ℝ → ℝ≥0,
      Measure.map ψ (Measure.map φ ((volume.restrict S).withDensity
        (fun t ↦ (w t : ℝ≥0∞)))) =
      (volume.restrict S).withDensity (fun t ↦ (w t : ℝ≥0∞)) := by
    intro w
    refine Measure.map_map_of_ae_leftInverse hφ hψ ?_
    filter_upwards [(withDensity_absolutelyContinuous (volume.restrict S)
      (fun t ↦ (w t : ℝ≥0∞))).ae_le (ae_restrict_mem hS)] with t ht
    exact hsec t ht
  have hν : (volume.restrict S).withDensity (fun t ↦ (w₁ t : ℝ≥0∞)) =
      (volume.restrict S).withDensity (fun t ↦ (w₂ t : ℝ≥0∞)) := by
    rw [← key w₁, ← key w₂, h]
  filter_upwards [(withDensity_eq_iff_of_sigmaFinite
    h₁.coe_nnreal_ennreal.aemeasurable h₂.coe_nnreal_ennreal.aemeasurable).mp hν] with t ht
  exact ENNReal.coe_inj.mp ht

/-- A right-angle cap determines its two surface densities up to Lebesgue-null sets: any two
pairs of densities of the same cap agree almost everywhere on `[0, π / 2]`. -/
theorem HasCapDensities.ae_eq {K : RightAngleCapSpace} {r s r' s' : ℝ → ℝ≥0}
    (h : HasCapDensities K r s) (h' : HasCapDensities K r' s') :
    (r =ᵐ[volume.restrict (Set.Icc 0 (Real.pi / 2))] r') ∧
    (s =ᵐ[volume.restrict (Set.Icc 0 (Real.pi / 2))] s') := by
  have hpi := Real.pi_pos
  refine ⟨?_, ?_⟩
  · rw [← Measure.restrict_congr_set (Ico_ae_eq_Icc (a := (0 : ℝ)) (b := Real.pi / 2))]
    exact ae_eq_of_map_withDensity_eq measurableSet_Ico
      Real.Angle.continuous_coe.measurable continuous_angleSection.measurable
      (fun t ht ↦ angleSection_coe ⟨by linarith [ht.1], ht.2.le⟩)
      h.1 h'.1 (h.2.2.1.symm.trans h'.2.2.1)
  · rw [← Measure.restrict_congr_set (Ioc_ae_eq_Icc (a := (0 : ℝ)) (b := Real.pi / 2))]
    exact ae_eq_of_map_withDensity_eq measurableSet_Ioc
      (φ := fun t : ℝ ↦ ((t + Real.pi / 2 : ℝ) : Real.Angle))
      (ψ := fun a : Real.Angle ↦ angleSection (a - ((Real.pi / 2 : ℝ) : Real.Angle)))
      (Real.Angle.continuous_coe.comp (continuous_id.add continuous_const)).measurable
      (continuous_angleSection.comp (continuous_id.sub continuous_const)).measurable
      (fun t ht ↦ angleSection_sub_coe ⟨by linarith [ht.1], ht.2⟩)
      h.2.1 h'.2.1 (h.2.2.2.symm.trans h'.2.2.2)

theorem balancedMaximumCap_hasDensities (K : RightAngleCapSpace)
    (hK : IsBalancedMaximumCap K) :
    ∃ r s : ℝ → NNReal, HasCapDensities K r s ∧
      ∀ r' s', HasCapDensities K r' s' →
        (r =ᵐ[volume.restrict (Set.Icc 0 (Real.pi / 2))] r') ∧
        (s =ᵐ[volume.restrict (Set.Icc 0 (Real.pi / 2))] s') := by
  obtain ⟨r, hrmeas, hr⟩ := exists_capDensity_right K hK
  obtain ⟨s, hsmeas, hs⟩ := exists_capDensity_left K hK
  have h : HasCapDensities K r s := ⟨hrmeas, hsmeas, hr, hs⟩
  exact ⟨r, s, h, fun _ _ h' ↦ h.ae_eq h'⟩

end MovingSofa

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
# Minkowski interpolation of right-angle caps

The cap conditions of `IsCap (π / 2)` and the injectivity condition of
`SatisfiesInjectivityCondition` are preserved by the Minkowski interpolation
`convexBodyCombination t K L = (1 - t) • K + t • L` of two right-angle caps.  Each statement
about the interpolation is phrased for an arbitrary cap whose underlying convex body is that
interpolation, so that it applies both to the cap produced by `isCap_convexBodyCombination`
and to an interpolated cap obtained by choice.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal Pointwise unitInterval

namespace MovingSofa

/-- Lowering a point of an interpolated right-angle cap onto the base line keeps it inside,
because the same projection can be applied to both summands. -/
theorem base_projection_mem_convexBodyCombination (t : I) (K L : CapSpace (Real.pi / 2))
    {q : Point} (hq : q ∈ (convexBodyCombination t K.val L.val : Set Point)) :
    q - q 1 • normalVector ((Real.pi / 2 : ℝ) : Real.Angle) ∈
      (convexBodyCombination t K.val L.val : Set Point) := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_convexBodyCombination_iff t K.val L.val q).1 hq
  refine (mem_convexBodyCombination_iff t K.val L.val _).2
    ⟨_, K.base_projection_mem ha, _, L.base_projection_mem hb, ?_⟩
  have hcoord : ((1 - (t : ℝ)) • a + (t : ℝ) • b) 1 =
      (1 - (t : ℝ)) * a 1 + (t : ℝ) * b 1 := by
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  rw [hcoord]
  module

/-- Right-angle caps are closed under Minkowski interpolation. -/
theorem isCap_convexBodyCombination (t : I) (K L : RightAngleCapSpace) :
    IsCap (Real.pi / 2) (convexBodyCombination t K.val L.val) := by
  have hsup := supportValue_convexBodyCombination t K.val L.val
  have hbase : supportValue (convexBodyCombination t K.val L.val)
      ((3 * Real.pi / 2 : ℝ) : Real.Angle) = 0 := by
    rw [hsup, K.property.2.2.2.2.2.1, L.property.2.2.2.2.2.1]; ring
  refine ⟨by positivity, le_rfl, ?_, ?_, ?_, hbase,
    hasHalfPlaneRepresentation_of_base_projection _ hbase
      (fun q hq ↦ base_projection_mem_convexBodyCombination t K L hq)⟩
  · rw [hsup, K.property.2.2.1, L.property.2.2.1]; ring
  · rw [hsup, K.property.2.2.2.1, L.property.2.2.2.1]; ring
  · rw [hsup, K.property.2.2.2.2.1, L.property.2.2.2.2.1]; ring

/-- An interpolated right-angle cap carries the interpolated surface densities: its surface
measure is the interpolation of the two surface measures, and pushing a weighted measure
forward is linear in the weight. -/
theorem hasCapDensities_of_eq_convexBodyCombination {t : I} {K L M : RightAngleCapSpace}
    (hM : (M.val : ConvexBody Point) = convexBodyCombination t K.val L.val)
    {r₁ s₁ r₂ s₂ : ℝ → ℝ≥0} (hK : HasCapDensities K r₁ s₁) (hL : HasCapDensities L r₂ s₂) :
    HasCapDensities M (fun x ↦ (1 - (t : ℝ)).toNNReal * r₁ x + (t : ℝ).toNNReal * r₂ x)
      (fun x ↦ (1 - (t : ℝ)).toNNReal * s₁ x + (t : ℝ).toNNReal * s₂ x) := by
  have hmeasure : surfaceAreaMeasure M.val =
      ENNReal.ofReal (1 - (t : ℝ)) • surfaceAreaMeasure K.val +
        ENNReal.ofReal (t : ℝ) • surfaceAreaMeasure L.val := by
    rw [hM]; exact surfaceAreaMeasure_convexBodyCombination t K.val L.val
  refine ⟨(measurable_const.mul hK.1).add (measurable_const.mul hL.1),
    (measurable_const.mul hK.2.1).add (measurable_const.mul hL.2.1), ?_, ?_⟩
  · rw [hmeasure, Measure.restrict_add, Measure.restrict_smul, Measure.restrict_smul,
      hK.2.2.1, hL.2.2.1]
    exact (Measure.map_withDensity_eq_smul_add_smul _ Real.Angle.continuous_coe.measurable _ _
      hK.1.coe_nnreal_ennreal hL.1.coe_nnreal_ennreal (fun x ↦ by simp [ENNReal.ofReal])).symm
  · rw [hmeasure, Measure.restrict_add, Measure.restrict_smul, Measure.restrict_smul,
      hK.2.2.2, hL.2.2.2]
    exact (Measure.map_withDensity_eq_smul_add_smul _
      (Real.Angle.continuous_coe.comp (continuous_id.add continuous_const)).measurable _ _
      hK.2.1.coe_nnreal_ennreal hL.2.1.coe_nnreal_ennreal
      (fun x ↦ by simp [ENNReal.ofReal])).symm

/-- The inner corner of an interpolated cap is the interpolation of the two inner corners. -/
theorem capInnerCorner_of_eq_convexBodyCombination {t : I} {K L M : RightAngleCapSpace}
    (hM : (M.val : ConvexBody Point) = convexBodyCombination t K.val L.val) (x : ℝ) :
    capInnerCorner M x =
      (1 - (t : ℝ)) • capInnerCorner K x + (t : ℝ) • capInnerCorner L x := by
  simp only [capInnerCorner, (rotatingHallwayParts_formulas _ _).2.1, hM,
    supportValue_convexBodyCombination]
  module

/-- The injectivity condition is inherited by Minkowski interpolations of right-angle caps: the
inner corner interpolates, so its two frame velocity components are the same combinations of
the original ones, and a combination with nonnegative weights summing to one preserves their
strict signs even at the two degenerate weights. -/
theorem satisfiesInjectivityCondition_of_eq_convexBodyCombination {t : I}
    {K L M : RightAngleCapSpace}
    (hM : (M.val : ConvexBody Point) = convexBodyCombination t K.val L.val)
    (hK : SatisfiesInjectivityCondition K) (hL : SatisfiesInjectivityCondition L) :
    SatisfiesInjectivityCondition M := by
  obtain ⟨⟨r₁, s₁, hd₁, -⟩, hC₁, hsign₁⟩ := hK
  obtain ⟨⟨r₂, s₂, hd₂, -⟩, hC₂, hsign₂⟩ := hL
  have hcornerfun : capInnerCorner M =
      fun x ↦ (1 - (t : ℝ)) • capInnerCorner K x + (t : ℝ) • capInnerCorner L x :=
    funext (capInnerCorner_of_eq_convexBodyCombination hM)
  have hpi : (0 : ℝ) < Real.pi / 2 := by positivity
  have ht0 : (0 : ℝ) ≤ (t : ℝ) := t.2.1
  have ht1 : (0 : ℝ) ≤ 1 - (t : ℝ) := sub_nonneg.mpr t.2.2
  -- A combination of two negative quantities with weights summing to one is negative.
  have hneg : ∀ a b : ℝ, a < 0 → b < 0 → (1 - (t : ℝ)) * a + (t : ℝ) * b < 0 := by
    intro a b ha hb
    rcases eq_or_lt_of_le ht0 with h | h
    · rw [← h]; simpa using ha
    · nlinarith [mul_nonpos_of_nonneg_of_nonpos ht1 ha.le, mul_neg_of_pos_of_neg h hb]
  have hpos : ∀ a b : ℝ, 0 < a → 0 < b → 0 < (1 - (t : ℝ)) * a + (t : ℝ) * b := by
    intro a b ha hb
    have := hneg (-a) (-b) (by linarith) (by linarith)
    linarith
  -- Density uniqueness needs no proof here: it holds for every right-angle cap.
  have hdens := hasCapDensities_of_eq_convexBodyCombination hM hd₁ hd₂
  refine ⟨⟨_, _, hdens, fun _ _ h' ↦ hdens.ae_eq h'⟩, ?_, ?_⟩
  · rw [hcornerfun]
    exact (hC₁.const_smul _).add (hC₂.const_smul _)
  · intro x hx
    have hxmem : x ∈ Set.Icc (0 : ℝ) (Real.pi / 2) := ⟨hx.1.le, hx.2.le⟩
    have hdK := ((hC₁.differentiableOn one_ne_zero) x hxmem).hasDerivWithinAt
    have hdL := ((hC₂.differentiableOn one_ne_zero) x hxmem).hasDerivWithinAt
    have hdM : HasDerivWithinAt (capInnerCorner M)
        ((1 - (t : ℝ)) • derivWithin (capInnerCorner K) (Set.Icc 0 (Real.pi / 2)) x +
          (t : ℝ) • derivWithin (capInnerCorner L) (Set.Icc 0 (Real.pi / 2)) x)
        (Set.Icc 0 (Real.pi / 2)) x := by
      rw [hcornerfun]
      exact (hdK.const_smul (1 - (t : ℝ))).add (hdL.const_smul (t : ℝ))
    rw [hdM.derivWithin (uniqueDiffOn_Icc hpi x hxmem), inner_add_left, inner_add_left,
      real_inner_smul_left, real_inner_smul_left, real_inner_smul_left, real_inner_smul_left]
    exact ⟨hneg _ _ (hsign₁ x hx).1 (hsign₂ x hx).1,
      hpos _ _ (hsign₁ x hx).2 (hsign₂ x hx).2⟩

end MovingSofa

end

end

end
