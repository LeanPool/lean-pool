/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Setting.ScalingInvariance
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Topology

/-!
# The parabolic rescaling as a change of variables

The parabolic rescaling `(y, s) ↦ (x₀ + μ y, t₀ + μ² s)` is a homeomorphism of space-time whose
Jacobian is the constant `μ⁵`. This file records what is needed to move a statement proved on the
unit cylinder to a statement on the cylinder `B(x₀, μ) × (t₀ - μ², t₀]`: the preimage of a
parabolic cylinder, the change of variables for lower Lebesgue integrals, and the transport of an
almost-everywhere statement. A last lemma assembles almost-everywhere bounds on a countable family
of sets into one bound on a set that the family covers.
-/

public section

open MeasureTheory Set
open scoped ENNReal
open CKN.Foundation.Parabolic CKN

noncomputable section

namespace CIV

/-- The parabolic rescaling, read as a homeomorphism of the product `Vec3 × ℝ`. -/
private def scalingHomeomorph (μ : ℝ) (hμ : 0 < μ) (z₀ : ParabolicPoint) :
    (Vec3 × ℝ) ≃ₜ (Vec3 × ℝ) :=
  Homeomorph.prodCongr
    ((Homeomorph.smulOfNeZero μ hμ.ne').trans (Homeomorph.addLeft z₀.1))
    ((Homeomorph.smulOfNeZero (μ ^ 2) (pow_pos hμ 2).ne').trans (Homeomorph.addLeft z₀.2))

private theorem scalingHomeomorph_eq (μ : ℝ) (hμ : 0 < μ) (z₀ : ParabolicPoint) :
    ⇑(scalingHomeomorph μ hμ z₀) = scalingParabolic μ z₀ := by
  funext z
  rfl

/-- The parabolic rescaling is a measurable embedding. -/
theorem measurableEmbedding_scalingParabolic {μ : ℝ} (hμ : 0 < μ) (z₀ : ParabolicPoint) :
    MeasurableEmbedding (scalingParabolic μ z₀) := by
  rw [← scalingHomeomorph_eq μ hμ z₀]
  exact (scalingHomeomorph μ hμ z₀).measurableEmbedding

/-- The parabolic rescaling is measurable. -/
theorem measurable_scalingParabolic {μ : ℝ} (hμ : 0 < μ) (z₀ : ParabolicPoint) :
    Measurable (scalingParabolic μ z₀) :=
  (measurableEmbedding_scalingParabolic hμ z₀).measurable

/-- Membership in a parabolic cylinder, read on the components of a space-time point. -/
theorem mem_parabolicCylinder_iff (x : Vec3) (t r : ℝ) (z : ParabolicPoint) :
    z ∈ parabolicCylinder x t r ↔
      vec3EuclideanNorm (z.1 - x) < r ∧ t - r ^ 2 < z.2 ∧ z.2 ≤ t := Iff.rfl

/-- A parabolic cylinder is measurable. -/
theorem measurableSet_parabolicCylinder (x : Vec3) (t r : ℝ) :
    MeasurableSet (parabolicCylinder x t r) :=
  (isOpen_vec3Ball x r).measurableSet.prod measurableSet_Ioc

/-- The rescaling carries the cylinder of radius `r` at the origin onto the cylinder of radius
`μ r` at `z₀`. -/
theorem preimage_scalingParabolic_parabolicCylinder {μ : ℝ} (hμ : 0 < μ)
    (z₀ : ParabolicPoint) (r : ℝ) :
    scalingParabolic μ z₀ ⁻¹' parabolicCylinder z₀.1 z₀.2 (μ * r) =
      parabolicCylinder 0 0 r := by
  have hμ2 : (0 : ℝ) < μ ^ 2 := pow_pos hμ 2
  ext z
  have hfst : (scalingParabolic μ z₀ z).1 - z₀.1 = μ • z.1 := by
    change z₀.1 + μ • z.1 - z₀.1 = μ • z.1
    rw [add_sub_cancel_left]
  have hsnd : (scalingParabolic μ z₀ z).2 = z₀.2 + μ ^ 2 * z.2 := rfl
  rw [Set.mem_preimage, mem_parabolicCylinder_iff, mem_parabolicCylinder_iff, hfst, hsnd,
    vec3EuclideanNorm_smul, abs_of_pos hμ, sub_zero]
  constructor
  · rintro ⟨ha, hb, hc⟩
    refine ⟨lt_of_mul_lt_mul_left ha hμ.le, ?_, ?_⟩
    · have hb0 : μ ^ 2 * (0 - r ^ 2) < μ ^ 2 * z.2 := by linarith only [hb]
      exact lt_of_mul_lt_mul_left hb0 hμ2.le
    · have hc0 : μ ^ 2 * z.2 ≤ μ ^ 2 * 0 := by linarith only [hc]
      exact le_of_mul_le_mul_left hc0 hμ2
  · rintro ⟨ha, hb, hc⟩
    refine ⟨mul_lt_mul_of_pos_left ha hμ, ?_, ?_⟩
    · have hb0 : μ ^ 2 * (0 - r ^ 2) < μ ^ 2 * z.2 := mul_lt_mul_of_pos_left hb hμ2
      linarith only [hb0]
    · have hc0 : μ ^ 2 * z.2 ≤ μ ^ 2 * 0 := mul_le_mul_of_nonneg_left hc hμ2.le
      linarith only [hc0]

/-- The rescaling pushes the measure restricted to a preimage forward to a multiple of the
measure restricted to the set. -/
theorem map_scalingParabolic_restrict_preimage {μ : ℝ} (hμ : 0 < μ) (z₀ : ParabolicPoint)
    {S : Set ParabolicPoint} (hS : MeasurableSet S) :
    Measure.map (scalingParabolic μ z₀)
        (volume.restrict (scalingParabolic μ z₀ ⁻¹' S)) =
      ENNReal.ofReal (μ⁻¹ ^ 5) • volume.restrict S := by
  have h := Measure.restrict_map (μ := (volume : Measure ParabolicPoint))
    (measurable_scalingParabolic hμ z₀) hS
  rw [← h, map_scalingParabolic μ hμ z₀, Measure.restrict_smul]

/-- Change of variables for a lower Lebesgue integral along the parabolic rescaling: no
measurability of the integrand is needed, because the rescaling is a measurable embedding. -/
theorem setLIntegral_comp_scalingParabolic {μ : ℝ} (hμ : 0 < μ) (z₀ : ParabolicPoint)
    {S : Set ParabolicPoint} (hS : MeasurableSet S) (F : ParabolicPoint → ℝ≥0∞) :
    ∫⁻ z in scalingParabolic μ z₀ ⁻¹' S, F (scalingParabolic μ z₀ z) =
      ENNReal.ofReal (μ⁻¹ ^ 5) * ∫⁻ z in S, F z := by
  have h := (measurableEmbedding_scalingParabolic hμ z₀).lintegral_map
    (μ := volume.restrict (scalingParabolic μ z₀ ⁻¹' S)) F
  rw [map_scalingParabolic_restrict_preimage hμ z₀ hS, lintegral_smul_measure] at h
  exact h.symm

/-- An almost-everywhere statement on the preimage of a set transports to the set itself. -/
theorem ae_restrict_of_ae_restrict_comp_scalingParabolic {μ : ℝ} (hμ : 0 < μ)
    (z₀ : ParabolicPoint) {S : Set ParabolicPoint} (hS : MeasurableSet S)
    {P : ParabolicPoint → Prop}
    (h : ∀ᵐ z ∂(volume.restrict (scalingParabolic μ z₀ ⁻¹' S)),
      P (scalingParabolic μ z₀ z)) :
    ∀ᵐ z ∂(volume.restrict S), P z := by
  have hc : ENNReal.ofReal (μ⁻¹ ^ 5) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    positivity
  have h' := (measurableEmbedding_scalingParabolic hμ z₀).ae_map_iff.2 h
  rw [map_scalingParabolic_restrict_preimage hμ z₀ hS] at h'
  exact (Measure.ae_ennreal_smul_measure_iff hc).1 h'

/-- Almost-everywhere bounds on a countable family of measurable sets give an
almost-everywhere bound on any measurable set the family covers. -/
theorem ae_restrict_of_countable_cover {α : Type*} [MeasurableSpace α] {m : Measure α}
    {ι : Type*} {J : Set ι} (hJ : J.Countable) {A : ι → Set α} {U : Set α}
    (hU : MeasurableSet U) (hA : ∀ i ∈ J, MeasurableSet (A i))
    (hcover : U ⊆ ⋃ i ∈ J, A i) {P : α → Prop}
    (h : ∀ i ∈ J, ∀ᵐ z ∂(m.restrict (A i)), P z) :
    ∀ᵐ z ∂(m.restrict U), P z := by
  rw [ae_iff, Measure.restrict_apply' hU]
  refine measure_mono_null (t := ⋃ i ∈ J, {z | ¬ P z} ∩ A i) ?_ ?_
  · rintro z ⟨hz, hzU⟩
    obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.1 (hcover hzU)
    exact mem_iUnion₂.2 ⟨i, hi, hz, hzi⟩
  · rw [measure_biUnion_null_iff hJ]
    intro i hi
    have hai := h i hi
    rw [ae_iff, Measure.restrict_apply' (hA i hi)] at hai
    exact hai

end CIV
