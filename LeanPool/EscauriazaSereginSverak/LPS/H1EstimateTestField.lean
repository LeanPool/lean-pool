/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.H1EstimateSolenoidalDense
public import LeanPool.EscauriazaSereginSverak.PartV.SerrinSlab
public import LeanPool.CaffarelliKohnNirenberg.Foundation.ParabolicMeasure
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeTestFunction
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpatialPartial
public import LeanPool.CaffarelliKohnNirenberg.Statements.TimePartial

/-!
# Separated space-time test fields

A product `χ(t) ψ(x)` of a smooth compactly supported time cutoff and a smooth
compactly supported spatial field is a space-time test field on any slab
containing the support of `χ`. Its partial derivatives split accordingly
(`lem:lps-H1-estimate`).
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- A square-integrable field on the slab is square integrable on the product
space with the product slab measure. -/
theorem lps_memLp_slab_to_prod {a b : ℝ} {E : Type} [NormedAddCommGroup E]
    {F : ParabolicPoint → E} {p : ℝ≥0∞}
    (hF : MemLp F p (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo a b)))) :
    MemLp (fun q : Vec3 × ℝ => F (parabolicHomeomorph.symm q)) p
      ((volume : Measure Vec3).prod (volume.restrict (Ioo a b))) := by
  have hSmeas : MeasurableSet (spaceTimeSet (Set.univ : Set Vec3) (Ioo a b)) :=
    MeasurableSet.univ.prod measurableSet_Ioo
  have hpre : parabolicHomeomorph.symm ⁻¹' spaceTimeSet (Set.univ : Set Vec3) (Ioo a b) =
      (Set.univ : Set Vec3) ×ˢ Ioo a b := by
    ext z
    rfl
  have hmp := CKN.parabolicHomeomorphSymm_measurePreserving.restrict_preimage hSmeas
  rw [hpre] at hmp
  have hslab : (volume : Measure (Vec3 × ℝ)).restrict ((Set.univ : Set Vec3) ×ˢ Ioo a b) =
      (volume : Measure Vec3).prod (volume.restrict (Ioo a b)) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  rw [← hslab]
  exact hF.comp_measurePreserving hmp

/-- The slab integral of a field equals the product-space integral of its
coordinate representative. -/
theorem lps_setIntegral_slab_to_prod {a b : ℝ} (F : ParabolicPoint → ℝ) :
    (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo a b), F z) =
      ∫ q : Vec3 × ℝ, F (parabolicHomeomorph.symm q)
        ∂((volume : Measure Vec3).prod (volume.restrict (Ioo a b))) := by
  rw [CKN.setIntegral_parabolic_to_product]
  have hslab : (volume : Measure (Vec3 × ℝ)).restrict ((Set.univ : Set Vec3) ×ˢ Ioo a b) =
      (volume : Measure Vec3).prod (volume.restrict (Ioo a b)) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  rw [hslab]

/-- The support of a separated field lies in the product of the supports. -/
theorem lps_separated_tsupport_subset {χ : ℝ → ℝ} {f : Vec3 → ℝ} :
    tsupport (fun z : Vec3 × ℝ => χ z.2 * f z.1) ⊆ tsupport f ×ˢ tsupport χ := by
  refine closure_minimal ?_ ((isClosed_tsupport f).prod (isClosed_tsupport χ))
  intro z hz
  have hz' : χ z.2 * f z.1 ≠ 0 := hz
  exact ⟨subset_tsupport _ (right_ne_zero_of_mul hz'), subset_tsupport _ (left_ne_zero_of_mul hz')⟩

/-- The scalar space-time test function `χ(t) f(x)`. -/
theorem lps_separated_test_mem {a b : ℝ} {χ : ℝ → ℝ} {f : Vec3 → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ) (hχs : tsupport χ ⊆ Ioo a b)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f) :
    (fun z : Vec3 × ℝ => χ z.2 * f z.1) ∈
      spaceTimeTestFunction (V := ℝ) (Set.univ : Set Vec3) (Ioo a b) := by
  refine ⟨(hχ.comp contDiff_snd).mul (hf.comp contDiff_fst), ?_, ?_⟩
  · exact IsCompact.of_isClosed_subset (hfc.prod hχc) (isClosed_tsupport _)
      lps_separated_tsupport_subset
  · intro z hz
    have := lps_separated_tsupport_subset (f := f) (χ := χ) hz
    exact ⟨mem_univ _, hχs this.2⟩

/-- The time derivative of a separated test function. -/
theorem lps_separated_timePartial {χ : ℝ → ℝ} {f : Vec3 → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (z : ParabolicPoint) :
    timePartial (fun y : ParabolicPoint => χ y.2 * f y.1) z = deriv χ z.2 * f z.1 := by
  unfold timePartial
  have hd : DifferentiableAt ℝ χ z.2 := hχ.differentiable (by simp) z.2
  change (fderiv ℝ (fun s : ℝ => χ s * f z.1) z.2) 1 = _
  rw [fderiv_mul_const hd]
  simp [mul_comm]

/-- The spatial derivative of a separated test function. -/
theorem lps_separated_spatialPartial {χ : ℝ → ℝ} {f : Vec3 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (j : Fin 3) (z : ParabolicPoint) :
    spatialPartial (fun y : ParabolicPoint => χ y.2 * f y.1) j z =
      χ z.2 * spatialDeriv f j z.1 := by
  unfold spatialPartial spatialDeriv
  have hd : DifferentiableAt ℝ f z.1 := hf.differentiable (by simp) z.1
  change (fderiv ℝ (fun x : Vec3 => χ z.2 * f x) z.1) (basisVec j) = _
  rw [fderiv_const_mul hd]
  simp

end ESS

end
