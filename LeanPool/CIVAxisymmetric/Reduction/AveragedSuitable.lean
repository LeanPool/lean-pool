/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Setting.RotationLemmas
public import LeanPool.CIVAxisymmetric.Setting.AngularMeanSmooth
public import LeanPool.CIVAxisymmetric.Statements.GlobalEnergyClass
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Averaged Suitable

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open MeasureTheory Set Matrix
open CKN.Foundation.Parabolic CKN
open scoped ENNReal

noncomputable section

namespace CIV

/-- Lebesgue measure on `ParabolicPoint` is `σ`-finite: it is (definitionally) the product
measure on `Vec3 × ℝ`, so this transfers the standard instance across the type alias.
The `private` modifier hides only the *name* of this declaration outside this file; the
registration itself is global, so typeclass synthesis still sees it in every module that
imports this one, `import CIV` included. Only this file's own Tonelli argument
(`lintegral_angularMeanScalar_rpow_lt_top`) makes use of it. -/
@[expose] private instance : SFinite (volume : Measure ParabolicPoint) :=
  inferInstanceAs (SFinite (volume : Measure (Vec3 × ℝ)))

/-- The matrix of the rotation `rotZ φ` in the standard basis. -/
@[expose] private def rotZMatrix (φ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![Real.cos φ, -Real.sin φ, 0; Real.sin φ, Real.cos φ, 0; 0, 0, 1]

private theorem rotZMatrix_mulVec (φ : ℝ) (x : Vec3) : rotZMatrix φ *ᵥ x = rotZ φ x := by
  funext i
  fin_cases i <;>
    simp [rotZMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three, rotZ, sub_eq_add_neg]

private theorem det_rotZMatrix (φ : ℝ) : (rotZMatrix φ).det = 1 := by
  simp [rotZMatrix, Matrix.det_fin_three]
  linear_combination Real.cos_sq_add_sin_sq φ

/-- The rotation `rotZ φ` preserves Lebesgue measure on `Vec3`: it is the linear map with
matrix `!![cos φ, -sin φ, 0; sin φ, cos φ, 0; 0, 0, 1]`, whose determinant is `1`. -/
theorem measurePreserving_rotZ (φ : ℝ) : MeasurePreserving (rotZ φ) volume volume := by
  have hdet : (rotZMatrix φ).det ≠ 0 := by rw [det_rotZMatrix]; norm_num
  have hmap := Real.map_matrix_volume_pi_eq_smul_volume_pi (ι := Fin 3) hdet
  rw [det_rotZMatrix] at hmap
  simp only [abs_one, inv_one, ENNReal.ofReal_one, one_smul] at hmap
  have hfun : (Matrix.toLin' (rotZMatrix φ) : Vec3 → Vec3) = rotZ φ := by
    funext x
    rw [Matrix.toLin'_apply]
    exact rotZMatrix_mulVec φ x
  rw [hfun] at hmap
  exact ⟨(continuous_rotZ φ).measurable, hmap⟩

/-- The map `z ↦ (rotZ φ z.1, z.2)` preserves Lebesgue measure on `ParabolicPoint`. -/
theorem measurePreserving_rotZ_prod (φ : ℝ) :
    MeasurePreserving (fun z : ParabolicPoint => (rotZ φ z.1, z.2)) volume volume := by
  have h := (measurePreserving_rotZ φ).prod (MeasurePreserving.id (volume : Measure ℝ))
  have hfun : (Prod.map (rotZ φ) (id : ℝ → ℝ)) = fun z : ParabolicPoint => (rotZ φ z.1, z.2) := by
    funext z
    rfl
  rwa [hfun] at h

/-- The map `z ↦ (rotZ φ z.1, z.2)` preserves Lebesgue measure restricted to the unit
cylinder, which is invariant under every rotation about the axis. -/
theorem measurePreserving_rotZ_unitCylinder (φ : ℝ) :
    MeasurePreserving (fun z : ParabolicPoint => (rotZ φ z.1, z.2))
      (volume.restrict unitCylinder) (volume.restrict unitCylinder) := by
  have hpre : (fun z : ParabolicPoint => (rotZ φ z.1, z.2)) ⁻¹' unitCylinder = unitCylinder := by
    ext z
    exact rotZ_mem_unitCylinder_iff φ z.1 z.2
  have h := (measurePreserving_rotZ_prod φ).restrict_preimage isOpen_unitCylinder_prod.measurableSet
  rwa [hpre] at h

/-- The joint map `(z, φ) ↦ (rotZ (-φ) z.1, z.2)` is measurable. -/
private theorem measurable_rotate_pair :
    Measurable (fun q : ParabolicPoint × ℝ => (rotZ (-q.2) q.1.1, q.1.2)) := by
  have hrot : Continuous (fun p : ℝ × Vec3 => rotZ p.1 p.2) := continuous_rotZ_uncurry
  fun_prop

/-- For every measurable target set `s` of measure zero, the preimage of `s` under the joint
rotation map has product measure zero, since each fixed-angle slice of the map is exactly
measure preserving on the unit cylinder. -/
private theorem rotate_pair_preimage_null {s : Set ParabolicPoint} (hs : MeasurableSet s)
    (hs0 : volume.restrict unitCylinder s = 0) :
    ((volume.restrict unitCylinder).prod (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))
      ((fun q : ParabolicPoint × ℝ => (rotZ (-q.2) q.1.1, q.1.2)) ⁻¹' s) = 0 := by
  rw [Measure.prod_apply_symm (measurable_rotate_pair hs)]
  have hzero : ∀ φ : ℝ, volume.restrict unitCylinder
      ((fun z : ParabolicPoint => (z, φ)) ⁻¹' ((fun q : ParabolicPoint × ℝ =>
        (rotZ (-q.2) q.1.1, q.1.2)) ⁻¹' s)) = 0 := by
    intro φ
    have heq : (fun z : ParabolicPoint => (z, φ)) ⁻¹' ((fun q : ParabolicPoint × ℝ =>
        (rotZ (-q.2) q.1.1, q.1.2)) ⁻¹' s) =
        (fun z : ParabolicPoint => (rotZ (-φ) z.1, z.2)) ⁻¹' s := rfl
    rw [heq]
    rw [(measurePreserving_rotZ_unitCylinder (-φ)).measure_preimage hs.nullMeasurableSet]
    exact hs0
  simp [hzero]

/-- The map `(z, φ) ↦ (rotZ (-φ) z.1, z.2)` is quasi-measure-preserving from the product of the
unit cylinder with an angle interval to the unit cylinder: a set of measure zero in the target
has preimage of measure zero, since each fixed-angle slice is exactly measure preserving on the
unit cylinder. -/
theorem quasiMeasurePreserving_rotZ_prod :
    Measure.QuasiMeasurePreserving (fun q : ParabolicPoint × ℝ => (rotZ (-q.2) q.1.1, q.1.2))
      ((volume.restrict unitCylinder).prod (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))))
      (volume.restrict unitCylinder) :=
  ⟨measurable_rotate_pair, Measure.AbsolutelyContinuous.mk fun s hs hs0 => by
    rw [Measure.map_apply measurable_rotate_pair hs]
    exact rotate_pair_preimage_null hs hs0⟩

/-- The interval integral defining the angular mean of a scalar field agrees, on the unit
cylinder, with the corresponding integral over `Ioc 0 (2π)`: both are the same Bochner
integral, since `0 ≤ 2π`. -/
private theorem angularMeanScalar_eq_integral_Ioc (g : ParabolicPoint → ℝ) (z : ParabolicPoint) :
    angularMeanScalar g z =
      (2 * Real.pi)⁻¹ • ∫ φ in Ioc (0 : ℝ) (2 * Real.pi), g (rotZ (-φ) z.1, z.2) := by
  rw [angularMeanScalar, intervalIntegral.integral_of_le Real.two_pi_pos.le]

/-- The angular mean of an almost-everywhere strongly measurable scalar field on the unit
cylinder is again almost-everywhere strongly measurable there: it is a parametric integral
of `p` composed with the (quasi-measure-preserving) joint rotation map, so
`AEStronglyMeasurable.integral_prod_right'` applies after transporting `p`'s a.e. strong
measurability through `quasiMeasurePreserving_rotZ_prod`. -/
theorem aestronglyMeasurable_angularMeanScalar {p : ParabolicPoint → ℝ}
    (hp : AEStronglyMeasurable p (volume.restrict unitCylinder)) :
    AEStronglyMeasurable (angularMeanScalar p) (volume.restrict unitCylinder) := by
  have hcomp : AEStronglyMeasurable
      (fun q : ParabolicPoint × ℝ => p (rotZ (-q.2) q.1.1, q.1.2))
      ((volume.restrict unitCylinder).prod (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) :=
    hp.comp_quasiMeasurePreserving quasiMeasurePreserving_rotZ_prod
  have hint : AEStronglyMeasurable
      (fun z : ParabolicPoint => ∫ φ in Ioc (0 : ℝ) (2 * Real.pi), p (rotZ (-φ) z.1, z.2))
      (volume.restrict unitCylinder) := hcomp.integral_prod_right'
  have heq : (fun z : ParabolicPoint => (2 * Real.pi)⁻¹ •
      ∫ φ in Ioc (0 : ℝ) (2 * Real.pi), p (rotZ (-φ) z.1, z.2)) = angularMeanScalar p := by
    funext z
    rw [angularMeanScalar_eq_integral_Ioc]
  rw [← heq]
  exact hint.const_smul ((2 * Real.pi)⁻¹ : ℝ)

/-- The rotated evaluation point `(x, t) ↦ (rotZ φ x, t)`, packaged as a named function so
that generic lemmas about measure-preserving maps and Lebesgue integrals can be applied to
it without the elaborator having to unfold the `ParabolicPoint := Vec3 × ℝ` alias inside a
raw λ-term under a binder. -/
@[expose] private def rotSlice (φ : ℝ) (z : ParabolicPoint) : ParabolicPoint := (rotZ φ z.1, z.2)

/-- A rotated slice of an almost-everywhere strongly measurable scalar field on the unit
cylinder has the same `∫⁻ ‖·‖ₑ ^ (3/2)` value as the field itself: change of variables along
the (exactly) measure-preserving map `rotSlice φ`. -/
private theorem lintegral_rotate_eq (φ : ℝ) {p : ParabolicPoint → ℝ}
    (hp : AEStronglyMeasurable p (volume.restrict unitCylinder)) :
    ∫⁻ z in unitCylinder, ‖p (rotSlice φ z)‖ₑ ^ (3 / 2 : ℝ)
      = ∫⁻ z in unitCylinder, ‖p z‖ₑ ^ (3 / 2 : ℝ) := by
  have hmp : MeasurePreserving (rotSlice φ)
      (volume.restrict unitCylinder) (volume.restrict unitCylinder) :=
    measurePreserving_rotZ_unitCylinder φ
  conv_rhs => rw [← hmp.map_eq]
  exact (lintegral_map' (f := fun z : ParabolicPoint => ‖p z‖ₑ ^ (3 / 2 : ℝ))
    (by rw [hmp.map_eq]; fun_prop) hmp.measurable.aemeasurable).symm

/-- The angular mean, evaluated in the extended-nonnegative-real norm and raised to the power
`3/2`, is bounded by the average over the rotation angle of the corresponding power of `p`
itself: Jensen's inequality for the power `3/2 ≥ 1`, obtained here from Hölder's inequality
(`eLpNorm'_le_eLpNorm'_mul_rpow_measure_univ`, comparing the `L¹` and `L^{3/2}` (semi)norms on
the finite-measure angle interval) after taking both sides to the power `3/2`. -/
private theorem key_bound {p : ParabolicPoint → ℝ} {z : ParabolicPoint}
    (hz : AEStronglyMeasurable (fun φ : ℝ => p (rotSlice (-φ) z))
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) :
    ‖angularMeanScalar p z‖ₑ ^ (3 / 2 : ℝ) ≤
      (ENNReal.ofReal (2 * Real.pi))⁻¹ *
        ∫⁻ φ in Ioc (0 : ℝ) (2 * Real.pi), ‖p (rotSlice (-φ) z)‖ₑ ^ (3 / 2 : ℝ) := by
  set c : ℝ≥0∞ := ENNReal.ofReal (2 * Real.pi) with hc_def
  have hc0 : c ≠ 0 := by
    rw [hc_def, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    positivity
  have hctop : c ≠ ⊤ := ENNReal.ofReal_ne_top
  have hcuniv : volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)) Set.univ = c := by
    rw [Measure.restrict_apply_univ, Real.volume_Ioc, hc_def]
    congr 1; ring
  have hstep1 : ‖∫ φ in Ioc (0 : ℝ) (2 * Real.pi), p (rotSlice (-φ) z)‖ₑ ≤
      ∫⁻ φ in Ioc (0 : ℝ) (2 * Real.pi), ‖p (rotSlice (-φ) z)‖ₑ :=
    enorm_integral_le_lintegral_enorm _
  have hstep2 := eLpNorm'_le_eLpNorm'_mul_rpow_measure_univ
    (f := fun φ : ℝ => p (rotSlice (-φ) z)) (μ := volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))
    (p := 1) (q := 3 / 2) (by norm_num) (by norm_num) hz
  rw [hcuniv, show (1 : ℝ) / 1 - 1 / (3 / 2) = 1 / 3 by norm_num] at hstep2
  have heLp1 : eLpNorm' (fun φ : ℝ => p (rotSlice (-φ) z)) 1
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) =
      ∫⁻ φ in Ioc (0 : ℝ) (2 * Real.pi), ‖p (rotSlice (-φ) z)‖ₑ := by
    rw [eLpNorm'_eq_lintegral_enorm]
    norm_num
  rw [heLp1] at hstep2
  have hcomb := hstep1.trans hstep2
  have hangular : ‖angularMeanScalar p z‖ₑ = c⁻¹ *
      ‖∫ φ in Ioc (0 : ℝ) (2 * Real.pi), p (rotSlice (-φ) z)‖ₑ := by
    rw [angularMeanScalar_eq_integral_Ioc, smul_eq_mul, enorm_mul]
    congr 1
    rw [Real.enorm_eq_ofReal (by positivity), hc_def, ENNReal.ofReal_inv_of_pos (by positivity)]
  rw [hangular]
  have hmono : (c⁻¹ * ‖∫ φ in Ioc (0 : ℝ) (2 * Real.pi), p (rotSlice (-φ) z)‖ₑ) ^ (3 / 2 : ℝ) ≤
      (c⁻¹ * (eLpNorm' (fun φ : ℝ => p (rotSlice (-φ) z)) (3 / 2)
        (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) * c ^ (1 / 3 : ℝ))) ^ (3 / 2 : ℝ) := by
    gcongr
  refine hmono.trans_eq ?_
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
    ← ENNReal.rpow_mul]
  rw [← lintegral_rpow_enorm_eq_rpow_eLpNorm' (f := fun φ : ℝ => p (rotSlice (-φ) z))
    (q := 3 / 2) (by norm_num)]
  rw [show (1 : ℝ) / 3 * (3 / 2) = 1 / 2 by norm_num]
  have hfactor : c⁻¹ ^ (3 / 2 : ℝ) * c ^ (1 / 2 : ℝ) = c⁻¹ := by
    rw [ENNReal.inv_rpow, ← ENNReal.rpow_neg, ← ENNReal.rpow_add _ _ hc0 hctop]
    norm_num
    exact ENNReal.rpow_neg_one c
  rw [mul_left_comm, hfactor, mul_comm]

/-- The angular mean of `p` composed with the rotation and evaluation map, as a function of
the pair (point, angle), is almost-everywhere strongly measurable on the product of the unit
cylinder with the angle interval: this is `p` transported along the quasi-measure-preserving
joint rotation map `quasiMeasurePreserving_rotZ_prod`. -/
private theorem aestronglyMeasurable_joint_rotSlice {p : ParabolicPoint → ℝ}
    (hp : AEStronglyMeasurable p (volume.restrict unitCylinder)) :
    AEStronglyMeasurable (fun q : ParabolicPoint × ℝ => p (rotSlice (-q.2) q.1))
      ((volume.restrict unitCylinder).prod (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) :=
  hp.comp_quasiMeasurePreserving quasiMeasurePreserving_rotZ_prod

/-- **The pressure energy bound for the angular mean.** If `p` lies in `L^{3/2}` on the unit
cylinder then so does its angular mean `angularMeanScalar p`, with the same `L^{3/2}` seminorm
bound. This is the scalar Minkowski-integral-inequality step of
`globalEnergyClass_angularMeanScalar`:
Jensen's inequality (`key_bound`) pointwise a.e. in space, `MeasureTheory.lintegral_lintegral_swap`
(Tonelli) to interchange the angle and space integrals, and `lintegral_rotate_eq` (exact
rotation invariance) to identify the inner space integral with `∫⁻ ‖p‖ₑ ^ (3/2)` for every
angle. -/
theorem lintegral_angularMeanScalar_rpow_lt_top {p : ParabolicPoint → ℝ}
    (hp : AEStronglyMeasurable p (volume.restrict unitCylinder))
    (hK : (∫⁻ z in unitCylinder, ‖p z‖ₑ ^ (3 / 2 : ℝ)) < ⊤) :
    (∫⁻ z in unitCylinder, ‖angularMeanScalar p z‖ₑ ^ (3 / 2 : ℝ)) < ⊤ := by
  set c : ℝ≥0∞ := ENNReal.ofReal (2 * Real.pi) with hc_def
  have hc0 : c ≠ 0 := by rw [hc_def, ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  have hctop : c ≠ ⊤ := ENNReal.ofReal_ne_top
  have hcinvtop : c⁻¹ ≠ ⊤ := by simp [hc0]
  have hjoint := aestronglyMeasurable_joint_rotSlice hp
  have hslice : ∀ᵐ z ∂(volume.restrict unitCylinder),
      AEStronglyMeasurable (fun φ : ℝ => p (rotSlice (-φ) z))
        (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))) := hjoint.prodMk_left
  have hbound : ∀ᵐ z ∂(volume.restrict unitCylinder),
      ‖angularMeanScalar p z‖ₑ ^ (3 / 2 : ℝ) ≤
        c⁻¹ * ∫⁻ φ in Ioc (0 : ℝ) (2 * Real.pi), ‖p (rotSlice (-φ) z)‖ₑ ^ (3 / 2 : ℝ) := by
    filter_upwards [hslice] with z hz using key_bound hz
  calc ∫⁻ z in unitCylinder, ‖angularMeanScalar p z‖ₑ ^ (3 / 2 : ℝ)
      ≤ ∫⁻ z in unitCylinder,
          c⁻¹ * ∫⁻ φ in Ioc (0 : ℝ) (2 * Real.pi), ‖p (rotSlice (-φ) z)‖ₑ ^ (3 / 2 : ℝ) :=
        lintegral_mono_ae hbound
    _ = c⁻¹ * ∫⁻ z in unitCylinder,
          ∫⁻ φ in Ioc (0 : ℝ) (2 * Real.pi), ‖p (rotSlice (-φ) z)‖ₑ ^ (3 / 2 : ℝ) :=
        lintegral_const_mul' c⁻¹ _ hcinvtop
    _ = c⁻¹ * ∫⁻ φ in Ioc (0 : ℝ) (2 * Real.pi),
          ∫⁻ z in unitCylinder, ‖p (rotSlice (-φ) z)‖ₑ ^ (3 / 2 : ℝ) := by
        rw [lintegral_lintegral_swap (hjoint.enorm.pow_const (3 / 2 : ℝ))]
    _ = c⁻¹ * ∫⁻ φ in Ioc (0 : ℝ) (2 * Real.pi), ∫⁻ z in unitCylinder, ‖p z‖ₑ ^ (3 / 2 : ℝ) := by
        congr 1
        apply lintegral_congr
        intro φ
        exact lintegral_rotate_eq (-φ) hp
    _ = c⁻¹ * (c * ∫⁻ z in unitCylinder, ‖p z‖ₑ ^ (3 / 2 : ℝ)) := by
        rw [lintegral_const]
        have hIocMeasure : volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)) Set.univ = c := by
          rw [Measure.restrict_apply_univ, Real.volume_Ioc, hc_def]
          congr 1; ring
        rw [hIocMeasure]
        ring
    _ = ∫⁻ z in unitCylinder, ‖p z‖ₑ ^ (3 / 2 : ℝ) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hc0 hctop, one_mul]
    _ < ⊤ := hK

/-- The angular mean of a triple in the energy class `eq:interior:energy:class` is again in
that class: `GlobalEnergyClass` leaves `u` and `Du` unchanged and asks only that the pressure
lie in `L^{3/2}(Q)`, and averaging over rotations cannot increase that norm
(`lintegral_angularMeanScalar_rpow_lt_top`). -/
theorem globalEnergyClass_angularMeanScalar
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3) (p : ParabolicPoint → ℝ)
    (henergy : GlobalEnergyClass u Du p) :
    GlobalEnergyClass u Du (angularMeanScalar p) := by
  obtain ⟨h1, h2, h3⟩ := henergy
  refine ⟨h1, h2, ?_⟩
  have hp : AEStronglyMeasurable p (volume.restrict unitCylinder) := h3.aestronglyMeasurable
  have hK : (∫⁻ z in unitCylinder, ‖p z‖ₑ ^ (3 / 2 : ℝ)) < ⊤ := by
    have := h3.eLpNorm_lt_top
    rwa [eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num) hp, eLpNorm'_eq_lintegral_enorm,
      show (ENNReal.ofReal (3 / 2 : ℝ)).toReal = 3 / 2 by
        rw [ENNReal.toReal_ofReal (by norm_num)],
      ENNReal.rpow_lt_top_iff_of_pos (by norm_num)] at this
  have hmem : MemLp (angularMeanScalar p) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict unitCylinder) := by
    rw [memLp_iff, eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num)
        (aestronglyMeasurable_angularMeanScalar hp), eLpNorm'_eq_lintegral_enorm,
      show (ENNReal.ofReal (3 / 2 : ℝ)).toReal = 3 / 2 by
        rw [ENNReal.toReal_ofReal (by norm_num)]]
    rw [ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0:ℝ) < 1 / (3/2 : ℝ))]
    exact lintegral_angularMeanScalar_rpow_lt_top hp hK
  exact hmem

end CIV
