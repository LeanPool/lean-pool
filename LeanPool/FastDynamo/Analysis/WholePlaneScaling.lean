/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Analysis.WholePlaneFourier
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Linear-isometric affine scaling on whole-plane `L²`

This module constructs the exact two-dimensional cell rescaling

`U_[p,ℓ] f (y) = ℓ⁻¹ f ((y - p) / ℓ)`

for `0 < ℓ`.  The Jacobian is proved at the measure level, so the map is
defined on `L²` equivalence classes without choosing representatives.  It is
then bundled as a complex linear isometric equivalence, with the explicit
inverse `U_[-ℓ⁻¹p,ℓ⁻¹]`.

Weak-derivative scaling is not asserted here: lifting this map to
the Sobolev graphs requires the affine chain rule for tempered distributions,
which is proved in `WholePlaneCoefficientScaling`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory
open scoped ENNReal

/-- The affine pullback used for the two-dimensional local-cell scaling. -/
def wholePlaneAffine (p : WholePlane) (ell : ℝ) (y : WholePlane) : WholePlane :=
  ell⁻¹ • (y - p)

/-- Pushforward of planar Lebesgue measure under the dilation `y ↦ y/ℓ`: for `ℓ > 0` it is
`ℓ²` times Lebesgue measure, the two-dimensional Jacobian. -/
theorem map_wholePlane_inv_smul_volume (ell : ℝ) (hell : 0 < ell) :
    Measure.map (fun y : WholePlane ↦ ell⁻¹ • y) volume =
      ENNReal.ofReal (ell ^ 2) • (volume : Measure WholePlane) := by
  rw [Measure.map_addHaar_smul (volume : Measure WholePlane) (inv_ne_zero hell.ne')]
  rw [finrank_euclideanSpace]
  simp only [Fintype.card_fin]
  congr 1
  rw [inv_pow, inv_inv]
  rw [abs_of_pos (sq_pos_of_pos hell)]

/-- The affine map `y ↦ (y - p)/ℓ` carries planar Lebesgue measure to `ℓ²` times Lebesgue
measure: the translation is measure preserving and the dilation supplies the Jacobian. -/
theorem measurePreserving_wholePlaneAffine (p : WholePlane) (ell : ℝ) (hell : 0 < ell) :
    MeasurePreserving (wholePlaneAffine p ell) (volume : Measure WholePlane)
      (ENNReal.ofReal (ell ^ 2) • (volume : Measure WholePlane)) := by
  have hdil : MeasurePreserving (fun y : WholePlane ↦ ell⁻¹ • y)
      (volume : Measure WholePlane)
      (ENNReal.ofReal (ell ^ 2) • (volume : Measure WholePlane)) :=
    ⟨measurable_const_smul _, map_wholePlane_inv_smul_volume ell hell⟩
  have htrans : MeasurePreserving (fun y : WholePlane ↦ y - p)
      (volume : Measure WholePlane) volume := by
    simpa [sub_eq_add_neg] using
      (measurePreserving_add_right (volume : Measure WholePlane) (-p))
  change MeasurePreserving (fun y : WholePlane ↦ ell⁻¹ • (y - p)) _ _
  exact hdil.comp htrans

/-- For `ℓ > 0` the half power of the density is `(ℓ²)^(1/2) = ℓ` in `ℝ≥0∞`; this is the factor
that appears when an `L²` seminorm is computed against the rescaled measure. -/
theorem wholePlane_density_rpow_half (ell : ℝ) (hell : 0 < ell) :
    ENNReal.ofReal (ell ^ 2) ^ (1 / (2 : ℝ≥0∞)).toReal = ENNReal.ofReal ell := by
  rw [show (1 / (2 : ℝ≥0∞)).toReal = (1 / 2 : ℝ) by norm_num]
  rw [ENNReal.ofReal_rpow_of_nonneg (sq_nonneg ell) (by positivity)]
  congr 1
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul hell.le]
  norm_num

/-- For `ℓ > 0` the extended norm of the complex scalar `ℓ` is `ENNReal.ofReal ℓ`. -/
theorem wholePlane_enorm_real (ell : ℝ) (hell : 0 < ell) :
    ‖(ell : ℂ)‖ₑ = ENNReal.ofReal ell := by
  simpa only [eNorm_eq_nnNorm, Complex.nnNorm_real] using
    Real.eNorm_eq_ofReal hell.le

section Rescale

variable (F : Type*) [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Multiplication by `ell⁻¹`, viewed in the correctly rescaled target measure. -/
def wholePlaneNormalizeTarget (ell : ℝ)
    (f : WholePlaneL2 F) :
    Lp F 2 (ENNReal.ofReal (ell ^ 2) • (volume : Measure WholePlane)) :=
  let c : ℂ := (ell : ℂ)⁻¹
  let hf : MemLp (c • (f : WholePlane → F)) 2
      (ENNReal.ofReal (ell ^ 2) • (volume : Measure WholePlane)) :=
    ((Lp.memLp f).smul_measure (c := ENNReal.ofReal (ell ^ 2)) (by simp)).const_smul c
  hf.toLp (c • (f : WholePlane → F))

/-- The normalization map is represented almost everywhere by pointwise multiplication by
`ℓ⁻¹`, now read against the rescaled measure. -/
theorem wholePlaneNormalizeTarget_coe_ae (ell : ℝ)
    (f : WholePlaneL2 F) :
    (wholePlaneNormalizeTarget F ell f : WholePlane → F) =ᵐ[
      ENNReal.ofReal (ell ^ 2) • (volume : Measure WholePlane)]
      ((ell : ℂ)⁻¹ • (f : WholePlane → F)) := by
  unfold wholePlaneNormalizeTarget
  exact MemLp.coeFn_toLp
    (((Lp.memLp f).smul_measure (c := ENNReal.ofReal (ell ^ 2)) (by simp)).const_smul
      (ell : ℂ)⁻¹)

/-- The factor `ℓ⁻¹` exactly cancels the `ℓ²` density: for `ℓ > 0` the `L²` seminorm of the
normalized field against the rescaled measure equals the original `L²` seminorm. -/
theorem eLpNorm_wholePlaneNormalizeTarget (ell : ℝ) (hell : 0 < ell)
    (f : WholePlaneL2 F) :
    eLpNorm (wholePlaneNormalizeTarget F ell f : WholePlane → F) 2
        (ENNReal.ofReal (ell ^ 2) • (volume : Measure WholePlane)) =
      eLpNorm (f : WholePlane → F) 2 volume := by
  rw [eLpNorm_congr_ae (wholePlaneNormalizeTarget_coe_ae F ell f)]
  rw [eLpNorm_const_smul]
  rw [eLpNorm_smul_measure_of_ne_zero (by positivity : ENNReal.ofReal (ell ^ 2) ≠ 0)]
  rw [wholePlane_density_rpow_half ell hell]
  rw [eNorm_inv (by exact_mod_cast hell.ne')]
  rw [wholePlane_enorm_real ell hell]
  rw [smul_eq_mul]
  rw [← mul_assoc]
  rw [ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hell |>.ne') (by simp)]
  rw [one_mul]

/-- Quotient-norm form of the cancellation: normalizing to the rescaled measure preserves the
`L²` norm. -/
theorem norm_wholePlaneNormalizeTarget (ell : ℝ) (hell : 0 < ell)
    (f : WholePlaneL2 F) :
    ‖wholePlaneNormalizeTarget F ell f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  rw [eLpNorm_wholePlaneNormalizeTarget F ell hell f]

/-- The exact `L²`-normalized affine rescaling on the whole plane. -/
def wholePlaneRescale (p : WholePlane) (ell : ℝ) (hell : 0 < ell)
    (f : WholePlaneL2 F) : WholePlaneL2 F :=
  Lp.compMeasurePreserving (wholePlaneAffine p ell)
    (measurePreserving_wholePlaneAffine p ell hell)
    (wholePlaneNormalizeTarget F ell f)

/-- The cell rescaling is represented almost everywhere by `y ↦ ℓ⁻¹ f((y - p)/ℓ)`, which is the
paper's `U_n` (Paper §5, the rescaling displayed before Lemma 5.2). -/
theorem wholePlaneRescale_coe_ae (p : WholePlane) (ell : ℝ) (hell : 0 < ell)
    (f : WholePlaneL2 F) :
    (wholePlaneRescale F p ell hell f : WholePlane → F) =ᵐ[volume]
      fun y ↦ (ell : ℂ)⁻¹ • f (wholePlaneAffine p ell y) := by
  apply (Lp.coeFn_compMeasurePreserving _ _).trans
  exact (measurePreserving_wholePlaneAffine p ell hell).quasiMeasurePreserving.ae_eq_comp
    (wholePlaneNormalizeTarget_coe_ae F ell f)

/-- The cell rescaling preserves the `L²` norm; this is exactly what the normalizing factor
`ℓ⁻¹` achieves in two transverse dimensions. -/
theorem norm_wholePlaneRescale (p : WholePlane) (ell : ℝ) (hell : 0 < ell)
    (f : WholePlaneL2 F) :
    ‖wholePlaneRescale F p ell hell f‖ = ‖f‖ := by
  unfold wholePlaneRescale
  rw [Lp.norm_compMeasurePreserving]
  exact norm_wholePlaneNormalizeTarget F ell hell f

/-- The normalized affine rescaling as a complex-linear map. -/
def wholePlaneRescaleLinear (p : WholePlane) (ell : ℝ) (hell : 0 < ell) :
    WholePlaneL2 F →ₗ[ℂ] WholePlaneL2 F where
  toFun := wholePlaneRescale F p ell hell
  map_add' f g := by
    apply Lp.ext
    have haddScaled := Measure.ae_smul_measure (Lp.coeFn_add f g)
      (ENNReal.ofReal (ell ^ 2))
    have haddPull :=
      (measurePreserving_wholePlaneAffine p ell hell).quasiMeasurePreserving.ae_eq_comp
        haddScaled
    filter_upwards [wholePlaneRescale_coe_ae F p ell hell (f + g),
      wholePlaneRescale_coe_ae F p ell hell f,
      wholePlaneRescale_coe_ae F p ell hell g,
      Lp.coeFn_add (wholePlaneRescale F p ell hell f)
        (wholePlaneRescale F p ell hell g), haddPull]
      with y hfg hf hg hout hpull
    rw [hfg, hout]
    change (ell : ℂ)⁻¹ •
        ((f + g : WholePlaneL2 F) : WholePlane → F) (wholePlaneAffine p ell y) =
      (wholePlaneRescale F p ell hell f : WholePlane → F) y +
        (wholePlaneRescale F p ell hell g : WholePlane → F) y
    have hpull' :
        ((f + g : WholePlaneL2 F) : WholePlane → F) (wholePlaneAffine p ell y) =
          f (wholePlaneAffine p ell y) + g (wholePlaneAffine p ell y) := by
      simpa only [Function.comp_apply, Pi.add_apply] using hpull
    rw [hpull', hf, hg]
    exact smul_add _ _ _
  map_smul' c f := by
    apply Lp.ext
    have hsmulScaled := Measure.ae_smul_measure (Lp.coeFn_smul c f)
      (ENNReal.ofReal (ell ^ 2))
    have hsmulPull :=
      (measurePreserving_wholePlaneAffine p ell hell).quasiMeasurePreserving.ae_eq_comp
        hsmulScaled
    filter_upwards [wholePlaneRescale_coe_ae F p ell hell (c • f),
      wholePlaneRescale_coe_ae F p ell hell f,
      Lp.coeFn_smul c (wholePlaneRescale F p ell hell f), hsmulPull]
      with y hcf hf hout hpull
    rw [hcf]
    have hout' :
        (((RingHom.id ℂ) c • wholePlaneRescale F p ell hell f : WholePlaneL2 F) :
          WholePlane → F) y =
          c • (wholePlaneRescale F p ell hell f : WholePlane → F) y := by
      simpa only [RingHom.id_apply, Pi.smul_apply] using hout
    rw [hout']
    change (ell : ℂ)⁻¹ •
        ((c • f : WholePlaneL2 F) : WholePlane → F) (wholePlaneAffine p ell y) =
      c • (wholePlaneRescale F p ell hell f : WholePlane → F) y
    have hpull' :
        ((c • f : WholePlaneL2 F) : WholePlane → F) (wholePlaneAffine p ell y) =
          c • f (wholePlaneAffine p ell y) := by
      simpa only [Function.comp_apply, Pi.smul_apply] using hpull
    rw [hpull', hf]
    simp only [smul_smul]
    rw [mul_comm]

/-- Center parameter for the inverse affine rescaling. -/
def wholePlaneInverseCenter (p : WholePlane) (ell : ℝ) : WholePlane :=
  -ell⁻¹ • p

/-- The affine maps attached to `(p, ℓ)` and to `(-p/ℓ, ℓ⁻¹)` are mutually inverse; this is the
left-inverse direction. -/
theorem wholePlaneAffine_inverse_left (p : WholePlane) (ell : ℝ) (hell : 0 < ell)
    (y : WholePlane) :
    wholePlaneAffine p ell
      (wholePlaneAffine (wholePlaneInverseCenter p ell) ell⁻¹ y) = y := by
  ext j
  simp only [wholePlaneAffine, wholePlaneInverseCenter, PiLp.smul_apply,
    PiLp.sub_apply]
  simp only [smul_eq_mul]
  field_simp [hell.ne']
  ring

/-- Applying the rescaling with center `-p/ℓ` and scale `ℓ⁻¹` after the rescaling with center
`p` and scale `ℓ` returns the original field: the affine maps invert one another and the two
normalizing constants multiply to one.  This is `U_n⁻¹ U_n = id` (Paper §5). -/
theorem wholePlaneRescale_inverse_apply (p : WholePlane) (ell : ℝ) (hell : 0 < ell)
    (f : WholePlaneL2 F) :
    wholePlaneRescale F (wholePlaneInverseCenter p ell) ell⁻¹ (inv_pos.mpr hell)
        (wholePlaneRescale F p ell hell f) = f := by
  apply Lp.ext
  have houter := wholePlaneRescale_coe_ae F (wholePlaneInverseCenter p ell)
    ell⁻¹ (inv_pos.mpr hell) (wholePlaneRescale F p ell hell f)
  have hinnerScaled := Measure.ae_smul_measure
    (wholePlaneRescale_coe_ae F p ell hell f)
    (ENNReal.ofReal ((ell⁻¹) ^ 2))
  have hinnerPull :=
    (measurePreserving_wholePlaneAffine (wholePlaneInverseCenter p ell) ell⁻¹
      (inv_pos.mpr hell)).quasiMeasurePreserving.ae_eq_comp hinnerScaled
  filter_upwards [houter, hinnerPull] with y ho hi
  rw [ho]
  have hi' :
      (wholePlaneRescale F p ell hell f : WholePlane → F)
          (wholePlaneAffine (wholePlaneInverseCenter p ell) ell⁻¹ y) =
        (ell : ℂ)⁻¹ • f (wholePlaneAffine p ell
          (wholePlaneAffine (wholePlaneInverseCenter p ell) ell⁻¹ y)) := by
    simpa only [Function.comp_apply] using hi
  rw [hi', wholePlaneAffine_inverse_left p ell hell y]
  rw [smul_smul]
  simp [hell.ne']

/-- Taking the inverse center twice recovers the original center `p`. -/
theorem wholePlaneInverseCenter_involutive (p : WholePlane) (ell : ℝ)
    (hell : 0 < ell) :
    wholePlaneInverseCenter (wholePlaneInverseCenter p ell) ell⁻¹ = p := by
  ext j
  simp only [wholePlaneInverseCenter, PiLp.smul_apply]
  simp only [smul_eq_mul]
  field_simp [hell.ne']

/-- The composition in the opposite order is also the identity, so the cell rescaling is
invertible on `L²`. -/
theorem wholePlaneRescale_inverse_apply_right (p : WholePlane) (ell : ℝ)
    (hell : 0 < ell) (f : WholePlaneL2 F) :
    wholePlaneRescale F p ell hell
        (wholePlaneRescale F (wholePlaneInverseCenter p ell) ell⁻¹ (inv_pos.mpr hell) f) =
      f := by
  have h := wholePlaneRescale_inverse_apply F (wholePlaneInverseCenter p ell) ell⁻¹
    (inv_pos.mpr hell) f
  simpa only [inv_inv, wholePlaneInverseCenter_involutive p ell hell] using h

/-- The normalized affine rescaling as a complex-linear equivalence. -/
def wholePlaneRescaleLinearEquiv (p : WholePlane) (ell : ℝ) (hell : 0 < ell) :
    LinearEquiv (RingHom.id ℂ) (WholePlaneL2 F) (WholePlaneL2 F) where
  toLinearMap := wholePlaneRescaleLinear F p ell hell
  invFun := wholePlaneRescale F (wholePlaneInverseCenter p ell) ell⁻¹ (inv_pos.mpr hell)
  left_inv := wholePlaneRescale_inverse_apply F p ell hell
  right_inv := wholePlaneRescale_inverse_apply_right F p ell hell

/-- The normalized affine rescaling is a complex linear isometric equivalence
of whole-plane `L²`. -/
def wholePlaneRescaleLinearIsometryEquiv (p : WholePlane) (ell : ℝ) (hell : 0 < ell) :
    LinearIsometryEquiv (RingHom.id ℂ) (WholePlaneL2 F) (WholePlaneL2 F) where
  toLinearEquiv := wholePlaneRescaleLinearEquiv F p ell hell
  norm_map' := norm_wholePlaneRescale F p ell hell

/-- The bundled isometric equivalence acts by the normalized cell rescaling `U_{p,ℓ}`. -/
@[simp] theorem wholePlaneRescaleLinearIsometryEquiv_apply
    (p : WholePlane) (ell : ℝ) (hell : 0 < ell) (f : WholePlaneL2 F) :
    wholePlaneRescaleLinearIsometryEquiv F p ell hell f =
      wholePlaneRescale F p ell hell f :=
  rfl

/-- Its inverse is the rescaling with center `-p/ℓ` and scale `ℓ⁻¹`, that is `g ↦ ℓ g(p + ℓ ·)`
(Paper §5, the displayed formula for `U_n⁻¹`). -/
@[simp] theorem wholePlaneRescaleLinearIsometryEquiv_symm_apply
    (p : WholePlane) (ell : ℝ) (hell : 0 < ell) (f : WholePlaneL2 F) :
    (wholePlaneRescaleLinearIsometryEquiv F p ell hell).symm f =
      wholePlaneRescale F (wholePlaneInverseCenter p ell) ell⁻¹ (inv_pos.mpr hell) f :=
  rfl

end Rescale

end

end FastDynamo
