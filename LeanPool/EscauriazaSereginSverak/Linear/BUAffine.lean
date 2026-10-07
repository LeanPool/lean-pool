/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Statements.HasSpaceTimeWeakDerivs
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Vec3Norm
public import LeanPool.CaffarelliKohnNirenberg.Setting.ScalingInvarianceTests

/-!
# Affine parabolic coordinates for backward uniqueness

The time iteration and finite-slab arguments in `lem:bu-iterate` and `thm:bu`
use positive spatial dilation and an affine time change.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The affine parabolic change of variables based at time `τ`. -/
@[expose] def buAffinePoint (τ scale : ℝ) (z : ParabolicPoint) : ParabolicPoint :=
  (scale • z.1, τ + scale ^ 2 * z.2)

/-- A field in affine parabolic coordinates. -/
@[expose] def buAffineField (τ scale : ℝ) (w : ParabolicPoint → Vec3) :
    ParabolicPoint → Vec3 :=
  fun z => w (buAffinePoint τ scale z)

/-- The first spatial weak derivative in affine parabolic coordinates. -/
@[expose] def buAffineDw (τ scale : ℝ) (Dw : ParabolicPoint → Fin 3 → Vec3) :
    ParabolicPoint → Fin 3 → Vec3 :=
  fun z i j => scale * Dw (buAffinePoint τ scale z) i j

/-- The second spatial weak derivative in affine parabolic coordinates. -/
@[expose] def buAffineD2w (τ scale : ℝ)
    (D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3) :
    ParabolicPoint → Fin 3 → Fin 3 → Vec3 :=
  fun z i j k => scale ^ 2 * D2w (buAffinePoint τ scale z) i j k

/-- The weak time derivative in affine parabolic coordinates. -/
@[expose] def buAffineDtw (τ scale : ℝ) (Dtw : ParabolicPoint → Vec3) :
    ParabolicPoint → Vec3 :=
  fun z i => scale ^ 2 * Dtw (buAffinePoint τ scale z) i

/-- The affine coordinates agree with the parabolic dilation and translation
used by the integration change-of-variables formulas. -/
theorem buAffinePoint_eq_scalingParabolic (τ scale : ℝ) :
    buAffinePoint τ scale =
      scalingParabolic scale ((0 : Vec3), τ) := by
  funext z
  simp only [buAffinePoint, scalingParabolic, parabolicTranslate,
    parabolicScale, zero_add]
  rfl

/-- The inverse image of a time slab under the affine map is the unit
positive-time cylinder. -/
theorem buAffinePoint_preimage_halfSlab
    (τ scale : ℝ) (hscale : 0 < scale) :
    buAffinePoint τ scale ⁻¹'
        spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo τ (τ + scale ^ 2)) =
      spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1) := by
  ext z
  have hs2 : 0 < scale ^ 2 := sq_pos_of_pos hscale
  constructor
  · rintro ⟨hx, ht⟩
    change 0 < scale * z.1 2 at hx
    change τ + scale ^ 2 * z.2 ∈ Ioo τ (τ + scale ^ 2) at ht
    have hy : 0 < z.1 2 :=
      (mul_pos_iff_of_pos_left hscale).mp hx
    have ht0mul : 0 < scale ^ 2 * z.2 := by linarith only [ht.1]
    have ht0 : 0 < z.2 :=
      (mul_pos_iff_of_pos_left hs2).mp ht0mul
    have ht1mul : scale ^ 2 * z.2 < scale ^ 2 * 1 := by
      linarith only [ht.2]
    have ht1 : z.2 < 1 :=
      (mul_lt_mul_iff_of_pos_left hs2).mp ht1mul
    exact ⟨hy, ht0, ht1⟩
  · rintro ⟨hx, ht⟩
    change 0 < scale * z.1 2 ∧
      τ + scale ^ 2 * z.2 ∈ Ioo τ (τ + scale ^ 2)
    refine ⟨mul_pos hscale hx, ?_⟩
    constructor
    · linarith only [mul_pos hs2 ht.1]
    · have h := mul_lt_mul_of_pos_left ht.2 hs2
      nlinarith only [h]

/-- The affine parabolic map preserves the positive half-space cylinder when
its image time interval stays below one. -/
theorem buAffinePoint_mem_halfCylinder
    (τ scale : ℝ) (hτ : 0 ≤ τ) (hscale : 0 < scale)
    (hupper : τ + scale ^ 2 ≤ 1) {z : ParabolicPoint}
    (hz : z ∈ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1)) :
    buAffinePoint τ scale z ∈
      spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1) := by
  rcases hz with ⟨hx, ht⟩
  change 0 < scale * z.1 2 ∧
    τ + scale ^ 2 * z.2 ∈ Ioo 0 1
  refine ⟨mul_pos hscale hx, ?_⟩
  have hs2 : 0 < scale ^ 2 := sq_pos_of_pos hscale
  constructor
  · exact lt_of_lt_of_le (mul_pos hs2 ht.1) (le_add_of_nonneg_left hτ)
  · calc
      τ + scale ^ 2 * z.2 < τ + scale ^ 2 * 1 := by
        linarith only [mul_lt_mul_of_pos_left ht.2 hs2]
      _ = τ + scale ^ 2 := by ring
      _ ≤ 1 := hupper

/-- The affine parabolic map also preserves the cylinder with its initial
time face included. -/
theorem buAffinePoint_mem_halfClosure
    (τ scale : ℝ) (hτ : 0 ≤ τ) (hscale : 0 < scale)
    (hupper : τ + scale ^ 2 ≤ 1) {z : ParabolicPoint}
    (hz : z ∈ {x : Vec3 | 0 < x 2} ×ˢ Ico 0 1) :
    buAffinePoint τ scale z ∈ {x : Vec3 | 0 < x 2} ×ˢ Ico 0 1 := by
  rcases hz with ⟨hx, ht⟩
  change 0 < scale * z.1 2 ∧ τ + scale ^ 2 * z.2 ∈ Ico 0 1
  refine ⟨mul_pos hscale hx, ?_⟩
  have hs2 : 0 < scale ^ 2 := sq_pos_of_pos hscale
  constructor
  · exact add_nonneg hτ (mul_nonneg hs2.le ht.1)
  · calc
      τ + scale ^ 2 * z.2 < τ + scale ^ 2 * 1 := by
        linarith only [mul_lt_mul_of_pos_left ht.2 hs2]
      _ = τ + scale ^ 2 := by ring
      _ ≤ 1 := hupper

/-- The affine parabolic map is continuous. -/
theorem buAffinePoint_continuous (τ scale : ℝ) :
    Continuous (buAffinePoint τ scale) := by
  have hs : Continuous (fun z : ParabolicPoint => scale • z.1) :=
    (continuous_const_smul scale).comp continuous_fst_parabolicPoint
  have ht : Continuous (fun z : ParabolicPoint => τ + scale ^ 2 * z.2) :=
    continuous_const.add
      ((continuous_const_mul (scale ^ 2)).comp continuous_snd_parabolicPoint)
  exact continuous_prod_to_parabolicPoint.comp (hs.prodMk ht)

/-- Continuity up to the initial time face transports under the affine map. -/
theorem buAffineField_continuousOn
    (τ scale : ℝ) (hτ : 0 ≤ τ) (hscale : 0 < scale)
    (hupper : τ + scale ^ 2 ≤ 1)
    (w : ParabolicPoint → Vec3)
    (hw : ContinuousOn w ({x : Vec3 | 0 < x 2} ×ˢ Ico 0 1)) :
    ContinuousOn (buAffineField τ scale w)
      ({x : Vec3 | 0 < x 2} ×ˢ Ico 0 1) := by
  change ContinuousOn (w ∘ buAffinePoint τ scale) _
  exact hw.comp (buAffinePoint_continuous τ scale).continuousOn
    (fun z hz => buAffinePoint_mem_halfClosure τ scale hτ hscale hupper hz)

/-- The affine field has the prescribed zero trace at normalized time zero. -/
theorem buAffineField_initial_zero
    (τ scale : ℝ) (w : ParabolicPoint → Vec3)
    (hzero : ∀ x : Vec3, 0 < x 2 → w (x, τ) = 0)
    (hscale : 0 < scale) (y : Vec3) (hy : 0 < y 2) :
    buAffineField τ scale w (y, 0) = 0 := by
  change w (scale • y, τ + scale ^ 2 * 0) = 0
  simp only [mul_zero, add_zero]
  have hy' : 0 < (scale • y) 2 := by
    change 0 < scale * y 2
    exact mul_pos hscale hy
  exact hzero (scale • y) hy'

/-- Gaussian growth is preserved when the rescaled exponent is bounded by the
target exponent. -/
theorem buAffineField_growth
    (M A τ scale : ℝ) (hscale : 0 < scale)
    (hA : M * scale ^ 2 ≤ A)
    (hτ : 0 ≤ τ) (hupper : τ + scale ^ 2 ≤ 1)
    (w : ParabolicPoint → Vec3)
    (hgrowth : ∀ z ∈ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1),
      vec3EuclideanNorm (w z) ≤
        Real.exp (M * vec3EuclideanNorm z.1 ^ 2))
    {z : ParabolicPoint}
    (hz : z ∈ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1)) :
    vec3EuclideanNorm (buAffineField τ scale w z) ≤
      Real.exp (A * vec3EuclideanNorm z.1 ^ 2) := by
  have hz' := buAffinePoint_mem_halfCylinder τ scale hτ hscale hupper hz
  have hg := hgrowth (buAffinePoint τ scale z) hz'
  have hnorm : vec3EuclideanNorm (scale • z.1) ^ 2 =
      scale ^ 2 * vec3EuclideanNorm z.1 ^ 2 := by
    rw [vec3EuclideanNorm_smul, abs_of_pos hscale]
    ring
  change vec3EuclideanNorm (w (buAffinePoint τ scale z)) ≤ _
  calc
    _ ≤ Real.exp (M * vec3EuclideanNorm (scale • z.1) ^ 2) := hg
    _ = Real.exp ((M * scale ^ 2) * vec3EuclideanNorm z.1 ^ 2) := by
      rw [hnorm]
      ring_nf
    _ ≤ Real.exp (A * vec3EuclideanNorm z.1 ^ 2) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_right hA (sq_nonneg _)

end ESS
