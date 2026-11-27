/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.SpatialHeatFourierKernel
public import LeanPool.VacuumBellSeparation.FreeField.TimeZeroGram

/-!
# Actual Gaussian convolution of two spatial Fourier tests

The full momentum/position joint integral is absolutely convergent.
Fubini and the proved normalized Gaussian transform identify the fixed
positive-time pairing with the actual spatial heat kernel.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory
open scoped InnerProductSpace ComplexConjugate

/-- Spatial heat joint. -/
noncomputable def spatialHeatJoint (t : ℝ) (f g : SpatialTestFunction)
    (q : EuclideanSpace ℝ (Fin 3) ×
      (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))) : ℂ :=
  Complex.exp (-(t : ℂ) * (‖q.1‖ : ℂ) ^ 2 +
    Complex.I * (inner ℝ (q.2.1 - q.2.2) q.1 : ℂ)) * (f.1 q.2.1 : ℂ) * (g.1 q.2.2 : ℂ)

theorem norm_spatialHeatJoint (t : ℝ) (f g : SpatialTestFunction)
    (p : EuclideanSpace ℝ (Fin 3)) (xy : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) :
    ‖spatialHeatJoint t f g (p, xy)‖ =
      Real.exp (-t * ‖p‖ ^ 2) * (‖f.1 xy.1‖ * ‖g.1 xy.2‖) := by
  simp only [spatialHeatJoint, norm_mul, Complex.norm_exp, Complex.norm_real,
    Complex.add_re, Complex.neg_re, Complex.neg_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, pow_two, mul_zero, zero_mul, sub_zero,
    add_zero, mul_assoc]

theorem integrable_spatialHeatJoint {t : ℝ} (ht : 0 < t) (f g : SpatialTestFunction) :
    Integrable (spatialHeatJoint t f g) (volume.prod (volume.prod volume)) := by
  have hf : Integrable f.1 := f.2.1.continuous.integrable_of_hasCompactSupport f.2.2
  have hg : Integrable g.1 := g.2.1.continuous.integrable_of_hasCompactSupport g.2.2
  have hh : Integrable (fun p : EuclideanSpace ℝ (Fin 3) => Real.exp (-t * ‖p‖ ^ 2)) := by
    simpa only [inner_zero_left, Complex.ofReal_zero, mul_zero, add_zero,
      Complex.norm_exp, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
        Complex.ofReal_re,
      Complex.ofReal_im, pow_two, zero_mul, mul_zero, sub_zero] using
      (integrable_spatialHeatFourierIntegrand ht 0).norm
  apply (hh.mul_prod (hf.norm.mul_prod hg.norm)).mono'
  · exact (show Continuous (spatialHeatJoint t f g) by
      unfold spatialHeatJoint
      have hfc := f.2.1.continuous
      have hgc := g.2.1.continuous
      fun_prop).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun q => (norm_spatialHeatJoint t f g q.1 q.2).le)

theorem spatialHeatJoint_factor (t : ℝ) (f g : SpatialTestFunction)
    (p x y : EuclideanSpace ℝ (Fin 3)) :
    spatialHeatJoint t f g (p, (x, y)) = (Real.exp (-t * ‖p‖ ^ 2) : ℂ) *
      ((Complex.exp (-(Complex.I * (inner ℝ (-p) x : ℂ))) * (f.1 x : ℂ)) *
        (Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * (g.1 y : ℂ))) := by
  unfold spatialHeatJoint
  rw [Complex.ofReal_exp]
  have he : -(t : ℂ) * (‖p‖ : ℂ) ^ 2 + Complex.I * (inner ℝ (x - y) p : ℂ) =
      ((-t * ‖p‖ ^ 2 : ℝ) : ℂ) - Complex.I * (inner ℝ (-p) x : ℂ) -
        Complex.I * (inner ℝ p y : ℂ) := by
    rw [inner_sub_left, inner_neg_left, real_inner_comm x p, real_inner_comm y p]
    push_cast
    ring
  rw [he, Complex.exp_sub, Complex.exp_sub]
  simp only [Complex.exp_neg]
  ring

theorem integral_spatialHeatJoint_positions (t : ℝ) (f g : SpatialTestFunction)
    (p : EuclideanSpace ℝ (Fin 3)) :
    (∫ xy, spatialHeatJoint t f g (p, xy) ∂volume.prod volume) =
      (Real.exp (-t * ‖p‖ ^ 2) : ℂ) *
        (conj (spatialFourier f p) * spatialFourier g p) := by
  have he (xy : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) :
      spatialHeatJoint t f g (p, xy) = (Real.exp (-t * ‖p‖ ^ 2) : ℂ) *
        ((Complex.exp (-(Complex.I * (inner ℝ (-p) xy.1 : ℂ))) * (f.1 xy.1 : ℂ)) *
          (Complex.exp (-(Complex.I * (inner ℝ p xy.2 : ℂ))) * (g.1 xy.2 : ℂ))) :=
    spatialHeatJoint_factor t f g p xy.1 xy.2
  simp_rw [he]
  rw [integral_const_mul, integral_prod_mul
    (fun x : EuclideanSpace ℝ (Fin 3) =>
      Complex.exp (-(Complex.I * (inner ℝ (-p) x : ℂ))) * (f.1 x : ℂ))
    (fun y : EuclideanSpace ℝ (Fin 3) =>
      Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) * (g.1 y : ℂ))]
  change _ * (spatialFourier f (-p) * spatialFourier g p) = _
  rw [spatialFourier_neg]

theorem integral_spatialHeatJoint_momentum {t : ℝ} (ht : 0 < t) (f g : SpatialTestFunction)
    (xy : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) :
    (∫ p : EuclideanSpace ℝ (Fin 3), spatialHeatJoint t f g (p, xy)) =
      (((2 * Real.pi) ^ 3 : ℝ) : ℂ) * (spatialHeatKernel t (xy.1 - xy.2) : ℂ) *
        (f.1 xy.1 : ℂ) * (g.1 xy.2 : ℂ) := by
  simp only [spatialHeatJoint]
  rw [integral_mul_const, integral_mul_const, integral_spatialHeatFourierIntegrand ht]
  simp only [spatialHeatKernel, Complex.ofReal_mul, Complex.ofReal_div]
  field_simp [Real.pi_ne_zero]

theorem spatialFourier_heat_convolution {t : ℝ} (ht : 0 < t) (f g : SpatialTestFunction) :
    (((2 * Real.pi) ^ 3 : ℝ) : ℂ)⁻¹ *
      (∫ p : EuclideanSpace ℝ (Fin 3), (Real.exp (-t * ‖p‖ ^ 2) : ℂ) *
        (conj (spatialFourier f p) * spatialFourier g p)) =
      ∫ xy, (spatialHeatKernel t (xy.1 - xy.2) : ℂ) *
        (f.1 xy.1 : ℂ) * (g.1 xy.2 : ℂ) ∂volume.prod volume := by
  have hj := integrable_spatialHeatJoint ht f g
  calc
    _ = (((2 * Real.pi) ^ 3 : ℝ) : ℂ)⁻¹ *
        ∫ p : EuclideanSpace ℝ (Fin 3), ∫ xy, spatialHeatJoint t f g (p,
          xy) ∂volume.prod volume := by
      simp_rw [integral_spatialHeatJoint_positions]
    _ = (((2 * Real.pi) ^ 3 : ℝ) : ℂ)⁻¹ *
        ∫ xy, (∫ p : EuclideanSpace ℝ (Fin 3), spatialHeatJoint t f g (p,
          xy)) ∂volume.prod volume := by
      rw [integral_integral_swap (f := fun p xy => spatialHeatJoint t f g (p, xy)) hj]
    _ = _ := by
      simp_rw [integral_spatialHeatJoint_momentum ht, mul_assoc]
      rw [integral_const_mul, ← mul_assoc,
        inv_mul_cancel₀ (by exact_mod_cast (show (2 * Real.pi) ^ 3 ≠ 0 by positivity)), one_mul]

end VacuumBellSeparation
