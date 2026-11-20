/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Function.L2Space
public import LeanPool.FastDynamo.Analysis.WholePlaneIntegralWeakDerivative
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.MeasureTheory.Integral.DivergenceTheorem

/-!
# Radial exponential envelopes on the whole plane

The whole-plane realization of the discontinuous Ponomarenko mode
(`lem:jump-horizontal-mode`) needs `L2` control of the exterior branch and of its derivatives,
which decay exponentially in the radius.  This module supplies the polar-coordinate estimate that
turns such pointwise bounds into planar `L2` bounds (used in `Local/HorizontalModeH1.lean`,
`Local/PonomarenkoExteriorDerivativeDecay.lean` and
`Local/PonomarenkoExteriorSecondPartialBounds.lean`).

The common point is the polar Jacobian.  A volume-preserving identification of `WholePlane` with
`R x R` gives the polar integral formula.  After
pullback to `(r, theta)` the square of a radial exponential envelope is multiplied by one power of
`r`, which remains integrable at infinity, so exterior pointwise exponential bounds become planar
`L2` bounds.

Nothing here depends on the Ponomarenko formulas: no `L2` or `H1` field is constructed, and no
particular mode is claimed to satisfy the pointwise envelope.

## Contents

* Whole-plane polar coordinates.
* Radial exponential envelopes on the whole plane: integrability transport through polar
  coordinates and the exterior radial envelope.
-/

@[expose] public section

/-!
## Whole-plane polar coordinates

This part supplies a volume-preserving identification of `WholePlane` with `ℝ × ℝ` and the
polar reconstruction map `wholePlanePolarMap`, through which the polar-coordinate integral
formula of Mathlib is applied below.  It constructs no `L2` or `H1` field.
-/

noncomputable section

namespace FastDynamo
namespace WholePlanePolarIBP

open MeasureTheory Set Filter Topology

/-! ## Whole-plane polar coordinates -/

/-- The canonical measurable equivalence from a coordinate pair to the repository's
Euclidean whole plane. -/
def prodEquivWholePlane : (ℝ × ℝ) ≃ᵐ WholePlane :=
  MeasurableEquiv.finTwoArrow.symm.trans (MeasurableEquiv.toLp 2 (Fin 2 → ℝ))

/-- The coordinate-pair identification sends the first factor to the first Cartesian coordinate
of the plane. -/
@[simp] theorem prodEquivWholePlane_apply_fst (p : ℝ × ℝ) :
    prodEquivWholePlane p (0 : Fin 2) = p.1 := by
  simp [prodEquivWholePlane]

/-- The coordinate-pair identification sends the second factor to the second Cartesian
coordinate of the plane. -/
@[simp] theorem prodEquivWholePlane_apply_snd (p : ℝ × ℝ) :
    prodEquivWholePlane p (1 : Fin 2) = p.2 := by
  simp [prodEquivWholePlane]

/-- The coordinate-pair identification preserves planar Lebesgue measure. -/
theorem measurePreserving_prodEquivWholePlane :
    MeasurePreserving prodEquivWholePlane := by
  exact (PiLp.volume_preserving_toLp (Fin 2)).comp
    (volume_preserving_finTwoArrow ℝ).symm

/-- Polar reconstruction as a point of the repository's `WholePlane`. -/
def wholePlanePolarMap (p : ℝ × ℝ) : WholePlane :=
  prodEquivWholePlane (polarCoord.symm p)

/-- First Cartesian coordinate of the polar reconstruction: `x₀ = r cos θ`. -/
@[simp] theorem wholePlanePolarMap_apply_zero (p : ℝ × ℝ) :
    wholePlanePolarMap p (0 : Fin 2) = p.1 * Real.cos p.2 := by
  simp [wholePlanePolarMap, polarCoord_symm_apply]

/-- Second Cartesian coordinate of the polar reconstruction: `x₁ = r sin θ`. -/
@[simp] theorem wholePlanePolarMap_apply_one (p : ℝ × ℝ) :
    wholePlanePolarMap p (1 : Fin 2) = p.1 * Real.sin p.2 := by
  simp [wholePlanePolarMap, polarCoord_symm_apply]

end WholePlanePolarIBP
end FastDynamo

/-!
## Radial exponential envelopes on the whole plane

This part supplies the reusable measure-theoretic estimate needed to turn exterior
pointwise exponential bounds into planar `L2` bounds.  The key point is the polar Jacobian:
after pullback to `(r, theta)`, the square of a radial exponential envelope is multiplied by
one power of `r`, which remains integrable at infinity.

The results are independent of the Ponomarenko formulas.  They make no assertion that any
particular mode satisfies the pointwise envelope.
-/

noncomputable section

namespace FastDynamo
namespace WholePlaneRadialExponential

open MeasureTheory Set
open WholePlanePolarIBP

/-! ## Integrability transport through polar coordinates -/

/-- Integrability counterpart of the polar-coordinate integral formula.  This theorem
records the polar Jacobian and also transports from coordinate pairs to the repository's
`WholePlane`. -/
theorem integrableOn_comp_wholePlanePolarMap_iff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : WholePlane → E) :
    IntegrableOn (fun p : ℝ × ℝ ↦ p.1 • f (wholePlanePolarMap p))
        polarCoord.target ↔
      Integrable f := by
  let g : ℝ × ℝ → E := fun q ↦ f (prodEquivWholePlane q)
  have hchange :
      IntegrableOn g (polarCoord.symm '' polarCoord.target) ↔
        IntegrableOn
          (fun p : ℝ × ℝ ↦
            |(fderivPolarCoordSymm p).det| • g (polarCoord.symm p))
          polarCoord.target :=
    integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
      polarCoord.open_target.measurableSet
      (fun p _ ↦ (hasFDerivAt_polarCoord_symm p).hasFDerivWithinAt)
      polarCoord.symm.injOn g
  rw [polarCoord.symm_image_target_eq_source] at hchange
  calc
    IntegrableOn (fun p : ℝ × ℝ ↦ p.1 • f (wholePlanePolarMap p))
        polarCoord.target ↔
        IntegrableOn
          (fun p : ℝ × ℝ ↦
            |(fderivPolarCoordSymm p).det| • g (polarCoord.symm p))
          polarCoord.target := by
      apply integrableOn_congr_fun
      · intro p hp
        have hp0 : 0 < p.1 := hp.1
        change p.1 • f (wholePlanePolarMap p) =
          |(fderivPolarCoordSymm p).det| • g (polarCoord.symm p)
        simp only [det_fderivPolarCoordSymm, abs_of_pos hp0, g,
          wholePlanePolarMap]
      · exact polarCoord.open_target.measurableSet
    _ ↔ IntegrableOn g polarCoord.source := hchange.symm
    _ ↔ IntegrableOn g (Set.univ : Set (ℝ × ℝ)) :=
      integrableOn_congr_set_ae polarCoord_source_ae_eq_univ
    _ ↔ Integrable g := integrableOn_univ
    _ ↔ Integrable f := by
      change Integrable (f ∘ prodEquivWholePlane) volume ↔ Integrable f volume
      exact measurePreserving_prodEquivWholePlane.integrable_comp_emb
        prodEquivWholePlane.measurableEmbedding

/-- The Euclidean norm of the repository's polar reconstruction is the absolute value of the
radial coordinate. -/
@[simp] theorem norm_wholePlanePolarMap (p : ℝ × ℝ) :
    ‖wholePlanePolarMap p‖ = |p.1| := by
  rw [EuclideanSpace.norm_eq]
  simp only [Fin.sum_univ_two, wholePlanePolarMap_apply_zero,
    wholePlanePolarMap_apply_one, Real.norm_eq_abs, sq_abs]
  rw [← Real.sqrt_sq_eq_abs]
  congr 1
  nlinarith [Real.sin_sq_add_cos_sq p.2]

/-! ## The exterior radial envelope -/

/-- A radial exponential envelope normalized to equal one at radius one. -/
def radialExponentialEnvelope (a : ℝ) (y : WholePlane) : ℝ :=
  Real.exp (-a * (‖y‖ - 1))

/-- The closed exterior of the unit disk. -/
def unitExterior : Set WholePlane :=
  {y | 1 ≤ ‖y‖}

/-- The closed exterior `{y | 1 ≤ ‖y‖}` of the unit disk is measurable. -/
theorem measurableSet_unitExterior : MeasurableSet unitExterior := by
  exact measurableSet_le measurable_const continuous_norm.measurable

/-- For `a > 0` the polar integrand `r ↦ r·e^{-2a(r-1)}` obtained from squaring a radial
exponential envelope is integrable on `(0, ∞)`: the single Jacobian power of `r` is beaten by the
exponential decay.  This is what makes exterior exponential bounds give `L²` bounds. -/
private theorem integrableOn_radialWeight_sq
    {a : ℝ} (ha : 0 < a) :
    IntegrableOn
      (fun r : ℝ ↦ r * (Real.exp (-a * (r - 1))) ^ 2)
      (Ioi 0) := by
  have hbase : IntegrableOn
      (fun r : ℝ ↦ r ^ (1 : ℝ) * Real.exp (-(2 * a) * r ^ (1 : ℝ)))
      (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow
      (by norm_num : (-1 : ℝ) < 1) zero_lt_one (mul_pos two_pos ha)
  have hscaled : IntegrableOn
      (fun r : ℝ ↦ Real.exp (2 * a) *
        (r ^ (1 : ℝ) * Real.exp (-(2 * a) * r ^ (1 : ℝ))))
      (Ioi 0) :=
    hbase.const_mul (Real.exp (2 * a))
  refine hscaled.congr_fun ?_ measurableSet_Ioi
  intro r hr
  simp only [Real.rpow_one]
  rw [← Real.exp_nat_mul]
  change Real.exp (2 * a) * (r * Real.exp (-(2 * a) * r)) =
    r * Real.exp (2 * (-a * (r - 1)))
  rw [show (2 : ℝ) * (-a * (r - 1)) = 2 * a + (-(2 * a) * r) by ring]
  rw [Real.exp_add]
  ring

/-- The square of the normalized radial exponential is integrable on the full plane.  This
slightly stronger form is convenient: restriction to any measurable exterior region then
costs no additional estimate. -/
theorem integrable_sq_radialExponentialEnvelope
    {a : ℝ} (ha : 0 < a) :
    Integrable (fun y : WholePlane ↦ (radialExponentialEnvelope a y) ^ 2) := by
  have hr := integrableOn_radialWeight_sq ha
  have htheta : IntegrableOn (fun _ : ℝ ↦ (1 : ℝ))
      (Ioo (-Real.pi) Real.pi) :=
    integrableOn_const measure_Ioo_lt_top.ne
  have hprod : IntegrableOn
      (fun p : ℝ × ℝ ↦
        (p.1 * (Real.exp (-a * (p.1 - 1))) ^ 2) * (1 : ℝ))
      (Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi) := by
    rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
    exact hr.integrable.mul_prod htheta.integrable
  apply (integrableOn_comp_wholePlanePolarMap_iff
    (fun y : WholePlane ↦ (radialExponentialEnvelope a y) ^ 2)).mp
  change IntegrableOn
    (fun p : ℝ × ℝ ↦ p.1 •
      (radialExponentialEnvelope a (wholePlanePolarMap p)) ^ 2)
    (Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi)
  refine hprod.congr_fun ?_ (measurableSet_Ioi.prod measurableSet_Ioo)
  intro p hp
  have hp0 : 0 < p.1 := hp.1
  simp only [radialExponentialEnvelope, norm_wholePlanePolarMap,
    abs_of_pos hp0, smul_eq_mul, mul_one]

/-- The normalized radial exponential itself belongs to planar `L2`. -/
theorem memLp_two_radialExponentialEnvelope
    {a : ℝ} (ha : 0 < a) :
    MemLp (radialExponentialEnvelope a) 2 volume := by
  have hcontinuous : Continuous (radialExponentialEnvelope a) := by
    unfold radialExponentialEnvelope
    fun_prop
  exact (memLp_two_iff_integrable_sq
    hcontinuous.aestronglyMeasurable).2
      (integrable_sq_radialExponentialEnvelope ha)

/-- Exterior restriction of the radial exponential's `L2` bound. -/
theorem memLp_two_radialExponentialEnvelope_unitExterior
    {a : ℝ} (ha : 0 < a) :
    MemLp (radialExponentialEnvelope a) 2
      (volume.restrict unitExterior) :=
  (memLp_two_radialExponentialEnvelope ha).restrict unitExterior

/-- Any a.e. strongly measurable exterior field dominated by a constant multiple of the
radial exponential envelope belongs to exterior `L2`.  The constant need not be assumed
nonnegative: the pointwise upper bound itself is the only condition used. -/
theorem memLp_two_unitExterior_of_norm_le_radialExponential
    {F : Type*} [NormedAddCommGroup F]
    {f : WholePlane → F} {a C : ℝ}
    (ha : 0 < a)
    (hf : AEStronglyMeasurable f (volume.restrict unitExterior))
    (hbound : ∀ᵐ y ∂volume.restrict unitExterior,
      ‖f y‖ ≤ C * radialExponentialEnvelope a y) :
    MemLp f 2 (volume.restrict unitExterior) := by
  exact ((memLp_two_radialExponentialEnvelope_unitExterior ha).const_mul C).mono'
    hf hbound

end WholePlaneRadialExponential
end FastDynamo
