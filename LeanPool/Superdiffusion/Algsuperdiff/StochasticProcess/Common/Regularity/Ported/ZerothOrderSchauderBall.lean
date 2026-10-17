/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.Regularity.Ported.ZerothOrderSchauder

/-!
# ZerothOrderSchauderBall

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Interior Schauder estimate on an arbitrary Euclidean ball

The small-contrast chain proves its interior Hölder estimate on the fixed unit
ball `smallContrastUnitBall d = euclideanBall 0 1`, concluding on the
concentric ball of radius `1/2`.  Every consumer works instead on a ball
`euclideanBall x₀ r` sitting inside a given open set, so the estimate has to be
transported along the affine chart

`ballChart x₀ r : x ↦ r • x + x₀`,

which carries `euclideanBall 0 s` onto `euclideanBall x₀ (r * s)` and pushes
Lebesgue measure to `r ^ d` times Lebesgue measure.  The normalization used for
the transported solution is `v x = r⁻¹ * u (r • x + x₀)`, so that
`∇v x = ∇u (r • x + x₀)`.

The three scalings that produce the explicit radius powers of the conclusion
are isolated as named theorems:

* `vectorLpSizeOn_two_ballTransfer_grad` — the gradient `L²` size scales by
  `r ^ (-(d : ℝ)/2)`;
* `scalarLInfSizeOn_ballScalarSource` — the transported scalar source has
  `L^∞` size `r` times the original;
* `holderBound_of_ballTransfer` — the Hölder pull-back
  `|u x - u y| = r * |v (r⁻¹ • (x - x₀)) - v (r⁻¹ • (y - x₀))|`.

The vector source of the transported equation is `0`, so the factor
`(1 - alpha)⁻¹` carried by `smallContrastDataSize` multiplies `0` and does not
appear in the constant of the conclusion.
-/

namespace Algsuperdiff.StochasticProcess.Common.Regularity.Ported

open MeasureTheory HCPolySupport Filter Topology
open scoped Pointwise ENNReal
open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## The affine chart -/

/-- The affine chart carrying the unit ball onto `euclideanBall x₀ r`. -/
def ballChart (x₀ : Vec d) (r : ℝ) : Vec d → Vec d := fun x => r • x + x₀

/-- The inverse of `ballChart x₀ r`. -/
def ballChartInv (x₀ : Vec d) (r : ℝ) : Vec d → Vec d := fun y => r⁻¹ • (y - x₀)

@[simp] theorem ballChart_apply (x₀ : Vec d) (r : ℝ) (x : Vec d) :
    ballChart x₀ r x = r • x + x₀ := rfl

@[simp] theorem ballChartInv_apply (x₀ : Vec d) (r : ℝ) (y : Vec d) :
    ballChartInv x₀ r y = r⁻¹ • (y - x₀) := rfl

theorem ballChart_ballChartInv (x₀ : Vec d) {r : ℝ} (hr : 0 < r) (y : Vec d) :
    ballChart x₀ r (ballChartInv x₀ r y) = y := by
  ext i
  simp [ballChart, ballChartInv, hr.ne', sub_eq_add_neg]

/-- Membership in a concentric ball is invariant under the chart, with radii
scaled by `r`. -/
theorem ballChart_mem_euclideanBall_iff (x₀ : Vec d) {r s : ℝ} (hr : 0 < r)
    (x : Vec d) :
    ballChart x₀ r x ∈ euclideanBall x₀ (r * s) ↔
      x ∈ euclideanBall (0 : Vec d) s := by
  have hkey : euclideanSqDist (r • x + x₀) x₀ = r ^ 2 * euclideanSqDist x 0 :=
    euclideanSqDist_affine_center x₀ x r
  have hr2 : 0 < r ^ 2 := by positivity
  constructor
  · intro hx
    have hx' : r ^ 2 * euclideanSqDist x 0 < r ^ 2 * s ^ 2 := by
      have := hx
      rw [show (euclideanBall x₀ (r * s)) = {z | euclideanSqDist z x₀ < (r * s) ^ 2} from rfl]
        at this
      simpa [ballChart, hkey, mul_pow] using this
    exact lt_of_mul_lt_mul_left (by linarith only [hx']) hr2.le
  · intro hx
    have hx' : euclideanSqDist x 0 < s ^ 2 := hx
    change euclideanSqDist (ballChart x₀ r x) x₀ < (r * s) ^ 2
    simpa [ballChart, hkey, mul_pow] using
      (mul_lt_mul_of_pos_left hx' hr2)

theorem measurableEmbedding_ballChart (x₀ : Vec d) {r : ℝ} (hr : 0 < r) :
    MeasurableEmbedding (ballChart (d := d) x₀ r) := by
  have h : ballChart (d := d) x₀ r =
      ((Homeomorph.smulOfNeZero r hr.ne').trans (Homeomorph.addRight x₀) :
        Vec d ≃ₜ Vec d) := rfl
  rw [h]
  exact (Homeomorph.measurableEmbedding _)

theorem continuous_ballChartInv (x₀ : Vec d) (r : ℝ) :
    Continuous (ballChartInv (d := d) x₀ r) :=
  (continuous_const_smul _).comp (continuous_id.sub continuous_const)

/-! ## Measure transport along the chart -/

/-- The chart pushes Lebesgue measure restricted to the unit ball forward to
`(r ^ d)⁻¹` times Lebesgue measure restricted to `euclideanBall x₀ r`. -/
theorem map_ballChart_volume_restrict (x₀ : Vec d) {r : ℝ} (hr : 0 < r) :
    Measure.map (ballChart (d := d) x₀ r)
        (volume.restrict (smallContrastUnitBall d)) =
      ENNReal.ofReal ((r ^ d)⁻¹) • volume.restrict (euclideanBall x₀ r) := by
  have hsmul : Measurable (fun x : Vec d => r • x) := measurable_const_smul r
  have hadd : Measurable (fun x : Vec d => x + x₀) := measurable_add_const x₀
  have hcomp : Measure.map (ballChart (d := d) x₀ r)
      (volume.restrict (smallContrastUnitBall d)) =
      Measure.map (fun x : Vec d => x + x₀)
        (Measure.map (fun x : Vec d => r • x)
          (volume.restrict (smallContrastUnitBall d))) := by
    rw [Measure.map_map hadd hsmul]
    rfl
  have hdil := map_smul_volume_restrict (d := d) hr (smallContrastUnitBall d)
  have htrans :=
    (measurePreserving_addRight_restrict_translateSet (d := d) x₀
      (r • smallContrastUnitBall d)).map_eq
  have hball : translateSet x₀ (r • smallContrastUnitBall d) = euclideanBall x₀ r :=
    (euclideanBall_eq_translateSet_smul_unit_of_pos x₀ hr).symm
  rw [hcomp, hdil, Measure.map_smul _ hadd.aemeasurable, htrans, hball]

/-- Change of variables for a set integral over the chart. -/
theorem setIntegral_comp_ballChart (x₀ : Vec d) {r : ℝ} (hr : 0 < r)
    (F : Vec d → ℝ) :
    ∫ x in smallContrastUnitBall d, F (r • x + x₀) ∂volume =
      (r ^ d)⁻¹ * ∫ y in euclideanBall x₀ r, F y ∂volume := by
  have hemb := measurableEmbedding_ballChart (d := d) x₀ hr
  have h1 : ∫ y, F y ∂(Measure.map (ballChart (d := d) x₀ r)
        (volume.restrict (smallContrastUnitBall d))) =
      ∫ x in smallContrastUnitBall d, F (r • x + x₀) ∂volume :=
    hemb.integral_map F
  rw [← h1, map_ballChart_volume_restrict x₀ hr, integral_smul_measure]
  have hpow : (0 : ℝ) < r ^ d := pow_pos hr d
  simp [ENNReal.toReal_ofReal (le_of_lt (inv_pos.mpr hpow)), smul_eq_mul]

/-- The inverse chart pushes Lebesgue measure restricted to `euclideanBall x₀ r`
forward to `r ^ d` times Lebesgue measure restricted to the unit ball. -/
theorem map_ballChartInv_volume_restrict (x₀ : Vec d) {r : ℝ} (hr : 0 < r) :
    Measure.map (ballChartInv (d := d) x₀ r)
        (volume.restrict (euclideanBall x₀ r)) =
      ENNReal.ofReal (r ^ d) • volume.restrict (smallContrastUnitBall d) := by
  have hsmul : Measurable (fun y : Vec d => r⁻¹ • y) := measurable_const_smul r⁻¹
  have hsub : Measurable (fun y : Vec d => y - x₀) := measurable_sub_const x₀
  have hball : euclideanBall x₀ r = translateSet x₀ (r • smallContrastUnitBall d) :=
    euclideanBall_eq_translateSet_smul_unit_of_pos x₀ hr
  have hcomp : Measure.map (ballChartInv (d := d) x₀ r)
      (volume.restrict (euclideanBall x₀ r)) =
      Measure.map (fun y : Vec d => r⁻¹ • y)
        (Measure.map (fun y : Vec d => y - x₀)
          (volume.restrict (euclideanBall x₀ r))) := by
    rw [Measure.map_map hsmul hsub]
    rfl
  have htrans : Measure.map (fun y : Vec d => y - x₀)
      (volume.restrict (euclideanBall x₀ r)) =
      volume.restrict (r • smallContrastUnitBall d) := by
    rw [hball]
    exact (measurePreserving_subRight_restrict_translateSet (d := d) x₀
      (r • smallContrastUnitBall d)).map_eq
  have hdil := map_smul_volume_restrict (d := d) (inv_pos.mpr hr)
    (r • smallContrastUnitBall d)
  have hpre : r⁻¹ • (r • smallContrastUnitBall d) = smallContrastUnitBall d := by
    rw [smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  have hconst : ((r⁻¹ ^ d)⁻¹) = r ^ d := by
    rw [inv_pow, inv_inv]
  rw [hcomp, htrans, hdil, hpre, hconst]

/-- The chart is quasi measure preserving, so a.e. statements on
`euclideanBall x₀ r` pull back to the unit ball. -/
theorem quasiMeasurePreserving_ballChart (x₀ : Vec d) {r : ℝ} (hr : 0 < r) :
    Measure.QuasiMeasurePreserving (ballChart (d := d) x₀ r)
      (volume.restrict (smallContrastUnitBall d))
      (volume.restrict (euclideanBall x₀ r)) := by
  refine ⟨(measurableEmbedding_ballChart (d := d) x₀ hr).measurable, ?_⟩
  rw [map_ballChart_volume_restrict x₀ hr]
  exact Measure.smul_absolutelyContinuous

/-- The inverse chart is quasi measure preserving, so a.e. statements on the
unit ball push forward to `euclideanBall x₀ r`. -/
theorem quasiMeasurePreserving_ballChartInv (x₀ : Vec d) {r : ℝ} (hr : 0 < r) :
    Measure.QuasiMeasurePreserving (ballChartInv (d := d) x₀ r)
      (volume.restrict (euclideanBall x₀ r))
      (volume.restrict (smallContrastUnitBall d)) := by
  refine ⟨(continuous_ballChartInv (d := d) x₀ r).measurable, ?_⟩
  rw [map_ballChartInv_volume_restrict x₀ hr]
  exact Measure.smul_absolutelyContinuous

/-! ## Transport of Sobolev witnesses -/

/-- Transport an `H¹` witness along an equality of domains. -/
def h1OfSetEq {U W : Set (Vec d)} (h : U = W) (u : H1Function U) :
    H1Function W := by
  subst h; exact u

@[simp] theorem h1OfSetEq_toFun {U W : Set (Vec d)} (h : U = W)
    (u : H1Function U) : (h1OfSetEq h u).toFun = u.toFun := by
  subst h; rfl

@[simp] theorem h1OfSetEq_grad {U W : Set (Vec d)} (h : U = W)
    (u : H1Function U) : (h1OfSetEq h u).grad = u.grad := by
  subst h; rfl

/-- Transport an `H¹₀` witness along an equality of domains. -/
def h10OfSetEq {U W : Set (Vec d)} (h : U = W) (u : H10Function U) :
    H10Function W := by
  subst h; exact u

@[simp] theorem h10OfSetEq_toH1Function {U W : Set (Vec d)} (h : U = W)
    (u : H10Function U) :
    (h10OfSetEq h u).toH1Function = h1OfSetEq h u.toH1Function := by
  subst h; rfl

/-- The unit-ball normalization `v x = r⁻¹ * u (r • x + x₀)` of an `H¹`
function on `euclideanBall x₀ r`.  With this normalization the gradient is the
plain pull-back of the gradient of `u`. -/
def ballTransfer (x₀ : Vec d) {r : ℝ} (hr : 0 < r)
    (u : H1Function (euclideanBall x₀ r)) : H1Function (smallContrastUnitBall d) :=
  H1Function.undilateSet (U := smallContrastUnitBall d) hr rfl
    (H1Function.untranslate x₀
      (h1OfSetEq (euclideanBall_eq_translateSet_smul_unit_of_pos x₀ hr) u))

@[simp] theorem ballTransfer_toFun (x₀ : Vec d) {r : ℝ} (hr : 0 < r)
    (u : H1Function (euclideanBall x₀ r)) (x : Vec d) :
    (ballTransfer x₀ hr u).toFun x = r⁻¹ * u.toFun (r • x + x₀) := by
  simp only [ballTransfer, H1Function.undilateSet_toFun, H1Function.untranslate_toFun]
  exact congrArg (fun f => r⁻¹ * f (r • x + x₀))
    (h1OfSetEq_toFun (euclideanBall_eq_translateSet_smul_unit_of_pos x₀ hr) u)

@[simp] theorem ballTransfer_grad (x₀ : Vec d) {r : ℝ} (hr : 0 < r)
    (u : H1Function (euclideanBall x₀ r)) (x : Vec d) :
    (ballTransfer x₀ hr u).grad x = u.grad (r • x + x₀) := by
  simp only [ballTransfer, H1Function.undilateSet_grad, H1Function.untranslate_grad]
  exact congrFun
    (h1OfSetEq_grad (euclideanBall_eq_translateSet_smul_unit_of_pos x₀ hr) u) (r • x + x₀)

/-- The test-function direction of the chart: an `H¹₀` witness on the unit ball
becomes an `H¹₀` witness on `euclideanBall x₀ r`. -/
def ballTestTransfer (x₀ : Vec d) {r : ℝ} (hr : 0 < r)
    (psi : H10Function (smallContrastUnitBall d)) :
    H10Function (euclideanBall x₀ r) :=
  h10OfSetEq (euclideanBall_eq_translateSet_smul_unit_of_pos x₀ hr).symm
    (H10Function.translate
      (H10Function.unscale (U := r • smallContrastUnitBall d) (inv_pos.mpr hr)
        (h10OfSetEq (by
          rw [smul_smul, inv_mul_cancel₀ hr.ne', one_smul]) psi)) x₀)

@[simp] theorem ballTestTransfer_toFun (x₀ : Vec d) {r : ℝ} (hr : 0 < r)
    (psi : H10Function (smallContrastUnitBall d)) (y : Vec d) :
    (ballTestTransfer x₀ hr psi).toH1Function.toFun y =
      psi.toH1Function.toFun (r⁻¹ • (y - x₀)) := by
  have hproof2 : smallContrastUnitBall d = r⁻¹ • (r • smallContrastUnitBall d) := by
    rw [smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  have step1 :
      (h10OfSetEq (euclideanBall_eq_translateSet_smul_unit_of_pos x₀ hr).symm
          ((H10Function.unscale (inv_pos.mpr hr) (h10OfSetEq hproof2 psi)).translate
            x₀)).toH1Function.toFun y
        = ((H10Function.unscale (inv_pos.mpr hr) (h10OfSetEq hproof2 psi)).translate
            x₀).toH1Function.toFun y :=
    (congrArg (fun v => v.toFun y)
        (h10OfSetEq_toH1Function (euclideanBall_eq_translateSet_smul_unit_of_pos x₀ hr).symm
          ((H10Function.unscale (inv_pos.mpr hr) (h10OfSetEq hproof2 psi)).translate x₀))).trans
      (congrFun
        (h1OfSetEq_toFun (euclideanBall_eq_translateSet_smul_unit_of_pos x₀ hr).symm
          ((H10Function.unscale (inv_pos.mpr hr) (h10OfSetEq hproof2 psi)).translate
            x₀).toH1Function)
        y)
  have step2 :
      ((H10Function.unscale (inv_pos.mpr hr) (h10OfSetEq hproof2 psi)).translate
          x₀).toH1Function.toFun y
        = psi.toH1Function.toFun (r⁻¹ • (y - x₀)) :=
    (congrArg (fun v => v.toFun (r⁻¹ • (y - x₀))) (h10OfSetEq_toH1Function hproof2 psi)).trans
      (congrFun (h1OfSetEq_toFun hproof2 psi.toH1Function) (r⁻¹ • (y - x₀)))
  exact step1.trans step2

@[simp] theorem ballTestTransfer_grad (x₀ : Vec d) {r : ℝ} (hr : 0 < r)
    (psi : H10Function (smallContrastUnitBall d)) (y : Vec d) :
    (ballTestTransfer x₀ hr psi).toH1Function.grad y =
      r⁻¹ • psi.toH1Function.grad (r⁻¹ • (y - x₀)) := by
  have hproof2 : smallContrastUnitBall d = r⁻¹ • (r • smallContrastUnitBall d) := by
    rw [smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  have step1 :
      (h10OfSetEq (euclideanBall_eq_translateSet_smul_unit_of_pos x₀ hr).symm
          ((H10Function.unscale (inv_pos.mpr hr) (h10OfSetEq hproof2 psi)).translate
            x₀)).toH1Function.grad y
        = ((H10Function.unscale (inv_pos.mpr hr) (h10OfSetEq hproof2 psi)).translate
            x₀).toH1Function.grad y :=
    (congrArg (fun v => v.grad y)
        (h10OfSetEq_toH1Function (euclideanBall_eq_translateSet_smul_unit_of_pos x₀ hr).symm
          ((H10Function.unscale (inv_pos.mpr hr) (h10OfSetEq hproof2 psi)).translate x₀))).trans
      (congrFun
        (h1OfSetEq_grad (euclideanBall_eq_translateSet_smul_unit_of_pos x₀ hr).symm
          ((H10Function.unscale (inv_pos.mpr hr) (h10OfSetEq hproof2 psi)).translate
            x₀).toH1Function)
        y)
  have step2 :
      ((H10Function.unscale (inv_pos.mpr hr) (h10OfSetEq hproof2 psi)).translate
          x₀).toH1Function.grad y
        = r⁻¹ • psi.toH1Function.grad (r⁻¹ • (y - x₀)) :=
    congrArg (r⁻¹ • ·)
      ((congrArg (fun v => v.grad (r⁻¹ • (y - x₀))) (h10OfSetEq_toH1Function hproof2 psi)).trans
        (congrFun (h1OfSetEq_grad hproof2 psi.toH1Function) (r⁻¹ • (y - x₀))))
  exact step1.trans step2

/-! ## The transported data and its scalings -/

/-- The coefficient field read in the chart. -/
def ballCoeff (a : CoeffField d) (x₀ : Vec d) (r : ℝ) : CoeffField d :=
  fun x => a (ballChart x₀ r x)

/-- The scalar source of the transported equation. -/
def ballScalarSource (g : Vec d → ℝ) (x₀ : Vec d) (r : ℝ) : Vec d → ℝ :=
  fun x => r * g (ballChart x₀ r x)

theorem measurable_ballCoeff {a : CoeffField d} (ha : Measurable a)
    (x₀ : Vec d) {r : ℝ} (hr : 0 < r) :
    Measurable (ballCoeff a x₀ r) :=
  ha.comp (measurableEmbedding_ballChart (d := d) x₀ hr).measurable

/-- The identity distance of the coefficient transfers to the unit ball,
because the chart pushes Lebesgue measure to a positive multiple of Lebesgue
measure. -/
theorem coefficientIdentityDistanceLE_ballCoeff {a : CoeffField d}
    (x₀ : Vec d) {r delta : ℝ} (hr : 0 < r)
    (ha : CoefficientIdentityDistanceLE (euclideanBall x₀ r) a delta) :
    CoefficientIdentityDistanceLE (smallContrastUnitBall d)
      (ballCoeff a x₀ r) delta :=
  (quasiMeasurePreserving_ballChart (d := d) x₀ hr).ae ha

/-- The `L^p` seminorm read in the chart. -/
theorem eLpNorm_comp_ballChart (x₀ : Vec d) {r : ℝ} (hr : 0 < r)
    (F : Vec d → ℝ) (p : ℝ≥0∞) :
    eLpNorm (fun x => F (ballChart x₀ r x)) p
        (volume.restrict (smallContrastUnitBall d)) =
      ENNReal.ofReal ((r ^ d)⁻¹) ^ (1 / p).toReal *
        eLpNorm F p (volume.restrict (euclideanBall x₀ r)) := by
  have hemb := measurableEmbedding_ballChart (d := d) x₀ hr
  have hne : ENNReal.ofReal ((r ^ d)⁻¹) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    positivity
  calc
    eLpNorm (fun x => F (ballChart x₀ r x)) p
        (volume.restrict (smallContrastUnitBall d))
        = eLpNorm F p (Measure.map (ballChart (d := d) x₀ r)
            (volume.restrict (smallContrastUnitBall d))) :=
          (hemb.eLpNorm_map_measure).symm
    _ = eLpNorm F p (ENNReal.ofReal ((r ^ d)⁻¹) •
            volume.restrict (euclideanBall x₀ r)) := by
          rw [map_ballChart_volume_restrict x₀ hr]
    _ = ENNReal.ofReal ((r ^ d)⁻¹) ^ (1 / p).toReal *
            eLpNorm F p (volume.restrict (euclideanBall x₀ r)) := by
          rw [eLpNorm_smul_measure_of_ne_zero hne]
          rfl

/-- Membership in `L^p` read in the chart. -/
theorem memLp_comp_ballChart (x₀ : Vec d) {r : ℝ} (hr : 0 < r)
    {F : Vec d → ℝ} {p : ℝ≥0∞}
    (hF : MemLp F p (volume.restrict (euclideanBall x₀ r))) :
    MemLp (fun x => F (ballChart x₀ r x)) p
      (volume.restrict (smallContrastUnitBall d)) := by
  have hemb := measurableEmbedding_ballChart (d := d) x₀ hr
  have hmap : MemLp F p (Measure.map (ballChart (d := d) x₀ r)
      (volume.restrict (smallContrastUnitBall d))) := by
    rw [map_ballChart_volume_restrict x₀ hr]
    exact hF.smul_measure ENNReal.ofReal_ne_top
  exact hemb.memLp_map_measure_iff.mp hmap

/-- **First scaling.** The gradient `L²` size of the transported solution. -/
theorem vectorLpSizeOn_two_ballTransfer_grad (x₀ : Vec d) {r : ℝ} (hr : 0 < r)
    (u : H1Function (euclideanBall x₀ r)) :
    vectorLpSizeOn (smallContrastUnitBall d) 2 (ballTransfer x₀ hr u).grad =
      r ^ (-(d : ℝ) / 2) * vectorLpSizeOn (euclideanBall x₀ r) 2 u.grad := by
  have hrewrite :
      (fun x => euclideanNorm ((ballTransfer x₀ hr u).grad x)) =
        fun x => (fun y => euclideanNorm (u.grad y)) (ballChart x₀ r x) := by
    funext x
    simp [ballChart]
  have htwo : ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) := by
    simp [ENNReal.ofReal_ofNat]
  have hexp : ((1 : ℝ≥0∞) / 2).toReal = (2 : ℝ)⁻¹ := by
    rw [ENNReal.toReal_div]
    norm_num
  have hpow : (0 : ℝ) < r ^ d := pow_pos hr d
  have hposinv : (0 : ℝ) < (r ^ d)⁻¹ := inv_pos.mpr hpow
  have hscale :
      (ENNReal.ofReal ((r ^ d)⁻¹) ^ ((1 : ℝ≥0∞) / 2).toReal).toReal =
        r ^ (-(d : ℝ) / 2) := by
    rw [hexp, ENNReal.ofReal_rpow_of_nonneg hposinv.le (by norm_num),
      ENNReal.toReal_ofReal (Real.rpow_nonneg hposinv.le _)]
    have hbase : ((r : ℝ) ^ d)⁻¹ = r ^ (-(d : ℝ)) := by
      rw [Real.rpow_neg hr.le, Real.rpow_natCast]
    rw [hbase, ← Real.rpow_mul hr.le]
    norm_num
    congr 1
    ring
  unfold vectorLpSizeOn
  rw [hrewrite, htwo,
    eLpNorm_comp_ballChart x₀ hr (fun y => euclideanNorm (u.grad y)) 2,
    ENNReal.toReal_mul, hscale]

/-- **Second scaling.** The `L^∞` size of the transported scalar source. -/
theorem scalarLInfSizeOn_ballScalarSource (x₀ : Vec d) {r : ℝ} (hr : 0 < r)
    (g : Vec d → ℝ) :
    scalarLInfSizeOn (smallContrastUnitBall d) (ballScalarSource g x₀ r) =
      r * scalarLInfSizeOn (euclideanBall x₀ r) g := by
  have hfun : ballScalarSource g x₀ r =
      r • fun x => g (ballChart x₀ r x) := by
    funext x
    simp [ballScalarSource, Pi.smul_apply, smul_eq_mul]
  have hexp : ((1 : ℝ≥0∞) / ⊤).toReal = 0 := by simp
  unfold scalarLInfSizeOn
  rw [hfun, eLpNorm_const_smul,
    eLpNorm_comp_ballChart x₀ hr (fun y => g y) ⊤, hexp,
    ENNReal.rpow_zero, one_mul, Real.enorm_eq_ofReal hr.le, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hr.le]

/-- The transported scalar source is bounded when the original one is. -/
theorem memScalarLInfOn_ballScalarSource (x₀ : Vec d) {r : ℝ} (hr : 0 < r)
    {g : Vec d → ℝ} (hg : MemScalarLInfOn (euclideanBall x₀ r) g) :
    MemScalarLInfOn (smallContrastUnitBall d) (ballScalarSource g x₀ r) := by
  have hcomp : MemLp (fun x => g (ballChart x₀ r x)) (⊤ : ℝ≥0∞)
      (volume.restrict (smallContrastUnitBall d)) :=
    memLp_comp_ballChart x₀ hr hg
  have hfun : ballScalarSource g x₀ r =
      r • fun x => g (ballChart x₀ r x) := by
    funext x
    simp [ballScalarSource, Pi.smul_apply, smul_eq_mul]
  rw [MemScalarLInfOn, hfun]
  exact hcomp.const_smul r

/-! ## The transported equation -/

/-- The zeroth-order weak equation with a vanishing vector source transfers to
the unit ball, with coefficient `ballCoeff` and scalar source
`ballScalarSource`. -/
theorem isMatrixDivFormWeakSolutionZerothOrderOn_ballTransfer
    {a : CoeffField d} (x₀ : Vec d) {r : ℝ} (hr : 0 < r)
    {u : H1Function (euclideanBall x₀ r)} {g : Vec d → ℝ}
    (hu : IsMatrixDivFormWeakSolutionZerothOrderOn a (euclideanBall x₀ r) u g 0) :
    IsMatrixDivFormWeakSolutionZerothOrderOn (ballCoeff a x₀ r)
      (smallContrastUnitBall d) (ballTransfer x₀ hr u)
      (ballScalarSource g x₀ r) 0 := by
  intro psi
  have hrd : (0 : ℝ) < r ^ d := pow_pos hr d
  set A : ℝ := ∫ y in euclideanBall x₀ r,
    vecDot (matVecMul (a y) (u.grad y))
      (psi.toH1Function.grad (r⁻¹ • (y - x₀))) ∂volume with hA
  set B : ℝ := ∫ y in euclideanBall x₀ r,
    g y * psi.toH1Function.toFun (r⁻¹ • (y - x₀)) ∂volume with hB
  have hphi := hu (ballTestTransfer x₀ hr psi)
  have hsmulInv : ∀ x : Vec d, r⁻¹ • (r • x) = x := by
    intro x
    rw [smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  simp only [ballTestTransfer_grad, ballTestTransfer_toFun, Pi.zero_apply,
    vecDot_zero_left, integral_zero, sub_zero, vecDot_smul_right, mul_zero] at hphi
  have hkey : r⁻¹ * A = B := by
    rw [hA, hB, ← integral_const_mul]
    exact hphi
  have hL : ∫ x in smallContrastUnitBall d,
      vecDot (matVecMul (ballCoeff a x₀ r x) ((ballTransfer x₀ hr u).grad x))
        (psi.toH1Function.grad x) ∂volume = (r ^ d)⁻¹ * A := by
    have hcov := setIntegral_comp_ballChart x₀ hr
      (fun y => vecDot (matVecMul (a y) (u.grad y))
        (psi.toH1Function.grad (r⁻¹ • (y - x₀))))
    have hfun : (fun x : Vec d =>
        vecDot (matVecMul (a (r • x + x₀)) (u.grad (r • x + x₀)))
          (psi.toH1Function.grad (r⁻¹ • ((r • x + x₀) - x₀)))) =
        fun x : Vec d =>
        vecDot (matVecMul (ballCoeff a x₀ r x) ((ballTransfer x₀ hr u).grad x))
          (psi.toH1Function.grad x) := by
      funext x
      simp [ballCoeff, ballChart, hsmulInv]
    rw [hA, ← hcov, ← hfun]
  have hR : ∫ x in smallContrastUnitBall d,
      ballScalarSource g x₀ r x * psi.toH1Function.toFun x ∂volume =
      r * ((r ^ d)⁻¹ * B) := by
    have hcov := setIntegral_comp_ballChart x₀ hr
      (fun y => g y * psi.toH1Function.toFun (r⁻¹ • (y - x₀)))
    have hfun : (fun x : Vec d =>
        ballScalarSource g x₀ r x * psi.toH1Function.toFun x) =
        fun x : Vec d => r *
          (g (r • x + x₀) * psi.toH1Function.toFun (r⁻¹ • ((r • x + x₀) - x₀))) := by
      funext x
      simp [ballScalarSource, ballChart, hsmulInv, mul_assoc]
    rw [hfun, integral_const_mul, hcov, hB]
  rw [hL, hR]
  simp only [Pi.zero_apply, vecDot_zero_left, integral_zero, sub_zero]
  have hAB : A = r * B := by
    field_simp at hkey
    linarith only [hkey]
  rw [hAB]
  ring

/-! ## The interior estimate on `euclideanBall x₀ r` -/

/-- **Third scaling.** A Hölder bound on the concentric half unit ball becomes,
after the pull-back `u x = r * v (r⁻¹ • (x - x₀))`, a Hölder bound on
`euclideanBall x₀ (r/2)` with the constant multiplied by `r ^ (1 - alpha)`. -/
theorem holderBound_of_ballTransfer (x₀ : Vec d) {r : ℝ} (hr : 0 < r)
    {alpha K : ℝ} {v : Vec d → ℝ}
    (hv : EuclideanHolderBoundOn (smallContrastBall d (1 / 2)) alpha K v) :
    EuclideanHolderBoundOn (euclideanBall x₀ (r / 2)) alpha (r ^ (1 - alpha) * K)
      (fun y => r * v (ballChartInv x₀ r y)) := by
  have hhalf : r * (1 / 2 : ℝ) = r / 2 := by ring
  intro X hX Y hY
  have hXmem : ballChartInv x₀ r X ∈ smallContrastBall d (1 / 2) := by
    refine (ballChart_mem_euclideanBall_iff x₀ hr (ballChartInv x₀ r X)).1 ?_
    rw [ballChart_ballChartInv x₀ hr, hhalf]
    exact hX
  have hYmem : ballChartInv x₀ r Y ∈ smallContrastBall d (1 / 2) := by
    refine (ballChart_mem_euclideanBall_iff x₀ hr (ballChartInv x₀ r Y)).1 ?_
    rw [ballChart_ballChartInv x₀ hr, hhalf]
    exact hY
  have hdiff : ballChartInv x₀ r X - ballChartInv x₀ r Y = r⁻¹ • (X - Y) := by
    ext i
    simp [ballChartInv, mul_sub]
  have hnorm : euclideanNorm (ballChartInv x₀ r X - ballChartInv x₀ r Y) =
      r⁻¹ * euclideanNorm (X - Y) := by
    rw [hdiff, euclideanNorm_smul, abs_of_nonneg (inv_nonneg.mpr hr.le)]
  have hsplit : (r⁻¹ * euclideanNorm (X - Y)) ^ alpha =
      r ^ (-alpha) * euclideanNorm (X - Y) ^ alpha := by
    rw [Real.mul_rpow (inv_nonneg.mpr hr.le) (euclideanNorm_nonneg _),
      ← Real.rpow_neg_one r, ← Real.rpow_mul hr.le]
    norm_num
  have hexp : r * r ^ (-alpha) = r ^ (1 - alpha) := by
    nth_rewrite 1 [← Real.rpow_one r]
    rw [← Real.rpow_add hr, sub_eq_add_neg]
  have hcoeff : r * (r ^ (-alpha) * K) = r ^ (1 - alpha) * K := by
    rw [← mul_assoc, hexp]
  calc
    |r * v (ballChartInv x₀ r X) - r * v (ballChartInv x₀ r Y)|
        = r * |v (ballChartInv x₀ r X) - v (ballChartInv x₀ r Y)| := by
          rw [← mul_sub, abs_mul, abs_of_nonneg hr.le]
    _ ≤ r * (K * euclideanNorm (ballChartInv x₀ r X - ballChartInv x₀ r Y) ^ alpha) :=
          mul_le_mul_of_nonneg_left (hv _ hXmem _ hYmem) hr.le
    _ = r * (K * (r ^ (-alpha) * euclideanNorm (X - Y) ^ alpha)) := by
          rw [hnorm, hsplit]
    _ = (r * (r ^ (-alpha) * K)) * euclideanNorm (X - Y) ^ alpha := by ring
    _ = r ^ (1 - alpha) * K * euclideanNorm (X - Y) ^ alpha := by rw [hcoeff]

/-- Interior Hölder estimate on an arbitrary Euclidean ball, with a bounded
scalar source and no vector source.  The constant is the explicit dimensional
coefficient of the unit-ball estimate times the two scaled data terms; because
the vector source vanishes, the factor `(1 - alpha)⁻¹` of the general estimate
is absent. -/
theorem schauder_holder_euclideanBall_zerothOrder [NeZero d]
    {a : CoeffField d} (x₀ : Vec d) {r : ℝ} (hr : 0 < r)
    {u : H1Function (euclideanBall x₀ r)} {g : Vec d → ℝ} {delta alpha : ℝ}
    (hd : 2 ≤ d) (halpha : alpha ∈ Set.Ico (1 / 2 : ℝ) 1)
    (hdelta0 : 0 ≤ delta) (hdelta : delta ≤ smallContrastThreshold d alpha)
    (hameas : Measurable a)
    (ha : CoefficientIdentityDistanceLE (euclideanBall x₀ r) a delta)
    (hu : IsMatrixDivFormWeakSolutionZerothOrderOn a (euclideanBall x₀ r) u g 0)
    (hg : MemScalarLInfOn (euclideanBall x₀ r) g) :
    ∃ v : Vec d → ℝ,
      ContinuousOn v (euclideanBall x₀ (r / 2)) ∧
      v =ᵐ[volume.restrict (euclideanBall x₀ r)] u.toFun ∧
      EuclideanHolderBoundOn (euclideanBall x₀ (r / 2)) alpha
        (smallContrastZerothSchauderConstant d *
          (r ^ (1 - alpha - (d : ℝ) / 2) *
              vectorLpSizeOn (euclideanBall x₀ r) 2 u.grad +
            r ^ (2 - alpha) * scalarLInfSizeOn (euclideanBall x₀ r) g)) v := by
  have hf0 : MemVectorLpOn (smallContrastUnitBall d)
      (schauderSourceExponent d alpha) (0 : Vec d → Vec d) := by
    have hzero : (fun x : Vec d => HilbertVec.ofVec ((0 : Vec d → Vec d) x)) = 0 := by
      funext x
      simp
    rw [MemVectorLpOn, hzero]
    exact MemLp.zero
  have hvecZero : vectorLpSizeOn (smallContrastUnitBall d)
      (schauderSourceExponent d alpha) (0 : Vec d → Vec d) = 0 := by
    have hzero : (fun x : Vec d => euclideanNorm ((0 : Vec d → Vec d) x)) = 0 := by
      funext x
      simp
    unfold vectorLpSizeOn
    rw [hzero]
    simp
  have hconc := schauder_interior_holder_zerothOrder (d := d) hd halpha hdelta0 hdelta
    (measurable_ballCoeff hameas x₀ hr)
    (coefficientIdentityDistanceLE_ballCoeff x₀ hr ha)
    (isMatrixDivFormWeakSolutionZerothOrderOn_ballTransfer x₀ hr hu)
    (memScalarLInfOn_ballScalarSource x₀ hr hg) hf0
  obtain ⟨-, vRep, hvcont, hvae, hvholder⟩ := hconc
  have hdata : smallContrastZerothOrderDataSize d alpha (ballTransfer x₀ hr u) 0
      (ballScalarSource g x₀ r) =
      r ^ (-(d : ℝ) / 2) * vectorLpSizeOn (euclideanBall x₀ r) 2 u.grad +
        r * scalarLInfSizeOn (euclideanBall x₀ r) g := by
    unfold smallContrastZerothOrderDataSize smallContrastDataSize
    rw [vectorLpSizeOn_two_ballTransfer_grad x₀ hr u,
      scalarLInfSizeOn_ballScalarSource x₀ hr g, hvecZero]
    ring
  rw [hdata] at hvholder
  refine ⟨fun y => r * vRep (ballChartInv x₀ r y), ?_, ?_, ?_⟩
  · have hmaps : Set.MapsTo (ballChartInv (d := d) x₀ r)
        (euclideanBall x₀ (r / 2)) (smallContrastBall d (1 / 2)) := by
      intro y hy
      refine (ballChart_mem_euclideanBall_iff x₀ hr (ballChartInv x₀ r y)).1 ?_
      rw [ballChart_ballChartInv x₀ hr, show r * (1 / 2 : ℝ) = r / 2 by ring]
      exact hy
    exact continuousOn_const.mul
      (hvcont.comp (continuous_ballChartInv (d := d) x₀ r).continuousOn hmaps)
  · have hpull := (quasiMeasurePreserving_ballChartInv (d := d) x₀ hr).ae hvae
    filter_upwards [hpull] with y hy
    have hy' : vRep (ballChartInv x₀ r y) =
        r⁻¹ * u.toFun (r • ballChartInv x₀ r y + x₀) := by
      simpa using hy
    have hinv : r • ballChartInv x₀ r y + x₀ = y :=
      ballChart_ballChartInv x₀ hr y
    rw [hy', hinv, ← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul]
  · have hcst : r ^ (1 - alpha) *
        (smallContrastZerothSchauderConstant d *
          (r ^ (-(d : ℝ) / 2) * vectorLpSizeOn (euclideanBall x₀ r) 2 u.grad +
            r * scalarLInfSizeOn (euclideanBall x₀ r) g)) =
        smallContrastZerothSchauderConstant d *
          (r ^ (1 - alpha - (d : ℝ) / 2) *
              vectorLpSizeOn (euclideanBall x₀ r) 2 u.grad +
            r ^ (2 - alpha) * scalarLInfSizeOn (euclideanBall x₀ r) g) := by
      have h1 : r ^ (1 - alpha) * r ^ (-(d : ℝ) / 2) =
          r ^ (1 - alpha - (d : ℝ) / 2) := by
        rw [← Real.rpow_add hr]
        congr 1
        ring
      have h2 : r ^ (1 - alpha) * r = r ^ (2 - alpha) := by
        nth_rewrite 2 [← Real.rpow_one r]
        rw [← Real.rpow_add hr]
        congr 1
        ring
      calc
        r ^ (1 - alpha) *
            (smallContrastZerothSchauderConstant d *
              (r ^ (-(d : ℝ) / 2) * vectorLpSizeOn (euclideanBall x₀ r) 2 u.grad +
                r * scalarLInfSizeOn (euclideanBall x₀ r) g))
            = smallContrastZerothSchauderConstant d *
              ((r ^ (1 - alpha) * r ^ (-(d : ℝ) / 2)) *
                  vectorLpSizeOn (euclideanBall x₀ r) 2 u.grad +
                (r ^ (1 - alpha) * r) *
                  scalarLInfSizeOn (euclideanBall x₀ r) g) := by ring
        _ = _ := by rw [h1, h2]
    have := holderBound_of_ballTransfer (d := d) x₀ hr hvholder
    rwa [hcst] at this

end

end Algsuperdiff.StochasticProcess.Common.Regularity.Ported
