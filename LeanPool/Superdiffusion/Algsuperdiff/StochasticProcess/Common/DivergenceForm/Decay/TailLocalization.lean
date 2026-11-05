/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.Decay.Geometry
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.Decay.PointwiseDecay

/-!
# TailLocalization

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Localization and local energy for the resolvent tail estimate

The tail estimate for `mu z - div (a grad z) = g` at a point `x` whose
source vanishes on the ball of radius `r` about `x` uses one fixed
localization: the smooth radial cutoff `agmonTailCutoff x r`, equal to one on
the ball of radius `3 r / 4` and supported inside the ball of radius `r`.  Its
transition layer therefore sits entirely inside the region where the source
vanishes, which is what makes the estimate decay away from the source.

Two quantitative facts about that localization are recorded, both with the
scaling the tail function needs: the coordinate-gradient bound
`agmonTailCutoffGradientBound d r`, which scales like `r ^ (-2)`, and the
volume bound `agmonTailLayerVolume d r` for the transition layer, which scales
like `r ^ d`.

The local energy is then paid for entirely by that layer.  Testing the
equation with `eta ^ 2 * z` gives a Caccioppoli inequality in which the source
term drops (the source vanishes where `eta` does not) and the mass term has a
good sign, so the gradient energy on the ball of radius `r / 2` is bounded by
the layer term alone.  With the maximum-principle bound `|z| <= 1 / mu` this
produces `agmonTailGradientSize d lam Lam mu r`, the gradient size the
interior Schauder estimate consumes.

The first two results convert an integral bound on the squared Euclidean
magnitude of a vector field into a bound on the `L^2` size the Schauder
estimate is stated with.

## Main results

- `DivergenceFormProcess.Decay.vectorLpSizeOn_two_le`
- `DivergenceFormProcess.Decay.agmonTailCutoff`
- `DivergenceFormProcess.Decay.vecNormSq_fderiv_agmonTailCutoff_le`
- `DivergenceFormProcess.Decay.volume_layer_agmonTailCutoff_le`
-/

noncomputable section

namespace DivergenceFormProcess.Decay

open HCPolySupport MeasureTheory
open DivergenceFormProcess.Form
open Algsuperdiff.StochasticProcess.Common.Regularity.Ported
open scoped ENNReal

variable {d : ℕ}

/-! ### The Euclidean `L²` size of a vector field -/

/-- The Euclidean magnitude of an `L²` vector field is a scalar `L²`
function. -/
theorem memLp_euclideanNorm {W : Set (Vec d)} {f : Vec d → Vec d}
    (hf : MemVectorL2 W f) :
    MemLp (fun y => euclideanNorm (f y)) 2 (volumeMeasureOn W) := by
  have h1 : MemLp (fun y => ‖hilbertifyVecField f y‖) 2 (volumeMeasureOn W) :=
    (memHilbertVectorL2_hilbertifyVecField hf).norm
  have hEq : (fun y => ‖hilbertifyVecField f y‖) =
      fun y : Vec d => euclideanNorm (f y) := by
    funext y
    exact (euclideanNorm_eq_norm_ofVec (f y)).symm
  rw [hEq] at h1
  exact h1

/-- An integral bound on the squared Euclidean magnitude is a bound on the
`L²` size the Schauder estimate consumes. -/
theorem vectorLpSizeOn_two_le {W : Set (Vec d)} {f : Vec d → Vec d} {E : ℝ}
    (hf : MemVectorL2 W f) (hE : 0 ≤ E)
    (hint : (∫ y in W, vecNormSq (f y) ∂volume) ≤ E ^ 2) :
    vectorLpSizeOn W 2 f ≤ E := by
  have hmem := memLp_euclideanNorm hf
  have hkey := hmem.eLpNorm_eq_integral_rpow_norm
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  have hfun : (fun a : Vec d => ‖euclideanNorm (f a)‖ ^ (ENNReal.toReal 2)) =
      fun a => vecNormSq (f a) := by
    funext a
    rw [Real.norm_of_nonneg (euclideanNorm_nonneg _)]
    have h2 : ENNReal.toReal (2 : ℝ≥0∞) = ((2 : ℕ) : ℝ) := by norm_num
    rw [h2, Real.rpow_natCast, euclideanNorm_sq]
  have htwo : ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) := by
    simp [ENNReal.ofReal_ofNat]
  unfold vectorLpSizeOn
  rw [htwo, hkey, hfun]
  have hinv : (ENNReal.toReal (2 : ℝ≥0∞))⁻¹ = 1 / 2 := by norm_num
  rw [hinv, ← Real.sqrt_eq_rpow, ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
  calc Real.sqrt (∫ a in W, vecNormSq (f a) ∂volume)
      ≤ Real.sqrt (E ^ 2) := Real.sqrt_le_sqrt hint
    _ = E := Real.sqrt_sq hE

/-! ### The localization -/

/-- The localization of the tail estimate: one on the ball of radius
`3 r / 4` about `x`, supported inside the ball of radius `r`. -/
def agmonTailCutoff (x : Vec d) (r : ℝ) : Vec d → ℝ :=
  QuantitativeBallCutoff.canonicalFun x (3 * r / 4) (7 * r / 8)

theorem contDiff_agmonTailCutoff (x : Vec d) {r : ℝ} (hr : 0 < r) :
    ContDiff ℝ (⊤ : ℕ∞) (agmonTailCutoff x r) :=
  QuantitativeBallCutoff.canonicalFun_smooth x (by linarith only [hr])
    (by linarith only [hr])

theorem hasCompactSupport_agmonTailCutoff (x : Vec d) {r : ℝ} (hr : 0 < r) :
    HasCompactSupport (agmonTailCutoff x r) :=
  QuantitativeBallCutoff.canonicalFun_hasCompactSupport x
    (by linarith only [hr]) (by linarith only [hr])

theorem tsupport_agmonTailCutoff_subset (x : Vec d) {r : ℝ} (hr : 0 < r) :
    tsupport (agmonTailCutoff x r) ⊆ euclideanBall x r :=
  QuantitativeBallCutoff.canonicalFun_tsupport_subset_euclideanBall x
    (by linarith only [hr]) (by linarith only [hr]) (by linarith only [hr])

theorem agmonTailCutoff_eq_one (x : Vec d) {r : ℝ} (hr : 0 < r) {y : Vec d}
    (hy : y ∈ euclideanBall x (3 * r / 4)) :
    agmonTailCutoff x r y = 1 :=
  QuantitativeBallCutoff.canonicalFun_eq_one_on_inner (by linarith only [hr])
    (by linarith only [hr]) hy

/-- The coordinate-gradient bound of the tail localization: it scales like
`r⁻²`. -/
def agmonTailCutoffGradientBound (d : ℕ) (r : ℝ) : ℝ :=
  (d : ℝ) * (smoothTransitionProfile.derivBound * (2 * (d : ℝ) / (r / 8))) ^ 2

theorem agmonTailCutoffGradientBound_nonneg (d : ℕ) (r : ℝ) :
    0 ≤ agmonTailCutoffGradientBound d r := by
  unfold agmonTailCutoffGradientBound
  positivity

theorem vecNormSq_fderiv_agmonTailCutoff_le (x : Vec d) {r : ℝ} (hr : 0 < r)
    (y : Vec d) :
    vecNormSq (fun i => (fderiv ℝ (agmonTailCutoff x r) y) (basisVec i)) ≤
      agmonTailCutoffGradientBound d r := by
  have hbase := vecNormSq_fderiv_ballCutoff_le x (r := 3 * r / 4) (s := 7 * r / 8)
    (by linarith only [hr]) (by linarith only [hr]) y
  rw [show 7 * r / 8 - 3 * r / 4 = r / 8 by ring] at hbase
  exact hbase

/-- The transition layer of the tail localization sits outside the ball of
radius `3 r / 4`. -/
theorem le_euclideanNorm_of_fderiv_agmonTailCutoff_ne_zero (x : Vec d) {r : ℝ}
    (hr : 0 < r) {y : Vec d}
    (hy : fderiv ℝ (agmonTailCutoff x r) y ≠ 0) :
    3 * r / 4 ≤ euclideanNorm (y - x) := by
  refine le_euclideanNorm_sub_of_notMem_euclideanBall (fun hmem => hy ?_)
  exact fderiv_eq_zero_of_eventuallyEq_one (isOpen_euclideanBall x (3 * r / 4))
    (fun w hw => agmonTailCutoff_eq_one x hr hw) hmem

/-- The volume bound for the transition layer of the tail localization: it
scales like `r ^ d`. -/
def agmonTailLayerVolume (d : ℕ) (r : ℝ) : ℝ :=
  (volume (smallContrastUnitBall d)).toReal * r ^ d

theorem agmonTailLayerVolume_nonneg (d : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ agmonTailLayerVolume d r := by
  unfold agmonTailLayerVolume
  exact mul_nonneg ENNReal.toReal_nonneg (pow_nonneg hr d)

theorem volume_layer_agmonTailCutoff_le [NeZero d] (x : Vec d) {r : ℝ}
    (hr : 0 < r) (Om : Set (Vec d)) :
    (volume {y ∈ Om | fderiv ℝ (agmonTailCutoff x r) y ≠ 0}).toReal ≤
      agmonTailLayerVolume d r := by
  have hsub : {y ∈ Om | fderiv ℝ (agmonTailCutoff x r) y ≠ 0} ⊆
      euclideanBall x r := by
    intro y hy
    refine tsupport_agmonTailCutoff_subset x hr ?_
    by_contra hcon
    exact hy.2 (fderiv_of_notMem_tsupport ℝ hcon)
  have hmono := measure_mono (μ := volume) hsub
  have htop : volume (euclideanBall x r) ≠ ⊤ :=
    HCPolySupport.Book.Ch01.volume_euclideanBall_ne_top x r
  refine (ENNReal.toReal_mono htop hmono).trans (le_of_eq ?_)
  simpa only [agmonTailLayerVolume] using
    volume_euclideanBall_toReal_eq_unit_mul_pow x hr

/-! ### The local energy bound -/

/-- The local gradient size supplied to the Schauder estimate: the
Caccioppoli bound at the tail localization, read off on the ball of radius
`r / 2`. -/
def agmonTailGradientSize (d : ℕ) (lam Lam mu r : ℝ) : ℝ :=
  2 * Lam / lam * (1 / mu) *
    Real.sqrt (agmonTailCutoffGradientBound d r * agmonTailLayerVolume d r)

theorem agmonTailGradientSize_nonneg (d : ℕ) {lam Lam mu r : ℝ} (hlam : 0 < lam)
    (hLam : 0 < Lam) (hmu : 0 < mu) :
    0 ≤ agmonTailGradientSize d lam Lam mu r := by
  unfold agmonTailGradientSize
  have h1 : (0 : ℝ) ≤ 2 * Lam / lam := by positivity
  have h2 : (0 : ℝ) ≤ 1 / mu := by positivity
  exact mul_nonneg (mul_nonneg h1 h2) (Real.sqrt_nonneg _)

end DivergenceFormProcess.Decay
