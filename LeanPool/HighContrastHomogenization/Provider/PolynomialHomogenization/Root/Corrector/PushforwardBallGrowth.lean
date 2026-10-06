/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.PushforwardEngineInput
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorNormalizedL2Bridge
public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Corrector.PushforwardBallGrowth

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The Liouville growth row under a translation by an arbitrary real vector

The growth conjunct of `MemLiouvilleClass` is a **volume-normalized** `L²`
average over centred Euclidean balls, rescaled by `r ^ (-(1 + ϑ))`.  This
module transports it along a translation `v ↦ v (· + t)` by an arbitrary real
vector and an additive recentring `v ↦ v - c`.

The geometry is one line: `B_r + t ⊆ B_{2 r}` as soon as `‖t‖ ≤ r`.  The work
is the `ℝ≥0∞` bookkeeping — the division by `volume V` in `eVolumeAverage`
cancels only after `volume V` is shown to be neither `0` nor `∞`, which for a
positive-radius Euclidean ball is exactly `isOpen_euclideanBall` and
`Book.Ch01.volume_euclideanBall_ne_top`.

The additive constant is the one place a sign condition on `ϑ` enters: the
recentred function only satisfies the same growth row when `r ^ (-(1 + ϑ))`
itself tends to zero, i.e. when `1 + ϑ > 0`.  See the sign condition discussed
in `PushforwardRealTranslateLiouville`.
-/

namespace HCPolySupport
namespace HighContrast
namespace Root

open MeasureTheory Set _root_.Filter
open scoped ENNReal Pointwise

noncomputable section

variable {d : ℕ}

/-! ## Centred and off-centre Euclidean balls -/

/-- Translating the centred ball by `t` gives the ball centred at `t`. -/
theorem translateSet_euclideanBall (t : Vec d) (r : ℝ) :
    translateSet t (euclideanBall d r) = euclideanBallAt t r := by
  ext x
  rw [HCPolySupport.mem_translateSet_iff_sub_mem]
  simp only [euclideanBall, euclideanBallAt, Set.mem_ofPred_eq, sub_zero]

/-- Lebesgue volume does not see the centre of a Euclidean ball. -/
theorem volume_euclideanBallAt_eq (t : Vec d) (r : ℝ) :
    volume (euclideanBallAt t r) = volume (euclideanBall d r) := by
  rw [← translateSet_euclideanBall t r, HCPolySupport.volume_translateSet_eq]

/-- A positive-radius centred ball has nonzero volume. -/
theorem volume_euclideanBall_ne_zero {r : ℝ} (hr : 0 < r) :
    volume (euclideanBall d r) ≠ 0 :=
  ne_of_gt (IsOpen.measure_pos volume (isOpen_euclideanBall d r)
    (euclideanBall_nonempty (0 : Vec d) hr))

/-- A centred ball has finite volume. -/
theorem volume_euclideanBall_ne_top (r : ℝ) :
    volume (euclideanBall d r) ≠ ⊤ :=
  Book.Ch01.volume_euclideanBall_ne_top (0 : Vec d) r

/-- Positive dilation scales Lebesgue volume by the dimension power. -/
theorem volume_smul_set {r : ℝ} (hr : 0 ≤ r) (U : Set (Vec d)) :
    volume (r • U) = ENNReal.ofReal (r ^ d) * volume U := by
  simpa [Vec] using
    (MeasureTheory.Measure.addHaar_smul_of_nonneg
      (μ := (volume : Measure (Vec d))) hr U)

/-- The centred ball of radius `r` is the `r`-dilate of the unit ball. -/
theorem euclideanBall_eq_smul_unit {r : ℝ} (hr : 0 < r) :
    euclideanBall d r = r • euclideanBall d 1 := by
  have h := HCPolySupport.euclideanBall_eq_translateSet_smul_unit_of_pos
    (0 : Vec d) hr
  rw [HCPolySupport.translateSet_zero] at h
  exact h

/-- Volume of a centred ball, factored through the unit ball. -/
theorem volume_euclideanBall_eq_ofReal_pow_mul {r : ℝ} (hr : 0 < r) :
    volume (euclideanBall d r) =
      ENNReal.ofReal (r ^ d) * volume (euclideanBall d 1) := by
  rw [euclideanBall_eq_smul_unit hr, volume_smul_set hr.le]

/-- Doubling the radius multiplies the volume by `2 ^ d`, exactly. -/
theorem volume_euclideanBall_two_mul {r : ℝ} (hr : 0 < r) :
    volume (euclideanBall d (2 * r)) =
      ENNReal.ofReal ((2 : ℝ) ^ d) * volume (euclideanBall d r) := by
  rw [volume_euclideanBall_eq_ofReal_pow_mul (by linarith only [hr] : (0 : ℝ) < 2 * r),
    volume_euclideanBall_eq_ofReal_pow_mul hr, ← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ d), ← mul_pow]

/-- **The one geometric step.**  A ball of radius `r` centred at `t` lies inside
the centred ball of radius `2 r` as soon as the Euclidean length of `t` is at
most `r`. -/
theorem euclideanBallAt_subset_euclideanBall_two_mul (t : Vec d) {r : ℝ}
    (ht : Real.sqrt (vecNormSq t) ≤ r) :
    euclideanBallAt t r ⊆ euclideanBall d (2 * r) := by
  have hr : 0 ≤ r := le_trans (Real.sqrt_nonneg _) ht
  intro x hx
  have hx' : vecNormSq (x - t) < r ^ 2 := hx
  have hsub : Real.sqrt (vecNormSq (x - t)) < r := by
    have hlt := Real.sqrt_lt_sqrt (vecNormSq_nonneg (x - t)) hx'
    rwa [Real.sqrt_sq hr] at hlt
  have hxt : (x - t) + t = x := by
    ext i
    simp [sub_eq_add_neg, add_assoc]
  have htri : Real.sqrt (vecNormSq x) ≤
      Real.sqrt (vecNormSq (x - t)) + Real.sqrt (vecNormSq t) := by
    have h := sqrt_vecNormSq_add_le (x - t) t
    rwa [hxt] at h
  have hlt : Real.sqrt (vecNormSq x) < 2 * r := by
    calc Real.sqrt (vecNormSq x)
        ≤ Real.sqrt (vecNormSq (x - t)) + Real.sqrt (vecNormSq t) := htri
      _ < 2 * r := by linarith only [hsub, ht]
  show vecNormSq (x - 0) < (2 * r) ^ 2
  rw [sub_zero, pow_two]
  have hmm := mul_self_lt_mul_self (Real.sqrt_nonneg (vecNormSq x)) hlt
  rwa [Real.mul_self_sqrt (vecNormSq_nonneg x)] at hmm

/-! ## The normalized norm under a translation -/

/-- The normalized `L²` norm of a translated function on the centred ball is the
normalized norm of the function on the translated ball.  Both the numerator and
the volume in the denominator move with the translation. -/
theorem normalizedL2Norm_translate (t : Vec d) (r : ℝ) (f : Vec d → ℝ) :
    normalizedL2Norm (euclideanBall d r) (fun x => f (x + t)) =
      normalizedL2Norm (euclideanBallAt t r) f := by
  have hint : (∫⁻ x in euclideanBall d r, ENNReal.ofReal (f (x + t) ^ 2) ∂volume) =
      ∫⁻ y in euclideanBallAt t r, ENNReal.ofReal (f y ^ 2) ∂volume := by
    have h := (HCPolySupport.measurePreserving_addRight_restrict_translateSet t
        (euclideanBall d r)).lintegral_comp_emb
        (Homeomorph.addRight t).measurableEmbedding
        (fun y => ENNReal.ofReal (f y ^ 2))
    rw [translateSet_euclideanBall] at h
    simpa using h
  simp only [normalizedL2Norm, eVolumeAverage, hint, volume_euclideanBallAt_eq]

/-- Recentring by a constant costs a factor `√2` and an additive constant.  The
bound is stated with the exact `ℝ≥0∞` constants it is proved with, so no
positivity side condition on the function is needed. -/
theorem normalizedL2Norm_sub_const_le {V : Set (Vec d)} (hVzero : volume V ≠ 0)
    (hVtop : volume V ≠ ⊤) (f : Vec d → ℝ) (c : ℝ) :
    normalizedL2Norm V (fun x => f x - c) ≤
      ENNReal.ofReal 2 ^ (1 / 2 : ℝ) * normalizedL2Norm V f +
        ENNReal.ofReal (2 * c ^ 2) ^ (1 / 2 : ℝ) := by
  have hpoint : ∀ x : Vec d,
      ENNReal.ofReal ((f x - c) ^ 2) ≤
        ENNReal.ofReal 2 * ENNReal.ofReal (f x ^ 2) +
          ENNReal.ofReal (2 * c ^ 2) := by
    intro x
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hexp : (f x - c) ^ 2 = 2 * f x ^ 2 + 2 * c ^ 2 - (f x + c) ^ 2 := by ring
    linarith only [sq_nonneg (f x + c), hexp]
  have hmono : (∫⁻ x in V, ENNReal.ofReal ((f x - c) ^ 2) ∂volume) ≤
      ENNReal.ofReal 2 * (∫⁻ x in V, ENNReal.ofReal (f x ^ 2) ∂volume) +
        ENNReal.ofReal (2 * c ^ 2) * volume V := by
    calc (∫⁻ x in V, ENNReal.ofReal ((f x - c) ^ 2) ∂volume)
        ≤ ∫⁻ x in V, (ENNReal.ofReal 2 * ENNReal.ofReal (f x ^ 2) +
            ENNReal.ofReal (2 * c ^ 2)) ∂volume := lintegral_mono hpoint
      _ = ENNReal.ofReal 2 * (∫⁻ x in V, ENNReal.ofReal (f x ^ 2) ∂volume) +
            ENNReal.ofReal (2 * c ^ 2) * volume V := by
          rw [lintegral_add_right _ measurable_const,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, setLIntegral_const]
  have hdiv : eVolumeAverage V (fun x => ENNReal.ofReal ((f x - c) ^ 2)) ≤
      ENNReal.ofReal 2 * eVolumeAverage V (fun x => ENNReal.ofReal (f x ^ 2)) +
        ENNReal.ofReal (2 * c ^ 2) := by
    unfold eVolumeAverage
    calc (∫⁻ x in V, ENNReal.ofReal ((f x - c) ^ 2) ∂volume) / volume V
        ≤ (ENNReal.ofReal 2 * (∫⁻ x in V, ENNReal.ofReal (f x ^ 2) ∂volume) +
            ENNReal.ofReal (2 * c ^ 2) * volume V) / volume V := by
          gcongr
      _ = ENNReal.ofReal 2 *
            ((∫⁻ x in V, ENNReal.ofReal (f x ^ 2) ∂volume) / volume V) +
              ENNReal.ofReal (2 * c ^ 2) := by
          rw [ENNReal.add_div, mul_div_assoc,
            ENNReal.mul_div_cancel_right hVzero hVtop]
  calc normalizedL2Norm V (fun x => f x - c)
      = (eVolumeAverage V (fun x => ENNReal.ofReal ((f x - c) ^ 2))) ^ (1 / 2 : ℝ) :=
        rfl
    _ ≤ (ENNReal.ofReal 2 * eVolumeAverage V (fun x => ENNReal.ofReal (f x ^ 2)) +
          ENNReal.ofReal (2 * c ^ 2)) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow hdiv (by norm_num)
    _ ≤ (ENNReal.ofReal 2 *
            eVolumeAverage V (fun x => ENNReal.ofReal (f x ^ 2))) ^ (1 / 2 : ℝ) +
          ENNReal.ofReal (2 * c ^ 2) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_add_le_add_rpow _ _ (by norm_num) (by norm_num)
    _ = ENNReal.ofReal 2 ^ (1 / 2 : ℝ) * normalizedL2Norm V f +
          ENNReal.ofReal (2 * c ^ 2) ^ (1 / 2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        rfl

/-! ## The growth row transports -/

/-- The growth row for the translated function alone: a fixed real translation
costs exactly the constant `(2 ^ d) ^ (1/2) * 2 ^ (1 + ϑ)`.  No sign condition
on `ϑ` is used here. -/
theorem tendsto_growth_realTranslate {theta : ℝ} (v : Vec d → ℝ) (t : Vec d)
    (h : Tendsto (fun r : ℝ => ENNReal.ofReal (r ^ (-(1 + theta))) *
      normalizedL2Norm (euclideanBall d r) v) atTop (nhds 0)) :
    Tendsto (fun r : ℝ => ENNReal.ofReal (r ^ (-(1 + theta))) *
      normalizedL2Norm (euclideanBall d r) (fun y => v (y + t)))
      atTop (nhds 0) := by
  have hdouble : Tendsto (fun r : ℝ => (2 : ℝ) * r) atTop atTop :=
    _root_.Filter.Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2) tendsto_id
  have hcomp : Tendsto (fun r : ℝ => ENNReal.ofReal ((2 * r) ^ (-(1 + theta))) *
      normalizedL2Norm (euclideanBall d (2 * r)) v) atTop (nhds 0) := by
    simpa [Function.comp] using! h.comp hdouble
  have hKtop : ENNReal.ofReal ((2 : ℝ) ^ d) ^ (1 / 2 : ℝ) *
      ENNReal.ofReal ((2 : ℝ) ^ (1 + theta)) ≠ ⊤ := by
    refine ENNReal.mul_ne_top ?_ ENNReal.ofReal_ne_top
    exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
  have hupper : Tendsto (fun r : ℝ =>
      ENNReal.ofReal ((2 : ℝ) ^ d) ^ (1 / 2 : ℝ) *
          ENNReal.ofReal ((2 : ℝ) ^ (1 + theta)) *
        (ENNReal.ofReal ((2 * r) ^ (-(1 + theta))) *
          normalizedL2Norm (euclideanBall d (2 * r)) v)) atTop (nhds 0) := by
    have := ENNReal.Tendsto.const_mul hcomp (Or.inr hKtop)
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [eventually_ge_atTop (max (Real.sqrt (vecNormSq t)) 1)] with r hr
  have hrT : Real.sqrt (vecNormSq t) ≤ r := le_trans (le_max_left _ _) hr
  have hr1 : (1 : ℝ) ≤ r := le_trans (le_max_right _ _) hr
  have hr0 : (0 : ℝ) < r := by linarith only [hr1]
  have hballzero : volume (euclideanBall d r) ≠ 0 := volume_euclideanBall_ne_zero hr0
  have hballtop : volume (euclideanBall d r) ≠ ⊤ := volume_euclideanBall_ne_top r
  have hAtzero : volume (euclideanBallAt t r) ≠ 0 := by
    rw [volume_euclideanBallAt_eq]; exact hballzero
  have hAttop : volume (euclideanBallAt t r) ≠ ⊤ := by
    rw [volume_euclideanBallAt_eq]; exact hballtop
  have hbigzero : volume (euclideanBall d (2 * r)) ≠ 0 :=
    volume_euclideanBall_ne_zero (by linarith only [hr0])
  have hbigtop : volume (euclideanBall d (2 * r)) ≠ ⊤ :=
    volume_euclideanBall_ne_top _
  have hratio : volume (euclideanBall d (2 * r)) / volume (euclideanBallAt t r) =
      ENNReal.ofReal ((2 : ℝ) ^ d) := by
    rw [volume_euclideanBallAt_eq, volume_euclideanBall_two_mul hr0,
      ENNReal.mul_div_cancel_right hballzero hballtop]
  have hcompare := normalizedL2Norm_mono_set_le_volumeRatio
    (euclideanBallAt_subset_euclideanBall_two_mul t hrT)
    hAtzero hAttop hbigzero hbigtop v
  rw [hratio] at hcompare
  have hpow : ENNReal.ofReal (r ^ (-(1 + theta))) =
      ENNReal.ofReal ((2 : ℝ) ^ (1 + theta)) *
        ENNReal.ofReal ((2 * r) ^ (-(1 + theta))) := by
    have hreal : r ^ (-(1 + theta)) =
        (2 : ℝ) ^ (1 + theta) * (2 * r) ^ (-(1 + theta)) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hr0.le, ← mul_assoc,
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2), add_neg_cancel,
        Real.rpow_zero, one_mul]
    rw [hreal, ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (1 + theta))]
  calc ENNReal.ofReal (r ^ (-(1 + theta))) *
        normalizedL2Norm (euclideanBall d r) (fun y => v (y + t))
      = ENNReal.ofReal ((2 : ℝ) ^ (1 + theta)) *
          ENNReal.ofReal ((2 * r) ^ (-(1 + theta))) *
            normalizedL2Norm (euclideanBallAt t r) v := by
        rw [hpow, normalizedL2Norm_translate]
    _ ≤ ENNReal.ofReal ((2 : ℝ) ^ (1 + theta)) *
          ENNReal.ofReal ((2 * r) ^ (-(1 + theta))) *
            (ENNReal.ofReal ((2 : ℝ) ^ d) ^ (1 / 2 : ℝ) *
              normalizedL2Norm (euclideanBall d (2 * r)) v) :=
        by gcongr
    _ = ENNReal.ofReal ((2 : ℝ) ^ d) ^ (1 / 2 : ℝ) *
          ENNReal.ofReal ((2 : ℝ) ^ (1 + theta)) *
            (ENNReal.ofReal ((2 * r) ^ (-(1 + theta))) *
              normalizedL2Norm (euclideanBall d (2 * r)) v) := by ring

/-- **The growth row of `MemLiouvilleClass`, transported.**  A translation by an
arbitrary real vector together with an arbitrary additive recentring preserves
the `o(r ^ (1 + ϑ))` normalized growth, provided `1 + ϑ > 0`.

The hypothesis `0 < theta` is used *only* for the additive constant, and it is
necessary: at `theta = -1` the row is scale-invariant and a nonzero constant
violates it. -/
theorem tendsto_growth_realTranslate_subConst {theta : ℝ} (htheta : 0 < theta)
    (v : Vec d → ℝ) (t : Vec d) (c : ℝ)
    (h : Tendsto (fun r : ℝ => ENNReal.ofReal (r ^ (-(1 + theta))) *
      normalizedL2Norm (euclideanBall d r) v) atTop (nhds 0)) :
    Tendsto (fun r : ℝ => ENNReal.ofReal (r ^ (-(1 + theta))) *
      normalizedL2Norm (euclideanBall d r) (fun y => v (y + t) - c))
      atTop (nhds 0) := by
  have hbase := tendsto_growth_realTranslate (theta := theta) v t h
  have hrpow : Tendsto (fun r : ℝ => ENNReal.ofReal (r ^ (-(1 + theta))))
      atTop (nhds 0) := by
    have h1 : Tendsto (fun r : ℝ => r ^ (-(1 + theta))) atTop (nhds 0) :=
      tendsto_rpow_neg_atTop (by linarith only [htheta])
    simpa using ENNReal.tendsto_ofReal h1
  have hconsttop : ENNReal.ofReal (2 * c ^ 2) ^ (1 / 2 : ℝ) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
  have hfirst : Tendsto (fun r : ℝ => ENNReal.ofReal 2 ^ (1 / 2 : ℝ) *
      (ENNReal.ofReal (r ^ (-(1 + theta))) *
        normalizedL2Norm (euclideanBall d r) (fun y => v (y + t))))
      atTop (nhds 0) := by
    have hne : ENNReal.ofReal 2 ^ (1 / 2 : ℝ) ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
    simpa using ENNReal.Tendsto.const_mul hbase (Or.inr hne)
  have hsecond : Tendsto (fun r : ℝ => ENNReal.ofReal (2 * c ^ 2) ^ (1 / 2 : ℝ) *
      ENNReal.ofReal (r ^ (-(1 + theta)))) atTop (nhds 0) := by
    simpa using ENNReal.Tendsto.const_mul hrpow (Or.inr hconsttop)
  have hupper := hfirst.add hsecond
  rw [add_zero] at hupper
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr0
  have hballzero : volume (euclideanBall d r) ≠ 0 := volume_euclideanBall_ne_zero hr0
  have hballtop : volume (euclideanBall d r) ≠ ⊤ := volume_euclideanBall_ne_top r
  have hstep := normalizedL2Norm_sub_const_le hballzero hballtop
    (fun y => v (y + t)) c
  calc ENNReal.ofReal (r ^ (-(1 + theta))) *
        normalizedL2Norm (euclideanBall d r) (fun y => v (y + t) - c)
      ≤ ENNReal.ofReal (r ^ (-(1 + theta))) *
          (ENNReal.ofReal 2 ^ (1 / 2 : ℝ) *
              normalizedL2Norm (euclideanBall d r) (fun y => v (y + t)) +
            ENNReal.ofReal (2 * c ^ 2) ^ (1 / 2 : ℝ)) := by gcongr
    _ = ENNReal.ofReal 2 ^ (1 / 2 : ℝ) *
          (ENNReal.ofReal (r ^ (-(1 + theta))) *
            normalizedL2Norm (euclideanBall d r) (fun y => v (y + t))) +
          ENNReal.ofReal (2 * c ^ 2) ^ (1 / 2 : ℝ) *
            ENNReal.ofReal (r ^ (-(1 + theta))) := by ring

end

end Root
end HighContrast
end HCPolySupport
