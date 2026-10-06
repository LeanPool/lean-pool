/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteLipschitzCoreBestFit
public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteLipschitzCoreRecurrence
public import LeanPool.HighContrastHomogenization.Provider.Regularity.LiouvilleCubeRestriction

/-!
# High-contrast homogenization: Provider.Regularity.LiouvilleOriginCubeBallBridge

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Comparing origin cubes with scale-matched Euclidean balls

The radius `sqrt d * 3^q` encloses the origin cube `Q_q`, with a
dimension-only normalized-volume loss.  This is the geometric bridge needed
to feed the frozen continuous-radius Liouville limit into finite Caccioppoli.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory Set _root_.Filter
open scoped ENNReal Topology

noncomputable section

/-- The origin cube at natural generation `q` lies in the centered Euclidean
ball of radius `sqrt d * 3^q`. -/
theorem openCubeSet_originCube_subset_scaleMatchedEuclideanBall
    {d : ℕ} [NeZero d] (q : ℕ) :
    openCubeSet (originCube d (q : ℤ)) ⊆
      euclideanBall d (Real.sqrt d * (3 : ℝ) ^ q) := by
  have hdreal : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
  have hscale : 0 < (3 : ℝ) ^ q := pow_pos (by norm_num) q
  intro x hx
  have hxcoord := (mem_openCubeSet_originCube_iff.mp hx)
  norm_num only [zpow_natCast] at hxcoord
  have hsum : vecNormSq x < (d : ℝ) * ((3 : ℝ) ^ q) ^ 2 := by
    rw [vecNormSq_eq_sum_sq]
    have hterm : ∀ i : Fin d, x i ^ 2 < ((3 : ℝ) ^ q) ^ 2 := by
      intro i
      rcases hxcoord i with ⟨hlo, hhi⟩
      have habs : |x i| < (3 : ℝ) ^ q := by
        rw [abs_lt]
        constructor <;> linarith only [hlo, hhi, hscale]
      rw [← sq_abs]
      exact (sq_lt_sq₀ (abs_nonneg _) hscale.le).2 habs
    calc
      ∑ i, x i ^ 2 < ∑ _i : Fin d, ((3 : ℝ) ^ q) ^ 2 :=
        Finset.sum_lt_sum_of_nonempty
          ⟨⟨0, NeZero.pos d⟩, Finset.mem_univ _⟩
          (fun i _ => hterm i)
      _ = (d : ℝ) * ((3 : ℝ) ^ q) ^ 2 := by
        simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hrSq : (d : ℝ) * ((3 : ℝ) ^ q) ^ 2 =
      (Real.sqrt d * (3 : ℝ) ^ q) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hdreal.le]
  simpa only [euclideanBall, euclideanBallAt, Set.mem_ofPred_eq, sub_zero, hrSq]
    using hsum

/-- The scale-matched ball-to-cube volume ratio is bounded by the volume of a
dimension-only centered cube. -/
theorem scaleMatchedEuclideanBall_volume_ratio_le
    {d : ℕ} [NeZero d] (q : ℕ) :
    volume (euclideanBall d (Real.sqrt d * (3 : ℝ) ^ q)) /
        volume (openCubeSet (originCube d (q : ℤ))) ≤
      ENNReal.ofReal ((2 * Real.sqrt d) ^ d) := by
  let L : ℝ := (3 : ℝ) ^ q
  let r : ℝ := Real.sqrt d * L
  have hdreal : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
  have hL : 0 < L := by dsimp [L]; positivity
  have hr : 0 < r := mul_pos (Real.sqrt_pos.2 hdreal) hL
  have hmono : volume (euclideanBall d r) ≤
      volume (centeredOpenCube d (2 * r)) :=
    measure_mono (euclideanBall_subset_centeredOpenCube_two_mul hr)
  have hballTop : volume (euclideanBall d r) ≠ ⊤ :=
    Book.Ch01.volume_euclideanBall_ne_top (0 : Vec d) r
  have hcubeZero : volume (openCubeSet (originCube d (q : ℤ))) ≠ 0 := by
    have hreal : (volume (openCubeSet (originCube d (q : ℤ)))).toReal ≠ 0 := by
      rw [volume_openCubeSet_toReal, cubeVolume_eq_scaleFactor_pow,
        cubeScaleFactor_originCube]
      positivity
    exact (ENNReal.toReal_ne_zero.mp hreal).1
  have hcubeTop : volume (openCubeSet (originCube d (q : ℤ))) ≠ ⊤ :=
    (volume_openCubeSet_lt_top (originCube d (q : ℤ))).ne
  have hratioTop : volume (euclideanBall d r) /
      volume (openCubeSet (originCube d (q : ℤ))) ≠ ⊤ :=
    ENNReal.div_ne_top hballTop hcubeZero
  apply (ENNReal.toReal_le_toReal hratioTop ENNReal.ofReal_ne_top).1
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ (2 * Real.sqrt d) ^ d),
    ENNReal.toReal_div]
  have hmonoReal := ENNReal.toReal_mono
    (by
      have hcenterTop : volume (centeredOpenCube d (2 * r)) ≠ ⊤ := by
        exact ne_of_lt
          (isBoundedDomain_axisCube (fun _ : Fin d => -(2 * r) / 2) (2 * r)).volume_lt_top
      exact hcenterTop) hmono
  rw [volume_openCubeSet_toReal, cubeVolume_eq_scaleFactor_pow,
    cubeScaleFactor_originCube]
  rw [volume_centeredOpenCube_toReal (by positivity)] at hmonoReal
  dsimp only [r, L] at hmonoReal
  calc
    (volume (euclideanBall d (Real.sqrt d * (3 : ℝ) ^ q))).toReal /
          ((3 : ℝ) ^ (q : ℤ)) ^ d ≤
        (2 * (Real.sqrt d * (3 : ℝ) ^ q)) ^ d /
          ((3 : ℝ) ^ (q : ℤ)) ^ d :=
      div_le_div_of_nonneg_right hmonoReal (by positivity)
    _ = (2 * Real.sqrt d) ^ d := by
      norm_num only [zpow_natCast]
      field_simp
      rw [mul_pow]
      ring

/-- The normalized `L²` norm on an origin cube is controlled by the frozen
norm on its scale-matched enclosing ball with a dimension-only `ENNReal`
factor. -/
theorem normalizedL2Norm_originCube_le_scaleMatchedEuclideanBall
    {d : ℕ} [NeZero d] (q : ℕ) (v : Vec d → ℝ) :
    normalizedL2Norm (openCubeSet (originCube d (q : ℤ))) v ≤
      (ENNReal.ofReal ((2 * Real.sqrt d) ^ d)) ^ (1 / 2 : ℝ) *
        normalizedL2Norm
          (euclideanBall d (Real.sqrt d * (3 : ℝ) ^ q)) v := by
  let Q : TriadicCube d := originCube d (q : ℤ)
  let B : Set (Vec d) := euclideanBall d (Real.sqrt d * (3 : ℝ) ^ q)
  have hdreal : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
  have hr : 0 < Real.sqrt d * (3 : ℝ) ^ q := by positivity
  have hQzero : volume (openCubeSet Q) ≠ 0 := by
    have hreal : (volume (openCubeSet Q)).toReal ≠ 0 := by
      rw [volume_openCubeSet_toReal]
      exact (cubeVolume_pos Q).ne'
    exact (ENNReal.toReal_ne_zero.mp hreal).1
  have hQtop : volume (openCubeSet Q) ≠ ⊤ :=
    (volume_openCubeSet_lt_top Q).ne
  have hBzero : volume B ≠ 0 :=
    (ENNReal.toReal_ne_zero.mp
      (Book.Ch01.volume_euclideanBall_toReal_ne_zero (0 : Vec d) hr)).1
  have hBtop : volume B ≠ ⊤ :=
    Book.Ch01.volume_euclideanBall_ne_top (0 : Vec d) _
  have hbase := normalizedL2Norm_mono_set_le_volumeRatio
    (openCubeSet_originCube_subset_scaleMatchedEuclideanBall q)
    hQzero hQtop hBzero hBtop v
  have hratio := scaleMatchedEuclideanBall_volume_ratio_le (d := d) q
  calc
    normalizedL2Norm (openCubeSet Q) v ≤
        (volume B / volume (openCubeSet Q)) ^ (1 / 2 : ℝ) *
          normalizedL2Norm B v := hbase
    _ ≤ (ENNReal.ofReal ((2 * Real.sqrt d) ^ d)) ^ (1 / 2 : ℝ) *
          normalizedL2Norm B v := by gcongr

/-- Along natural triadic generations, the scale-matched frozen prefactor
times the normalized cube norm tends to zero. -/
theorem tendsto_scaleMatchedRadius_normalizedL2Norm_originCube_of_liouvilleGrowth
    {d : ℕ} [NeZero d] {theta : ℝ} {v : Vec d → ℝ}
    (hgrowth : Tendsto
      (fun r : ℝ => ENNReal.ofReal (r ^ (-(1 + theta))) *
        normalizedL2Norm (euclideanBall d r) v)
      atTop (nhds 0)) :
    Tendsto
      (fun q : ℕ =>
        ENNReal.ofReal
            ((Real.sqrt d * (3 : ℝ) ^ q) ^ (-(1 + theta))) *
          normalizedL2Norm (openCubeSet (originCube d (q : ℤ))) v)
      atTop (nhds 0) := by
  let C : ℝ≥0∞ :=
    (ENNReal.ofReal ((2 * Real.sqrt d) ^ d)) ^ (1 / 2 : ℝ)
  have hdreal : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
  have hpow : Tendsto (fun q : ℕ => (3 : ℝ) ^ q) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hradius : Tendsto
      (fun q : ℕ => Real.sqrt d * (3 : ℝ) ^ q) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos (Real.sqrt_pos.2 hdreal)).2 hpow
  have hball := hgrowth.comp hradius
  have hCtop : C ≠ ⊤ := by
    dsimp only [C]
    exact (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top).ne
  have hright : Tendsto
      (fun q : ℕ => C *
        (ENNReal.ofReal
            ((Real.sqrt d * (3 : ℝ) ^ q) ^ (-(1 + theta))) *
          normalizedL2Norm
            (euclideanBall d (Real.sqrt d * (3 : ℝ) ^ q)) v))
      atTop (nhds 0) := by
    have hmul := ENNReal.Tendsto.const_mul hball (Or.inr hCtop)
    simpa only [mul_zero] using! hmul
  apply tendsto_zero_of_le_of_tendsto_zero (fun q => ?_) hright
  have hcube := normalizedL2Norm_originCube_le_scaleMatchedEuclideanBall q v
  dsimp only [C]
  calc
    ENNReal.ofReal
          ((Real.sqrt d * (3 : ℝ) ^ q) ^ (-(1 + theta))) *
        normalizedL2Norm (openCubeSet (originCube d (q : ℤ))) v ≤
      ENNReal.ofReal
          ((Real.sqrt d * (3 : ℝ) ^ q) ^ (-(1 + theta))) *
        (C * normalizedL2Norm
          (euclideanBall d (Real.sqrt d * (3 : ℝ) ^ q)) v) := by
      simpa only [mul_comm] using mul_le_mul_right hcube
        (ENNReal.ofReal
          ((Real.sqrt d * (3 : ℝ) ^ q) ^ (-(1 + theta))))
    _ = C *
        (ENNReal.ofReal
            ((Real.sqrt d * (3 : ℝ) ^ q) ^ (-(1 + theta))) *
          normalizedL2Norm
            (euclideanBall d (Real.sqrt d * (3 : ℝ) ^ q)) v) := by
      ac_rfl

/-- With local `L²` membership available, the preceding frozen-norm limit is
exactly the `o(R^theta)` statement for the scale-normalized zero-affine
candidate error used by finite Caccioppoli. -/
theorem tendsto_scaleMatchedRadius_zeroAffineError_of_liouvilleGrowth
    {d : ℕ} [NeZero d] {theta : ℝ} {v : Vec d → ℝ}
    (hmem : ∀ q : ℕ,
      MemLp v 2 (normalizedCubeMeasure (originCube d (q : ℤ))))
    (hgrowth : Tendsto
      (fun r : ℝ => ENNReal.ofReal (r ^ (-(1 + theta))) *
        normalizedL2Norm (euclideanBall d r) v)
      atTop (nhds 0)) :
    Tendsto
      (fun q : ℕ => ENNReal.ofReal
        ((Real.sqrt d * (3 : ℝ) ^ q) ^ (-theta) *
          normalizedAffineCandidateError
            (originCube d (q : ℤ)) v 0 0))
      atTop (nhds 0) := by
  have hdreal : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
  have hsqrt : 0 < Real.sqrt d := Real.sqrt_pos.2 hdreal
  have hbase :=
    tendsto_scaleMatchedRadius_normalizedL2Norm_originCube_of_liouvilleGrowth
      hgrowth
  have hscaled : Tendsto
      (fun q : ℕ => ENNReal.ofReal (Real.sqrt d) *
        (ENNReal.ofReal
            ((Real.sqrt d * (3 : ℝ) ^ q) ^ (-(1 + theta))) *
          normalizedL2Norm (openCubeSet (originCube d (q : ℤ))) v))
      atTop (nhds 0) := by
    have hmul := ENNReal.Tendsto.const_mul
      (a := ENNReal.ofReal (Real.sqrt d)) hbase (Or.inr ENNReal.ofReal_ne_top)
    simpa only [mul_zero] using hmul
  refine hscaled.congr fun q => ?_
  let L : ℝ := (3 : ℝ) ^ q
  let R : ℝ := Real.sqrt d * L
  have hL : 0 < L := by dsimp [L]; positivity
  have hR : 0 < R := mul_pos hsqrt hL
  have hnorm := normalizedL2Norm_openCubeSet_eq_ofReal_cubeLpNorm
    (originCube d (q : ℤ)) v (hmem q)
  have herror : normalizedAffineCandidateError
      (originCube d (q : ℤ)) v 0 0 =
        L⁻¹ * cubeLpNorm (originCube d (q : ℤ)) 2 v := by
    unfold normalizedAffineCandidateError normalizedCubeL2Distance
      cubeBesovScaleWeight
    simp only [cubeScaleFactor_originCube, zero_add, vecDot_zero_left,
      sub_zero]
    norm_num only [zpow_natCast]
    rw [Real.rpow_neg_one]
  have hreal : R ^ (-theta) * L⁻¹ =
      Real.sqrt d * R ^ (-(1 + theta)) := by
    rw [show -(1 + theta) = -theta + -1 by ring,
      Real.rpow_add hR]
    rw [Real.rpow_neg_one]
    field_simp
    dsimp only [R]
    ring
  rw [herror]
  rw [ENNReal.ofReal_mul (Real.rpow_nonneg hR.le _),
    ENNReal.ofReal_mul (inv_nonneg.mpr hL.le), hnorm]
  have hRdef : Real.sqrt d * (3 : ℝ) ^ q = R := rfl
  rw [hRdef]
  have hcoeffENN :
      ENNReal.ofReal (Real.sqrt d) * ENNReal.ofReal (R ^ (-(1 + theta))) =
        ENNReal.ofReal (R ^ (-theta)) * ENNReal.ofReal L⁻¹ := by
    rw [← ENNReal.ofReal_mul hsqrt.le,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hR.le _)]
    exact congrArg ENNReal.ofReal hreal.symm
  calc
    ENNReal.ofReal (Real.sqrt d) *
          (ENNReal.ofReal (R ^ (-(1 + theta))) *
            ENNReal.ofReal (cubeLpNorm (originCube d (q : ℤ)) 2 v)) =
        (ENNReal.ofReal (Real.sqrt d) *
          ENNReal.ofReal (R ^ (-(1 + theta)))) *
            ENNReal.ofReal (cubeLpNorm (originCube d (q : ℤ)) 2 v) := by ac_rfl
    _ = (ENNReal.ofReal (R ^ (-theta)) * ENNReal.ofReal L⁻¹) *
          ENNReal.ofReal (cubeLpNorm (originCube d (q : ℤ)) 2 v) := by
      rw [hcoeffENN]
    _ = ENNReal.ofReal (R ^ (-theta)) *
          (ENNReal.ofReal L⁻¹ *
            ENNReal.ofReal (cubeLpNorm (originCube d (q : ℤ)) 2 v)) := by ac_rfl

/-- The Liouville-growth input in frozen-class form: a Liouville member has
scale-normalized zero-affine error `o(R^theta)` along the triadic radii. -/
theorem tendsto_scaleMatchedRadius_zeroAffineError_of_memLiouvilleClass
    {d : ℕ} [NeZero d] {b : CoeffField d} {theta : ℝ}
    {v : Vec d → ℝ} {Dv : Vec d → Vec d}
    (hv : MemLiouvilleClass b theta v Dv) :
    Tendsto
      (fun q : ℕ => ENNReal.ofReal
        ((Real.sqrt d * (3 : ℝ) ^ q) ^ (-theta) *
          normalizedAffineCandidateError
            (originCube d (q : ℤ)) v 0 0))
      atTop (nhds 0) := by
  apply tendsto_scaleMatchedRadius_zeroAffineError_of_liouvilleGrowth
    (fun q => memLp_normalizedCubeMeasure_of_liouvilleGrowth
      hv.1.1.1 hv.2.2 q) hv.2.2

end

end HighContrast
end HCPolySupport
