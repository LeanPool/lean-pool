/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationOscillationDisplay

/-!
# LocalizationFluctuationOscillationBridge

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The oscillation cell of `e.nablaw.oscillations` bounds the Besov depth term

Step 2 of `l.approximate.recurrence.formula` feeds `e.lower.bound.oscillations`
into the duality leg, which is stated in the finite-depth positive `q = 2`
Besov seminorms of `CoarseGraining`'s
`cubeBesovPositiveVectorPartialSeminormTwo`.  The two are written in different
languages:

* the oscillation display carries `meshOscillationCell n u R`, the square root of
  `Book.Ch01.meanSquareOscillationVecOn (openCubeAtScale (triadicCubeShift R) n) u`
  -- the manuscript's `‖grad w - (grad w)_{z + cu_n}‖_{L2bar(z + cu_n)}`, based at
  the cube's own site `z`;
* the Besov tower carries `cubeBesovPositiveVectorDepthAverage`, built from
  `(cubeLpNorm R' (2) (cubeFluctuationVec R' u))^2` on the triadic descendants.

This module identifies the carriers and proves the (only) comparison the Step-2
chain needs.  Two facts do the work.

1. `openCubeAtScale_triadicCubeShift_eq_openCubeSet`: at a cube's own scale, the
   site-based open window *is* the open cube -- an identity, not an inclusion.
2. `sq_cubeLpNorm_two_cubeFluctuationVec_le_meanSquareOscillationVecOn`: the
   two `L^2` fluctuation quantities differ only by the ambient norm used, the
   CoarseGraining `cubeLpNorm` reading the Pi sup norm and
   `meanSquareOscillationVecOn` the coordinate sum.  Since `‖v‖_infty^2 <=
   sum_k v_k^2` pointwise, the comparison holds **with constant `1` in the
   direction Step 2 uses** (the Besov seminorm is the smaller quantity), so no
   dimensional loss enters the fluctuation estimate.

The consequence `cubeBesovPositiveVectorDepthAverage_le_descendantsAverage_sq`
is the form the multi-depth fold consumes: the depth-`j` term of the tower on a
cube `Q` is at most the depth-`j` descendant average of the squared oscillation
cells at scale `Q.scale - j`, which is exactly the quantity the free-buffer
oscillation display bounds at buffer `Q.scale - j`.

## Binders

`hu`, the `L^2` membership of the field on the cube(s), is the standing
integrability of every quantity in sight and is a conditional A obligation of
this module, discharged by the caller from `e.nablaw.in.L.eight`.  Nothing else
is assumed: no smallness, no moment, no measurability and no sample-space
proposition occurs.

## Scope

There is no `sorry`.

## References

* ABK26, `e.nablaw.oscillations`, `e.lower.bound.oscillations`, the duality leg
  of Step 2.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open HCPolySupport HCPolySupport.Book.Ch03 MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The site-based window is the cube -/

/-- **At a cube's own scale the site-based open window is the open cube.**
Unconditional. -/
theorem openCubeAtScale_triadicCubeShift_eq_openCubeSet (R : TriadicCube d) :
    openCubeAtScale (triadicCubeShift R) R.scale = openCubeSet R := by
  have hpow : Real.rpow (3 : ℝ) ((R.scale : ℤ) : ℝ) = (3 : ℝ) ^ R.scale :=
    Real.rpow_intCast 3 R.scale
  ext y
  simp only [openCubeAtScale, openCubeSet, Set.mem_ofPred_eq, triadicCubeShift,
    cubeScaleFactor, hpow]
  constructor
  · intro hy i
    have h := abs_lt.mp (hy i)
    constructor <;> [linarith [h.1]; linarith [h.2]]
  · intro hy i
    have h := hy i
    rw [abs_lt]
    constructor <;> [linarith [h.1]; linarith [h.2]]

/-! ## The two `L^2` fluctuation quantities -/

/-- The Pi sup norm is dominated by the coordinate `L^2` norm. -/
theorem norm_sq_le_vecNormSq (v : Vec d) : ‖v‖ ^ 2 ≤ vecNormSq v := by
  have hnn : 0 ≤ vecNormSq v := by
    unfold vecNormSq vecDot
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hle : ‖v‖ ≤ Real.sqrt (vecNormSq v) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun i => ?_
    rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
    refine Real.sqrt_le_sqrt ?_
    have hmem : i ∈ (Finset.univ : Finset (Fin d)) := Finset.mem_univ i
    have hsum : v i * v i ≤ ∑ k : Fin d, v k * v k :=
      Finset.single_le_sum (f := fun k : Fin d => v k * v k)
        (fun k _ => mul_self_nonneg (v k)) hmem
    calc v i ^ 2 = v i * v i := by ring
      _ ≤ ∑ k : Fin d, v k * v k := hsum
      _ = vecNormSq v := rfl
  have hsq : Real.sqrt (vecNormSq v) * Real.sqrt (vecNormSq v) = vecNormSq v :=
    Real.mul_self_sqrt hnn
  nlinarith [hle, norm_nonneg v, Real.sqrt_nonneg (vecNormSq v), hsq]

/-- The cube average of a vector field is its volume average over the open cube.
Unconditional; the cube boundary is Lebesgue null. -/
theorem cubeAverageVec_eq_volumeAverageVec_openCubeSet (Q : TriadicCube d)
    (u : Vec d → Vec d) : cubeAverageVec Q u = volumeAverageVec (openCubeSet Q) u := by
  funext i
  simp [cubeAverageVec, volumeAverageVec, cubeAverage, volumeAverage,
    volume_openCubeSet_eq_volume_cubeSet, volume_cubeSet_toReal,
    setIntegral_cubeSet_eq_setIntegral_openCubeSet]

/-- **The Besov depth term is below the oscillation cell.**  The squared `L^2`
cube norm of the fluctuation is at most the mean-square oscillation on the same
cube, the comparison constant being `1`.

on the `L^2` membership `hu`. -/
theorem sq_cubeLpNorm_two_cubeFluctuationVec_le_meanSquareOscillationVecOn
    (Q : TriadicCube d) (u : Vec d → Vec d)
    (hu : MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    (cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuationVec Q u)) ^ 2 ≤
      Book.Ch01.meanSquareOscillationVecOn (openCubeSet Q) u := by
  classical
  have hF : MemLp (cubeFluctuationVec Q u) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    memLp_cubeFluctuationVec Q u hu
  have hFmem : MemVectorL2 (cubeSet Q) (cubeFluctuationVec Q u) :=
    memVectorL2_cubeSet_of_memLp_normalizedCubeMeasure Q hF
  have hvec_int : IntegrableOn (fun x => vecNormSq (cubeFluctuationVec Q u x))
      (cubeSet Q) volume := by
    simpa [vecNormSq] using integrableOn_vecDot_of_memVectorL2 hFmem hFmem
  have hF_vol : MemLp (cubeFluctuationVec Q u) (2 : ℝ≥0∞)
      (volume.restrict (cubeSet Q)) := by
    simpa [MemVectorL2, volumeMeasureOn] using hFmem
  have hnorm_int : IntegrableOn (fun x => ‖cubeFluctuationVec Q u x‖ ^ (2 : ℕ))
      (cubeSet Q) volume := by
    have h := hF_vol.integrable_norm_rpow (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
    simpa using! h
  have hlp_sq : (cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuationVec Q u)) ^ (2 : ℕ) =
      cubeAverage Q (fun x => ‖cubeFluctuationVec Q u x‖ ^ (2 : ℕ)) := by
    simpa using
      cubeLpNorm_rpow_eq_cubeAverage_norm_rpow (Q := Q) (p := (2 : ℝ≥0∞))
        (f := cubeFluctuationVec Q u) (by norm_num) (by norm_num) hF
  have havg : cubeAverage Q (fun x => ‖cubeFluctuationVec Q u x‖ ^ (2 : ℕ)) ≤
      cubeAverage Q (fun x => vecNormSq (cubeFluctuationVec Q u x)) := by
    unfold cubeAverage
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (cubeVolume_nonneg Q))
    exact integral_mono_ae hnorm_int hvec_int <|
      (ae_restrict_iff' (measurableSet_cubeSet Q)).2 <|
        Filter.Eventually.of_forall fun x _hx =>
          norm_sq_le_vecNormSq (cubeFluctuationVec Q u x)
  have hosc : Book.Ch01.meanSquareOscillationVecOn (openCubeSet Q) u =
      volumeAverage (openCubeSet Q)
        (fun x => vecNormSq (u x - cubeAverageVec Q u)) := by
    unfold Book.Ch01.meanSquareOscillationVecOn
    rw [cubeAverageVec_eq_volumeAverageVec_openCubeSet Q u]
    refine Book.Ch01.meanSquareDeviationVecOn_eq_volumeAverage_vecNormSq_sub ?_
    intro k
    have hint : IntegrableOn
        (fun x => (u x k - volumeAverageVec (openCubeSet Q) u k) ^ 2)
        (cubeSet Q) volume := by
      have hcong : (fun x => (u x k - volumeAverageVec (openCubeSet Q) u k) ^ 2) =
          fun x => (cubeFluctuationVec Q u x k) ^ 2 := by
        funext x
        simp [cubeFluctuationVec, cubeAverageVec_eq_volumeAverageVec_openCubeSet Q u]
      rw [hcong]
      have hcomp : MemScalarL2 (cubeSet Q) (fun x => cubeFluctuationVec Q u x k) :=
        memScalarL2_coord_of_memVectorL2 hFmem k
      simpa [pow_two, MemScalarL2, volumeMeasureOn, IntegrableOn] using!
        hcomp.integrable_mul hcomp
    exact integrableOn_cubeSet_iff_integrableOn_openCubeSet.mp hint
  have hcubeavg : cubeAverage Q (fun x => vecNormSq (cubeFluctuationVec Q u x)) =
      volumeAverage (openCubeSet Q) (fun x => vecNormSq (u x - cubeAverageVec Q u)) := by
    simp [cubeAverage, volumeAverage, cubeFluctuationVec,
      volume_openCubeSet_eq_volume_cubeSet, volume_cubeSet_toReal,
      setIntegral_cubeSet_eq_setIntegral_openCubeSet]
  rw [hosc, ← hcubeavg]
  calc (cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuationVec Q u)) ^ 2
      = cubeAverage Q (fun x => ‖cubeFluctuationVec Q u x‖ ^ (2 : ℕ)) := hlp_sq
    _ ≤ cubeAverage Q (fun x => vecNormSq (cubeFluctuationVec Q u x)) := havg

/-- **The bridge at the display's own name.**  On a cube of scale `n` the Besov
depth term is at most the square of the oscillation cell of
`e.nablaw.oscillations`.

on the `L^2` membership `hu`. -/
theorem sq_cubeLpNorm_two_cubeFluctuationVec_le_sq_meshOscillationCell
    {n : ℤ} (Q : TriadicCube d) (hsc : Q.scale = n) (u : Vec d → Vec d)
    (hu : MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    (cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuationVec Q u)) ^ 2 ≤
      (meshOscillationCell n u Q) ^ 2 := by
  have hmain := sq_cubeLpNorm_two_cubeFluctuationVec_le_meanSquareOscillationVecOn Q u hu
  have hset : openCubeAtScale (triadicCubeShift Q) n = openCubeSet Q := by
    rw [← hsc]
    exact openCubeAtScale_triadicCubeShift_eq_openCubeSet Q
  have hnn : 0 ≤ Book.Ch01.meanSquareOscillationVecOn
      (openCubeAtScale (triadicCubeShift Q) n) u := by
    rw [hset]
    exact le_trans (sq_nonneg _) hmain
  have hsq : (meshOscillationCell n u Q) ^ 2 =
      Book.Ch01.meanSquareOscillationVecOn
        (openCubeAtScale (triadicCubeShift Q) n) u := by
    unfold meshOscillationCell
    rw [sq, Real.mul_self_sqrt hnn]
  rw [hsq, hset]
  exact hmain

/-- **The multi-depth form.**  The depth-`j` term of the positive `q = 2` Besov
tower on `Q` is at most the depth-`j` descendant average of the squared
oscillation cells at scale `Q.scale - j`.

on the `L^2` memberships on the descendants. -/
theorem cubeBesovPositiveVectorDepthAverage_le_descendantsAverage_sq
    (Q : TriadicCube d) (u : Vec d → Vec d) (j : ℕ)
    (hu : ∀ R ∈ descendantsAtDepth Q j,
      MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure R)) :
    cubeBesovPositiveVectorDepthAverage Q u j ≤
      descendantsAverage Q j
        (fun R => (meshOscillationCell (Q.scale - (j : ℤ)) u R) ^ 2) := by
  unfold cubeBesovPositiveVectorDepthAverage
  refine descendantsAverage_le_descendantsAverage Q j fun R hR => ?_
  exact sq_cubeLpNorm_two_cubeFluctuationVec_le_sq_meshOscillationCell R
    (scale_eq_sub_of_mem_descendantsAtDepth hR) u (hu R hR)

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
