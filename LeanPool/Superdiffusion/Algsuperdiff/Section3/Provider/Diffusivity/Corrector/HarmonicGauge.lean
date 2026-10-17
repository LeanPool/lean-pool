/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.OscillationCubeFamily
public import LeanPool.HighContrastHomogenization.Support.Book.Ch01.Theorems.MeanSquareDeviation
public import LeanPool.HighContrastHomogenization.Support.Book.Ch01.Theorems.NormScaling

/-!
# HarmonicGauge

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Cube/ball gauge transfer for interior harmonic estimates

`Vec d = Fin d -> R` carries the **sup** metric, while every interior estimate
for a harmonic function is naturally stated on **Euclidean** balls.
CoarseGraining keeps the two gauges separate on the same carrier:
`openCubeAtScale` is the sup-ball and `euclideanBall`
(`Sobolev/Foundations/Cutoff/Euclidean`) is the explicit round ball defined
through `vecNormSq`.  This module proves the two containments relating them, the
elementary arithmetic they cost, and the exact volume of a Euclidean ball.

## Contents

* `sqrt_natCast_le_natCast_add_one_div_two` -- the elementary
  `sqrt d <= (d + 1)/2`, which is where the dimensional factor of the
  cube-to-ball direction is paid.
* `vecNormSq_sub_center_le_of_mem_openCubeAtScale` -- the sharp centred
  coordinate bound `|x - z|^2 <= d (3^m/2)^2` on the cube of scale `m`.
* `openCubeAtScale_subset_euclideanBall` -- a cube of scale `m` sits inside every
  Euclidean ball of radius `> sqrt d * 3^m / 2`.  This is the direction that
  costs the `sqrt d`.
* `euclideanClosedBall_subset_openCubeAtScale` -- the free direction: a Euclidean
  closed ball of radius `< 3^m / 2` sits inside the cube of scale `m`.
* `volume_euclideanBall_toReal`, `euclideanUnitBallVolume_pos` -- the exact
  volume `r^d omega_d` of a Euclidean ball and the positivity of the unit-ball
  constant `omega_d`, from which every dimension-only cube-to-ball volume ratio
  downstream is read off.

The triadic-gap form of the first inclusion --- for a gap `k >= d + 2`, the
Euclidean ball of radius `3^{n+k}/8` around any point of the fine cube
`z + cu_n` stays inside the coarse cube `z + cu_{n+k}` --- is
`Corrector.OscillationDecayGap.euclideanBall_eighth_subset_openCubeAtScale_of_gap`.
That is exactly why the arbitrary-gap oscillation estimate carries the
restriction `k >= d + 2`: a single triadic child need not sit inside the
Euclidean ball an interior estimate requires.

## References

* ABK26, `e.nablaw.oscillations`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.Corrector

open HCPolySupport HCPolySupport.Book.Ch03 MeasureTheory

/-- `sqrt d <= (d + 1) / 2`, the elementary bound `4 d <= (d + 1)^2`. -/
theorem sqrt_natCast_le_natCast_add_one_div_two (d : ℕ) :
    Real.sqrt (d : ℝ) ≤ ((d : ℝ) + 1) / 2 := by
  have hsq : (d : ℝ) ≤ (((d : ℝ) + 1) / 2) ^ 2 := by
    nlinarith [sq_nonneg ((d : ℝ) - 1)]
  have hmono := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (by positivity)] at hmono

variable {d : ℕ}

/-- **The centred coordinate bound.**

Every point of the cube `z + cu_m` is at squared Euclidean distance at most
`d (3^m / 2)^2` from the centre.  This is the sharp constant: the sup-ball of
radius `3^m/2` is contained in the Euclidean ball of radius `sqrt d * 3^m / 2`
and in no smaller one. -/
theorem vecNormSq_sub_center_le_of_mem_openCubeAtScale {z : Vec d} {m : ℤ}
    {x : Vec d} (hx : x ∈ openCubeAtScale z m) :
    vecNormSq (x - z) ≤ (d : ℝ) * ((3 : ℝ) ^ m / 2) ^ 2 := by
  rw [mem_openCubeAtScale_iff] at hx
  have hexp : vecNormSq (x - z) = ∑ i : Fin d, ((x - z) i) ^ 2 := by
    simp [vecNormSq, vecDot, sq]
  rw [hexp]
  calc ∑ i : Fin d, ((x - z) i) ^ 2
      ≤ ∑ _i : Fin d, ((3 : ℝ) ^ m / 2) ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        have hi : |x i - z i| < (3 : ℝ) ^ m / 2 := hx i
        have hval : (x - z) i = x i - z i := by simp
        rw [hval, ← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hi.le 2
    _ = (d : ℝ) * ((3 : ℝ) ^ m / 2) ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **The expensive direction.**

A cube of scale `m` is contained in every concentric Euclidean ball of radius
strictly larger than `sqrt d * 3^m / 2`. -/
theorem openCubeAtScale_subset_euclideanBall {z : Vec d} {m : ℤ} {r : ℝ}
    (hr : Real.sqrt (d : ℝ) * ((3 : ℝ) ^ m / 2) < r) :
    openCubeAtScale z m ⊆ euclideanBall z r := by
  intro x hx
  have hb := vecNormSq_sub_center_le_of_mem_openCubeAtScale hx
  have hnn : 0 ≤ Real.sqrt (d : ℝ) * ((3 : ℝ) ^ m / 2) :=
    mul_nonneg (Real.sqrt_nonneg _) (by positivity)
  have hsq : (Real.sqrt (d : ℝ) * ((3 : ℝ) ^ m / 2)) ^ 2 =
      (d : ℝ) * ((3 : ℝ) ^ m / 2) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
  have hlt : (d : ℝ) * ((3 : ℝ) ^ m / 2) ^ 2 < r ^ 2 := by
    rw [← hsq]
    nlinarith
  change euclideanSqDist x z < r ^ 2
  exact lt_of_le_of_lt hb hlt

/-- **The free direction.**

A concentric Euclidean closed ball of radius strictly below the half-width
`3^m / 2` is contained in the cube of scale `m`; no dimensional factor is paid
because the sup norm never exceeds the Euclidean norm. -/
theorem euclideanClosedBall_subset_openCubeAtScale {z : Vec d} {m : ℤ} {r : ℝ}
    (hr0 : 0 ≤ r) (hr : r < (3 : ℝ) ^ m / 2) :
    euclideanClosedBall z r ⊆ openCubeAtScale z m := by
  intro x hx
  rw [mem_openCubeAtScale_iff]
  intro i
  have hxi : (x i - z i) ^ 2 ≤ r ^ 2 :=
    le_trans (sq_coord_sub_le_euclideanSqDist x z i) hx
  exact lt_of_le_of_lt (abs_le_of_sq_le_sq hxi hr0) hr

/-- The exact real volume of an explicit Euclidean ball of positive radius. -/
theorem volume_euclideanBall_toReal (z : Vec d) {r : ℝ} (hr : 0 < r) :
    (volume (euclideanBall z r)).toReal =
      r ^ d * Book.Ch01.euclideanUnitBallVolume d := by
  rw [euclideanBall_eq_translateSet_smul_unit_of_pos z hr, volume_translateSet_eq,
    Book.Ch01.volume_smul_toReal_of_pos hr]
  rfl

theorem euclideanUnitBallVolume_pos (d : ℕ) :
    0 < Book.Ch01.euclideanUnitBallVolume d :=
  lt_of_le_of_ne ENNReal.toReal_nonneg
    (Ne.symm (Book.Ch01.volume_euclideanBall_toReal_ne_zero (0 : Vec d)
      (by norm_num : (0 : ℝ) < 1)))

end Algsuperdiff.Section3.Provider.Diffusivity.Corrector
