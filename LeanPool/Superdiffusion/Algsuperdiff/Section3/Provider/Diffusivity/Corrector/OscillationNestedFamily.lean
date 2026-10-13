/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.HarmonicReplaceMinkowski
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.OscillationNestedTransport

/-!
# OscillationNestedFamily

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Scale bookkeeping for the nested-recentring telescope

The nested-recentring route of `OscillationTelescope` compares normalized
mean-square quantities across the concentric cube family
`U_j = z + cu_{n+j}`.  Two conversions occur over and over in that comparison and
are isolated here.

* **The volume-ratio step.**  A harmonic replacement born at scale `n+j` is
  controlled only on its own cube, while the telescope needs its size on every
  finer cube.  Restricting a normalized mean-square deviation from `U_{j+i}` to
  `U_j` costs exactly the volume ratio `3^{id}`, hence the factor `rho^i` after
  taking square roots, where `rho = sqrt (3^d)`.  This single geometric constant
  is the `rho` of `OscillationTelescope`, and it is also what makes the
  small-gap branch of the assembly affordable.
* **The recentring step.**  Passing from an oscillation (deviation from the
  cube average) to a deviation from an arbitrary centre is free in the right
  direction, and the `L^2` hypotheses under which it is legal are exactly `L^2`
  membership of the field on the cube.

The remaining two lemmas are the elementary `sqrt`/`pow` interchange used to
write the volume-ratio factor as `rho^i`, and the invariance of the
mean-square deviation from the origin under a sign change, which is how a
difference of two replacements is split by the triangle inequality.

## Contents

* `instIsFiniteMeasureVolumeMeasureOnOpenCubeAtScale` -- the finiteness
  instance for concentric cubes, so that the `L^2` A applies without local
  `haveI`s.
* `sqrt_pow_natCast` -- `sqrt (x^i) = (sqrt x)^i` for `0 <= x`.
* `meanSquareDeviationVecOn_neg` -- sign invariance of the deviation from `0`.
* `sqrt_meanSquareOscillationVecOn_le_sqrt_meanSquareDeviationVecOn_of_memVectorL2`
  -- the recentring step under `L^2` membership.
* `sqrt_meanSquareDeviationVecOn_le_pow_mul_of_le` -- **the volume-ratio step**
  on the concentric family, with the factor `rho^i`.

## Portability

This file depends only on **Mathlib**, on **CoarseGraining**
(`Homogenization.*`) and on the oscillation layer of this same directory.  It
mentions no object of the manuscript: no model, no cutoff, no shell, no
corrector, no `sigmaBar`.  It is intended to be portable into CoarseGraining by
a single mechanical namespace rename.

## References

* ABK26, `e.nablaw.oscillations` (the eventual consumer).
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.Corrector

open HCPolySupport HCPolySupport.Book.Ch03 MeasureTheory

variable {d : ℕ}

/-- A concentric cube has finite volume, so the `L^2` A applies on it. -/
instance instIsFiniteMeasureVolumeMeasureOnOpenCubeAtScale (z : Vec d) (m : ℤ) :
    IsFiniteMeasure (volumeMeasureOn (openCubeAtScale z m)) :=
  isFiniteMeasure_restrict.mpr (volume_openCubeAtScale_ne_top z m)

/-- `sqrt (x ^ i) = (sqrt x) ^ i` for a nonnegative base.  Used to write the
triadic volume ratio `3^{id}` as the `i`-th power of the single constant
`rho = sqrt (3^d)`. -/
theorem sqrt_pow_natCast {x : ℝ} (hx : 0 ≤ x) (i : ℕ) :
    Real.sqrt (x ^ i) = Real.sqrt x ^ i := by
  induction i with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, pow_succ, Real.sqrt_mul (pow_nonneg hx k), ih]

/-- The mean-square deviation from the origin does not see a sign change.  This
is what lets the triangle inequality split the difference of two harmonic
replacements into their two individual sizes. -/
theorem meanSquareDeviationVecOn_neg (V : Set (Vec d)) (f : Vec d → Vec d) :
    Book.Ch01.meanSquareDeviationVecOn V (fun x => -f x) 0 =
      Book.Ch01.meanSquareDeviationVecOn V f 0 := by
  refine Finset.sum_congr rfl fun k _ => ?_
  have hfun : (fun y => ((-f y) k - (0 : Vec d) k) ^ 2)
      = fun y => (f y k - (0 : Vec d) k) ^ 2 := by
    funext y
    have hneg : (-f y) k = -(f y k) := rfl
    have hzero : (0 : Vec d) k = 0 := rfl
    rw [hneg, hzero]
    ring
  show volumeAverage V (fun y => ((-f y) k - (0 : Vec d) k) ^ 2)
    = volumeAverage V (fun y => (f y k - (0 : Vec d) k) ^ 2)
  rw [hfun]

/-- **Recentring under `L^2` membership.**

The normalized `L^2` oscillation of a square-integrable field is at most its
normalized `L^2` deviation from any centre. -/
theorem sqrt_meanSquareOscillationVecOn_le_sqrt_meanSquareDeviationVecOn_of_memVectorL2
    {V : Set (Vec d)} (hfin : volume V ≠ ⊤) (hpos : 0 < (volume V).toReal)
    [IsFiniteMeasure (volumeMeasureOn V)] {f : Vec d → Vec d}
    (hf : MemVectorL2 V f) (c : Vec d) :
    Real.sqrt (Book.Ch01.meanSquareOscillationVecOn V f) ≤
      Real.sqrt (Book.Ch01.meanSquareDeviationVecOn V f c) := by
  have hint : ∀ i : Fin d, IntegrableOn (fun x => f x i) V volume := fun i =>
    (memScalarL2_coord_of_memVectorL2 hf i).integrable (by norm_num)
  have hint2 : ∀ i : Fin d, IntegrableOn (fun x => (f x i) ^ 2) V volume := by
    intro i
    have hcoord : MemScalarL2 V (fun x => f x i) := memScalarL2_coord_of_memVectorL2 hf i
    simpa [pow_two] using! hcoord.integrable_mul hcoord
  exact Real.sqrt_le_sqrt
    (meanSquareOscillationVecOn_le_meanSquareDeviationVecOn hfin hpos c hint hint2)

/-- **The volume-ratio step on the concentric family.**

If the coarse cube `z + cu_{m'}` sits `i` triadic scales above the fine cube
`z + cu_m`, then restricting the normalized `L^2` deviation from the coarse cube
to the fine one costs exactly `rho^i`, where `rho = sqrt (3^d)` is the square
root of the one-step volume ratio. -/
theorem sqrt_meanSquareDeviationVecOn_le_pow_mul_of_le (z : Vec d) {m m' : ℤ} {i : ℕ}
    (hi : m + (i : ℤ) = m') {f : Vec d → Vec d}
    (hf : MemVectorL2 (openCubeAtScale z m') f) (c : Vec d) :
    Real.sqrt (Book.Ch01.meanSquareDeviationVecOn (openCubeAtScale z m) f c) ≤
      Real.sqrt ((3 : ℝ) ^ d) ^ i *
        Real.sqrt (Book.Ch01.meanSquareDeviationVecOn (openCubeAtScale z m') f c) := by
  subst hi
  have hsub : openCubeAtScale z m ⊆ openCubeAtScale z (m + (i : ℤ)) :=
    openCubeAtScale_subset_of_le z (by omega)
  have hint : ∀ k : Fin d,
      IntegrableOn (fun y => (f y k - c k) ^ 2) (openCubeAtScale z (m + (i : ℤ))) volume :=
    fun k => Book.Ch01.integrableOn_coord_sub_const_sq_of_memVectorL2 hf c k
  have hratio := meanSquareDeviationVecOn_le_volume_ratio_mul hsub
    (volume_openCubeAtScale_toReal_pos z m)
    (volume_openCubeAtScale_toReal_pos z (m + (i : ℤ))) hint
  have hval : (volume (openCubeAtScale z (m + (i : ℤ)))).toReal /
      (volume (openCubeAtScale z m)).toReal = ((3 : ℝ) ^ d) ^ i := by
    rw [volume_openCubeAtScale_toReal, volume_openCubeAtScale_toReal]
    have h3 : (3 : ℝ) ^ (m + (i : ℤ)) = (3 : ℝ) ^ m * (3 : ℝ) ^ i := by
      rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_natCast]
    have hne : ((3 : ℝ) ^ m) ^ d ≠ 0 := by
      have hp : (0 : ℝ) < (3 : ℝ) ^ m := zpow_three_pos m
      positivity
    rw [h3, mul_pow]
    rw [mul_comm (((3 : ℝ) ^ m) ^ d) (((3 : ℝ) ^ i) ^ d), mul_div_assoc,
      div_self hne, mul_one, pow_right_comm]
  rw [hval] at hratio
  have hnn : (0 : ℝ) ≤ ((3 : ℝ) ^ d) ^ i := by positivity
  calc Real.sqrt (Book.Ch01.meanSquareDeviationVecOn (openCubeAtScale z m) f c)
      ≤ Real.sqrt (((3 : ℝ) ^ d) ^ i *
          Book.Ch01.meanSquareDeviationVecOn (openCubeAtScale z (m + (i : ℤ))) f c) :=
        Real.sqrt_le_sqrt hratio
    _ = Real.sqrt (((3 : ℝ) ^ d) ^ i) *
          Real.sqrt (Book.Ch01.meanSquareDeviationVecOn
            (openCubeAtScale z (m + (i : ℤ))) f c) := Real.sqrt_mul hnn _
    _ = Real.sqrt ((3 : ℝ) ^ d) ^ i *
          Real.sqrt (Book.Ch01.meanSquareDeviationVecOn
            (openCubeAtScale z (m + (i : ℤ))) f c) := by
        rw [sqrt_pow_natCast (by positivity : (0 : ℝ) ≤ (3 : ℝ) ^ d)]

end Algsuperdiff.Section3.Provider.Diffusivity.Corrector
