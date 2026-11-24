/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.RadialPoissonCertificate
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Polar mass of squared-radius profiles

In positive complex dimension, Haar polar coordinates and the substitution
`s = r ^ 2` express the integral of a squared-radius profile through its
weighted one-variable integral.  Applied to the difference of two normalized
radial kernels, equality of their total masses forces that weighted integral
to vanish.

The formula is intentionally restricted to `0 < n`.  In complex dimension
zero the ambient Haar space is a singleton and the weighted `Ioi 0` expression
is not the correct polar model.
-/

@[expose] public section

open Set Metric MeasureTheory
open scoped ENNReal NNReal Topology

namespace SGPT.Foundations.Analysis.Pending.RadialPolarMass

open FirstPass
open HolomorphicPullback
open RadialPoissonCertificate

/-- Polar integration for a profile of the squared norm on a positive
dimensional standard complex model. -/
theorem integral_sqNorm_radial {n : ℕ} (hn : 0 < n) (f : ℝ → ℝ) :
    ∫ x : ComplexModel n, f (‖x‖ ^ 2) ∂volume =
      ((n : ℝ) * volume.real (ball (0 : ComplexModel n) 1)) *
        ∫ s in Ioi (0 : ℝ), s ^ (n - 1) * f s := by
  let _ : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let _ : Nontrivial (ComplexModel n) := inferInstance
  rw [MeasureTheory.integral_fun_norm_addHaar
    (volume : Measure (ComplexModel n)) (fun r : ℝ => f (r ^ 2))]
  rw [finrank_real_complexModel]
  have hsubst := MeasureTheory.integral_comp_rpow_Ioi_of_pos
    (g := fun s : ℝ => s ^ (n - 1) * f s) (p := (2 : ℝ)) (by norm_num)
  have hpoint :
      (fun r : ℝ => ((2 : ℝ) * r ^ ((2 : ℝ) - 1)) •
          ((r ^ (2 : ℝ)) ^ (n - 1) * f (r ^ (2 : ℝ)))) =
        fun r => 2 * (r ^ (2 * n - 1) * f (r ^ 2)) := by
    funext r
    rw [show 2 * n - 1 = 2 * (n - 1) + 1 by omega, pow_succ, pow_mul]
    norm_num [Real.rpow_two, Real.rpow_one]
    ring
  rw [hpoint, integral_const_mul] at hsubst
  simp only [nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat, smul_eq_mul]
  rw [← hsubst]
  ring

/-- Every two normalized explicit radial kernels have zero weighted
squared-radius mass difference in positive complex dimension. -/
theorem integral_explicitRadialKernelSqDifference_weighted_eq_zero
    {n : ℕ} (hn : 0 < n) (R : ℝ) (hR : 0 < R) (a b : ℕ) :
    ∫ s in Ioi (0 : ℝ), s ^ (n - 1) *
        explicitRadialKernelSqDifference (n := n) R hR a b s = 0 := by
  have hka : Integrable (explicitRadialKernel (n := n) R hR a) volume :=
    (explicitRadialKernel_contDiff R hR a).continuous.integrable_of_hasCompactSupport
      (explicitRadialKernel_hasCompactSupport R hR a)
  have hkb : Integrable (explicitRadialKernel (n := n) R hR b) volume :=
    (explicitRadialKernel_contDiff R hR b).continuous.integrable_of_hasCompactSupport
      (explicitRadialKernel_hasCompactSupport R hR b)
  have hspatial :
      ∫ x : ComplexModel n,
          (explicitRadialKernel R hR a x - explicitRadialKernel R hR b x) ∂volume = 0 := by
    rw [integral_sub hka hkb, explicitRadialKernel_integral_one,
      explicitRadialKernel_integral_one, sub_self]
  have hprofile :
      ∫ x : ComplexModel n,
          explicitRadialKernelSqDifference (n := n) R hR a b (‖x‖ ^ 2) ∂volume = 0 := by
    calc
      _ = ∫ x : ComplexModel n,
          (explicitRadialKernel R hR a x - explicitRadialKernel R hR b x) ∂volume := by
            apply integral_congr_ae
            filter_upwards with x
            exact (explicitRadialKernel_sub_eq_sqDifference_norm_sq R hR a b x).symm
      _ = 0 := hspatial
  have hpolar := integral_sqNorm_radial hn
    (explicitRadialKernelSqDifference (n := n) R hR a b)
  have hmul :
      ((n : ℝ) * volume.real (ball (0 : ComplexModel n) 1)) *
          ∫ s in Ioi (0 : ℝ), s ^ (n - 1) *
            explicitRadialKernelSqDifference (n := n) R hR a b s = 0 := by
    rw [← hpolar, hprofile]
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hn
  have hvolume : 0 < volume.real (ball (0 : ComplexModel n) 1) :=
    ENNReal.toReal_pos (measure_ball_pos volume 0 one_pos).ne'
      measure_ball_lt_top.ne
  exact (mul_eq_zero.mp hmul).resolve_left (mul_ne_zero hnReal.ne' hvolume.ne')

end SGPT.Foundations.Analysis.Pending.RadialPolarMass
