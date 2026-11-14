/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Schauder.CubeSchauderAeIbp

/-!
# CubeSchauderAeSlopeDefect

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Cube Schauder: the slope-defect inequality of the a.e. identification

The master inequality of the a.e. identification `Ψ = ∇w`.  Fix a base point
`z ∈ □_m` and a scale `j` small enough that the Euclidean ball of radius `3^j/2`
around `z` sits inside `□_m`, and let `η = campanatoCutoff z j`.  For an
arbitrary affine competitor `ℓ = (c,g)` and an arbitrary reference vector `v`,

```text
  |g_i − v_i| · ∫_{□_m} η
      ≤ |∫_{□_m} (∂_i u − g_i) η|  +  ∫_{□_m} |∂_i u − v_i| η
      ≤ C(d)·3^{-j}·‖u − ℓ‖_{L²(W_j)}·|W_j|  +  ∫_{W_j} |∂_i u − v_i| ,
```

with `W_j = (z+□_j) ∩ □_m`.  Both right-hand terms are localized: the first is
`C(d)·K·√(3^j)·|W_j|` at the affine minimizer under the Campanato datum, and the
second is `|W_j|` times the oscillation average of `∂_i u` around `v` on the
window.  The left factor is bounded below by
`(3^j/(8(d+1)))^d = |euclideanBall z (3^j/8)|`'s own lower bound, because `η = 1`
there.

Taking `v = ∇u(z)` at a Lebesgue point of `∇u` and letting `j → −∞` therefore
forces `g_i → (∇u)_i(z)`, i.e. `Ψ(z) = ∇u(z)`.  **That last limit is not taken
here**: this module supplies the deterministic inequality only, and the Lebesgue
differentiation step remains the open residue.

## References

* ABK26.
-/

namespace Algsuperdiff.Section4.Provider.Schauder

open MeasureTheory Filter Topology
open HCPolySupport
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay
open Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

noncomputable section

variable {d : ℕ}

/-! ## 1. The cutoff has a definite mass -/

theorem euclideanBall_mono {z : Vec d} {r R : ℝ} (hr : 0 ≤ r) (hrR : r ≤ R) :
    euclideanBall z r ⊆ euclideanBall z R := by
  intro y hy
  have hy' : euclideanSqDist y z < r ^ 2 := hy
  have hsq : r ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ hr hrR 2
  exact lt_of_lt_of_le hy' hsq

/-- **The cutoff's mass.**  `∫_{□_m} η ≥ (3^j/(8(d+1)))^d`, because `η = 1` on
the Euclidean ball of radius `3^j/8` and that ball sits inside `□_m`. -/
theorem integral_campanatoCutoff_ge {m j : ℤ} {z : Vec d}
    (hsub : euclideanBall z ((3 : ℝ) ^ j / 2) ⊆ openCubeSet (originCube d m)) :
    ((3 : ℝ) ^ j / (8 * ((d : ℝ) + 1))) ^ d
      ≤ ∫ y in openCubeSet (originCube d m), campanatoCutoff z j y ∂volume := by
  have h3 : (0 : ℝ) < (3 : ℝ) ^ j := zpow_pos (by norm_num) j
  have hr : (0 : ℝ) < (3 : ℝ) ^ j / 8 := by linarith only [h3]
  have hBsub : euclideanBall z ((3 : ℝ) ^ j / 8) ⊆ openCubeSet (originCube d m) :=
    subset_trans (euclideanBall_mono hr.le (by linarith only [h3])) hsub
  have hBmeas : MeasurableSet (euclideanBall z ((3 : ℝ) ^ j / 8)) :=
    (isOpen_euclideanBall z _).measurableSet
  have hηint : Integrable (campanatoCutoff z j) (volume : Measure (Vec d)) :=
    Continuous.integrable_of_hasCompactSupport
      (campanatoCutoff_smooth z j).continuous (campanatoCutoff_hasCompactSupport z j)
  have hvol : ((3 : ℝ) ^ j / (8 * ((d : ℝ) + 1))) ^ d
      ≤ (volume (euclideanBall z ((3 : ℝ) ^ j / 8))).toReal := by
    have h := volume_toReal_euclideanBall_ge z hr
    refine le_trans (le_of_eq ?_) h
    congr 1
    field_simp
  have hBint : ∫ y in euclideanBall z ((3 : ℝ) ^ j / 8), campanatoCutoff z j y ∂volume
      = (volume (euclideanBall z ((3 : ℝ) ^ j / 8))).toReal := by
    have hcongr : ∫ y in euclideanBall z ((3 : ℝ) ^ j / 8), campanatoCutoff z j y ∂volume
        = ∫ _y in euclideanBall z ((3 : ℝ) ^ j / 8), (1 : ℝ) ∂volume := by
      refine setIntegral_congr_fun hBmeas fun y hy => ?_
      exact campanatoCutoff_eq_one hy
    rw [hcongr, setIntegral_const, measureReal_def, smul_eq_mul, mul_one]
  have hmono : ∫ y in euclideanBall z ((3 : ℝ) ^ j / 8), campanatoCutoff z j y ∂volume
      ≤ ∫ y in openCubeSet (originCube d m), campanatoCutoff z j y ∂volume := by
    refine setIntegral_mono_set hηint.integrableOn
      (Filter.Eventually.of_forall fun y => campanatoCutoff_nonneg z j y)
      (LE.le.eventuallyLE hBsub)
  rw [hBint] at hmono
  linarith only [hvol, hmono]

/-! ## 2. Integrability of the two cutoff pairings -/

private theorem integrable_grad_sub_const_mul_cutoff {m j : ℤ} (z : Vec d)
    (u : H1Function (openCubeSet (originCube d m))) (a : ℝ) (i : Fin d) :
    Integrable (fun y => (u.grad y i - a) * campanatoCutoff z j y)
      (volume.restrict (openCubeSet (originCube d m))) := by
  have hUdom : IsOpenBoundedConvexDomain (openCubeSet (originCube d m)) :=
    isOpenBoundedConvexDomain_openCubeSet _
  have : IsFiniteMeasure (volume.restrict (openCubeSet (originCube d m))) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact hUdom.volume_lt_top
  have hgL2 : MemLp (fun y => u.grad y i) 2
      (volume.restrict (openCubeSet (originCube d m))) := by
    simpa only [volumeMeasureOn] using u.gradMemL2 i
  have hgint : Integrable (fun y => u.grad y i - a)
      (volume.restrict (openCubeSet (originCube d m))) :=
    (hgL2.integrable one_le_two).sub (integrable_const a)
  refine (hgint.bdd_mul (c := 1)
    (campanatoCutoff_smooth z j).continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)).congr ?_
  · rw [Real.norm_eq_abs, abs_of_nonneg (campanatoCutoff_nonneg z j y)]
    exact campanatoCutoff_le_one z j y
  · filter_upwards with y using mul_comm _ _

/-! ## 3. The slope-defect inequality -/

/-- **The slope-defect inequality.**

For any affine competitor `ℓ = (c,g)` and any reference vector `v`, the defect
`|g_i − v_i|`, weighted by the cutoff's mass, is controlled by the cutoff
pairing bound plus the oscillation of `∂_i u` around `v_i` on the window.  Both
right-hand terms are localized to `W_j = (z+□_j) ∩ □_m`. -/
theorem abs_slope_sub_le_cutoff_split {m j : ℤ} {z : Vec d}
    (hz : z ∈ openCubeSet (originCube d m)) (hjm : j - 1 ≤ m)
    (hsub : euclideanBall z ((3 : ℝ) ^ j / 2) ⊆ openCubeSet (originCube d m))
    (u : H1Function (openCubeSet (originCube d m))) (c : ℝ) (g v : Vec d) (i : Fin d) :
    |g i - v i| * (∫ y in openCubeSet (originCube d m), campanatoCutoff z j y ∂volume)
      ≤ cutoffIbpConst d * (3 : ℝ) ^ (-j)
          * (affineDistOn (truncatedWindow z m j) u.toFun c g
              * (volume (truncatedWindow z m j)).toReal)
        + ∫ y in truncatedWindow z m j, |u.grad y i - v i| ∂volume := by
  have hUdom : IsOpenBoundedConvexDomain (openCubeSet (originCube d m)) :=
    isOpenBoundedConvexDomain_openCubeSet _
  have : IsFiniteMeasure (volume.restrict (openCubeSet (originCube d m))) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact hUdom.volume_lt_top
  have hWU : truncatedWindow z m j ⊆ openCubeSet (originCube d m) :=
    truncatedWindow_subset_domain z m j
  have hUmeas : MeasurableSet (openCubeSet (originCube d m)) :=
    measurableSet_openCubeSet _
  have hA := integrable_grad_sub_const_mul_cutoff (j := j) z u (g i) i
  have hB := integrable_grad_sub_const_mul_cutoff (j := j) z u (v i) i
  have hηint : Integrable (campanatoCutoff z j)
      (volume.restrict (openCubeSet (originCube d m))) :=
    (Continuous.integrable_of_hasCompactSupport (campanatoCutoff_smooth z j).continuous
      (campanatoCutoff_hasCompactSupport z j)).integrableOn
  -- the algebraic split
  have hsplit : (g i - v i)
        * (∫ y in openCubeSet (originCube d m), campanatoCutoff z j y ∂volume)
      = (∫ y in openCubeSet (originCube d m),
            (u.grad y i - v i) * campanatoCutoff z j y ∂volume)
        - ∫ y in openCubeSet (originCube d m),
            (u.grad y i - g i) * campanatoCutoff z j y ∂volume := by
    rw [← integral_sub hB hA, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    ring
  -- the oscillation term, localized
  have hzero : ∀ y ∈ openCubeSet (originCube d m) \ truncatedWindow z m j,
      |(u.grad y i - v i) * campanatoCutoff z j y| = 0 := by
    rintro y ⟨hyU, hyW⟩
    have hnb : y ∉ euclideanBall z ((3 : ℝ) ^ j / 2) := fun hb =>
      hyW ⟨euclideanBall_subset_image_add_openCubeSet z j hb, hyU⟩
    have hns : y ∉ tsupport (campanatoCutoff z j) := fun h =>
      hnb (campanatoCutoff_tsupport_subset z j h)
    rw [image_eq_zero_of_notMem_tsupport hns]
    simp
  have hosc1 : |∫ y in openCubeSet (originCube d m),
        (u.grad y i - v i) * campanatoCutoff z j y ∂volume|
      ≤ ∫ y in openCubeSet (originCube d m),
        |(u.grad y i - v i) * campanatoCutoff z j y| ∂volume := by
    have h := norm_integral_le_integral_norm
      (μ := volume.restrict (openCubeSet (originCube d m)))
      (fun y => (u.grad y i - v i) * campanatoCutoff z j y)
    simpa only [Real.norm_eq_abs] using h
  have hosc2 : ∫ y in openCubeSet (originCube d m),
        |(u.grad y i - v i) * campanatoCutoff z j y| ∂volume
      = ∫ y in truncatedWindow z m j,
        |(u.grad y i - v i) * campanatoCutoff z j y| ∂volume :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hUmeas hWU hzero
  have hgvW : Integrable (fun y => |u.grad y i - v i|)
      (volume.restrict (truncatedWindow z m j)) := by
    have hgL2 : MemLp (fun y => u.grad y i) 2
        (volume.restrict (openCubeSet (originCube d m))) := by
      simpa only [volumeMeasureOn] using u.gradMemL2 i
    have hW : MemLp (fun y => u.grad y i) 2
        (volume.restrict (truncatedWindow z m j)) :=
      memLp_restrict_of_subset hWU hgL2
    have : IsFiniteMeasure (volume.restrict (truncatedWindow z m j)) := by
      refine ⟨?_⟩
      rw [Measure.restrict_apply_univ]
      exact (isOpenBoundedConvexDomain_truncatedWindow z m j).volume_lt_top
    exact ((hW.integrable one_le_two).sub (integrable_const (v i))).abs
  have hosc3 : ∫ y in truncatedWindow z m j,
        |(u.grad y i - v i) * campanatoCutoff z j y| ∂volume
      ≤ ∫ y in truncatedWindow z m j, |u.grad y i - v i| ∂volume := by
    refine integral_mono (hB.mono_measure (Measure.restrict_mono hWU le_rfl)).abs hgvW ?_
    intro y
    change |(u.grad y i - v i) * campanatoCutoff z j y| ≤ |u.grad y i - v i|
    rw [abs_mul, abs_of_nonneg (campanatoCutoff_nonneg z j y)]
    exact mul_le_of_le_one_right (abs_nonneg _) (campanatoCutoff_le_one z j y)
  -- the pairing term
  have hpair := abs_integral_grad_sub_slope_mul_cutoff_le hz hjm hsub u c g i
  -- assemble
  have habs : |(g i - v i)
        * (∫ y in openCubeSet (originCube d m), campanatoCutoff z j y ∂volume)|
      ≤ (∫ y in truncatedWindow z m j, |u.grad y i - v i| ∂volume)
        + |∫ y in openCubeSet (originCube d m),
            (u.grad y i - g i) * campanatoCutoff z j y ∂volume| := by
    rw [hsplit]
    refine (abs_sub _ _).trans ?_
    have h := hosc1.trans (le_of_eq hosc2) |>.trans hosc3
    linarith only [h]
  have hmass : (0 : ℝ)
      ≤ ∫ y in openCubeSet (originCube d m), campanatoCutoff z j y ∂volume :=
    integral_nonneg fun y => campanatoCutoff_nonneg z j y
  have hgoal : |g i - v i|
        * (∫ y in openCubeSet (originCube d m), campanatoCutoff z j y ∂volume)
      = |(g i - v i)
        * (∫ y in openCubeSet (originCube d m), campanatoCutoff z j y ∂volume)| := by
    rw [abs_mul, abs_of_nonneg hmass]
  rw [hgoal]
  linarith only [habs, hpair]

end

end Algsuperdiff.Section4.Provider.Schauder
