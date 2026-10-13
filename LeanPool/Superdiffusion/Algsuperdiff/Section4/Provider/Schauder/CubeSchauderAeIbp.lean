/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Schauder.CubeSchauderAeCutoff
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepSchauderExcess
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.CubeMoments

/-!
# CubeSchauderAeIbp

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Cube Schauder: the integration-by-parts step of the a.e. identification

For the smooth cutoff `η = campanatoCutoff z j` supported inside `□_m`, the weak
gradient identity of `u ∈ H¹(□_m)` and the same identity for the *smooth* affine
competitor `ℓ = (c,g)` combine into

```text
  ∫_{□_m} (∂_i u − g_i)·η  =  −∫_{□_m} (u − ℓ)·∂_i η ,
```

and the right-hand side is bounded by `‖∂_i η‖_∞ · ∫_{W_j} |u − ℓ|`, because
`∂_i η` vanishes off the Euclidean ball of radius `3^j/2`, which sits inside the
window `W_j = (z+□_j) ∩ □_m`.  The `L¹ ≤ L²` comparison of
`CubeSchauderAeCutoff` then converts the last integral into the window's own
`L²` distance to `ℓ`:

```text
  |∫_{□_m} (∂_i u − g_i)·η|  ≤  C(d)·3^{-j} · ‖u − ℓ‖_{L²(W_j)} · |W_j| .
```

At the affine minimizer of `W_j` the middle factor is the unnormalized excess,
so the Campanato datum `E(u, W_j) ≤ K√(3^j)` turns the bound into
`C(d)·K·√(3^j)·|W_j|`.

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

/-! ## 1. The affine competitor is smooth -/

theorem contDiff_affineEval (c : ℝ) (g : Vec d) : ContDiff ℝ 1 (affineEval c g) := by
  have heq : affineEval c g = fun x => c + vecDotCLM g x := by
    funext x
    rw [affineEval, vecDotCLM_apply]
  rw [heq]
  exact contDiff_const.add (vecDotCLM g).contDiff

theorem fderiv_affineEval_apply (c : ℝ) (g : Vec d) (x : Vec d) (i : Fin d) :
    (fderiv ℝ (affineEval c g) x) (basisVec i) = g i := by
  rw [(hasFDerivAt_affineEval c g x).fderiv, vecDotCLM_apply, vecDot_basisVec_right]

/-! ## 2. Continuity and compact support of the cutoff derivative -/

theorem continuous_fderiv_campanatoCutoff_apply (z : Vec d) (j : ℤ) (i : Fin d) :
    Continuous fun y => (fderiv ℝ (campanatoCutoff z j) y) (basisVec i) :=
  ((campanatoCutoff_smooth z j).continuous_fderiv (by norm_num)).clm_apply continuous_const

theorem hasCompactSupport_fderiv_campanatoCutoff_apply (z : Vec d) (j : ℤ) (i : Fin d) :
    HasCompactSupport fun y => (fderiv ℝ (campanatoCutoff z j) y) (basisVec i) :=
  HasCompactSupport.fderiv_apply (𝕜 := ℝ) (campanatoCutoff_hasCompactSupport z j)
    (basisVec i)

/-! ## 3. The integration-by-parts identity -/

/-- **The cutoff pairing identity.**

The weak gradient identity of `u`, minus the classical one for the smooth affine
competitor `ℓ = (c,g)`.  No hypothesis beyond the support condition on the
cutoff. -/
theorem integral_grad_sub_slope_mul_cutoff {m j : ℤ} {z : Vec d}
    (hsub : euclideanBall z ((3 : ℝ) ^ j / 2) ⊆ openCubeSet (originCube d m))
    (u : H1Function (openCubeSet (originCube d m))) (c : ℝ) (g : Vec d) (i : Fin d) :
    ∫ y in openCubeSet (originCube d m),
        (u.grad y i - g i) * campanatoCutoff z j y ∂volume
      = -∫ y in openCubeSet (originCube d m),
          (u.toFun y - affineEval c g y)
            * (fderiv ℝ (campanatoCutoff z j) y) (basisVec i) ∂volume := by
  have hUdom : IsOpenBoundedConvexDomain (openCubeSet (originCube d m)) :=
    isOpenBoundedConvexDomain_openCubeSet _
  have : IsFiniteMeasure (volume.restrict (openCubeSet (originCube d m))) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact hUdom.volume_lt_top
  have hη := campanatoCutoff_smooth z j
  have hηc := campanatoCutoff_hasCompactSupport z j
  have hηs : tsupport (campanatoCutoff z j) ⊆ openCubeSet (originCube d m) :=
    subset_trans (campanatoCutoff_tsupport_subset z j) hsub
  have h1 := u.hasWeakGradient i (campanatoCutoff z j) hη hηc hηs
  have h2 := (HasWeakGradientOn.of_contDiff
    (U := openCubeSet (originCube d m)) (contDiff_affineEval c g))
    i (campanatoCutoff z j) hη hηc hηs
  -- the four integrability slots
  have hDcont := continuous_fderiv_campanatoCutoff_apply z j i
  have hDbd : ∀ y, ‖(fderiv ℝ (campanatoCutoff z j) y) (basisVec i)‖
      ≤ cutoffIbpConst d * (3 : ℝ) ^ (-j) := by
    intro y
    rw [Real.norm_eq_abs]
    exact abs_fderiv_campanatoCutoff_apply_le z j y i
  have huL2 : MemLp u.toFun 2 (volume.restrict (openCubeSet (originCube d m))) := by
    simpa only [volumeMeasureOn] using u.memL2
  have hgL2 : MemLp (fun y => u.grad y i) 2
      (volume.restrict (openCubeSet (originCube d m))) := by
    simpa only [volumeMeasureOn] using u.gradMemL2 i
  have huint : Integrable u.toFun (volume.restrict (openCubeSet (originCube d m))) :=
    huL2.integrable one_le_two
  have hgint : Integrable (fun y => u.grad y i)
      (volume.restrict (openCubeSet (originCube d m))) :=
    hgL2.integrable one_le_two
  have hI1 : Integrable (fun y => u.toFun y
      * (fderiv ℝ (campanatoCutoff z j) y) (basisVec i))
      (volume.restrict (openCubeSet (originCube d m))) := by
    refine (huint.bdd_mul (c := cutoffIbpConst d * (3 : ℝ) ^ (-j))
      hDcont.aestronglyMeasurable (Filter.Eventually.of_forall hDbd)).congr ?_
    filter_upwards with y using mul_comm _ _
  have hI2 : Integrable (fun y => affineEval c g y
      * (fderiv ℝ (campanatoCutoff z j) y) (basisVec i))
      (volume.restrict (openCubeSet (originCube d m))) := by
    refine Integrable.integrableOn ?_
    refine Continuous.integrable_of_hasCompactSupport
      ((continuous_affineEval c g).mul hDcont) ?_
    exact (hasCompactSupport_fderiv_campanatoCutoff_apply z j i).mul_left
  have hI3 : Integrable (fun y => u.grad y i * campanatoCutoff z j y)
      (volume.restrict (openCubeSet (originCube d m))) := by
    refine (hgint.bdd_mul (c := 1) hη.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)).congr ?_
    · rw [Real.norm_eq_abs, abs_of_nonneg (campanatoCutoff_nonneg z j y)]
      exact campanatoCutoff_le_one z j y
    · filter_upwards with y using mul_comm _ _
  have hI4 : Integrable (fun y => g i * campanatoCutoff z j y)
      (volume.restrict (openCubeSet (originCube d m))) := by
    refine Integrable.integrableOn ?_
    exact (Continuous.integrable_of_hasCompactSupport hη.continuous hηc).const_mul _
  -- split both sides
  have hL : ∫ y in openCubeSet (originCube d m), (u.toFun y - affineEval c g y)
        * (fderiv ℝ (campanatoCutoff z j) y) (basisVec i) ∂volume
      = (∫ y in openCubeSet (originCube d m), u.toFun y
            * (fderiv ℝ (campanatoCutoff z j) y) (basisVec i) ∂volume)
        - ∫ y in openCubeSet (originCube d m), affineEval c g y
            * (fderiv ℝ (campanatoCutoff z j) y) (basisVec i) ∂volume := by
    rw [← integral_sub hI1 hI2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    ring
  have hR : ∫ y in openCubeSet (originCube d m),
        (u.grad y i - g i) * campanatoCutoff z j y ∂volume
      = (∫ y in openCubeSet (originCube d m), u.grad y i * campanatoCutoff z j y ∂volume)
        - ∫ y in openCubeSet (originCube d m), g i * campanatoCutoff z j y ∂volume := by
    rw [← integral_sub hI3 hI4]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    ring
  have h2' : ∫ y in openCubeSet (originCube d m), affineEval c g y
        * (fderiv ℝ (campanatoCutoff z j) y) (basisVec i) ∂volume
      = -∫ y in openCubeSet (originCube d m), g i * campanatoCutoff z j y ∂volume := by
    rw [h2]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show (fderiv ℝ (affineEval c g) y) (basisVec i) * campanatoCutoff z j y
      = g i * campanatoCutoff z j y
    rw [fderiv_affineEval_apply]
  rw [hR, hL, h1, h2']
  ring

/-! ## 4. The bound -/

/-- **The cutoff pairing bound.**

`|∫_{□_m} (∂_i u − g_i) η| ≤ C(d)·3^{-j}·‖u − ℓ‖_{L²(W_j)}·|W_j|`, for every
affine competitor `ℓ = (c,g)`. -/
theorem abs_integral_grad_sub_slope_mul_cutoff_le {m j : ℤ} {z : Vec d}
    (hz : z ∈ openCubeSet (originCube d m)) (hjm : j - 1 ≤ m)
    (hsub : euclideanBall z ((3 : ℝ) ^ j / 2) ⊆ openCubeSet (originCube d m))
    (u : H1Function (openCubeSet (originCube d m))) (c : ℝ) (g : Vec d) (i : Fin d) :
    |∫ y in openCubeSet (originCube d m),
        (u.grad y i - g i) * campanatoCutoff z j y ∂volume|
      ≤ cutoffIbpConst d * (3 : ℝ) ^ (-j)
          * (affineDistOn (truncatedWindow z m j) u.toFun c g
              * (volume (truncatedWindow z m j)).toReal) := by
  have hWU : truncatedWindow z m j ⊆ openCubeSet (originCube d m) :=
    truncatedWindow_subset_domain z m j
  have hUmeas : MeasurableSet (openCubeSet (originCube d m)) :=
    measurableSet_openCubeSet _
  have hWfin : volume (truncatedWindow z m j) ≠ ⊤ :=
    ne_of_lt (volume_truncatedWindow_lt_top z m j)
  have hWpos : 0 < (volume (truncatedWindow z m j)).toReal :=
    volume_toReal_truncatedWindow_pos z hz hjm
  have : IsFiniteMeasure (volume.restrict (truncatedWindow z m j)) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.2 hWfin
  have hMnn : (0 : ℝ) ≤ cutoffIbpConst d * (3 : ℝ) ^ (-j) :=
    mul_nonneg (cutoffIbpConst_nonneg d) (zpow_pos (by norm_num) _).le
  -- the `L²` datum on the window
  have huW : MemLp u.toFun 2 (volume.restrict (truncatedWindow z m j)) := by
    refine memLp_restrict_of_subset hWU ?_
    simpa only [volumeMeasureOn] using u.memL2
  have hsqW : IntegrableOn (fun y => (u.toFun y - affineEval c g y) ^ 2)
      (truncatedWindow z m j) volume :=
    integrableOn_sub_affineEval_sq_truncatedWindow z huW c g
  have haesm : AEStronglyMeasurable (fun y => u.toFun y - affineEval c g y)
      (volume.restrict (truncatedWindow z m j)) :=
    huW.aestronglyMeasurable.sub (continuous_affineEval c g).aestronglyMeasurable
  have hmemW : MemLp (fun y => u.toFun y - affineEval c g y) 2
      (volume.restrict (truncatedWindow z m j)) :=
    (memLp_two_iff_integrable_sq haesm).2 hsqW
  have hintW : Integrable (fun y => |u.toFun y - affineEval c g y|)
      (volume.restrict (truncatedWindow z m j)) :=
    (hmemW.integrable one_le_two).abs
  -- the pairing identity and the pointwise vanishing off the window
  rw [integral_grad_sub_slope_mul_cutoff hsub u c g i, abs_neg]
  have hzero : ∀ y ∈ openCubeSet (originCube d m) \ truncatedWindow z m j,
      |(u.toFun y - affineEval c g y)
        * (fderiv ℝ (campanatoCutoff z j) y) (basisVec i)| = 0 := by
    rintro y ⟨hyU, hyW⟩
    have hnb : y ∉ euclideanBall z ((3 : ℝ) ^ j / 2) := fun hb =>
      hyW ⟨euclideanBall_subset_image_add_openCubeSet z j hb, hyU⟩
    rw [fderiv_campanatoCutoff_eq_zero hnb]
    simp
  have hstep1 : |∫ y in openCubeSet (originCube d m), (u.toFun y - affineEval c g y)
        * (fderiv ℝ (campanatoCutoff z j) y) (basisVec i) ∂volume|
      ≤ ∫ y in openCubeSet (originCube d m), |(u.toFun y - affineEval c g y)
        * (fderiv ℝ (campanatoCutoff z j) y) (basisVec i)| ∂volume := by
    have h := norm_integral_le_integral_norm
      (μ := volume.restrict (openCubeSet (originCube d m)))
      (fun y => (u.toFun y - affineEval c g y)
        * (fderiv ℝ (campanatoCutoff z j) y) (basisVec i))
    simpa only [Real.norm_eq_abs] using h
  have hstep2 : ∫ y in openCubeSet (originCube d m), |(u.toFun y - affineEval c g y)
        * (fderiv ℝ (campanatoCutoff z j) y) (basisVec i)| ∂volume
      = ∫ y in truncatedWindow z m j, |(u.toFun y - affineEval c g y)
        * (fderiv ℝ (campanatoCutoff z j) y) (basisVec i)| ∂volume :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hUmeas hWU hzero
  have hptw : ∀ y, |(u.toFun y - affineEval c g y)
        * (fderiv ℝ (campanatoCutoff z j) y) (basisVec i)|
      ≤ cutoffIbpConst d * (3 : ℝ) ^ (-j) * |u.toFun y - affineEval c g y| := by
    intro y
    rw [abs_mul]
    have h := abs_fderiv_campanatoCutoff_apply_le z j y i
    have hmul := mul_le_mul_of_nonneg_left h (abs_nonneg (u.toFun y - affineEval c g y))
    linarith only [hmul]
  have hstep3 : ∫ y in truncatedWindow z m j, |(u.toFun y - affineEval c g y)
        * (fderiv ℝ (campanatoCutoff z j) y) (basisVec i)| ∂volume
      ≤ cutoffIbpConst d * (3 : ℝ) ^ (-j)
        * ∫ y in truncatedWindow z m j, |u.toFun y - affineEval c g y| ∂volume := by
    rw [← integral_const_mul]
    refine integral_mono ?_ (hintW.const_mul _) hptw
    have hFint : Integrable (fun y => (u.toFun y - affineEval c g y)
        * (fderiv ℝ (campanatoCutoff z j) y) (basisVec i))
        (volume.restrict (truncatedWindow z m j)) := by
      refine ((hmemW.integrable one_le_two).bdd_mul
        (c := cutoffIbpConst d * (3 : ℝ) ^ (-j))
        (continuous_fderiv_campanatoCutoff_apply z j i).aestronglyMeasurable
        (Filter.Eventually.of_forall fun y => ?_)).congr ?_
      · rw [Real.norm_eq_abs]
        exact abs_fderiv_campanatoCutoff_apply_le z j y i
      · filter_upwards with y using mul_comm _ _
    exact hFint.abs
  have hstep4 : ∫ y in truncatedWindow z m j, |u.toFun y - affineEval c g y| ∂volume
      ≤ affineDistOn (truncatedWindow z m j) u.toFun c g
        * (volume (truncatedWindow z m j)).toReal := by
    have h1 := setIntegral_abs_le_sqrt_mul_sqrt hWfin hWpos hmemW
    rw [sqrt_setIntegral_sq_eq_normalizedL2On hWpos] at h1
    refine h1.trans (le_of_eq ?_)
    rw [affineDistOn, mul_assoc,
      Real.mul_self_sqrt (ENNReal.toReal_nonneg (a := volume (truncatedWindow z m j)))]
  have hfin := mul_le_mul_of_nonneg_left hstep4 hMnn
  linarith only [hstep1, hstep2, hstep3, hfin]

end

end Algsuperdiff.Section4.Provider.Schauder
