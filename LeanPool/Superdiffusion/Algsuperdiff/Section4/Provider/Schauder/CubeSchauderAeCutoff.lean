/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Schauder.CubeSchauderPointwise
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.QuantitativeCutoff

/-!
# CubeSchauderAeCutoff

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Cube Schauder: the cutoff pairing of the a.e. identification

`CubeSchauderAssembly.exists_zeroDatumWitness_of_campanato` consumes the
almost-everywhere identification `Ψ = ∇w` of the Campanato slope field with the
`H¹` weak gradient.  The quantitative half of that identification is the
statement proved here: for the smooth cutoff `η` that is `1` on the Euclidean
ball of radius `3^j/8` around `z` and supported in the ball of radius `3^j/4`,

```text
  |∫_{□_m} (∂_i w − g_i) η|  =  |∫_{□_m} (w − ℓ) ∂_i η|
                             ≤  C(d)·3^{-j}·‖w − ℓ‖_{L²(W_j)}·|W_j| ,
```

where `ℓ = (c,g)` is *any* affine competitor and `W_j = (z+□_j) ∩ □_m`.  Fed
with the affine minimizer of the window and the Campanato datum
`E(w, W_j) ≤ K√(3^j)`, the right-hand side is `C(d)·K·√(3^j)·|W_j|`, which is
`o(|W_j|)` — the ingredient the Lebesgue-point argument needs.

The three components are:

* `setIntegral_abs_le_sqrt_mul_sqrt` — the `L¹ ≤ L²` comparison on a window of
  finite positive measure, proved from the elementary two-parameter bound
  `|f| ≤ (t f² + t⁻¹)/2` optimized at `t = √|W| / ‖f‖_{L²}`.  (The repository
  had no volume-average Cauchy–Schwarz; see `Support.NormalizedL2`'s note.)
* `campanatoCutoff` — CoarseGraining's quantitative ball cutoff at the radii
  `3^j/8` and `3^j/4`, together with the six facts the pairing needs.
* `integral_grad_sub_slope_mul_cutoff` — the integration-by-parts identity, the
  weak-gradient identity of `w` minus the same identity for the smooth affine
  competitor, and `abs_integral_grad_sub_slope_mul_cutoff_le` — its bound.

## References

* ABK26.
-/

namespace Algsuperdiff.Section4.Provider.Schauder

open MeasureTheory Filter Topology
open HCPolySupport
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

variable {d : ℕ}

/-! ## 1. The `L¹ ≤ L²` comparison on a window -/

private theorem sqrt_split_arith {I sA sV : ℝ} (hsA : 0 < sA) (hsV : 0 < sV)
    (h : I ≤ ((sV / sA) * (sA * sA) + (sV / sA)⁻¹ * (sV * sV)) / 2) :
    I ≤ sA * sV := by
  have hne : sA ≠ 0 := ne_of_gt hsA
  have hne' : sV ≠ 0 := ne_of_gt hsV
  have hid : ((sV / sA) * (sA * sA) + (sV / sA)⁻¹ * (sV * sV)) / 2 = sA * sV := by
    field_simp
    ring
  linarith only [h, hid]

/-- **`L¹ ≤ L²` on a window of finite positive measure.**

`∫_W |f| ≤ ‖f‖_{L²(W)}·|W|^{1/2}`.  Proved from the elementary pointwise bound
`|f| ≤ (t f² + t⁻¹)/2`, integrated and optimized at `t = |W|^{1/2}/‖f‖_{L²(W)}`;
the degenerate branch `‖f‖_{L²(W)} = 0` is handled separately. -/
theorem setIntegral_abs_le_sqrt_mul_sqrt {W : Set (Vec d)} (hWfin : volume W ≠ ⊤)
    (hWpos : 0 < (volume W).toReal) {f : Vec d → ℝ}
    (hf : MemLp f 2 (volume.restrict W)) :
    ∫ y in W, |f y| ∂volume
      ≤ Real.sqrt (∫ y in W, f y ^ 2 ∂volume) * Real.sqrt ((volume W).toReal) := by
  have : IsFiniteMeasure (volume.restrict W) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.2 hWfin
  have hint : Integrable f (volume.restrict W) := hf.integrable one_le_two
  have habs : Integrable (fun y => |f y|) (volume.restrict W) := hint.abs
  have hsq : Integrable (fun y => f y ^ 2) (volume.restrict W) :=
    (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).1 hf
  have hA0 : 0 ≤ ∫ y in W, f y ^ 2 ∂volume :=
    integral_nonneg fun y => sq_nonneg _
  rcases eq_or_lt_of_le hA0 with hAe | hApos
  · have hzero : (fun y => f y ^ 2) =ᵐ[volume.restrict W] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun y => sq_nonneg (f y)) hsq).1 hAe.symm
    have h1 : ∫ y in W, |f y| ∂volume = 0 := by
      refine integral_eq_zero_of_ae ?_
      filter_upwards [hzero] with y hy
      have hy2 : f y ^ 2 = 0 := hy
      have hy0 : f y = 0 := by
        have h := sq_eq_zero_iff.1 hy2
        exact h
      simp [hy0]
    rw [h1]
    exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  · obtain ⟨sA, hsA, hsAsq⟩ : ∃ s : ℝ, 0 < s ∧ s * s = ∫ y in W, f y ^ 2 ∂volume :=
      ⟨Real.sqrt _, Real.sqrt_pos.2 hApos, Real.mul_self_sqrt hA0⟩
    obtain ⟨sV, hsV, hsVsq⟩ : ∃ s : ℝ, 0 < s ∧ s * s = (volume W).toReal :=
      ⟨Real.sqrt _, Real.sqrt_pos.2 hWpos, Real.mul_self_sqrt hWpos.le⟩
    have hsAeq : Real.sqrt (∫ y in W, f y ^ 2 ∂volume) = sA := by
      rw [← hsAsq, Real.sqrt_mul_self hsA.le]
    have hsVeq : Real.sqrt ((volume W).toReal) = sV := by
      rw [← hsVsq, Real.sqrt_mul_self hsV.le]
    rw [hsAeq, hsVeq]
    have ht : 0 < sV / sA := div_pos hsV hsA
    have hne : (sV / sA) ≠ 0 := ne_of_gt ht
    have hptwise : ∀ y, |f y| ≤ ((sV / sA) * f y ^ 2 + (sV / sA)⁻¹) / 2 := by
      intro y
      have h0 : 0 ≤ (sV / sA) * (|f y| - (sV / sA)⁻¹) ^ 2 :=
        mul_nonneg ht.le (sq_nonneg _)
      have hid : (sV / sA) * (|f y| - (sV / sA)⁻¹) ^ 2
          = (sV / sA) * |f y| ^ 2 - 2 * |f y| + (sV / sA)⁻¹ := by
        field_simp
        ring
      rw [sq_abs] at hid
      linarith only [h0, hid]
    have hRHSint : Integrable (fun y => ((sV / sA) * f y ^ 2 + (sV / sA)⁻¹) / 2)
        (volume.restrict W) :=
      ((hsq.const_mul (sV / sA)).add (integrable_const _)).div_const 2
    have hmono : ∫ y in W, |f y| ∂volume
        ≤ ∫ y in W, ((sV / sA) * f y ^ 2 + (sV / sA)⁻¹) / 2 ∂volume :=
      integral_mono habs hRHSint hptwise
    have hcalc : ∫ y in W, ((sV / sA) * f y ^ 2 + (sV / sA)⁻¹) / 2 ∂volume
        = ((sV / sA) * (∫ y in W, f y ^ 2 ∂volume)
            + (sV / sA)⁻¹ * (volume W).toReal) / 2 := by
      rw [integral_div, integral_add (hsq.const_mul (sV / sA)) (integrable_const _),
        integral_const_mul, setIntegral_const, measureReal_def, smul_eq_mul]
      ring
    rw [hcalc, ← hsAsq, ← hsVsq] at hmono
    exact sqrt_split_arith hsA hsV hmono

/-- `√(∫_W f²) = ‖f‖_{L²(W)}·√|W|` on a window of finite positive measure. -/
theorem sqrt_setIntegral_sq_eq_normalizedL2On {W : Set (Vec d)}
    (hWpos : 0 < (volume W).toReal) (f : Vec d → ℝ) :
    Real.sqrt (∫ y in W, f y ^ 2 ∂volume)
      = normalizedL2On W f * Real.sqrt ((volume W).toReal) := by
  have hA0 : 0 ≤ ∫ y in W, f y ^ 2 ∂volume :=
    integral_nonneg fun y => sq_nonneg _
  have hne : (volume W).toReal ≠ 0 := ne_of_gt hWpos
  have hprod : (0 : ℝ) ≤ ((volume W).toReal)⁻¹ * (∫ y in W, f y ^ 2 ∂volume) :=
    mul_nonneg (by positivity) hA0
  rw [normalizedL2On, volumeAverage, ← Real.sqrt_mul hprod]
  congr 1
  field_simp

/-! ## 2. The Campanato cutoff -/

/-- **The Campanato cutoff at `z` and scale `j`**: CoarseGraining's quantitative
ball cutoff, equal to `1` on the Euclidean ball of radius `3^j/8` and supported
in the ball of radius `3^j/4`. -/
def campanatoCutoff (z : Vec d) (j : ℤ) : Vec d → ℝ :=
  QuantitativeBallCutoff.canonicalFun z ((3 : ℝ) ^ j / 8) ((3 : ℝ) ^ j / 4)

private theorem cutoff_radii (j : ℤ) :
    (0 : ℝ) < (3 : ℝ) ^ j / 8 ∧ (3 : ℝ) ^ j / 8 < (3 : ℝ) ^ j / 4
      ∧ (3 : ℝ) ^ j / 4 < (3 : ℝ) ^ j / 2 := by
  have h : (0 : ℝ) < (3 : ℝ) ^ j := zpow_pos (by norm_num) j
  refine ⟨by linarith only [h], by linarith only [h], by linarith only [h]⟩

theorem campanatoCutoff_smooth (z : Vec d) (j : ℤ) :
    ContDiff ℝ (⊤ : ℕ∞) (campanatoCutoff z j) :=
  QuantitativeBallCutoff.canonicalFun_smooth z (cutoff_radii j).1 (cutoff_radii j).2.1

theorem campanatoCutoff_hasCompactSupport (z : Vec d) (j : ℤ) :
    HasCompactSupport (campanatoCutoff z j) :=
  QuantitativeBallCutoff.canonicalFun_hasCompactSupport z (cutoff_radii j).1
    (cutoff_radii j).2.1

theorem campanatoCutoff_nonneg (z : Vec d) (j : ℤ) (y : Vec d) :
    0 ≤ campanatoCutoff z j y :=
  QuantitativeBallCutoff.canonicalFun_nonneg z _ _ y

theorem campanatoCutoff_le_one (z : Vec d) (j : ℤ) (y : Vec d) :
    campanatoCutoff z j y ≤ 1 :=
  QuantitativeBallCutoff.canonicalFun_le_one z _ _ y

theorem campanatoCutoff_eq_one {z : Vec d} {j : ℤ} {y : Vec d}
    (hy : y ∈ euclideanBall z ((3 : ℝ) ^ j / 8)) : campanatoCutoff z j y = 1 :=
  QuantitativeBallCutoff.canonicalFun_eq_one_on_inner (cutoff_radii j).1
    (cutoff_radii j).2.1 hy

theorem campanatoCutoff_tsupport_subset (z : Vec d) (j : ℤ) :
    tsupport (campanatoCutoff z j) ⊆ euclideanBall z ((3 : ℝ) ^ j / 2) :=
  QuantitativeBallCutoff.canonicalFun_tsupport_subset_euclideanBall z
    (cutoff_radii j).1 (cutoff_radii j).2.1 (cutoff_radii j).2.2

/-- The constant of the cutoff pairing: `16·d·θ'`, where `θ'` is the transition
profile's derivative bound. -/
def cutoffIbpConst (d : ℕ) : ℝ :=
  16 * (d : ℝ) * smoothTransitionProfile.derivBound

theorem cutoffIbpConst_nonneg (d : ℕ) : 0 ≤ cutoffIbpConst d :=
  mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg d))
    smoothTransitionProfile.derivBound_nonneg

theorem norm_fderiv_campanatoCutoff_le (z : Vec d) (j : ℤ) (y : Vec d) :
    ‖fderiv ℝ (campanatoCutoff z j) y‖ ≤ cutoffIbpConst d * (3 : ℝ) ^ (-j) := by
  have h := QuantitativeBallCutoff.canonicalFun_gradient_bound z (cutoff_radii j).1
    (cutoff_radii j).2.1 y
  refine h.trans (le_of_eq ?_)
  have hpos : (0 : ℝ) < (3 : ℝ) ^ j := zpow_pos (by norm_num) j
  have hne : ((3 : ℝ) ^ j) ≠ 0 := ne_of_gt hpos
  rw [cutoffIbpConst, zpow_neg]
  field_simp
  ring

private theorem norm_basisVec_le_one (i : Fin d) : ‖basisVec (d := d) i‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun k => ?_
  rw [basisVec_apply]
  by_cases hk : k = i <;> simp [hk]

theorem abs_fderiv_campanatoCutoff_apply_le (z : Vec d) (j : ℤ) (y : Vec d) (i : Fin d) :
    |(fderiv ℝ (campanatoCutoff z j) y) (basisVec i)|
      ≤ cutoffIbpConst d * (3 : ℝ) ^ (-j) := by
  have h1 : ‖(fderiv ℝ (campanatoCutoff z j) y) (basisVec i)‖
      ≤ ‖fderiv ℝ (campanatoCutoff z j) y‖ * ‖basisVec (d := d) i‖ :=
    ContinuousLinearMap.le_opNorm _ _
  have h2 : ‖fderiv ℝ (campanatoCutoff z j) y‖ * ‖basisVec (d := d) i‖
      ≤ ‖fderiv ℝ (campanatoCutoff z j) y‖ * 1 :=
    mul_le_mul_of_nonneg_left (norm_basisVec_le_one i) (norm_nonneg _)
  have h3 := norm_fderiv_campanatoCutoff_le z j y
  rw [Real.norm_eq_abs] at h1
  linarith only [h1, h2, h3]

/-- Off the Euclidean ball of radius `3^j/2` the cutoff's derivative vanishes. -/
theorem fderiv_campanatoCutoff_eq_zero {z : Vec d} {j : ℤ} {y : Vec d}
    (hy : y ∉ euclideanBall z ((3 : ℝ) ^ j / 2)) :
    fderiv ℝ (campanatoCutoff z j) y = 0 := by
  have hns : y ∉ tsupport (campanatoCutoff z j) := fun h =>
    hy (campanatoCutoff_tsupport_subset z j h)
  have hsub := support_fderiv_subset (𝕜 := ℝ) (f := campanatoCutoff z j)
  by_contra hne
  exact hns (hsub (by simpa [Function.mem_support] using hne))

/-- The Euclidean ball is contained in the sup-metric cube of the same radius,
hence in the translated triadic cube of scale `j`. -/
theorem euclideanBall_subset_image_add_openCubeSet (z : Vec d) (j : ℤ) :
    euclideanBall z ((3 : ℝ) ^ j / 2)
      ⊆ (fun y => z + y) '' openCubeSet (originCube d j) := by
  intro y hy
  refine ⟨y - z, ?_, by ring⟩
  have hR : (0 : ℝ) < (3 : ℝ) ^ j / 2 := by
    have h := zpow_pos (by norm_num : (0 : ℝ) < 3) j
    linarith only [h]
  have hsq : euclideanSqDist y z < ((3 : ℝ) ^ j / 2) ^ 2 := hy
  have hvn : vecNormSq (y - z) = euclideanSqDist y z := rfl
  have hnorm : ‖y - z‖ ≤ Real.sqrt (vecNormSq (y - z)) := norm_le_slopeMagnitude (y - z)
  have hlt : Real.sqrt (vecNormSq (y - z)) < (3 : ℝ) ^ j / 2 := by
    rw [hvn]
    exact (Real.sqrt_lt' hR).2 hsq
  have hylt : ‖y - z‖ < (3 : ℝ) ^ j / 2 := lt_of_le_of_lt hnorm hlt
  rw [mem_openCubeSet_originCube_iff]
  intro k
  have hcoord : |(y - z) k| ≤ ‖y - z‖ := by
    have h := norm_le_pi_norm (y - z) k
    rwa [Real.norm_eq_abs] at h
  have hb := abs_lt.1 (lt_of_le_of_lt hcoord hylt)
  exact ⟨by linarith only [hb.1], by linarith only [hb.2]⟩

end

end Algsuperdiff.Section4.Provider.Schauder
