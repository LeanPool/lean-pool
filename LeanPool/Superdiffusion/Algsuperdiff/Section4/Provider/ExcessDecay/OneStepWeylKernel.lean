/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepSchauderWeyl
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution

/-!
# OneStepWeylKernel

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The coordinate-carrier radial mollifier (Weyl, part 3)

`OneStepSchauderWeyl` proves the *mollification* half of Weyl's lemma: every
convolution of a weakly harmonic `H¹` function with a smooth compactly supported
kernel has vanishing coordinate Laplacian on the region where the reflected
kernel support stays inside the domain.  `OneStepSchauderReproducing` proves the
*reproducing* identity, but on the Euclidean carrier
`EuclideanSpace ℝ (Fin d)` and for the Euclidean-radial kernel
`radialKernelScaled`.

This module bridges the two carriers.  It transports the native radial kernel
to the CoarseGraining coordinate carrier `Vec d`,

```text
  weylKernel d ε := (radialKernelScaled d ε) ∘ toEuc ,
```

records its support geometry there (the Euclidean ball of radius `ε` is
contained in the *sup*-metric ball of radius `ε`, so nothing is lost), and
proves the two facts the representative half of Weyl's lemma consumes:

* `convolution_weylKernel_eq_self` — a `C²` function with vanishing coordinate
  Laplacian on `Metric.ball x ε` reproduces itself against `weylKernel d ε` at
  `x`;
* `euclideanCoordLaplacian_mollify_eq_zero` / `contDiff_mollify` — the
  mollification of the zero-extended weakly harmonic function is `C^∞` and has
  vanishing coordinate Laplacian at every point whose closed `r`-ball lies in the
  domain, for **any** smooth compactly supported kernel supported in
  `closedBall 0 r`.

The second item is stated for a general kernel on purpose: the representative
half runs the reproducing identity (which needs radiality) against the
mollification by a mathlib `ContDiffBump` (which is *not* radial but is the only
kernel for which mathlib supplies almost-everywhere convergence).  Both kernels
must therefore be admissible for the harmonicity half.
-/

open scoped Convolution
open MeasureTheory Metric InnerProductSpace
open HCPolySupport (Vec H1Function euclideanCoordLaplacian)
open Algsuperdiff.Section4.Support (IsWeaklyHarmonicOn)

namespace Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

noncomputable section

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-! ## 1. The kernel on the coordinate carrier -/

/-- The native unit-mass radial mollifier, read on the CoarseGraining coordinate
carrier `Vec d` through the identification `toEuc`. -/
def weylKernel (d : ℕ) (eps : ℝ) : Vec d → ℝ := fun z => radialKernelScaled d eps (toEuc z)

theorem weylKernel_apply (eps : ℝ) (z : Vec d) :
    weylKernel d eps z = radialKernelScaled d eps (toEuc z) := rfl

theorem weylKernel_contDiff {eps : ℝ} {n : ℕ∞} : ContDiff ℝ n (weylKernel d eps) :=
  (radialKernelScaled_contDiff d).comp (toEuc : Vec d ≃L[ℝ] 𝔼).contDiff

theorem weylKernel_continuous {eps : ℝ} : Continuous (weylKernel d eps) :=
  (weylKernel_contDiff (d := d) (eps := eps) (n := 1)).continuous

/-- **Evenness.**  The kernel is a function of the Euclidean norm, hence even. -/
theorem weylKernel_neg (eps : ℝ) (z : Vec d) : weylKernel d eps (-z) = weylKernel d eps z := by
  refine radialKernelScaled_radial d ?_
  rw [show (toEuc (-z) : 𝔼) = -(toEuc z) from map_neg _ z, norm_neg]

/-- The kernel vanishes outside the **sup**-metric ball of radius `eps`: the sup norm is dominated
by the Euclidean norm, so the Euclidean support constraint is the stronger one. -/
theorem weylKernel_eq_zero_of_le_norm {eps : ℝ} (heps : 0 < eps) {z : Vec d} (hz : eps ≤ ‖z‖) :
    weylKernel d eps z = 0 :=
  radialKernelScaled_eq_zero_of_le_norm d heps (le_trans hz (norm_le_norm_toEuc z))

theorem support_weylKernel_subset {eps : ℝ} (heps : 0 < eps) :
    Function.support (weylKernel d eps) ⊆ closedBall (0 : Vec d) eps := by
  intro z hz
  rw [Function.mem_support] at hz
  rw [mem_closedBall, dist_zero_right]
  by_contra h
  exact hz (weylKernel_eq_zero_of_le_norm heps (le_of_lt (not_le.mp h)))

theorem tsupport_weylKernel_subset {eps : ℝ} (heps : 0 < eps) :
    tsupport (weylKernel d eps) ⊆ closedBall (0 : Vec d) eps :=
  closure_minimal (support_weylKernel_subset heps) isClosed_closedBall

theorem weylKernel_hasCompactSupport {eps : ℝ} (heps : 0 < eps) :
    HasCompactSupport (weylKernel d eps) :=
  (isCompact_closedBall (0 : Vec d) eps).of_isClosed_subset isClosed_closure
    (tsupport_weylKernel_subset heps)

/-! ## 2. The reproducing identity on the coordinate carrier -/

/-- **Reproducing identity, coordinate carrier.**  A `C²` function whose coordinate Laplacian
vanishes on the sup-metric ball `Metric.ball x eps` reproduces itself at `x` against the
`eps`-scaled radial kernel.

The proof transports the Euclidean statement `reproducing_of_radial` across the measure-preserving
identification `toEuc`; the classical harmonicity hypothesis it needs is exactly what
`harmonicOnNhd_ball_comp_toEuc_symm` manufactures from the vanishing coordinate Laplacian, at the
same radius. -/
theorem convolution_weylKernel_eq_self [NeZero d] {w : Vec d → ℝ} (hw : ContDiff ℝ 2 w)
    {x : Vec d} {eps : ℝ} (heps : 0 < eps)
    (hzero : ∀ y ∈ ball x eps, euclideanCoordLaplacian w y = 0) :
    (weylKernel d eps ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] w) x = w x := by
  have hW : ContDiff ℝ 2 (w ∘ (toEuc.symm : 𝔼 → Vec d)) :=
    hw.comp (toEuc.symm : 𝔼 ≃L[ℝ] Vec d).contDiff
  have hharm : HarmonicOnNhd (w ∘ (toEuc.symm : 𝔼 → Vec d)) (ball (toEuc x) eps) :=
    harmonicOnNhd_ball_comp_toEuc_symm hw heps hzero
  have hrep : ∫ y : 𝔼, radialKernelScaled d eps (y - toEuc x) * (w ∘ toEuc.symm) y
      = (w ∘ toEuc.symm) (toEuc x) :=
    reproducing_of_radial hW hharm (radialKernelScaled_continuous d)
      (radialKernelScaled_hasCompactSupport d heps) (fun h => radialKernelScaled_radial d h)
      (le_refl eps) (fun z hz => radialKernelScaled_eq_zero_of_le_norm d heps hz)
      (radialKernelScaled_integral_eq_one d heps)
  have htrans : ∫ t : Vec d, weylKernel d eps (t - x) * w t ∂volume
      = ∫ y : 𝔼, radialKernelScaled d eps (y - toEuc x) * (w ∘ toEuc.symm) y ∂volume := by
    rw [← (measurePreserving_toEuc d).integral_comp (measurableEmbedding_toEuc d)
      (fun y : 𝔼 => radialKernelScaled d eps (y - toEuc x) * (w ∘ toEuc.symm) y)]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards with t
    have hsub : (toEuc (t - x) : 𝔼) = toEuc t - toEuc x := map_sub _ t x
    simp only [Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply, weylKernel_apply,
      hsub]
  have hvec : ∫ t : Vec d, weylKernel d eps (t - x) * w t ∂volume = w x :=
    htrans.trans (hrep.trans (by simp))
  rw [convolution_lsmul_swap, ← hvec]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with t
  rw [smul_eq_mul, ← neg_sub t x, weylKernel_neg]

/-! ## 3. The mollification of a weakly harmonic function -/

/-- The reflected support of a kernel supported in `closedBall 0 r` sits in `closedBall A r`. -/
theorem tsupport_comp_const_sub_subset_closedBall {K : Vec d → ℝ} {r : ℝ}
    (hKsub : tsupport K ⊆ closedBall (0 : Vec d) r) (A : Vec d) :
    tsupport (fun y : Vec d => K (A - y)) ⊆ closedBall A r := by
  have hpre : tsupport (fun y : Vec d => K (A - y)) = (fun y : Vec d => A - y) ⁻¹' tsupport K := by
    simpa [Function.comp_def] using tsupport_comp_eq_preimage K (Homeomorph.subLeft A)
  intro y hy
  rw [hpre, Set.mem_preimage] at hy
  have h := hKsub hy
  rw [mem_closedBall, dist_zero_right] at h
  rw [mem_closedBall, dist_eq_norm, ← norm_neg]
  simpa using h

/-- The zero extension of an `H¹` function is globally square integrable. -/
theorem memLp_indicator_h1 {U : Set (Vec d)} (hUm : MeasurableSet U) (u : H1Function U) :
    MemLp (Set.indicator U u.toFun) 2 volume := by
  rw [MeasureTheory.memLp_indicator_iff_restrict hUm]
  exact u.memL2

/-- The zero extension of an `H¹` function is locally integrable. -/
theorem locallyIntegrable_indicator_h1 {U : Set (Vec d)} (hUm : MeasurableSet U)
    (u : H1Function U) : LocallyIntegrable (Set.indicator U u.toFun) volume :=
  (memLp_indicator_h1 hUm u).locallyIntegrable (by norm_num)

/-- The mollification of the zero extension of an `H¹` function is `C^∞`. -/
theorem contDiff_mollify {U : Set (Vec d)} (hUm : MeasurableSet U) (u : H1Function U)
    {K : Vec d → ℝ} (hK_supp : HasCompactSupport K) (hK : ContDiff ℝ (⊤ : ℕ∞) K) :
    ContDiff ℝ (⊤ : ℕ∞)
      (K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] Set.indicator U u.toFun) :=
  HasCompactSupport.contDiff_convolution_left (L := ContinuousLinearMap.lsmul ℝ ℝ)
    (μ := volume) hK_supp hK (locallyIntegrable_indicator_h1 hUm u)

/-- **Harmonicity of the mollification, in the coordinate Laplacian.**  For *any* smooth kernel
supported in `closedBall 0 r`, the mollification of the zero extension of a weakly harmonic
function has vanishing coordinate Laplacian at every point whose closed `r`-ball lies inside the
domain. -/
theorem euclideanCoordLaplacian_mollify_eq_zero {U : Set (Vec d)} (hUopen : IsOpen U)
    {u : H1Function U} (hu : IsWeaklyHarmonicOn U u) {K : Vec d → ℝ} {r : ℝ}
    (hK_supp : HasCompactSupport K) (hK : ContDiff ℝ (⊤ : ℕ∞) K)
    (hKsub : tsupport K ⊆ closedBall (0 : Vec d) r) {A : Vec d} (hA : closedBall A r ⊆ U) :
    euclideanCoordLaplacian
      (K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] Set.indicator U u.toFun) A = 0 :=
  euclideanCoordLaplacian_convolution_indicator_eq_zero hUopen hu hK_supp hK A
    ((tsupport_comp_const_sub_subset_closedBall hKsub A).trans hA)

end

end Algsuperdiff.Section4.Provider.ExcessDecay.Schauder
