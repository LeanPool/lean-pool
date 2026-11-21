/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.EuclideanWeakHessianEstimates
public import Mathlib.Analysis.Normed.Lp.SmoothApprox

/-!
# Strong L² convergence of actual normalized mollifications

Contraction and actual density of smooth compact tests extend quantitative
mollifier convergence to every genuine measurable Lebesgue L² input. No
translation modulus or derivative is assumed on that input.
-/

public section

namespace CutoffRigidity

open MeasureTheory Filter Topology ContinuousLinearMap
open scoped Convolution ContDiff

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The `L²` class of the convolution of `f` with the normalized bump `φ`. -/
@[expose] noncomputable def bumpMollificationLp (φ : ContDiffBump (0 : E))
    (f : E → ℝ) (hfm : Measurable f) (hf : MemLp f 2 volume) : E →₂[volume] ℝ :=
  (bumpMollification_L2_contraction φ hfm hf).1.toLp (bumpMollification φ f)

/-- The actual normalized convolution is linear in its L² input. -/
theorem bumpMollification_sub_L2 (φ : ContDiffBump (0 : E)) {f g : E → ℝ}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    bumpMollification φ (fun x => f x - g x) =
      fun x => bumpMollification φ f x - bumpMollification φ g x := by
  have hcf := ConvolutionExists.of_memLp_memLp (lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ)
    (bumpKernel_memLp φ) hf
  have hcg := ConvolutionExists.of_memLp_memLp (lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ)
    (bumpKernel_memLp φ) hg
  funext x
  change (∫ y, (lsmul ℝ ℝ) (φ.normed volume y) (f (x - y) - g (x - y))) = _
  simp_rw [map_sub]
  exact integral_sub (hcf x) (hcg x)

theorem norm_bumpMollificationLp_le (φ : ContDiffBump (0 : E))
    (f : E → ℝ) (hfm : Measurable f) (hf : MemLp f 2 volume) :
    ‖bumpMollificationLp φ f hfm hf‖ ≤ ‖hf.toLp f‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  change ‖(bumpMollification_L2_contraction φ hfm hf).1.toLp _‖ ^ 2 ≤ _
  rw [norm_toLp_sq, norm_toLp_sq]
  exact (bumpMollification_L2_contraction φ hfm hf).2

theorem bumpMollificationLp_sub (φ : ContDiffBump (0 : E))
    (f g : E → ℝ) (hfm : Measurable f) (hgm : Measurable g)
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    bumpMollificationLp φ (fun x => f x - g x) (hfm.sub hgm) (hf.sub hg) =
      bumpMollificationLp φ f hfm hf - bumpMollificationLp φ g hgm hg := by
  apply Lp.ext
  filter_upwards [(bumpMollification_L2_contraction φ (hfm.sub hgm) (hf.sub hg)).1.coeFn_toLp,
    Lp.coeFn_sub (bumpMollificationLp φ f hfm hf) (bumpMollificationLp φ g hgm hg),
    (bumpMollification_L2_contraction φ hfm hf).1.coeFn_toLp,
    (bumpMollification_L2_contraction φ hgm hg).1.coeFn_toLp] with x hsub hs hfx hgx
  change (bumpMollification_L2_contraction φ (hfm.sub hgm) (hf.sub hg)).1.toLp _ x = _
  rw [hsub, hs]
  change bumpMollification φ (fun x => f x - g x) x =
    (bumpMollification_L2_contraction φ hfm hf).1.toLp _ x -
    (bumpMollification_L2_contraction φ hgm hg).1.toLp _ x
  rw [hfx, hgx]
  exact congrFun (bumpMollification_sub_L2 φ hf hg) x

theorem norm_bumpMollificationLp_sub_le (φ : ContDiffBump (0 : E))
    (f g : E → ℝ) (hfm : Measurable f) (hgm : Measurable g)
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    ‖bumpMollificationLp φ f hfm hf - bumpMollificationLp φ g hgm hg‖ ≤
      ‖hf.toLp f - hg.toLp g‖ := by
  rw [← bumpMollificationLp_sub]
  have h := norm_bumpMollificationLp_le φ (fun x => f x - g x) (hfm.sub hgm) (hf.sub hg)
  have he := MemLp.toLp_sub hf hg
  change (hf.sub hg).toLp (fun x => f x - g x) = hf.toLp f - hg.toLp g at he
  rw [he] at h
  exact h

/-- Smooth compact inputs have the quantitative actual L² distance bound. -/
theorem norm_bumpMollificationLp_sub_compact_le (φ : ContDiffBump (0 : E))
    {g : E → ℝ} (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g)
    (hgLp : MemLp g 2 volume) :
    ‖bumpMollificationLp φ g hg.continuous.measurable hgLp - hgLp.toLp g‖ ≤
      φ.rOut * ‖(c1_compact_gradient_memLp hg hgc).toLp (gradient g)‖ := by
  have he : bumpMollificationLp φ g hg.continuous.measurable hgLp - hgLp.toLp g =
      (bumpMollification_error_memLp φ hg hgc).toLp (fun x => bumpMollification φ g x - g x) := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_sub (bumpMollificationLp φ g hg.continuous.measurable hgLp) (hgLp.toLp
      g),
      (bumpMollification_L2_contraction φ hg.continuous.measurable hgLp).1.coeFn_toLp,
      hgLp.coeFn_toLp, (bumpMollification_error_memLp φ hg hgc).coeFn_toLp] with x hs hsm hgg he
    rw [hs, he]
    change (bumpMollification_L2_contraction φ hg.continuous.measurable hgLp).1.toLp _ x -
      hgLp.toLp g x = _
    rw [hsm, hgg]
  rw [he]
  exact bumpMollification_error_L2_norm_le φ hg hgc

/-- Every actual measurable L² input is approximated strongly by normalized
smooth bumps whose support radius tends to zero. -/
theorem bumpMollificationLp_tendsto (φ : ℕ → ContDiffBump (0 : E))
    (hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0))
    (f : E → ℝ) (hfm : Measurable f) (hf : MemLp f 2 volume) :
    Tendsto (fun n => bumpMollificationLp (φ n) f hfm hf) atTop (𝓝 (hf.toLp f)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hd : Dense {u : E →₂[volume] ℝ | ∃ g : E → ℝ,
      u =ᵐ[volume] g ∧ HasCompactSupport g ∧ ContDiff ℝ ∞ g} :=
    Lp.dense_hasCompactSupport_contDiff (by norm_num : (2 : ENNReal) ≠ ⊤)
  obtain ⟨g₀, ⟨g, hg₀, hgc, hgs⟩, hclose⟩ := Metric.mem_closure_iff.mp (hd (hf.toLp f))
    (ε / 4) (by positivity)
  have hg : ContDiff ℝ 1 g := hgs.of_le (by norm_num)
  have hgLp : MemLp g 2 volume := hg.continuous.memLp_of_hasCompactSupport hgc
  have heq : g₀ = hgLp.toLp g := by
    apply Lp.ext
    exact hg₀.trans hgLp.coeFn_toLp.symm
  rw [heq] at hclose
  have hnear : ‖hf.toLp f - hgLp.toLp g‖ < ε / 4 := by
    simpa only [dist_eq_norm] using hclose
  let N := ‖(c1_compact_gradient_memLp hg hgc).toLp (gradient g)‖
  have hsmall : ∀ᶠ n in atTop, (φ n).rOut * N < ε / 2 := by
    have hlim : Tendsto (fun n => (φ n).rOut * N) atTop (𝓝 0)
      := by simpa only [zero_mul] using hφ.mul_const N
    exact hlim.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / 2))
  filter_upwards [hsmall] with n hn
  rw [dist_eq_norm]
  have htriangle : ‖bumpMollificationLp (φ n) f hfm hf - hf.toLp f‖ ≤
      ‖bumpMollificationLp (φ n) f hfm hf - bumpMollificationLp (φ n) g hg.continuous.measurable
        hgLp‖ +
      ‖bumpMollificationLp (φ n) g hg.continuous.measurable hgLp - hgLp.toLp g‖ +
      ‖hgLp.toLp g - hf.toLp f‖  := by
    have h1 := dist_triangle (bumpMollificationLp (φ n) f hfm hf)
      (bumpMollificationLp (φ n) g hg.continuous.measurable hgLp) (hf.toLp f)
    have h2 := dist_triangle (bumpMollificationLp (φ n) g hg.continuous.measurable hgLp)
      (hgLp.toLp g) (hf.toLp f)
    simp only [dist_eq_norm] at h1 h2
    linarith
  have hc := norm_bumpMollificationLp_sub_le (φ n) f g hfm hg.continuous.measurable hf hgLp
  have hq := norm_bumpMollificationLp_sub_compact_le (φ n) hg hgc hgLp
  have hr : ‖hgLp.toLp g - hf.toLp f‖ < ε / 4 := by rw [norm_sub_rev]; exact hnear
  change (φ n).rOut * ‖(c1_compact_gradient_memLp hg hgc).toLp (gradient g)‖ < ε / 2 at hn
  linarith

end CutoffRigidity
