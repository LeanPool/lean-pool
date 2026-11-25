/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-!
# Iterated derivatives of convolution in the smooth factor

This file upgrades the one-derivative theorem for convolution with a compactly
supported smooth right factor to an arbitrary-order pointwise jet formula.
The statement is evaluated on a tuple of directions, so it can be used directly
in uniform derivative estimates for approximate identities and in transpose
pairing calculations.
-/

@[expose] public section

noncomputable section

open Set Function MeasureTheory TopologicalSpace
open scoped Convolution ContDiff

namespace SGPT.Foundations.Analysis.Pending

universe u𝕜 uG uE uE' uF

variable {𝕜 : Type u𝕜} {G : Type uG} {E : Type uE}
  {E' : Type uE'} {F : Type uF}
  [RCLike 𝕜]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F]
  {μ : Measure G} [SFinite μ] [μ.IsAddLeftInvariant]

/-- Pointwise postcomposition of an `n`-linear map by the second argument of
a continuous bilinear map, bundled as a continuous bilinear map. -/
noncomputable def convolutionRightIteratedCLM
    (L : E →L[𝕜] E' →L[𝕜] F) (n : ℕ) :
    E →L[𝕜] (G [×n]→L[𝕜] E') →L[𝕜] (G [×n]→L[𝕜] F) :=
  (ContinuousLinearMap.compContinuousMultilinearMapL 𝕜
    (fun _ : Fin n ↦ G) E' F).comp L

omit [MeasurableSpace G] [BorelSpace G] [NormedSpace ℝ F] in
@[simp]
theorem convolutionRightIteratedCLM_apply
    (L : E →L[𝕜] E' →L[𝕜] F) (n : ℕ) (u : E)
    (A : G [×n]→L[𝕜] E') (m : Fin n → G) :
    convolutionRightIteratedCLM (G := G) L n u A m = L u (A m) :=
  rfl

omit [MeasurableSpace G] [BorelSpace G] in
/-- Evaluating an iterated derivative on fixed directions preserves compact
support. -/
theorem hasCompactSupport_iteratedFDeriv_apply
    {g : G → E'} (hcg : HasCompactSupport g) (n : ℕ)
    (m : Fin n → G) :
    HasCompactSupport (fun x ↦ iteratedFDeriv 𝕜 n g x m) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (hcg.iteratedFDeriv (𝕜 := 𝕜) n)
  intro x hx
  apply subset_tsupport
  intro hzero
  exact hx (by simp only [hzero, zero_apply])

/-- Every iterated derivative of a convolution can be moved to the compactly
supported smooth right factor. -/
theorem iteratedFDeriv_convolution_right_apply
    (L : E →L[𝕜] E' →L[𝕜] F) {f : G → E} {g : G → E'}
    (hf : LocallyIntegrable f μ) (hcg : HasCompactSupport g)
    (hg : ContDiff 𝕜 (⊤ : ℕ∞) g) (n : ℕ) (x : G)
    (m : Fin n → G) :
    iteratedFDeriv 𝕜 n (f ⋆[L, μ] g) x m =
      ∫ t, L (f t) (iteratedFDeriv 𝕜 n g (x - t) m) ∂μ := by
  induction n generalizing x with
  | zero =>
      simp only [iteratedFDeriv_zero_apply, convolution_def]
  | succ n ih =>
      let q : Fin n → G := Fin.tail m
      let h : G → E' := fun y ↦ iteratedFDeriv 𝕜 n g y q
      have hhcompact : HasCompactSupport h :=
        hasCompactSupport_iteratedFDeriv_apply (𝕜 := 𝕜) hcg n q
      have hhsmooth : ContDiff 𝕜 (⊤ : ℕ∞) h := by
        have hiter : ContDiff 𝕜 (⊤ : ℕ∞)
            (iteratedFDeriv 𝕜 n g) := hg.iteratedFDeriv_right
          (m := ((⊤ : ℕ∞) : ℕ∞ω)) (i := n) (by
            change (((⊤ : ℕ∞) + (n : ℕ∞) : ℕ∞) : ℕ∞ω) ≤
              ((⊤ : ℕ∞) : ℕ∞ω)
            exact WithTop.coe_le_coe.mpr le_top)
        let ev : (G [×n]→L[𝕜] E') →L[𝕜] E' :=
          ContinuousMultilinearMap.apply 𝕜 (fun _ : Fin n ↦ G) E' q
        exact ev.contDiff.comp hiter
      have hhsmooth1 : ContDiff 𝕜 1 h := hhsmooth.of_le (by norm_num)
      have hconvSmooth : ContDiff 𝕜 (⊤ : ℕ∞) (f ⋆[L, μ] g) :=
        hcg.contDiff_convolution_right L hf hg
      have hdiffIterated : DifferentiableAt 𝕜
          (iteratedFDeriv 𝕜 n (f ⋆[L, μ] g)) x :=
        (hconvSmooth.differentiable_iteratedFDeriv (by
          exact WithTop.coe_lt_coe.mpr
            (ENat.natCast_lt_top n))).differentiableAt
      rw [hdiffIterated.iteratedFDeriv_succ_apply_left']
      have heq :
          (fun y ↦ iteratedFDeriv 𝕜 n (f ⋆[L, μ] g) y q) =
            f ⋆[L, μ] h := by
        funext y
        rw [ih y q]
        rfl
      rw [heq]
      have hderiv := hhcompact.hasFDerivAt_convolution_right
        L hf hhsmooth1 x
      rw [hderiv.fderiv]
      rw [convolution_precompR_apply L hf (hhcompact.fderiv 𝕜)
        (hhsmooth1.continuous_fderiv one_ne_zero) x (m 0)]
      apply integral_congr_ae
      filter_upwards [] with t
      congr 1
      have hgdiff : DifferentiableAt 𝕜
          (iteratedFDeriv 𝕜 n g) (x - t) :=
        (hg.differentiable_iteratedFDeriv (by
          exact WithTop.coe_lt_coe.mpr
            (ENat.natCast_lt_top n))).differentiableAt
      exact (hgdiff.iteratedFDeriv_succ_apply_left' (m := m)).symm

/-- Map-valued form of `iteratedFDeriv_convolution_right_apply`: the full
iterated derivative is the Bochner convolution of the original left factor
with the map-valued iterated derivative of the right factor. -/
theorem iteratedFDeriv_convolution_right
    (L : E →L[𝕜] E' →L[𝕜] F) {f : G → E} {g : G → E'}
    (hf : LocallyIntegrable f μ) (hcg : HasCompactSupport g)
    (hg : ContDiff 𝕜 (⊤ : ℕ∞) g) (n : ℕ) (x : G) :
    iteratedFDeriv 𝕜 n (f ⋆[L, μ] g) x =
      (f ⋆[convolutionRightIteratedCLM (G := G) L n, μ]
        iteratedFDeriv 𝕜 n g) x := by
  have hgcont : Continuous (iteratedFDeriv 𝕜 n g) :=
    hg.continuous_iteratedFDeriv (by
      exact WithTop.coe_le_coe.mpr
        (le_top : (n : ℕ∞) ≤ (⊤ : ℕ∞)))
  have hint : Integrable (fun t ↦
      convolutionRightIteratedCLM (G := G) L n (f t)
        (iteratedFDeriv 𝕜 n g (x - t))) μ :=
    (hcg.iteratedFDeriv (𝕜 := 𝕜) n).convolutionExists_right
      (convolutionRightIteratedCLM (G := G) L n) hf hgcont x
  ext m
  rw [iteratedFDeriv_convolution_right_apply L hf hcg hg n x m,
    convolution_def, ContinuousMultilinearMap.integral_apply hint]
  rfl

end SGPT.Foundations.Analysis.Pending
