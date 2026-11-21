/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.EuclideanConvolutionDerivatives
public import LeanPool.CutoffRigidity.EuclideanL2MollificationGeneral

/-! # Actual mollified estimates for distributional Laplace equations

Only the compact smooth kernel is differentiated. Distributional equations
are genuine integral identities, and no second derivative of the input is
postulated. Compact Hessian energy and L²-contractive mollification give
uniform second-derivative estimates for the smooth approximants.
-/

public section

namespace CutoffRigidity

open MeasureTheory ProbabilityTheory Filter Topology ContinuousLinearMap
open scoped ENNReal Convolution

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Actual coordinate differentiation under reflection and translation. -/
theorem coordinateDerivative_reflect {k : E → ℝ} (hk : Differentiable ℝ k)
    (a : E) (i : Fin d) (y : E) :
    coordinateDerivative i (fun z => k (a - z)) y = -coordinateDerivative i k (a - y) := by
  have hmap : HasFDerivAt (fun z : E => a - z) (-ContinuousLinearMap.id ℝ E) y := by
    simpa using (hasFDerivAt_id y).const_sub a
  have hc := (hk (a - y)).hasFDerivAt.comp y hmap
  have hder : HasFDerivAt (fun z => k (a - z))
      ((fderiv ℝ k (a - y)).comp (-ContinuousLinearMap.id ℝ E)) y := by
    simpa only [Function.comp_def] using hc
  unfold coordinateDerivative
  rw [hder.fderiv]
  simp

/-- The genuine Laplacian is invariant under translation and reflection. -/
theorem euclideanLaplacian_reflect {k : E → ℝ} (hk : ContDiff ℝ 2 k) (a y : E) :
    euclideanLaplacian (fun z => k (a - z)) y = euclideanLaplacian k (a - y) := by
  have hk1 := hk.differentiable (by norm_num)
  have hd (i : Fin d) := c1_coordinateDerivative_of_c2 hk i
  have hp (i : Fin d) : coordinateDerivative i (coordinateDerivative i (fun z => k (a - z))) y =
      coordinateDerivative i (coordinateDerivative i k) (a - y) := by
    rw [funext (coordinateDerivative_reflect hk1 a i)]
    have hmap : Differentiable ℝ (fun z : E => a - z) := by fun_prop
    have hg : Differentiable ℝ (fun z => coordinateDerivative i k (a - z)) :=
      ((hd i).differentiable (by norm_num)).comp hmap
    have heq : (fun z => -coordinateDerivative i k (a - z)) =
        (fun z => (-1 : ℝ) * coordinateDerivative i k (a - z)) := by funext z; ring
    rw [heq, coordinateDerivative_smul_classical hg (-1)]
    dsimp only
    rw [coordinateDerivative_reflect ((hd i).differentiable (by norm_num)) a i]
    ring
  change (∑ i : Fin d, coordinateDerivative i (coordinateDerivative i (fun z => k (a - z))) y) = _
  simp_rw [hp]
  rfl

/-- A genuine distributional Laplace equation becomes an actual pointwise
equation after convolution by a compact smooth kernel. -/
theorem convolution_laplacian_eq_of_distributional_equation
    {w F k : E → ℝ} (hw : LocallyIntegrable w volume) (hk : ContDiff ℝ 3 k)
    (hkc : HasCompactSupport k)
    (heq : ∀ ψ : E → ℝ, ContDiff ℝ 3 ψ → HasCompactSupport ψ →
      (∫ y, w y * euclideanLaplacian ψ y) = ∫ y, F y * ψ y) (x : E) :
    euclideanLaplacian (k ⋆[lsmul ℝ ℝ, volume] w) x = (k ⋆[lsmul ℝ ℝ, volume] F) x := by
  rw [euclideanLaplacian_convolution_kernel (hk.of_le (by norm_num)) hkc hw,
    scalar_convolution_eq_shifted_kernel, scalar_convolution_eq_shifted_kernel]
  let ψ (y : E) := k (x - y)
  have hψ : ContDiff ℝ 3 ψ := hk.comp (contDiff_const.sub contDiff_id)
  have hψc : HasCompactSupport ψ := hkc.comp_homeomorph (Homeomorph.subLeft x)
  have hh := heq ψ hψ hψc
  have hlap (y : E) : euclideanLaplacian ψ y = euclideanLaplacian k (x - y) :=
    euclideanLaplacian_reflect (hk.of_le (by norm_num)) x y
  simp_rw [hlap] at hh
  simpa only [ψ, mul_comm] using hh

/-- The actual normalized-kernel Jensen bound, without subtracting the input. -/
theorem bumpMollification_sq_le_of_memLp (φ : ContDiffBump (0 : E)) {f : E → ℝ}
    (hf : MemLp f 2 volume) (x : E) :
    (bumpMollification φ f x) ^ 2 ≤ ∫ y, f (x - y) ^ 2 ∂bumpProbability φ := by
  have hm := bumpProbability_shift_memLp φ hf x
  have hj := variance_nonneg (fun y => f (x - y)) (bumpProbability φ)
  rw [variance_eq_sub hm, bumpProbability_integral_eq_convolution] at hj
  simp only [Pi.pow_apply] at hj
  linarith

/-- Actual normalized smooth convolution is contractive in Lebesgue L².
Both output membership and the squared integral estimate are derived. -/
theorem bumpMollification_L2_contraction (φ : ContDiffBump (0 : E)) {f : E → ℝ}
    (hfm : Measurable f) (hf : MemLp f 2 volume) :
    MemLp (bumpMollification φ f) 2 volume ∧
      (∫ x, (bumpMollification φ f x) ^ 2) ≤ ∫ x, f x ^ 2 := by
  let F (x y : E) := ENNReal.ofReal (f (x - y) ^ 2)
  have hFm : Measurable (Function.uncurry F) :=
    ((hfm.comp (measurable_fst.sub measurable_snd)).pow_const 2).ennreal_ofReal
  have hp (x : E) : ENNReal.ofReal ((bumpMollification φ f x) ^ 2) ≤
      ∫⁻ y, F x y ∂bumpProbability φ := by
    have hi := ENNReal.ofReal_le_ofReal (bumpMollification_sq_le_of_memLp φ hf x)
    rw [ofReal_integral_eq_lintegral_ofReal (bumpProbability_shift_memLp φ hf x).integrable_sq
      (Filter.Eventually.of_forall fun y => sq_nonneg _)] at hi
    exact hi
  have hi := lintegral_mono (μ := (volume : Measure E)) hp
  rw [lintegral_lintegral_swap hFm.aemeasurable] at hi
  have hHaar (y : E) : (∫⁻ x, F x y) = ∫⁻ x, ENNReal.ofReal (f x ^ 2) := by
    simpa only [F, sub_eq_add_neg] using
      lintegral_add_right_eq_self (fun x => ENNReal.ofReal (f x ^ 2)) (-y)
  simp_rw [hHaar] at hi
  simp only [lintegral_const, measure_univ, mul_one] at hi
  rw [← ofReal_integral_eq_lintegral_ofReal hf.integrable_sq
    (Filter.Eventually.of_forall fun x => sq_nonneg _)] at hi
  have hsm : AEStronglyMeasurable (bumpMollification φ f) volume :=
    (bumpMollification_contDiff φ (hf.locallyIntegrable (by norm_num))).continuous
      |>.aestronglyMeasurable
  have hint : Integrable (fun x => bumpMollification φ f x ^ 2) volume := by
    refine ⟨hsm.pow 2, ?_⟩
    apply (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x => sq_nonneg _)).2
    exact lt_of_le_of_lt hi ENNReal.ofReal_lt_top
  refine ⟨(memLp_two_iff_integrable_sq hsm).mpr hint, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun x => sq_nonneg _)] at hi
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun x => sq_nonneg _)).mp hi

/-- A genuine distributional Laplace equation with an L² right-hand side
has uniformly bounded actual Hessians of compact smooth mollifications.
This is the local weak H² estimate prior to constructing second weak derivatives. -/
theorem mollified_distributional_hessian_energy_le
    {w F : E → ℝ} (hw : LocallyIntegrable w volume) (hwc : HasCompactSupport w)
    (hFm : Measurable F) (hF : MemLp F 2 volume)
    (heq : ∀ ψ : E → ℝ, ContDiff ℝ 3 ψ → HasCompactSupport ψ →
      (∫ y, w y * euclideanLaplacian ψ y) = ∫ y, F y * ψ y)
    (φ : ContDiffBump (0 : E)) :
    (∫ x, ∑ i : Fin d, ∑ j : Fin d,
      (coordinateDerivative j (coordinateDerivative i (bumpMollification φ w)) x) ^ 2) ≤
      ∫ x, F x ^ 2 := by
  have hsm : ContDiff ℝ 3 (bumpMollification φ w) :=
    (bumpMollification_contDiff φ hw).of_le (by norm_num)
  have hsc := bumpMollification_hasCompactSupport φ hwc
  rw [compact_euclidean_hessian_energy_eq_laplacian hsm hsc]
  have hlap (x : E) : euclideanLaplacian (bumpMollification φ w) x = bumpMollification φ F x :=
    convolution_laplacian_eq_of_distributional_equation hw (φ.contDiff_normed (n := 3))
      φ.hasCompactSupport_normed heq x
  simp_rw [hlap]
  exact (bumpMollification_L2_contraction φ hFm hF).2

end CutoffRigidity
