/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.EuclideanBochner
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Compact cutoff energy estimates for actual pointwise eigenfunctions

The integration by parts is applied to the genuine compact test `χ²f`.
Its integration hypotheses are proved from compact support and continuity,
rather than assumed globally for the eigenfunction.
-/

public section

namespace CutoffRigidity

open MeasureTheory Filter Topology
open scoped ENNReal

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The actual Gibbs energy identity for a compactly supported C¹ test and a
C² function, with every product-integrability condition discharged. -/
theorem compact_test_gibbs_energy {V g f : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hg : ContDiff ℝ 1 g) (hf : ContDiff ℝ 2 f)
    (hgc : HasCompactSupport g) :
    (∫ x, g x * langevinDifferentialOperator V f x ∂gibbsMeasure volume V) =
      -(∫ x, inner ℝ (gradient g x) (gradient f x) ∂gibbsMeasure volume V) := by
  have hg1 (i : Fin d) : Continuous (coordinateDerivative i g) := by
    have h : ContDiff ℝ 0 (coordinateDerivative i g) := by
      apply contDiff_coordinateDerivative
      convert hg using 1
      norm_num
    exact h.continuous
  have hf1 (i : Fin d) : ContDiff ℝ 1 (coordinateDerivative i f) := by
    apply contDiff_coordinateDerivative
    convert hf using 1
    norm_num
  have hf2 (i : Fin d) : Continuous (coordinateDerivative i (coordinateDerivative i f)) := by
    have h : ContDiff ℝ 0 (coordinateDerivative i (coordinateDerivative i f)) := by
      apply contDiff_coordinateDerivative
      convert hf1 i using 1
      norm_num
    exact h.continuous
  have hV1 (i : Fin d) : Continuous (coordinateDerivative i V) := by
    have h : ContDiff ℝ 1 (coordinateDerivative i V) := by
      apply contDiff_coordinateDerivative
      convert hV using 1
      norm_num
    exact h.continuous
  have hfc (i : Fin d) := (hf1 i).continuous
  have hgc1 (i : Fin d) : HasCompactSupport (coordinateDerivative i g) :=
    hgc.fderiv_apply ℝ (EuclideanSpace.single i 1)
  apply integral_mul_langevin_eq_neg_gradient_inner (hV.differentiable (by norm_num))
    (hg.differentiable (by norm_num)) hf
  · intro i
    change Integrable (fun x => g x * coordinateDerivative i f x) _
    apply integrable_gibbs_of_continuous_hasCompactSupport hV.continuous (by fun_prop)
    simpa only [Pi.mul_def] using hgc.mul_right (f' := coordinateDerivative i f)
  · intro i
    change Integrable (fun x => g x * coordinateDerivative i (coordinateDerivative i f) x) _
    apply integrable_gibbs_of_continuous_hasCompactSupport hV.continuous (by fun_prop)
    simpa only [Pi.mul_def] using hgc.mul_right (f' := coordinateDerivative i (coordinateDerivative
      i f))
  · intro i
    change Integrable (fun x => coordinateDerivative i g x * coordinateDerivative i f x) _
    apply integrable_gibbs_of_continuous_hasCompactSupport hV.continuous (by fun_prop)
    simpa only [Pi.mul_def] using (hgc1 i).mul_right (f' := coordinateDerivative i f)
  · intro i
    change Integrable (fun x => g x * coordinateDerivative i V x * coordinateDerivative i f x) _
    apply integrable_gibbs_of_continuous_hasCompactSupport hV.continuous (by fun_prop)
    simpa only [Pi.mul_def] using (hgc.mul_right (f' := coordinateDerivative i V)).mul_right
      (f' := coordinateDerivative i f)

/-- Actual gradient of the cutoff multiplier `χ²f`. -/
theorem gradient_cutoff_square_mul {χ f : E → ℝ}
    (hχ : Differentiable ℝ χ) (hf : Differentiable ℝ f) (x : E) :
    gradient (fun y => χ y ^ 2 * f y) x =
      χ x ^ 2 • gradient f x + (2 * χ x * f x) • gradient χ x := by
  apply ext_inner_right ℝ
  intro y
  have hc : DifferentiableAt ℝ (fun y => χ y ^ 2) x := by fun_prop
  rw [inner_gradient_left, fderiv_fun_mul hc (hf x),
    fderiv_fun_pow 2 (hχ x)]
  simp only [add_apply, smul_apply, smul_eq_mul, inner_add_left, inner_smul_left,
    inner_gradient_left, Nat.reduceSub, pow_one, nsmul_eq_mul]
  simp only [map_mul, map_pow, RCLike.conj_to_real, Nat.cast_ofNat]
  ring

/-- A compact scalar cutoff makes every continuous product Gibbs integrable. -/
theorem integrable_cutoff_mul_continuous {V χ g : E → ℝ}
    (hV : Continuous V) (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hg : Continuous g) :
    Integrable (fun x => χ x * g x) (gibbsMeasure volume V) := by
  apply integrable_gibbs_of_continuous_hasCompactSupport hV (hχ.mul hg)
  simpa only [Pi.mul_def] using hχc.mul_right (f' := g)

/-- The squared-cutoff version used in the local energy identity. -/
theorem integrable_cutoff_square_mul_continuous {V χ g : E → ℝ}
    (hV : Continuous V) (hχ : Continuous χ) (hχc : HasCompactSupport χ) (hg : Continuous g) :
    Integrable (fun x => χ x ^ 2 * g x) (gibbsMeasure volume V) := by
  have hcs : HasCompactSupport (fun x => χ x ^ 2) := by
    simpa only [Function.comp_def] using hχc.comp_left (g := fun y : ℝ => y ^ 2) (by norm_num)
  exact integrable_cutoff_mul_continuous hV (hχ.pow 2) hcs hg

/-- The exact local energy identity for an arbitrary C² function, with the
actual compact test `χ²f`; no eigenfunction or global-domain premise. -/
theorem cutoff_gibbs_energy_identity {V f χ : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f) (hχ : ContDiff ℝ 2 χ)
    (hχc : HasCompactSupport χ) :
    (∫ x, χ x ^ 2 * f x * langevinDifferentialOperator V f x ∂gibbsMeasure volume V) +
      (∫ x, χ x ^ 2 * ‖gradient f x‖ ^ 2 ∂gibbsMeasure volume V) +
        2 * (∫ x, χ x * f x * inner ℝ (gradient χ x) (gradient f x) ∂gibbsMeasure volume V) = 0
          := by
  have htest : ContDiff ℝ 1 (fun x => χ x ^ 2 * f x) :=
    ((hχ.pow 2).mul hf).of_le (by norm_num)
  have htestc : HasCompactSupport (fun x => χ x ^ 2 * f x) := by
    have hcs : HasCompactSupport (fun x => χ x ^ 2) := by
      simpa only [Function.comp_def] using hχc.comp_left (g := fun y : ℝ => y ^ 2) (by norm_num)
    simpa only [Pi.mul_def] using hcs.mul_right (f' := f)
  have hGf : Continuous (gradient f) := (differentiable_gradient_of_contDiff_two hf).continuous
  have hGχ : Continuous (gradient χ) := (differentiable_gradient_of_contDiff_two hχ).continuous
  have hA : Integrable (fun x => χ x ^ 2 * ‖gradient f x‖ ^ 2) (gibbsMeasure volume V) :=
    integrable_cutoff_square_mul_continuous hV.continuous hχ.continuous hχc (by fun_prop)
  have hC : Integrable (fun x => χ x * f x * inner ℝ (gradient χ x) (gradient f x))
      (gibbsMeasure volume V) := by
    have h := integrable_cutoff_mul_continuous hV.continuous hχ.continuous hχc
      (hf.continuous.mul (hGχ.inner hGf))
    simpa only [mul_assoc, Pi.mul_apply] using h
  have h := compact_test_gibbs_energy hV htest hf htestc
  have hright (x : E) : inner ℝ (gradient (fun y => χ y ^ 2 * f y) x) (gradient f x) =
      χ x ^ 2 * ‖gradient f x‖ ^ 2 +
        2 * (χ x * f x * inner ℝ (gradient χ x) (gradient f x)) := by
    rw [gradient_cutoff_square_mul (hχ.differentiable (by norm_num)) (hf.differentiable
      (by norm_num)),
      inner_add_left, real_inner_smul_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    ring
  simp_rw [hright] at h
  rw [integral_add hA (hC.const_mul 2), integral_const_mul] at h
  linarith

/-- The exact compact-cutoff eigenfunction energy identity. No global
integrability assumption on derivatives of f is used. -/
theorem eigenfunction_cutoff_energy_identity {V f χ : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f) (hχ : ContDiff ℝ 2 χ)
    (hχc : HasCompactSupport χ) (rate : ℝ)
    (heigen : ∀ x, langevinDifferentialOperator V f x = -rate * f x) :
    (∫ x, χ x ^ 2 * ‖gradient f x‖ ^ 2 ∂gibbsMeasure volume V) +
      2 * (∫ x, χ x * f x * inner ℝ (gradient χ x) (gradient f x) ∂gibbsMeasure volume V) =
      rate * (∫ x, χ x ^ 2 * f x ^ 2 ∂gibbsMeasure volume V) := by
  have h := cutoff_gibbs_energy_identity hV hf hχ hχc
  have hpoint (x : E) : χ x ^ 2 * f x * langevinDifferentialOperator V f x =
      -rate * (χ x ^ 2 * f x ^ 2) := by
    rw [heigen]
    ring
  simp_rw [hpoint] at h
  rw [integral_const_mul] at h
  linarith

/-- Caccioppoli's compact cutoff estimate, with all global derivative
integrability replaced by compactly supported test calculations. -/
theorem eigenfunction_caccioppoli {V f χ : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f) (hχ : ContDiff ℝ 2 χ)
    (hχc : HasCompactSupport χ) (rate : ℝ)
    (heigen : ∀ x, langevinDifferentialOperator V f x = -rate * f x) :
    (∫ x, χ x ^ 2 * ‖gradient f x‖ ^ 2 ∂gibbsMeasure volume V) ≤
      2 * rate * (∫ x, χ x ^ 2 * f x ^ 2 ∂gibbsMeasure volume V) +
        4 * (∫ x, f x ^ 2 * ‖gradient χ x‖ ^ 2 ∂gibbsMeasure volume V) := by
  have hχsqc : HasCompactSupport (fun x => χ x ^ 2) := by
    simpa only [Function.comp_def] using hχc.comp_left (g := fun y : ℝ => y ^ 2) (by norm_num)
  have hGf : Continuous (gradient f) := (differentiable_gradient_of_contDiff_two hf).continuous
  have hGχ : Continuous (gradient χ) := (differentiable_gradient_of_contDiff_two hχ).continuous
  have hGχc : HasCompactSupport (fun x => ‖gradient χ x‖ ^ 2) := by
    have h := (hχc.fderiv ℝ).comp_left
      (g := fun L : E →L[ℝ] ℝ => ‖(InnerProductSpace.toDual ℝ E).symm L‖ ^ 2) (by simp)
    exact h
  have hA : Integrable (fun x => χ x ^ 2 * ‖gradient f x‖ ^ 2) (gibbsMeasure volume V) := by
    apply integrable_gibbs_of_continuous_hasCompactSupport hV.continuous (by fun_prop)
    simpa only [Pi.mul_def] using hχsqc.mul_right (f' := fun x => ‖gradient f x‖ ^ 2)
  have hB : Integrable (fun x => f x ^ 2 * ‖gradient χ x‖ ^ 2) (gibbsMeasure volume V) := by
    apply integrable_gibbs_of_continuous_hasCompactSupport hV.continuous (by fun_prop)
    simpa only [Pi.mul_def] using hGχc.mul_left (f := fun x => f x ^ 2)
  have hC : Integrable (fun x => χ x * f x * inner ℝ (gradient χ x) (gradient f x))
      (gibbsMeasure volume V) := by
    apply integrable_gibbs_of_continuous_hasCompactSupport hV.continuous (by fun_prop)
    simpa only [Pi.mul_def] using (hχc.mul_right (f' := f)).mul_right
      (f' := fun x => inner ℝ (gradient χ x) (gradient f x))
  have hpoint (x : E) : 0 ≤ χ x ^ 2 * ‖gradient f x‖ ^ 2 +
      4 * (χ x * f x * inner ℝ (gradient χ x) (gradient f x)) +
        4 * (f x ^ 2 * ‖gradient χ x‖ ^ 2) := by
    have h := sq_nonneg ‖χ x • gradient f x + (2 * f x) • gradient χ x‖
    rw [norm_add_sq_real] at h
    simp only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
      real_inner_smul_left, real_inner_smul_right] at h
    rw [← real_inner_comm (gradient f x) (gradient χ x)] at h
    nlinarith
  have hbound : 0 ≤ ∫ x, χ x ^ 2 * ‖gradient f x‖ ^ 2 +
      4 * (χ x * f x * inner ℝ (gradient χ x) (gradient f x)) +
        4 * (f x ^ 2 * ‖gradient χ x‖ ^ 2) ∂gibbsMeasure volume V :=
    integral_nonneg (fun x => hpoint x)
  have hadd := integral_add (hA.add (hC.const_mul 4)) (hB.const_mul 4)
  simp only [Pi.add_apply] at hadd
  rw [hadd, integral_add hA (hC.const_mul 4), integral_const_mul, integral_const_mul] at hbound
  have he := eigenfunction_cutoff_energy_identity hV hf hχ hχc rate heigen
  linarith

/-- Scalar spatial rescaling of the actual gradient. -/
theorem gradient_comp_scalar {φ : E → ℝ} (hφ : Differentiable ℝ φ) (s : ℝ) (x : E) :
    gradient (fun y => φ (s • y)) x = s • gradient φ (s • x) := by
  let A : E →L[ℝ] E := s • ContinuousLinearMap.id ℝ E
  have heq : (fun y => φ (s • y)) = fun y => φ (A y + 0) := by
    funext y
    simp [A]
  apply ext_inner_right ℝ
  intro y
  rw [inner_gradient_left, heq, fderiv_comp_affine_apply A 0 (hφ _)]
  simp [A, inner_smul_left, inner_gradient_left]

/-- A continuous compactly supported vector field has a uniform norm bound. -/
theorem exists_nonneg_bound_of_continuous_compactSupport {G : E → E}
    (hG : Continuous G) (hGc : HasCompactSupport G) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖G x‖ ≤ C := by
  obtain ⟨C, hC⟩ := hGc.exists_bound_of_continuousOn hG.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro x
  by_cases hx : x ∈ tsupport G
  · exact (hC x hx).trans (le_max_left _ _)
  · have hzero : G x = 0 := Function.notMem_support.mp (fun hs => hx (subset_tsupport G hs))
    simpa only [hzero, norm_zero] using le_max_right C 0

/-- Actual smooth compact exhaustion at the C³ test regularity needed for weak Bochner. -/
theorem exists_smooth_C3_cutoff_exhaustion :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ χ : ℕ → E → ℝ,
      (∀ n, ContDiff ℝ 3 (χ n)) ∧ (∀ n, HasCompactSupport (χ n)) ∧
      (∀ n x, 0 ≤ χ n x ∧ χ n x ≤ 1) ∧
      (∀ x, ∀ᶠ n : ℕ in Filter.atTop, χ n x = 1) ∧
      (∀ n x, ‖gradient (χ n) x‖ ≤ C / ((n : ℝ) + 1)) := by
  let φ : ContDiffBump (0 : E) := ⟨1, 2, by norm_num, by norm_num⟩
  have hφ : ContDiff ℝ 2 (φ : E → ℝ) := φ.contDiff
  have hGφ : Continuous (gradient (φ : E → ℝ)) :=
    (differentiable_gradient_of_contDiff_two hφ).continuous
  have hGφc : HasCompactSupport (gradient (φ : E → ℝ)) := by
    exact (φ.hasCompactSupport.fderiv ℝ).comp_left
      (g := (InnerProductSpace.toDual ℝ E).symm) (by simp)
  obtain ⟨C, hC0, hC⟩ := exists_nonneg_bound_of_continuous_compactSupport hGφ hGφc
  let ψ (n : ℕ) : ContDiffBump (0 : E) :=
    ⟨(n : ℝ) + 1, 2 * ((n : ℝ) + 1), by positivity, by nlinarith [Nat.cast_nonneg (α := ℝ) n]⟩
  let χ : ℕ → E → ℝ := fun n x => ψ n x
  have hscale (n : ℕ) : χ n = fun x => φ ((((n : ℝ) + 1)⁻¹) • x) := by
    funext x
    dsimp only [χ]
    rw [(ψ n).apply, φ.apply]
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    simp [ψ, φ, hn]
  refine ⟨C, hC0, χ, (fun n => (ψ n).contDiff), (fun n => (ψ n).hasCompactSupport),
    (fun n x => ⟨(ψ n).nonneg, (ψ n).le_one⟩), ?_, ?_⟩
  · intro x
    have hevent : ∀ᶠ n : ℕ in Filter.atTop, ‖x‖ ≤ (n : ℝ) + 1 :=
      (tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop ‖x‖)).mono
        (fun n hn => by linarith)
    filter_upwards [hevent] with n hn
    apply (ψ n).one_of_mem_closedBall
    simpa [ψ, Metric.mem_closedBall, dist_zero_right] using hn
  · intro n x
    rw [hscale n, gradient_comp_scalar (hφ.differentiable (by norm_num))]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (by positivity : (0 : ℝ) < n + 1)]
    calc
      _ ≤ ((n : ℝ) + 1)⁻¹ * C := mul_le_mul_of_nonneg_left (hC _) (by positivity)
      _ = _ := by ring

/-- Actual smooth compact cutoffs tending pointwise eventually to one,
whose gradients have the required inverse-radius bound. -/
theorem exists_smooth_cutoff_exhaustion :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ χ : ℕ → E → ℝ,
      (∀ n, ContDiff ℝ 2 (χ n)) ∧ (∀ n, HasCompactSupport (χ n)) ∧
      (∀ n x, 0 ≤ χ n x ∧ χ n x ≤ 1) ∧
      (∀ x, ∀ᶠ n : ℕ in Filter.atTop, χ n x = 1) ∧
      (∀ n x, ‖gradient (χ n) x‖ ≤ C / ((n : ℝ) + 1)) := by
  obtain ⟨C, hC, χ, hχ, hχc, hbounds, hone, hgrad⟩ :=
    exists_smooth_C3_cutoff_exhaustion (d := d)
  exact ⟨C, hC, χ, fun n => (hχ n).of_le (by norm_num), hχc, hbounds, hone, hgrad⟩

/-- Genuine exhaustion of compact cutoffs proves square integrability of
the actual gradient of an L² pointwise eigenfunction. No global derivative
integration-domain assumption is used. -/
theorem eigenfunction_gradient_memLp_two {V f : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f)
    (hfLp : MemLp f 2 (gibbsMeasure volume V))
    (rate : ℝ) (hrate : 0 ≤ rate)
    (heigen : ∀ x, langevinDifferentialOperator V f x = -rate * f x) :
    MemLp (gradient f) 2 (gibbsMeasure volume V) := by
  obtain ⟨C, hC0, χ, hχ, hχc, hχbounds, hχone, hχgrad⟩ := exists_smooth_cutoff_exhaustion (d := d)
  have hGf : Continuous (gradient f) := (differentiable_gradient_of_contDiff_two hf).continuous
  have hfM : Measurable f := hf.continuous.measurable
  have hf2 : Integrable (fun x => f x ^ 2) (gibbsMeasure volume V) := hfLp.integrable_sq
  have hχsq (n : ℕ) (x : E) : 0 ≤ χ n x ^ 2 ∧ χ n x ^ 2 ≤ 1 := by
    have h := hχbounds n x
    constructor
    · positivity
    · nlinarith
  have hχG (n : ℕ) (x : E) : ‖gradient (χ n) x‖ ≤ C := by
    calc
      _ ≤ C / ((n : ℝ) + 1) := hχgrad n x
      _ ≤ C := by
        apply (div_le_iff₀ (by positivity : (0 : ℝ) < n + 1)).2
        nlinarith [mul_nonneg hC0 (Nat.cast_nonneg (α := ℝ) n)]
  have hFn (n : ℕ) : Integrable (fun x => χ n x ^ 2 * f x ^ 2) (gibbsMeasure volume V) := by
    have hχM : Measurable (χ n) := (hχ n).continuous.measurable
    apply hf2.mono' (by fun_prop)
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith [(hχsq n x).2, sq_nonneg (f x)]
  have hBn (n : ℕ) : Integrable (fun x => f x ^ 2 * ‖gradient (χ n) x‖ ^ 2)
      (gibbsMeasure volume V) := by
    have hc : Continuous (gradient (χ n)) :=
      (differentiable_gradient_of_contDiff_two (hχ n)).continuous
    apply (hf2.const_mul (C ^ 2)).mono' (by fun_prop)
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hsq : ‖gradient (χ n) x‖ ^ 2 ≤ C ^ 2 := by
      nlinarith [hχG n x, norm_nonneg (gradient (χ n) x)]
    nlinarith [mul_le_mul_of_nonneg_left hsq (sq_nonneg (f x))]
  have hAn (n : ℕ) : Integrable (fun x => χ n x ^ 2 * ‖gradient f x‖ ^ 2)
      (gibbsMeasure volume V) := by
    have hχcont : Continuous (χ n) := (hχ n).continuous
    apply integrable_gibbs_of_continuous_hasCompactSupport hV.continuous (by fun_prop)
    have hcs : HasCompactSupport (fun x => χ n x ^ 2) := by
      simpa only [Function.comp_def] using (hχc n).comp_left (g := fun y : ℝ => y ^ 2) (by norm_num)
    simpa only [Pi.mul_def] using hcs.mul_right (f' := fun x => ‖gradient f x‖ ^ 2)
  have hFbound (n : ℕ) :
      (∫ x, χ n x ^ 2 * f x ^ 2 ∂gibbsMeasure volume V) ≤
        ∫ x, f x ^ 2 ∂gibbsMeasure volume V := by
    apply integral_mono (hFn n) hf2
    intro x
    nlinarith [(hχsq n x).2, sq_nonneg (f x)]
  have hBbound (n : ℕ) :
      (∫ x, f x ^ 2 * ‖gradient (χ n) x‖ ^ 2 ∂gibbsMeasure volume V) ≤
        C ^ 2 * (∫ x, f x ^ 2 ∂gibbsMeasure volume V) := by
    rw [← integral_const_mul]
    apply integral_mono (hBn n) (hf2.const_mul (C ^ 2))
    intro x
    have hsq : ‖gradient (χ n) x‖ ^ 2 ≤ C ^ 2 := by
      nlinarith [hχG n x, norm_nonneg (gradient (χ n) x)]
    nlinarith [mul_le_mul_of_nonneg_left hsq (sq_nonneg (f x))]
  let M : ℝ := (2 * rate + 4 * C ^ 2) * (∫ x, f x ^ 2 ∂gibbsMeasure volume V)
  have hAbound (n : ℕ) :
      (∫ x, χ n x ^ 2 * ‖gradient f x‖ ^ 2 ∂gibbsMeasure volume V) ≤ M := by
    have h := eigenfunction_caccioppoli hV hf (hχ n) (hχc n) rate heigen
    have hF := mul_le_mul_of_nonneg_left (hFbound n) (show 0 ≤ 2 * rate by positivity)
    have hB := hBbound n
    dsimp [M]
    nlinarith
  let F (n : ℕ) (x : E) : ℝ≥0∞ := ENNReal.ofReal (χ n x ^ 2 * ‖gradient f x‖ ^ 2)
  have hFmeas (n : ℕ) : Measurable (F n) := by
    have hχM : Measurable (χ n) := (hχ n).continuous.measurable
    dsimp [F]
    fun_prop
  have hFlim (x : E) : Tendsto (fun n => F n x) atTop
      (𝓝 (ENNReal.ofReal (‖gradient f x‖ ^ 2))) := by
    have heq : (fun _ : ℕ => ENNReal.ofReal (‖gradient f x‖ ^ 2)) =ᶠ[atTop] fun n => F n x := by
      filter_upwards [hχone x] with n hn
      simp [F, hn]
    exact tendsto_const_nhds.congr' heq
  have hFatou := lintegral_liminf_le (μ := gibbsMeasure volume V) (f := F) (u := atTop) hFmeas
  simp_rw [(hFlim _).liminf_eq] at hFatou
  have hIntBound (n : ℕ) : (∫⁻ x, F n x ∂gibbsMeasure volume V) ≤ ENNReal.ofReal M := by
    have h := ofReal_integral_eq_lintegral_ofReal (hAn n)
      (Filter.Eventually.of_forall fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _))
    change ENNReal.ofReal (∫ x, χ n x ^ 2 * ‖gradient f x‖ ^ 2 ∂gibbsMeasure volume V) =
      ∫⁻ x, F n x ∂gibbsMeasure volume V at h
    rw [← h]
    exact ENNReal.ofReal_le_ofReal (hAbound n)
  have hlimBound : liminf (fun n => ∫⁻ x, F n x ∂gibbsMeasure volume V) atTop ≤ ENNReal.ofReal M :=
    liminf_le_of_frequently_le (Filter.Eventually.of_forall hIntBound).frequently
  apply (memLp_two_iff_integrable_sq_norm hGf.aestronglyMeasurable).2
  refine ⟨(hGf.norm.pow 2).aestronglyMeasurable, ?_⟩
  apply (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x => sq_nonneg _)).2
  exact lt_of_le_of_lt (hFatou.trans hlimBound) ENNReal.ofReal_lt_top

/-- Dominated convergence for the actual compact cutoff weights. -/
theorem cutoff_square_integral_tendsto {μ : Measure E} {g : E → ℝ}
    (hg : Integrable g μ) (hg0 : ∀ x, 0 ≤ g x) (χ : ℕ → E → ℝ)
    (hχ : ∀ n, Measurable (χ n)) (hχbounds : ∀ n x, 0 ≤ χ n x ∧ χ n x ≤ 1)
    (hχone : ∀ x, ∀ᶠ n : ℕ in atTop, χ n x = 1) :
    Tendsto (fun n => ∫ x, χ n x ^ 2 * g x ∂μ) atTop (𝓝 (∫ x, g x ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence g
  · intro n
    exact ((hχ n).pow_const 2).aestronglyMeasurable.mul hg.aestronglyMeasurable
  · exact hg
  · intro n
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (hg0 x))]
    have hb := hχbounds n x
    have hs : χ n x ^ 2 ≤ 1 := by nlinarith [hb.1, hb.2]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hs (hg0 x)
  · filter_upwards with x
    apply tendsto_const_nhds.congr'
    filter_upwards [hχone x] with n hn
    simp [hn]

/-- Exhausting the exact cutoff identity yields the genuine global energy
identity for L² C² pointwise eigenfunctions, with no derivative domain premise. -/
theorem eigenfunction_global_gradient_energy {V f : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f)
    (hfLp : MemLp f 2 (gibbsMeasure volume V))
    (rate : ℝ) (hrate : 0 ≤ rate)
    (heigen : ∀ x, langevinDifferentialOperator V f x = -rate * f x) :
    (∫ x, ‖gradient f x‖ ^ 2 ∂gibbsMeasure volume V) =
      rate * (∫ x, f x ^ 2 ∂gibbsMeasure volume V) := by
  obtain ⟨C, hC0, χ, hχ, hχc, hχbounds, hχone, hχgrad⟩ := exists_smooth_cutoff_exhaustion (d := d)
  have hgLp := eigenfunction_gradient_memLp_two hV hf hfLp rate hrate heigen
  have hGf : Continuous (gradient f) := (differentiable_gradient_of_contDiff_two hf).continuous
  have hfM : Measurable f := hf.continuous.measurable
  have hχG (n : ℕ) (x : E) : ‖gradient (χ n) x‖ ≤ C := by
    calc
      _ ≤ C / ((n : ℝ) + 1) := hχgrad n x
      _ ≤ C := by
        apply (div_le_iff₀ (by positivity : (0 : ℝ) < n + 1)).2
        nlinarith [mul_nonneg hC0 (Nat.cast_nonneg (α := ℝ) n)]
  have hscale : Tendsto (fun n : ℕ => C / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    have hden : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_apply] using
      (tendsto_inv_atTop_zero.comp hden).const_mul C
  have hgχ (x : E) : Tendsto (fun n => gradient (χ n) x) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => hχgrad n x) hscale
  have hχlim (x : E) : Tendsto (fun n => χ n x) atTop (𝓝 1) :=
    tendsto_const_nhds.congr' ((hχone x).mono (fun n hn => hn.symm))
  have hD : Integrable (fun x => C * |f x| * ‖gradient f x‖) (gibbsMeasure volume V) := by
    simpa only [Pi.mul_def, Real.norm_eq_abs, mul_assoc] using
      (hfLp.norm.integrable_mul hgLp.norm).const_mul C
  have hCross : Tendsto (fun n => ∫ x, χ n x * f x *
      inner ℝ (gradient (χ n) x) (gradient f x) ∂gibbsMeasure volume V) atTop (𝓝 0) := by
    have ht := tendsto_integral_of_dominated_convergence
      (μ := gibbsMeasure volume V) (F := fun n x => χ n x * f x *
        inner ℝ (gradient (χ n) x) (gradient f x)) (f := fun _ => (0 : ℝ))
      (fun x => C * |f x| * ‖gradient f x‖) ?_ hD ?_ ?_
    · simpa using ht
    · intro n
      have hc : Continuous (gradient (χ n)) :=
        (differentiable_gradient_of_contDiff_two (hχ n)).continuous
      have hmχ : Measurable (χ n) := (hχ n).continuous.measurable
      fun_prop
    · intro n
      filter_upwards with x
      have habs : |χ n x| ≤ 1 := by rw [abs_of_nonneg (hχbounds n x).1]; exact (hχbounds n x).2
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      calc
        _ ≤ (|χ n x| * |f x|) * (‖gradient (χ n) x‖ * ‖gradient f x‖) :=
          mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (by positivity)
        _ ≤ (1 * |f x|) * (C * ‖gradient f x‖) := by gcongr; exact hχG n x
        _ = _ := by ring
    · filter_upwards with x
      have ht := ((hχlim x).mul_const (f x)).mul
        ((hgχ x).inner (tendsto_const_nhds (x := gradient f x)))
      simpa using ht
  have hA := cutoff_square_integral_tendsto hgLp.norm.integrable_sq (fun x => sq_nonneg _)
    χ (fun n => (hχ n).continuous.measurable) hχbounds hχone
  have hF := cutoff_square_integral_tendsto hfLp.integrable_sq (fun x => sq_nonneg _)
    χ (fun n => (hχ n).continuous.measurable) hχbounds hχone
  have hleft := hA.add (hCross.const_mul 2)
  have hright := hF.const_mul rate
  have hid : (fun n => (∫ x, χ n x ^ 2 * ‖gradient f x‖ ^ 2 ∂gibbsMeasure volume V) +
      2 * (∫ x, χ n x * f x * inner ℝ (gradient (χ n) x) (gradient f x) ∂gibbsMeasure volume V)) =
      fun n => rate * (∫ x, χ n x ^ 2 * f x ^ 2 ∂gibbsMeasure volume V) := by
    funext n
    exact eigenfunction_cutoff_energy_identity hV hf (hχ n) (hχc n) rate heigen
  rw [← hid] at hright
  simpa using tendsto_nhds_unique hleft hright

end CutoffRigidity
