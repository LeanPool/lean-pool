/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.EigenfunctionCaccioppoli

/-!
# Localized Bochner rigidity without a global product domain

Compact cutoff tests are applied to the coordinate derivatives of an actual
C³ pointwise eigenfunction. The cutoff Hessian estimate is then exhausted
using the already proved global gradient L² bound. Spectral representatives
and the C²/weak-Bochner regularity bridge remain separate obligations.
-/

public section

namespace CutoffRigidity

open MeasureTheory Filter Topology
open scoped ENNReal

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

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

/-- The actual pointwise generator sends C² functions to continuous functions. -/
theorem continuous_langevinDifferentialOperator {V f : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f) :
    Continuous (langevinDifferentialOperator V f) := by
  have hd1 (i : Fin d) : ContDiff ℝ 1 (coordinateDerivative i f) := by
    apply contDiff_coordinateDerivative
    convert hf using 1
    norm_num
  have hd2 (i : Fin d) : Continuous (coordinateDerivative i (coordinateDerivative i f)) := by
    have h : ContDiff ℝ 0 (coordinateDerivative i (coordinateDerivative i f)) := by
      apply contDiff_coordinateDerivative
      convert hd1 i using 1
      norm_num
    exact h.continuous
  have hLap : Continuous (euclideanLaplacian f) := by
    change Continuous (fun x => ∑ i : Fin d, coordinateDerivative i (coordinateDerivative i f) x)
    fun_prop
  exact hLap.sub (((differentiable_gradient_of_contDiff_two hV).continuous).inner
    ((differentiable_gradient_of_contDiff_two hf).continuous))

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

/-- Differentiating an actual pointwise eigenfunction equation, using the
proved commutator rather than assuming a vector eigenfunction equation. -/
theorem langevin_coordinate_eigenfunction_equation {V f : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 3 f) (ρ : ℝ)
    (heigen : ∀ x, langevinDifferentialOperator V f x = -ρ * f x)
    (i : Fin d) (x : E) :
    langevinDifferentialOperator V (coordinateDerivative i f) x =
      -ρ * coordinateDerivative i f x +
        ∑ j : Fin d, coordinateDerivative i (coordinateDerivative j V) x * coordinateDerivative j f
          x := by
  have hder : coordinateDerivative i (langevinDifferentialOperator V f) x =
      -ρ * coordinateDerivative i f x := by
    unfold coordinateDerivative
    rw [funext heigen, fderiv_const_mul ((hf.differentiable (by norm_num)) x), smul_apply,
      smul_eq_mul]
  have h := coordinateDerivative_langevin_commutator hV hf i x
  linarith

/-- Local weighted Bochner energy from the actual compact tests `χ²∂if`.
All terms have compact support and their integrability is proved here. -/
theorem localized_eigenfunction_bochner_identity {V f χ : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 3 f) (hχ : ContDiff ℝ 2 χ)
    (hχc : HasCompactSupport χ) (ρ : ℝ)
    (heigen : ∀ x, langevinDifferentialOperator V f x = -ρ * f x) :
    (∫ x, ∑ i : Fin d, χ x ^ 2 * ‖gradient (coordinateDerivative i f) x‖ ^ 2
      ∂gibbsMeasure volume V) +
      2 * (∫ x, ∑ i : Fin d, χ x * coordinateDerivative i f x *
        inner ℝ (gradient χ x) (gradient (coordinateDerivative i f) x) ∂gibbsMeasure volume V) +
      (∫ x, ∑ i : Fin d, χ x ^ 2 * coordinateDerivative i f x *
        (∑ j : Fin d, coordinateDerivative i (coordinateDerivative j V) x * coordinateDerivative j
          f x)
          ∂gibbsMeasure volume V) =
      ρ * (∫ x, ∑ i : Fin d, χ x ^ 2 * (coordinateDerivative i f x) ^ 2
        ∂gibbsMeasure volume V) := by
  let u (i : Fin d) := coordinateDerivative i f
  have hu (i : Fin d) : ContDiff ℝ 2 (u i) := by
    apply contDiff_coordinateDerivative
    convert hf using 1
    norm_num
  have hGui (i : Fin d) : Continuous (gradient (u i)) :=
    (differentiable_gradient_of_contDiff_two (hu i)).continuous
  have huci (i : Fin d) := (hu i).continuous
  have hGχ : Continuous (gradient χ) := (differentiable_gradient_of_contDiff_two hχ).continuous
  have hVij (i j : Fin d) : Continuous (coordinateDerivative i (coordinateDerivative j V)) := by
    have h : ContDiff ℝ 0 (coordinateDerivative i (coordinateDerivative j V)) := by
      apply contDiff_coordinateDerivative
      apply contDiff_coordinateDerivative
      convert hV using 1
      norm_num
    exact h.continuous
  let A (i : Fin d) (x : E) := χ x ^ 2 * ‖gradient (u i) x‖ ^ 2
  let B (i : Fin d) (x : E) := χ x * u i x * inner ℝ (gradient χ x) (gradient (u i) x)
  let H (i : Fin d) (x : E) := χ x ^ 2 * u i x *
    (∑ j : Fin d, coordinateDerivative i (coordinateDerivative j V) x * u j x)
  let F (i : Fin d) (x : E) := χ x ^ 2 * (u i x) ^ 2
  have hAi (i : Fin d) : Integrable (A i) (gibbsMeasure volume V) := by
    exact integrable_cutoff_square_mul_continuous hV.continuous hχ.continuous hχc (by fun_prop)
  have hBi (i : Fin d) : Integrable (B i) (gibbsMeasure volume V) := by
    have h := integrable_cutoff_mul_continuous hV.continuous hχ.continuous hχc
      (g := fun x => u i x * inner ℝ (gradient χ x) (gradient (u i) x)) (by fun_prop)
    simpa only [B, mul_assoc] using h
  have hHi (i : Fin d) : Integrable (H i) (gibbsMeasure volume V) := by
    have h := integrable_cutoff_square_mul_continuous hV.continuous hχ.continuous hχc
      (g := fun x => u i x * ∑ j : Fin d, coordinateDerivative i (coordinateDerivative j V) x * u j
        x)
      (by fun_prop)
    simpa only [H, mul_assoc] using h
  have hFi (i : Fin d) : Integrable (F i) (gibbsMeasure volume V) :=
    integrable_cutoff_square_mul_continuous hV.continuous hχ.continuous hχc (by fun_prop)
  have hrow (i : Fin d) : (∫ x, A i x ∂gibbsMeasure volume V) +
      2 * (∫ x, B i x ∂gibbsMeasure volume V) + (∫ x, H i x ∂gibbsMeasure volume V) =
        ρ * (∫ x, F i x ∂gibbsMeasure volume V) := by
    have h := cutoff_gibbs_energy_identity hV (hu i) hχ hχc
    have hpoint (x : E) : χ x ^ 2 * u i x * langevinDifferentialOperator V (u i) x =
        -ρ * F i x + H i x := by
      rw [langevin_coordinate_eigenfunction_equation hV hf ρ heigen]
      dsimp only [F, H, u]
      ring
    change (∫ x, χ x ^ 2 * u i x * langevinDifferentialOperator V (u i) x ∂gibbsMeasure volume V) +
      (∫ x, A i x ∂gibbsMeasure volume V) + 2 * (∫ x, B i x ∂gibbsMeasure volume V) = 0 at h
    simp_rw [hpoint] at h
    rw [integral_add ((hFi i).const_mul (-ρ)) (hHi i), integral_const_mul] at h
    linarith
  have hs := Finset.sum_congr rfl (fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) => hrow i)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  rw [integral_finsetSum _ (fun i _ => hAi i), integral_finsetSum _ (fun i _ => hBi i),
    integral_finsetSum _ (fun i _ => hHi i), integral_finsetSum _ (fun i _ => hFi i)]
  exact hs

/-- Parseval's formula for the actual coordinate derivatives. -/
theorem sum_coordinateDerivative_sq (f : E → ℝ) (x : E) :
    (∑ i : Fin d, (coordinateDerivative i f x) ^ 2) = ‖gradient f x‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_congr rfl
  intro i hi
  rw [coordinateDerivative, fderiv_single_eq_gradient_coordinate]

/-- The potential term in the localized identity is the actual Hessian
quadratic form with the cutoff weight. -/
theorem cutoff_hessian_coordinate_contraction {V : E → ℝ}
    (hV : ContDiff ℝ 2 V) (f χ : E → ℝ) (x : E) :
    (∑ i : Fin d, χ x ^ 2 * coordinateDerivative i f x *
      (∑ j : Fin d, coordinateDerivative i (coordinateDerivative j V) x * coordinateDerivative j f
        x)) =
      χ x ^ 2 * fderiv ℝ (fderiv ℝ V) x (gradient f x) (gradient f x) := by
  rw [hessian_gradient_coordinate_contraction hV f]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The localized Hessian estimate at equality of curvature and eigenvalue.
Its right side involves only the global gradient energy, not third-derivative
integrability or a global Bochner domain. -/
theorem eigenfunction_cutoff_hessian_bound {V f χ : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 3 f) (hχ : ContDiff ℝ 2 χ)
    (hχc : HasCompactSupport χ) (ρ : ℝ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (heigen : ∀ x, langevinDifferentialOperator V f x = -ρ * f x) :
    (∫ x, χ x ^ 2 * (∑ i : Fin d, ‖gradient (coordinateDerivative i f) x‖ ^ 2)
      ∂gibbsMeasure volume V) ≤
      4 * (∫ x, ‖gradient χ x‖ ^ 2 * ‖gradient f x‖ ^ 2 ∂gibbsMeasure volume V) := by
  let u (i : Fin d) := coordinateDerivative i f
  have hu (i : Fin d) : ContDiff ℝ 2 (u i) := by
    apply contDiff_coordinateDerivative
    convert hf using 1
    norm_num
  have hGui (i : Fin d) : Continuous (gradient (u i)) :=
    (differentiable_gradient_of_contDiff_two (hu i)).continuous
  have huci (i : Fin d) := (hu i).continuous
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by norm_num)
  have hGf : Continuous (gradient f) := (differentiable_gradient_of_contDiff_two hf2).continuous
  have hGχ : Continuous (gradient χ) := (differentiable_gradient_of_contDiff_two hχ).continuous
  have hVV : Continuous (fderiv ℝ (fderiv ℝ V)) :=
    (((hV.fderiv_right (m := 1) (by norm_num)).fderiv_right (m := 0) (by norm_num))).continuous
  let A (x : E) := ∑ i : Fin d, χ x ^ 2 * ‖gradient (u i) x‖ ^ 2
  let B (x : E) := ∑ i : Fin d, χ x * u i x * inner ℝ (gradient χ x) (gradient (u i) x)
  let D (x : E) := ‖gradient χ x‖ ^ 2 * ‖gradient f x‖ ^ 2
  let H (x : E) := χ x ^ 2 * fderiv ℝ (fderiv ℝ V) x (gradient f x) (gradient f x)
  let F (x : E) := χ x ^ 2 * ‖gradient f x‖ ^ 2
  have hA : Integrable A (gibbsMeasure volume V) :=
    integrable_finsetSum _ (fun i _ =>
      integrable_cutoff_square_mul_continuous hV.continuous hχ.continuous hχc (by fun_prop))
  have hB : Integrable B (gibbsMeasure volume V) := by
    apply integrable_finsetSum
    intro i hi
    have h := integrable_cutoff_mul_continuous hV.continuous hχ.continuous hχc
      (g := fun x => u i x * inner ℝ (gradient χ x) (gradient (u i) x)) (by fun_prop)
    simpa only [mul_assoc] using h
  have hD : Integrable D (gibbsMeasure volume V) := by
    apply integrable_gibbs_of_continuous_hasCompactSupport hV.continuous (by fun_prop)
    have hc : HasCompactSupport (fun x => ‖gradient χ x‖ ^ 2) :=
      (hχc.fderiv ℝ).comp_left
        (g := fun L : E →L[ℝ] ℝ => ‖(InnerProductSpace.toDual ℝ E).symm L‖ ^ 2) (by simp)
    simpa only [Pi.mul_def] using hc.mul_right (f' := fun x => ‖gradient f x‖ ^ 2)
  have hH : Integrable H (gibbsMeasure volume V) :=
    integrable_cutoff_square_mul_continuous hV.continuous hχ.continuous hχc (by fun_prop)
  have hF : Integrable F (gibbsMeasure volume V) :=
    integrable_cutoff_square_mul_continuous hV.continuous hχ.continuous hχc (by fun_prop)
  have hcurv : ρ * (∫ x, F x ∂gibbsMeasure volume V) ≤
      ∫ x, H x ∂gibbsMeasure volume V := by
    rw [← integral_const_mul]
    apply integral_mono (hF.const_mul ρ) hH
    intro x
    dsimp only [H, F]
    nlinarith [mul_le_mul_of_nonneg_left (hHess x (gradient f x)) (sq_nonneg (χ x))]
  have hlocal := localized_eigenfunction_bochner_identity hV hf hχ hχc ρ heigen
  simp_rw [cutoff_hessian_coordinate_contraction hV f χ] at hlocal
  have hFpoint (x : E) : (∑ i : Fin d, χ x ^ 2 * (coordinateDerivative i f x) ^ 2) = F x := by
    rw [← Finset.mul_sum, sum_coordinateDerivative_sq]
  simp_rw [hFpoint] at hlocal
  change (∫ x, A x ∂gibbsMeasure volume V) + 2 * (∫ x, B x ∂gibbsMeasure volume V) +
    (∫ x, H x ∂gibbsMeasure volume V) = ρ * (∫ x, F x ∂gibbsMeasure volume V) at hlocal
  have hpoint (x : E) : 0 ≤ A x + 4 * B x + 4 * D x := by
    have hi (i : Fin d) : 0 ≤ χ x ^ 2 * ‖gradient (u i) x‖ ^ 2 +
        4 * (χ x * u i x * inner ℝ (gradient χ x) (gradient (u i) x)) +
          4 * ((u i x) ^ 2 * ‖gradient χ x‖ ^ 2) := by
      have h := sq_nonneg ‖χ x • gradient (u i) x + (2 * u i x) • gradient χ x‖
      rw [norm_add_sq_real] at h
      simp only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
        real_inner_smul_left, real_inner_smul_right] at h
      rw [← real_inner_comm (gradient (u i) x) (gradient χ x)] at h
      nlinarith
    have hs := Finset.sum_nonneg (fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) => hi i)
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
    have hsumD : (∑ i : Fin d, (u i x) ^ 2 * ‖gradient χ x‖ ^ 2) = D x := by
      rw [← Finset.sum_mul, sum_coordinateDerivative_sq]
      dsimp [D]
      ring
    simpa only [A, B, hsumD, Finset.mul_sum] using hs
  have hpositive : 0 ≤ ∫ x, A x + 4 * B x + 4 * D x ∂gibbsMeasure volume V :=
    integral_nonneg (fun x => hpoint x)
  have hadd := integral_add (hA.add (hB.const_mul 4)) (hD.const_mul 4)
  simp only [Pi.add_apply] at hadd
  rw [hadd, integral_add hA (hB.const_mul 4), integral_const_mul, integral_const_mul] at hpositive
  change (∫ x, χ x ^ 2 * (∑ i : Fin d, ‖gradient (u i) x‖ ^ 2) ∂gibbsMeasure volume V) ≤ _
  simp_rw [Finset.mul_sum]
  change (∫ x, A x ∂gibbsMeasure volume V) ≤ 4 * (∫ x, D x ∂gibbsMeasure volume V)
  linarith

/-- Cutoff exhaustion makes the squared Hessian vanish everywhere for an
actual C³ L² eigenfunction at curvature equality. No global derivative
integration-domain assumption is imposed. -/
theorem c3_eigenfunction_hessian_zero {V f : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 3 f)
    (hfLp : MemLp f 2 (gibbsMeasure volume V)) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (heigen : ∀ x, langevinDifferentialOperator V f x = -ρ * f x) (x : E) :
    fderiv ℝ (fderiv ℝ f) x = 0 := by
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by norm_num)
  have hgLp := eigenfunction_gradient_memLp_two hV hf2 hfLp ρ hρ heigen
  have hGf : Continuous (gradient f) := (differentiable_gradient_of_contDiff_two hf2).continuous
  have hgradSq : Integrable (fun y => ‖gradient f y‖ ^ 2) (gibbsMeasure volume V) :=
    hgLp.norm.integrable_sq
  have hu (i : Fin d) : ContDiff ℝ 2 (coordinateDerivative i f) := by
    apply contDiff_coordinateDerivative
    convert hf using 1
    norm_num
  have hGui (i : Fin d) : Continuous (gradient (coordinateDerivative i f)) :=
    (differentiable_gradient_of_contDiff_two (hu i)).continuous
  let G (y : E) := ∑ i : Fin d, ‖gradient (coordinateDerivative i f) y‖ ^ 2
  have hGcont : Continuous G := by fun_prop
  have hG0 (y : E) : 0 ≤ G y := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  obtain ⟨C, hC0, χ, hχ, hχc, hχbounds, hχone, hχgrad⟩ := exists_smooth_cutoff_exhaustion (d := d)
  let c (n : ℕ) := C / ((n : ℝ) + 1)
  have hc0 (n : ℕ) : 0 ≤ c n := by positivity
  have hcLim : Tendsto c atTop (𝓝 0) := by
    have hden : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
    simpa only [c, div_eq_mul_inv, mul_zero, Function.comp_apply] using
      (tendsto_inv_atTop_zero.comp hden).const_mul C
  have hAn (n : ℕ) : Integrable (fun y => χ n y ^ 2 * G y) (gibbsMeasure volume V) :=
    integrable_cutoff_square_mul_continuous hV.continuous (hχ n).continuous (hχc n) hGcont
  have hBn (n : ℕ) : Integrable
      (fun y => ‖gradient (χ n) y‖ ^ 2 * ‖gradient f y‖ ^ 2) (gibbsMeasure volume V) := by
    have hGχ : Continuous (gradient (χ n)) :=
      (differentiable_gradient_of_contDiff_two (hχ n)).continuous
    apply (hgradSq.const_mul (c n ^ 2)).mono' (by fun_prop)
    filter_upwards with y
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hsq : ‖gradient (χ n) y‖ ^ 2 ≤ c n ^ 2 := by
      have h := hχgrad n y
      change ‖gradient (χ n) y‖ ≤ c n at h
      nlinarith [hc0 n, norm_nonneg (gradient (χ n) y)]
    exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
  have hBbound (n : ℕ) :
      (∫ y, ‖gradient (χ n) y‖ ^ 2 * ‖gradient f y‖ ^ 2 ∂gibbsMeasure volume V) ≤
        c n ^ 2 * (∫ y, ‖gradient f y‖ ^ 2 ∂gibbsMeasure volume V) := by
    rw [← integral_const_mul]
    apply integral_mono (hBn n) (hgradSq.const_mul (c n ^ 2))
    intro y
    have hsq : ‖gradient (χ n) y‖ ^ 2 ≤ c n ^ 2 := by
      have h := hχgrad n y
      change ‖gradient (χ n) y‖ ≤ c n at h
      nlinarith [hc0 n, norm_nonneg (gradient (χ n) y)]
    exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
  have hAbound (n : ℕ) :
      (∫ y, χ n y ^ 2 * G y ∂gibbsMeasure volume V) ≤
        4 * c n ^ 2 * (∫ y, ‖gradient f y‖ ^ 2 ∂gibbsMeasure volume V) := by
    have h := eigenfunction_cutoff_hessian_bound hV hf (hχ n) (hχc n) ρ hHess heigen
    change (∫ y, χ n y ^ 2 * G y ∂gibbsMeasure volume V) ≤ _ at h
    nlinarith [hBbound n]
  let F (n : ℕ) (y : E) : ℝ≥0∞ := ENNReal.ofReal (χ n y ^ 2 * G y)
  have hFmeas (n : ℕ) : Measurable (F n) := by
    have hχM : Measurable (χ n) := (hχ n).continuous.measurable
    have hGM : Measurable G := hGcont.measurable
    dsimp [F]
    fun_prop
  have hFlim (y : E) : Tendsto (fun n => F n y) atTop (𝓝 (ENNReal.ofReal (G y))) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hχone y] with n hn
    simp [F, hn]
  have hFbound (n : ℕ) : (∫⁻ y, F n y ∂gibbsMeasure volume V) ≤
      ENNReal.ofReal (4 * c n ^ 2 * (∫ y, ‖gradient f y‖ ^ 2 ∂gibbsMeasure volume V)) := by
    have h := ofReal_integral_eq_lintegral_ofReal (hAn n)
      (Filter.Eventually.of_forall fun y => mul_nonneg (sq_nonneg _) (hG0 y))
    change ENNReal.ofReal (∫ y, χ n y ^ 2 * G y ∂gibbsMeasure volume V) =
      ∫⁻ y, F n y ∂gibbsMeasure volume V at h
    rw [← h]
    exact ENNReal.ofReal_le_ofReal (hAbound n)
  have hRLim : Tendsto
      (fun n => ENNReal.ofReal (4 * c n ^ 2 * (∫ y, ‖gradient f y‖ ^ 2 ∂gibbsMeasure volume V)))
      atTop (𝓝 0) := by
    have hh := ((hcLim.pow 2).const_mul 4).mul_const
      (∫ y, ‖gradient f y‖ ^ 2 ∂gibbsMeasure volume V)
    simpa [Function.comp_def] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp hh
  have hIntLim : Tendsto (fun n => ∫⁻ y, F n y ∂gibbsMeasure volume V) atTop (𝓝 0) := by
    have hlow (n : ℕ) : (0 : ℝ≥0∞) ≤ ∫⁻ y, F n y ∂gibbsMeasure volume V := bot_le
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hRLim hlow hFbound
  have hFatou := lintegral_liminf_le (μ := gibbsMeasure volume V) (f := F) (u := atTop) hFmeas
  simp_rw [(hFlim _).liminf_eq] at hFatou
  rw [hIntLim.liminf_eq] at hFatou
  have hENN : (∫⁻ y, ENNReal.ofReal (G y) ∂gibbsMeasure volume V) = 0 := le_antisymm hFatou bot_le
  have hae := (lintegral_eq_zero_iff' hGcont.measurable.ennreal_ofReal.aemeasurable).mp hENN
  have hGfun : G = fun _ => (0 : ℝ) := by
    apply gibbsMeasure_eq_of_ae_eq volume hV.continuous.measurable hGcont continuous_const
    filter_upwards [hae] with y hy
    exact le_antisymm (ENNReal.ofReal_eq_zero.mp hy) (hG0 y)
  have hrows (i : Fin d) : gradient (coordinateDerivative i f) x = 0 := by
    have hx := congrFun hGfun x
    have he := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) => sq_nonneg
        ‖gradient (coordinateDerivative i f) x‖)).mp hx i (Finset.mem_univ i)
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp he)
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) x
  have hcoef (i j : Fin d) :
      fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) = 0 := by
    rw [← second_fderiv_apply_const hd]
    change fderiv ℝ (coordinateDerivative j f) x (EuclideanSpace.single i 1) = 0
    rw [fderiv_single_eq_gradient_coordinate, hrows j]
    simp
  ext u v
  change fderiv ℝ (fderiv ℝ f) x u v = 0
  rw [bilinear_euclidean_coordinate_expansion]
  simp_rw [hcoef]
  simp

/-- Domain-free C³ intermediate of the source rigidity conclusion: actual
L² eigenfunctions at curvature equality are affine. The spectral/C²
regularity bridge remains separate. -/
theorem c3_L2_eigenfunction_is_affine {V f : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 3 f)
    (hfLp : MemLp f 2 (gibbsMeasure volume V)) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (heigen : ∀ x, langevinDifferentialOperator V f x = -ρ * f x) (x : E) :
    f x = f 0 + inner ℝ (gradient f 0) x := by
  exact eq_affine_inner_gradient_of_contDiff_two_of_hessian_zero
    (hf.of_le (by norm_num)) (c3_eigenfunction_hessian_zero hV hf hfLp ρ hρ hHess heigen) x

end CutoffRigidity
