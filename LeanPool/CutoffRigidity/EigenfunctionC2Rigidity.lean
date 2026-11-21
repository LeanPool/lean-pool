/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.EigenfunctionWeakBochner
public import LeanPool.CutoffRigidity.CompactDifferenceQuotients
public import LeanPool.CutoffRigidity.EuclideanDerivatives

/-!
# Curvature equality rigidity at the paper's C² regularity

Actual compact finite differences test the differentiated weak equation.
Local dominated convergence uses only first and second derivatives of f.
-/

public section

namespace CutoffRigidity

open MeasureTheory Filter Topology
open scoped ENNReal

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- Compactly weighted actual difference quotients converge in the Gibbs integral. -/
theorem integral_compact_weight_differenceQuotient_tendsto {V f w : E → ℝ}
    (hV : Continuous V) (hf : ContDiff ℝ 1 f) (hw : Continuous w)
    (hwc : HasCompactSupport w) (v : E) :
    Tendsto (fun n => ∫ x, w x * directionalDifferenceQuotient f v (differenceStep n) x
      ∂gibbsMeasure volume V) atTop
      (𝓝 (∫ x, w x * fderiv ℝ f x v ∂gibbsMeasure volume V)) := by
  obtain ⟨M, hM, hbound⟩ := directionalDifferenceQuotient_bounded_on_compact hf v hwc
  have hD : Integrable (fun x => M * |w x|) (gibbsMeasure volume V) := by
    apply integrable_gibbs_of_continuous_hasCompactSupport hV (by fun_prop)
    exact (hwc.comp_left (g := fun t : ℝ => M * |t|) (by simp))
  apply tendsto_integral_of_dominated_convergence (fun x => M * |w x|)
  · intro n
    have hq : Continuous (directionalDifferenceQuotient f v (differenceStep n)) := by
      unfold directionalDifferenceQuotient
      fun_prop
    exact (hw.mul hq).aestronglyMeasurable
  · exact hD
  · intro n
    filter_upwards with x
    by_cases hx : x ∈ tsupport w
    · have hb := hbound x hx (differenceStep n) (differenceStep_pos n) (differenceStep_le_one n)
      rw [norm_mul, Real.norm_eq_abs (w x)]
      nlinarith [abs_nonneg (w x)]
    · have hwx : w x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [hwx]
  · filter_upwards with x
    exact (directionalDifferenceQuotient_tendsto (hf.differentiable
      (by norm_num)) v x).const_mul (w x)

/-- Compactly weighted vector difference quotients converge against actual
continuous vector fields, without any global derivative integrability. -/
theorem integral_compact_weight_inner_differenceQuotient_tendsto
    {V w : E → ℝ} {G H : E → E} (hV : Continuous V)
    (hG : ContDiff ℝ 1 G) (hH : Continuous H) (hw : Continuous w)
    (hwc : HasCompactSupport w) (v : E) :
    Tendsto (fun n => ∫ x, w x * inner ℝ
      (directionalDifferenceQuotient G v (differenceStep n) x) (H x)
      ∂gibbsMeasure volume V) atTop
      (𝓝 (∫ x, w x * inner ℝ (fderiv ℝ G x v) (H x) ∂gibbsMeasure volume V)) := by
  obtain ⟨M, hM, hbound⟩ := directionalDifferenceQuotient_bounded_on_compact hG v hwc
  have hD : Integrable (fun x => M * |w x| * ‖H x‖) (gibbsMeasure volume V) := by
    apply integrable_gibbs_of_continuous_hasCompactSupport hV (by fun_prop)
    have hc : HasCompactSupport (fun x => M * |w x|) :=
      hwc.comp_left (g := fun t : ℝ => M * |t|) (by simp)
    simpa only [Pi.mul_def] using hc.mul_right (f' := fun x => ‖H x‖)
  apply tendsto_integral_of_dominated_convergence (fun x => M * |w x| * ‖H x‖)
  · intro n
    have hq : Continuous (directionalDifferenceQuotient G v (differenceStep n)) := by
      unfold directionalDifferenceQuotient
      fun_prop
    exact (hw.mul (hq.inner hH)).aestronglyMeasurable
  · exact hD
  · intro n
    filter_upwards with x
    by_cases hx : x ∈ tsupport w
    · have hb := hbound x hx (differenceStep n) (differenceStep_pos n) (differenceStep_le_one n)
      rw [Real.norm_eq_abs, abs_mul]
      calc
        _ ≤ |w x| * (‖directionalDifferenceQuotient G v (differenceStep n) x‖ * ‖H x‖) :=
          mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (abs_nonneg _)
        _ ≤ |w x| * (M * ‖H x‖) := by gcongr
        _ = M * |w x| * ‖H x‖ := by ring
    · have hwx : w x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [hwx]
  · filter_upwards with x
    exact ((directionalDifferenceQuotient_tendsto (hG.differentiable (by norm_num)) v x).inner
      tendsto_const_nhds).const_mul (w x)

/-- The exact localized derivative energy at C² regularity. The compact test
χ²∂if is obtained from actual C² finite-difference tests, rather than by
assuming an unavailable third derivative of f. -/
theorem c2_eigenfunction_localized_row_energy {V f χ : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f) (hχ : ContDiff ℝ 2 χ)
    (hχc : HasCompactSupport χ) (ρ : ℝ)
    (heigen : ∀ x, langevinDifferentialOperator V f x = -ρ * f x) (i : Fin d) :
    (∫ x, χ x ^ 2 * ‖gradient (coordinateDerivative i f) x‖ ^ 2 ∂gibbsMeasure volume V) +
      2 * (∫ x, χ x * coordinateDerivative i f x *
        inner ℝ (gradient χ x) (gradient (coordinateDerivative i f) x) ∂gibbsMeasure volume V) +
      (∫ x, χ x ^ 2 * coordinateDerivative i f x *
        (∑ j : Fin d, coordinateDerivative i (coordinateDerivative j V) x * coordinateDerivative j
          f x)
          ∂gibbsMeasure volume V) =
      ρ * (∫ x, χ x ^ 2 * (coordinateDerivative i f x) ^ 2 ∂gibbsMeasure volume V) := by
  let μ := gibbsMeasure volume V
  let v : E := EuclideanSpace.single i 1
  let u := coordinateDerivative i f
  let q (n : ℕ) := directionalDifferenceQuotient f v (differenceStep n)
  let ψ (n : ℕ) (x : E) := χ x ^ 2 * q n x
  let H (x : E) := ∑ j : Fin d,
    coordinateDerivative i (coordinateDerivative j V) x * coordinateDerivative j f x
  have hu : ContDiff ℝ 1 u := c1_coordinateDerivative_of_c2 hf i
  have hGu : Continuous (gradient u) := continuous_gradient_of_c1 hu
  have hGχ : Continuous (gradient χ) := continuous_gradient_of_c1 (hχ.of_le (by norm_num))
  have hH : Continuous H := by
    have hh (j : Fin d) := continuous_coordinateDerivative_of_c1 (c1_coordinateDerivative_of_c2 hV
      j) i
    have hj (j : Fin d) := (c1_coordinateDerivative_of_c2 hf j).continuous
    fun_prop
  have hq (n : ℕ) : ContDiff ℝ 2 (q n) := contDiff_directionalDifferenceQuotient hf v _
  have hGq (n : ℕ) : Continuous (gradient (q n)) := continuous_gradient_of_c1 ((hq n).of_le
    (by norm_num))
  have hcs : HasCompactSupport (fun x => χ x ^ 2) :=
    hχc.comp_left (g := fun t : ℝ => t ^ 2) (by simp)
  have hψ (n : ℕ) : ContDiff ℝ 2 (ψ n) := (hχ.pow 2).mul (hq n)
  have hψc (n : ℕ) : HasCompactSupport (ψ n) := by
    simpa only [ψ, Pi.mul_def] using hcs.mul_right (f' := q n)
  let wB (x : E) := χ x * inner ℝ (gradient χ x) (gradient u x)
  have hwB : Continuous wB := by fun_prop
  have hwBc : HasCompactSupport wB := by
    simpa only [wB, Pi.mul_def] using hχc.mul_right
      (f' := fun x => inner ℝ (gradient χ x) (gradient u x))
  have hA (n : ℕ) : Integrable
      (fun x => χ x ^ 2 * inner ℝ (gradient (q n) x) (gradient u x)) μ :=
    integrable_cutoff_square_mul_continuous hV.continuous hχ.continuous hχc (by fun_prop)
  have hB (n : ℕ) : Integrable (fun x => wB x * q n x) μ :=
    integrable_cutoff_mul_continuous hV.continuous hwB hwBc (hq n).continuous
  have hpoint (n : ℕ) (x : E) : inner ℝ (gradient (ψ n) x) (gradient u x) =
      χ x ^ 2 * inner ℝ (gradient (q n) x) (gradient u x) + 2 * (wB x * q n x) := by
    rw [gradient_cutoff_square_mul (hχ.differentiable (by norm_num))
      ((hq n).differentiable (by norm_num)), inner_add_left,
      real_inner_smul_left, real_inner_smul_left]
    dsimp only [wB]
    ring
  have hAlim := integral_compact_weight_inner_differenceQuotient_tendsto hV.continuous
    (contDiff_gradient_of_c2 hf) hGu (hχ.continuous.pow 2) hcs v
  dsimp only [v] at hAlim
  simp_rw [fderiv_gradient_coordinate hf i] at hAlim
  have hAlim' : Tendsto (fun n => ∫ x, χ x ^ 2 * inner ℝ (gradient (q n) x) (gradient u x) ∂μ)
      atTop (𝓝 (∫ x, χ x ^ 2 * ‖gradient u x‖ ^ 2 ∂μ)) := by
    simpa only [q, v, u, μ, Pi.pow_apply,
      ← gradient_directionalDifferenceQuotient (hf.differentiable (by norm_num)),
      real_inner_self_eq_norm_sq] using hAlim
  have hBlim := integral_compact_weight_differenceQuotient_tendsto hV.continuous
    (hf.of_le (by norm_num)) hwB hwBc v
  have hGlim : Tendsto (fun n => ∫ x, inner ℝ (gradient (ψ n) x) (gradient u x) ∂μ)
      atTop (𝓝 ((∫ x, χ x ^ 2 * ‖gradient u x‖ ^ 2 ∂μ) +
        2 * (∫ x, wB x * u x ∂μ))) := by
    have hh := hAlim'.add (hBlim.const_mul 2)
    convert hh using 1
    · ext n
      simp_rw [hpoint]
      rw [integral_add (hA n) ((hB n).const_mul 2), integral_const_mul]
    · rfl
  have hwH : Continuous (fun x => χ x ^ 2 * H x) := by fun_prop
  have hwHc : HasCompactSupport (fun x => χ x ^ 2 * H x) := by
    simpa only [Pi.mul_def] using hcs.mul_right (f' := H)
  have hHlim := integral_compact_weight_differenceQuotient_tendsto hV.continuous
    (hf.of_le (by norm_num)) hwH hwHc v
  have hwF : Continuous (fun x => χ x ^ 2 * u x) := by fun_prop
  have hwFc : HasCompactSupport (fun x => χ x ^ 2 * u x) := by
    simpa only [Pi.mul_def] using hcs.mul_right (f' := u)
  have hFlim := integral_compact_weight_differenceQuotient_tendsto hV.continuous
    (hf.of_le (by norm_num)) hwF hwFc v
  have hweak (n : ℕ) := c2_eigenfunction_differentiated_weak_equation
    hV hf (hψ n) (hψc n) ρ heigen i
  have heq (n : ℕ) : (∫ x, inner ℝ (gradient (ψ n) x) (gradient u x) ∂μ) +
      (∫ x, (χ x ^ 2 * H x) * q n x ∂μ) =
      ρ * (∫ x, (χ x ^ 2 * u x) * q n x ∂μ) := by
    have hh := hweak n
    simp_rw [coordinateDerivative, ← inner_gradient_eq_sum_fderiv_single] at hh
    simpa only [μ, ψ, H, u, coordinateDerivative, mul_assoc, mul_left_comm, mul_comm] using hh
  have hh := tendsto_nhds_unique (hGlim.add hHlim)
    (((hFlim.const_mul ρ).congr' (Filter.Eventually.of_forall fun n => (heq n).symm)))
  simpa only [μ, u, v, H, wB, coordinateDerivative, pow_two,
    mul_assoc, mul_left_comm, mul_comm] using hh

/-- Local weighted Bochner energy from the actual compact tests `χ²∂if`.
All terms have compact support and their integrability is proved here. -/
theorem c2_localized_eigenfunction_bochner_identity {V f χ : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f) (hχ : ContDiff ℝ 2 χ)
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
  have hu (i : Fin d) : ContDiff ℝ 1 (u i) := by
    apply contDiff_coordinateDerivative
    convert hf using 1
    norm_num
  have hGui (i : Fin d) : Continuous (gradient (u i)) :=
    continuous_gradient_of_c1 (hu i)
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
    exact c2_eigenfunction_localized_row_energy hV hf hχ hχc ρ heigen i
  have hs := Finset.sum_congr rfl (fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) => hrow i)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  rw [integral_finsetSum _ (fun i _ => hAi i), integral_finsetSum _ (fun i _ => hBi i),
    integral_finsetSum _ (fun i _ => hHi i), integral_finsetSum _ (fun i _ => hFi i)]
  exact hs


/-- The localized Hessian estimate at equality of curvature and eigenvalue.
Its right side involves only the global gradient energy, not third-derivative
integrability or a global Bochner domain. -/
theorem c2_eigenfunction_cutoff_hessian_bound {V f χ : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f) (hχ : ContDiff ℝ 2 χ)
    (hχc : HasCompactSupport χ) (ρ : ℝ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (heigen : ∀ x, langevinDifferentialOperator V f x = -ρ * f x) :
    (∫ x, χ x ^ 2 * (∑ i : Fin d, ‖gradient (coordinateDerivative i f) x‖ ^ 2)
      ∂gibbsMeasure volume V) ≤
      4 * (∫ x, ‖gradient χ x‖ ^ 2 * ‖gradient f x‖ ^ 2 ∂gibbsMeasure volume V) := by
  let u (i : Fin d) := coordinateDerivative i f
  have hu (i : Fin d) : ContDiff ℝ 1 (u i) := by
    apply contDiff_coordinateDerivative
    convert hf using 1
    norm_num
  have hGui (i : Fin d) : Continuous (gradient (u i)) :=
    continuous_gradient_of_c1 (hu i)
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
  have hlocal := c2_localized_eigenfunction_bochner_identity hV hf hχ hχc ρ heigen
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
actual C² L² eigenfunction at curvature equality. No global derivative
integration-domain assumption is imposed. -/
theorem c2_eigenfunction_hessian_zero {V f : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f)
    (hfLp : MemLp f 2 (gibbsMeasure volume V)) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (heigen : ∀ x, langevinDifferentialOperator V f x = -ρ * f x) (x : E) :
    fderiv ℝ (fderiv ℝ f) x = 0 := by
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by norm_num)
  have hgLp := eigenfunction_gradient_memLp_two hV hf2 hfLp ρ hρ heigen
  have hGf : Continuous (gradient f) := (differentiable_gradient_of_contDiff_two hf2).continuous
  have hgradSq : Integrable (fun y => ‖gradient f y‖ ^ 2) (gibbsMeasure volume V) :=
    hgLp.norm.integrable_sq
  have hu (i : Fin d) : ContDiff ℝ 1 (coordinateDerivative i f) := by
    apply contDiff_coordinateDerivative
    convert hf using 1
    norm_num
  have hGui (i : Fin d) : Continuous (gradient (coordinateDerivative i f)) :=
    continuous_gradient_of_c1 (hu i)
  let G (y : E) := ∑ i : Fin d, ‖gradient (coordinateDerivative i f) y‖ ^ 2
  have hGcont : Continuous G := by fun_prop
  have hG0 (y : E) : 0 ≤ G y := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  obtain ⟨C, hC0, χ, hχ, hχc, hχbounds, hχone, hχgrad⟩ := exists_smooth_cutoff_exhaustion (d := d)
  let c (n : ℕ) := C / ((n : ℝ) + 1)
  have hcLim : Tendsto c atTop (𝓝 0) := cutoff_inverse_radius_tendsto_zero C
  have hcutoffSq (n : ℕ) (y : E) : ‖gradient (χ n) y‖ ^ 2 ≤ c n ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (hχgrad n y) 2
  have hAn (n : ℕ) : Integrable (fun y => χ n y ^ 2 * G y) (gibbsMeasure volume V) :=
    integrable_cutoff_square_mul_continuous hV.continuous (hχ n).continuous (hχc n) hGcont
  have hBn (n : ℕ) : Integrable
      (fun y => ‖gradient (χ n) y‖ ^ 2 * ‖gradient f y‖ ^ 2) (gibbsMeasure volume V) := by
    have hGχ : Continuous (gradient (χ n)) :=
      (differentiable_gradient_of_contDiff_two (hχ n)).continuous
    apply (hgradSq.const_mul (c n ^ 2)).mono' (by fun_prop)
    filter_upwards with y
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_right (hcutoffSq n y) (sq_nonneg _)
  have hBbound (n : ℕ) :
      (∫ y, ‖gradient (χ n) y‖ ^ 2 * ‖gradient f y‖ ^ 2 ∂gibbsMeasure volume V) ≤
        c n ^ 2 * (∫ y, ‖gradient f y‖ ^ 2 ∂gibbsMeasure volume V) := by
    rw [← integral_const_mul]
    apply integral_mono (hBn n) (hgradSq.const_mul (c n ^ 2))
    intro y
    exact mul_le_mul_of_nonneg_right (hcutoffSq n y) (sq_nonneg _)
  have hAbound (n : ℕ) :
      (∫ y, χ n y ^ 2 * G y ∂gibbsMeasure volume V) ≤
        4 * c n ^ 2 * (∫ y, ‖gradient f y‖ ^ 2 ∂gibbsMeasure volume V) := by
    have h := c2_eigenfunction_cutoff_hessian_bound hV hf (hχ n) (hχc n) ρ hHess heigen
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
  have hFatou := lintegral_le_of_ae_tendsto_bounds (fun n => (hFmeas n).aemeasurable)
    (Filter.Eventually.of_forall hFlim) hFbound hRLim
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

/-- Domain-free C² pointwise form of the source rigidity conclusion: actual
L² eigenfunctions at curvature equality are affine. The spectral representative
bridge remains separate. -/
theorem c2_L2_eigenfunction_is_affine {V f : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f)
    (hfLp : MemLp f 2 (gibbsMeasure volume V)) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (heigen : ∀ x, langevinDifferentialOperator V f x = -ρ * f x) (x : E) :
    f x = f 0 + inner ℝ (gradient f 0) x := by
  exact eq_affine_inner_gradient_of_contDiff_two_of_hessian_zero
    (hf.of_le (by norm_num)) (c2_eigenfunction_hessian_zero hV hf hfLp ρ hρ hHess heigen) x

/-- The localized Bochner identity for a C³ eigenfunction. -/
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
        ∂gibbsMeasure volume V) :=
  c2_localized_eigenfunction_bochner_identity hV (hf.of_le (by norm_num)) hχ hχc ρ heigen

/-- The cutoff Hessian estimate for a C³ eigenfunction. -/
theorem eigenfunction_cutoff_hessian_bound {V f χ : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 3 f) (hχ : ContDiff ℝ 2 χ)
    (hχc : HasCompactSupport χ) (ρ : ℝ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (heigen : ∀ x, langevinDifferentialOperator V f x = -ρ * f x) :
    (∫ x, χ x ^ 2 * (∑ i : Fin d, ‖gradient (coordinateDerivative i f) x‖ ^ 2)
      ∂gibbsMeasure volume V) ≤
      4 * (∫ x, ‖gradient χ x‖ ^ 2 * ‖gradient f x‖ ^ 2 ∂gibbsMeasure volume V) :=
  c2_eigenfunction_cutoff_hessian_bound hV (hf.of_le (by norm_num)) hχ hχc ρ hHess heigen

/-- An L² C³ eigenfunction at curvature equality has zero Hessian. -/
theorem c3_eigenfunction_hessian_zero {V f : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 3 f)
    (hfLp : MemLp f 2 (gibbsMeasure volume V)) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (heigen : ∀ x, langevinDifferentialOperator V f x = -ρ * f x) (x : E) :
    fderiv ℝ (fderiv ℝ f) x = 0 :=
  c2_eigenfunction_hessian_zero hV (hf.of_le (by norm_num)) hfLp ρ hρ hHess heigen x

/-- An L² C³ eigenfunction at curvature equality is affine. -/
theorem c3_L2_eigenfunction_is_affine {V f : E → ℝ}
    (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 3 f)
    (hfLp : MemLp f 2 (gibbsMeasure volume V)) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hHess : ∀ x z : E, ρ * ‖z‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ V) x z z)
    (heigen : ∀ x, langevinDifferentialOperator V f x = -ρ * f x) (x : E) :
    f x = f 0 + inner ℝ (gradient f 0) x :=
  c2_L2_eigenfunction_is_affine hV (hf.of_le (by norm_num)) hfLp ρ hρ hHess heigen x

end CutoffRigidity
