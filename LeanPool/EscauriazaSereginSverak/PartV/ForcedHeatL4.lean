/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.ForcedHeatCriticalFinal
public import LeanPool.EscauriazaSereginSverak.PartV.ForcedHeatEnergyEstimate
public import Mathlib.Analysis.MeanInequalities

/-!
# The `L⁴` bound for the smooth forced heat response

The energy estimate and the Gagliardo–Nirenberg inequality give
`∫∫ |Z|^{10/3} ≤ C (∫∫ |g|²)^{5/3}`; interpolating with the critical `L⁵`
bound gives `∫∫ |Z|⁴ ≤ C (∫∫ |g|²) (∫∫ |g|^{5/2})^{4/5}`, the smooth-data form
of `eq:pv-stokes-l4` in `lem:pv-stokes`.
-/

public section

open CKN

open MeasureTheory Set Filter
open CKN.Foundation.Heat CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The space-time `L^{10/3}` bound of the smooth forced heat response in terms
of the space-time `L²` norm of the tensor. -/
theorem response_tenThirds_le {g : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ}
    (hg : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (g i j)) (hgc : ∀ i j, HasCompactSupport (g i j))
    (hgpos : ∀ i j, tsupport (g i j) ⊆ {p | 0 < p.2}) {τ : ℝ} (hτ : 0 ≤ τ) :
    Integrable (fun p => ∑ i : Fin 3, |responseVec g p i| ^ (10 / 3 : ℝ))
        ((volume : Measure Vec3).prod (volume.restrict (Ioc 0 τ))) ∧
    ∫ p, ∑ i : Fin 3, |responseVec g p i| ^ (10 / 3 : ℝ)
        ∂((volume : Measure Vec3).prod (volume.restrict (Ioc 0 τ))) ≤
      gagliardoNirenbergSobolevConstant.toReal ^ 2 *
        (∫ p, ∑ i : Fin 3, ∑ j : Fin 3, (g i j p) ^ 2
          ∂((volume : Measure Vec3).prod (volume.restrict (Ioc 0 τ)))) ^ (5 / 3 : ℝ) := by
  set μ := (volume : Measure Vec3).prod (volume.restrict (Ioc (0 : ℝ) τ))
  set E2 : ℝ := ∫ p, ∑ i : Fin 3, ∑ j : Fin 3, (g i j p) ^ 2 ∂μ with hE2
  set κ : ℝ := gagliardoNirenbergSobolevConstant.toReal
  obtain ⟨hAint, hBint, _⟩ := response_sq_window_integrable hg hgc 0 τ
  have hE20 : 0 ≤ E2 := integral_nonneg fun p =>
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  obtain ⟨M, hM, hdec⟩ := vecTimeDiv_response_decay hg hgc
  let U : Fin 3 → Vec3 × ℝ → ℝ := fun k => causalHeatConv (vecTimeDiv g k)
  have hU (k : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (U k) :=
    causalHeatConv_contDiff (vecTimeDiv_contDiff hg k) (vecTimeDiv_hasCompactSupport hgc k)
  -- pointwise decay of the powers
  have hpow (i : Fin 3) (p : Vec3 × ℝ) : |responseVec g p i| ^ (10 / 3 : ℝ) ≤
      M ^ (4 / 3 : ℝ) * M ^ 2 / (1 + vec3EuclideanNorm p.1) ^ 6 := by
    have hw : 1 ≤ (1 + vec3EuclideanNorm p.1) ^ 3 := one_le_pow₀ (by
      have := vec3EuclideanNorm_nonneg p.1
      linarith only [this])
    have hb := (hdec i i i p).1
    have hbM : |responseVec g p i| ≤ M := hb.trans (div_le_self hM hw)
    have hsq : |responseVec g p i| ^ 2 ≤ M ^ 2 / (1 + vec3EuclideanNorm p.1) ^ 6 := by
      have h := pow_le_pow_left₀ (abs_nonneg _) hb 2
      rw [div_pow, ← pow_mul] at h
      exact h
    calc
      |responseVec g p i| ^ (10 / 3 : ℝ) =
          |responseVec g p i| ^ (4 / 3 : ℝ) * |responseVec g p i| ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_add' (abs_nonneg _) (by norm_num)]
        norm_num
      _ ≤ M ^ (4 / 3 : ℝ) * (M ^ 2 / (1 + vec3EuclideanNorm p.1) ^ 6) :=
        mul_le_mul (Real.rpow_le_rpow (abs_nonneg _) hbM (by norm_num)) hsq
          (sq_nonneg _) (by positivity)
      _ = _ := by ring
  have hZc (i : Fin 3) : Continuous (fun p => responseVec g p i) := (hU i).continuous
  have hFc : Continuous (fun p => ∑ i : Fin 3, |responseVec g p i| ^ (10 / 3 : ℝ)) :=
    continuous_finsetSum _ fun i _ => (hZc i).abs.rpow_const fun _ => Or.inr (by norm_num)
  have hFint : Integrable (fun p => ∑ i : Fin 3, |responseVec g p i| ^ (10 / 3 : ℝ)) μ := by
    refine integrable_window_of_decay (C := 3 * (M ^ (4 / 3 : ℝ) * M ^ 2)) hFc (by positivity)
      fun x t _ => ?_
    rw [abs_of_nonneg (Finset.sum_nonneg fun i _ => by positivity)]
    calc
      ∑ i : Fin 3, |responseVec g (x, t) i| ^ (10 / 3 : ℝ) ≤
          ∑ _i : Fin 3, M ^ (4 / 3 : ℝ) * M ^ 2 / (1 + vec3EuclideanNorm x) ^ 6 :=
        Finset.sum_le_sum fun i _ => hpow i (x, t)
      _ = _ := by simp; ring
  refine ⟨hFint, ?_⟩
  -- the slice estimate
  have hslice : ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) τ)),
      ∫ x, ∑ i : Fin 3, |responseVec g (x, t) i| ^ (10 / 3 : ℝ) ≤
        (κ ^ 2 * E2 ^ (2 / 3 : ℝ)) *
          ∫ x, ∑ i : Fin 3, ∑ j : Fin 3, (responseGrad g j (x, t) i) ^ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have henergy := response_energy_le hg hgc hgpos ht.1.le
    obtain ⟨hA', hB', _⟩ := response_sq_window_integrable hg hgc 0 t
    have hwin := window_integral_mono ht.2 hBint fun p =>
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg (g i j p)
    have hgrad0 : 0 ≤ ∫ p, ∑ i : Fin 3, ∑ j : Fin 3, (responseGrad g j p i) ^ 2
        ∂((volume : Measure Vec3).prod (volume.restrict (Ioc 0 t))) :=
      integral_nonneg fun p => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
        sq_nonneg _
    have hL2 : ∫ x, ∑ i : Fin 3, (responseVec g (x, t) i) ^ 2 ≤ E2 := by
      linarith only [henergy, hwin, hgrad0]
    have hsc : Continuous (fun x : Vec3 => ((x, t) : Vec3 × ℝ)) :=
      continuous_id.prodMk continuous_const
    have hsl : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec3 => ((y, t) : Vec3 × ℝ)) :=
      contDiff_id.prodMk contDiff_const
    have hwt (x : Vec3) : 1 ≤ (1 + vec3EuclideanNorm x) ^ 3 := one_le_pow₀ (by
      have := vec3EuclideanNorm_nonneg x
      linarith only [this])
    have hsqdec {f : Vec3 → ℝ} (hf : ∀ x, |f x| ≤ M / (1 + vec3EuclideanNorm x) ^ 3)
        (x : Vec3) : |f x ^ 2| ≤ M ^ 2 / (1 + vec3EuclideanNorm x) ^ 6 := by
      rw [abs_of_nonneg (sq_nonneg _)]
      have h := pow_le_pow_left₀ (abs_nonneg _) (hf x) 2
      rw [sq_abs, div_pow, ← pow_mul] at h
      exact h
    have hcomp (i : Fin 3) : ∫ x, |responseVec g (x, t) i| ^ (10 / 3 : ℝ) ≤
        (κ ^ 2 * E2 ^ (2 / 3 : ℝ)) *
          ∫ x, ∑ j : Fin 3, (responseGrad g j (x, t) i) ^ 2 := by
      let f : Vec3 → ℝ := fun x => U i (x, t)
      have hf : ContDiff ℝ 1 f := ((hU i).comp hsl).of_le (by simp)
      have hDf (j : Fin 3) (x : Vec3) : fderiv ℝ f x (CKN.basisVec j) =
          responseGrad g j (x, t) i :=
        fderiv_slice_apply ((hU i).differentiable (by simp)) x t (CKN.basisVec j)
      have hf2 : Integrable (fun x => f x ^ 2) :=
        integrable_of_abs_le_decay_six' (sq_nonneg M) (((hU i).continuous.comp hsc).pow 2)
          (hsqdec fun x => (hdec i i i (x, t)).1)
      have hDf2 (j : Fin 3) : Integrable (fun x => (fderiv ℝ f x (CKN.basisVec j)) ^ 2) := by
        simp_rw [hDf]
        exact integrable_of_abs_le_decay_six' (sq_nonneg M)
          (((((hU i).continuous_fderiv (by simp)).clm_apply continuous_const).comp hsc).pow 2)
          (hsqdec fun x => (hdec i j j (x, t)).2.1)
      have hf103 : Integrable (fun x => |f x| ^ (10 / 3 : ℝ)) :=
        integrable_of_abs_le_decay_six' (C := M ^ (4 / 3 : ℝ) * M ^ 2) (by positivity)
          (((hU i).continuous.comp hsc).abs.rpow_const fun _ => Or.inr (by norm_num))
          fun x => by
            rw [abs_of_nonneg (by positivity)]
            exact hpow i (x, t)
      have hGN := integral_rpow_tenThirds_le hf hf2 hDf2 hf103
      simp_rw [hDf] at hGN
      have hfL2 : ∫ x, f x ^ 2 ≤ E2 := by
        refine le_trans ?_ hL2
        refine integral_mono hf2 (integrable_finsetSum _ fun k _ =>
          integrable_of_abs_le_decay_six' (sq_nonneg M)
            (((hU k).continuous.comp hsc).pow 2) (hsqdec fun x => (hdec k k k (x, t)).1))
          fun x => ?_
        exact Finset.single_le_sum (f := fun k => (responseVec g (x, t) k) ^ 2)
          (fun k _ => sq_nonneg _) (Finset.mem_univ i)
      have hgr0 : 0 ≤ ∫ x, ∑ j : Fin 3, (responseGrad g j (x, t) i) ^ 2 :=
        integral_nonneg fun x => Finset.sum_nonneg fun j _ => sq_nonneg _
      refine hGN.trans ?_
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (integral_nonneg fun x => sq_nonneg _) hfL2 (by norm_num))
        (sq_nonneg _)) hgr0
    have hcompint (i : Fin 3) : Integrable (fun x => |responseVec g (x, t) i| ^ (10 / 3 : ℝ)) :=
      integrable_of_abs_le_decay_six' (C := M ^ (4 / 3 : ℝ) * M ^ 2) (by positivity)
        ((((hU i).continuous.comp hsc).abs.rpow_const fun _ => Or.inr (by norm_num)))
        fun x => by
          rw [abs_of_nonneg (by positivity)]
          exact hpow i (x, t)
    have hgradint (i : Fin 3) : Integrable (fun x => ∑ j : Fin 3,
        (responseGrad g j (x, t) i) ^ 2) :=
      integrable_finsetSum _ fun j _ => integrable_of_abs_le_decay_six' (sq_nonneg M)
        (((((hU i).continuous_fderiv (by simp)).clm_apply continuous_const).comp hsc).pow 2)
        (hsqdec fun x => (hdec i j j (x, t)).2.1)
    rw [integral_finsetSum _ fun i _ => hcompint i, integral_finsetSum _ fun i _ => hgradint i,
      Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => hcomp i
  have hFslice := hFint.integral_prod_right
  have hGslice := hAint.integral_prod_right
  have hstep := integral_mono_ae hFslice (hGslice.const_mul _) hslice
  rw [integral_const_mul, ← integral_prod_symm _ hAint, ← integral_prod_symm _ hFint] at hstep
  refine hstep.trans ?_
  have henergy := response_energy_le hg hgc hgpos hτ
  have hL20 : 0 ≤ ∫ x, ∑ i : Fin 3, (responseVec g (x, τ) i) ^ 2 :=
    integral_nonneg fun x => Finset.sum_nonneg fun i _ => sq_nonneg _
  have hgradE : ∫ p, ∑ i : Fin 3, ∑ j : Fin 3, (responseGrad g j p i) ^ 2 ∂μ ≤ E2 := by
    linarith only [henergy, hL20]
  calc
    κ ^ 2 * E2 ^ (2 / 3 : ℝ) * ∫ p, ∑ i : Fin 3, ∑ j : Fin 3, (responseGrad g j p i) ^ 2 ∂μ ≤
        κ ^ 2 * E2 ^ (2 / 3 : ℝ) * E2 :=
      mul_le_mul_of_nonneg_left hgradE (by positivity)
    _ = κ ^ 2 * E2 ^ (5 / 3 : ℝ) := by
      rw [mul_assoc, show (5 / 3 : ℝ) = 2 / 3 + 1 by norm_num,
        Real.rpow_add' hE20 (by norm_num), Real.rpow_one]

/-- The absolute constant of the smooth-data `L⁴` estimate. -/
@[expose] def responseL4Constant : ℝ :=
  ((3 : ℝ) ^ (2 / 3 : ℝ) * gagliardoNirenbergSobolevConstant.toReal ^ 2) ^ (3 / 5 : ℝ) *
    criticalResponseConstant ^ (2 / 5 : ℝ)

theorem responseL4Constant_nonneg : 0 ≤ responseL4Constant := by
  have := criticalResponseConstant_nonneg
  unfold responseL4Constant
  positivity

/-- The `L⁴` estimate for the smooth forced heat response:
`∫∫ |Z|⁴ ≤ C (∫∫ |g|²) (∫∫ |g|^{5/2})^{4/5}` with an absolute constant `C`. -/
theorem response_L4_estimate {g : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ}
    (hg : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (g i j)) (hgc : ∀ i j, HasCompactSupport (g i j))
    (hgpos : ∀ i j, tsupport (g i j) ⊆ {p | 0 < p.2}) {τ : ℝ} (hτ : 0 ≤ τ) :
    ∫ p, (∑ i : Fin 3, (responseVec g p i) ^ 2) ^ 2
        ∂((volume : Measure Vec3).prod (volume.restrict (Ioc 0 τ))) ≤
      responseL4Constant *
        (∫ p, ∑ i : Fin 3, ∑ j : Fin 3, (g i j p) ^ 2
          ∂((volume : Measure Vec3).prod (volume.restrict (Ioc 0 τ)))) *
        (∫ p, (∑ i : Fin 3, ∑ j : Fin 3, (g i j p) ^ 2) ^ (5 / 4 : ℝ)
          ∂((volume : Measure Vec3).prod (volume.restrict (Ioc 0 τ)))) ^ (4 / 5 : ℝ) := by
  set μ := (volume : Measure Vec3).prod (volume.restrict (Ioc (0 : ℝ) τ))
  set E2 : ℝ := ∫ p, ∑ i : Fin 3, ∑ j : Fin 3, (g i j p) ^ 2 ∂μ with hE2
  set B : ℝ := ∫ p, (∑ i : Fin 3, ∑ j : Fin 3, (g i j p) ^ 2) ^ (5 / 4 : ℝ) ∂μ with hB
  set κ : ℝ := gagliardoNirenbergSobolevConstant.toReal
  have hE20 : 0 ≤ E2 := integral_nonneg fun p =>
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hB0 : 0 ≤ B := integral_nonneg fun p => Real.rpow_nonneg
    (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _) _
  obtain ⟨h103int, h103⟩ := response_tenThirds_le hg hgc hgpos hτ
  obtain ⟨h52int, _⟩ := response_rpow_five_le hg hgc hgpos hτ
  have h52 := (response_critical_estimate hg hgc hgpos hτ).1
  let q : Vec3 × ℝ → ℝ := fun p => ∑ i : Fin 3, (responseVec g p i) ^ 2
  have hq0 (p : Vec3 × ℝ) : 0 ≤ q p := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hU (k : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (causalHeatConv (vecTimeDiv g k)) :=
    causalHeatConv_contDiff (vecTimeDiv_contDiff hg k) (vecTimeDiv_hasCompactSupport hgc k)
  have hqc : Continuous q := continuous_finsetSum _ fun i _ => (hU i).continuous.pow 2
  have hq53 (p : Vec3 × ℝ) : q p ^ (5 / 3 : ℝ) ≤
      (3 : ℝ) ^ (2 / 3 : ℝ) * ∑ i : Fin 3, |responseVec g p i| ^ (10 / 3 : ℝ) := by
    have h := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg (s := Finset.univ)
      (f := fun i => (responseVec g p i) ^ 2) (p := (5 / 3 : ℝ)) (by norm_num)
      (fun i _ => sq_nonneg _)
    simp only [Finset.card_univ, Fintype.card_fin] at h
    have hterm (i : Fin 3) : ((responseVec g p i) ^ 2) ^ (5 / 3 : ℝ) =
        |responseVec g p i| ^ (10 / 3 : ℝ) := by
      rw [← sq_abs, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
      norm_num
    simp only [hterm] at h
    convert h using 2
    norm_num
  have hq53int : Integrable (fun p => q p ^ (5 / 3 : ℝ)) μ :=
    (h103int.const_mul _).mono' ((hqc.rpow_const fun _ => Or.inr (by norm_num)).aestronglyMeasurable)
      (Eventually.of_forall fun p => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hq0 p) _)]
        exact hq53 p)
  have hA10 : ∫ p, q p ^ (5 / 3 : ℝ) ∂μ ≤ (3 : ℝ) ^ (2 / 3 : ℝ) * (κ ^ 2 * E2 ^ (5 / 3 : ℝ)) := by
    calc
      ∫ p, q p ^ (5 / 3 : ℝ) ∂μ ≤
          ∫ p, (3 : ℝ) ^ (2 / 3 : ℝ) * ∑ i : Fin 3, |responseVec g p i| ^ (10 / 3 : ℝ) ∂μ :=
        integral_mono hq53int (h103int.const_mul _) hq53
      _ ≤ _ := by
        rw [integral_const_mul]
        exact mul_le_mul_of_nonneg_left h103 (by positivity)
  have hmem53 : MemLp q (ENNReal.ofReal (5 / 3)) μ := by
    rw [← integrable_norm_rpow_iff hqc.aestronglyMeasurable (by norm_num) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (by norm_num)]
    refine hq53int.congr (Eventually.of_forall fun p => ?_)
    simp only [Real.norm_eq_abs, abs_of_nonneg (hq0 p)]
  have hmem52 : MemLp q (ENNReal.ofReal (5 / 2)) μ := by
    rw [← integrable_norm_rpow_iff hqc.aestronglyMeasurable (by norm_num) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (by norm_num)]
    refine h52int.congr (Eventually.of_forall fun p => ?_)
    simp only [Real.norm_eq_abs, abs_of_nonneg (hq0 p)]
    rfl
  have hconj : (5 / 3 : ℝ).HolderConjugate (5 / 2) :=
    (Real.holderConjugate_iff_eq_conjExponent (by norm_num)).2 (by norm_num)
  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg hconj (Eventually.of_forall hq0)
    (Eventually.of_forall hq0) hmem53 hmem52
  have hA100 : 0 ≤ ∫ p, q p ^ (5 / 3 : ℝ) ∂μ :=
    integral_nonneg fun p => Real.rpow_nonneg (hq0 p) _
  have hA50 : 0 ≤ ∫ p, q p ^ (5 / 2 : ℝ) ∂μ :=
    integral_nonneg fun p => Real.rpow_nonneg (hq0 p) _
  have hf1 : (∫ p, q p ^ (5 / 3 : ℝ) ∂μ) ^ (1 / (5 / 3 : ℝ)) ≤
      ((3 : ℝ) ^ (2 / 3 : ℝ) * κ ^ 2) ^ (3 / 5 : ℝ) * E2 := by
    calc
      (∫ p, q p ^ (5 / 3 : ℝ) ∂μ) ^ (1 / (5 / 3 : ℝ)) ≤
          ((3 : ℝ) ^ (2 / 3 : ℝ) * (κ ^ 2 * E2 ^ (5 / 3 : ℝ))) ^ (3 / 5 : ℝ) := by
        rw [show (1 : ℝ) / (5 / 3) = 3 / 5 by norm_num]
        exact Real.rpow_le_rpow hA100 hA10 (by norm_num)
      _ = ((3 : ℝ) ^ (2 / 3 : ℝ) * κ ^ 2) ^ (3 / 5 : ℝ) * E2 := by
        rw [← mul_assoc, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hE20]
        norm_num
  have hf2 : (∫ p, q p ^ (5 / 2 : ℝ) ∂μ) ^ (1 / (5 / 2 : ℝ)) ≤
      criticalResponseConstant ^ (2 / 5 : ℝ) * B ^ (4 / 5 : ℝ) := by
    have hC := criticalResponseConstant_nonneg
    calc
      (∫ p, q p ^ (5 / 2 : ℝ) ∂μ) ^ (1 / (5 / 2 : ℝ)) ≤
          (criticalResponseConstant * B ^ 2) ^ (2 / 5 : ℝ) := by
        rw [show (1 : ℝ) / (5 / 2) = 2 / 5 by norm_num]
        exact Real.rpow_le_rpow hA50 h52 (by norm_num)
      _ = criticalResponseConstant ^ (2 / 5 : ℝ) * B ^ (4 / 5 : ℝ) := by
        rw [Real.mul_rpow hC (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hB0]
        norm_num
  have hsq : (fun p => (∑ i : Fin 3, (responseVec g p i) ^ 2) ^ 2) = fun p => q p * q p := by
    funext p
    simp only [q, sq]
  rw [hsq]
  refine hH.trans ?_
  calc
    _ ≤ (((3 : ℝ) ^ (2 / 3 : ℝ) * κ ^ 2) ^ (3 / 5 : ℝ) * E2) *
        (criticalResponseConstant ^ (2 / 5 : ℝ) * B ^ (4 / 5 : ℝ)) :=
      mul_le_mul hf1 hf2 (Real.rpow_nonneg hA50 _) (by positivity)
    _ = _ := by
      unfold responseL4Constant
      ring

end ESS

end
