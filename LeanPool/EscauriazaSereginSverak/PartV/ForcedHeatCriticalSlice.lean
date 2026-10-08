/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.ForcedHeatCriticalGN

/-!
# Slice estimates for the regularized critical test

At each time the Gagliardo–Nirenberg inequality applied to the regularized
critical profile `heatRegG η (Z)` bounds its `L^{10/3}` norm by the regularized
entropy and the entropy dissipation; over a time window the regularized
critical inequality bounds both by `Y = ∫∫ |Z| |g|²`. These are the two
inputs of the critical estimate in `lem:pv-stokes`.
-/

public section

open MeasureTheory Set Filter
open scoped Topology
open CKN CKN.Foundation.Heat CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- A continuous function on Vec3 bounded by `C (1 + |x|)^{-6}` is integrable. -/
theorem integrable_of_abs_le_decay_six' {C : ℝ} (hC : 0 ≤ C) {f : Vec3 → ℝ}
    (hf : Continuous f) (hb : ∀ x, |f x| ≤ C / (1 + vec3EuclideanNorm x) ^ 6) :
    Integrable f :=
  (heat_decay_six_integrable C hC).mono' hf.aestronglyMeasurable
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hb x)

/-- The entropy dissipation of the regularized critical test dominates the
weighted squared gradient. -/
theorem heatRegTest_dissipation_ge {η : ℝ} (hη : 0 < η) (v a : Vec3) :
    (heatRegSq η v ^ (1 / 2 : ℝ) - η) * ∑ i : Fin 3, a i ^ 2 ≤
      ∑ i : Fin 3, fderiv ℝ (heatRegTest η) v a i * a i := by
  have hρ0 : 0 ≤ heatRegSq η v ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_nonneg (heatRegSq_pos hη v).le _
  have hsum : ∑ i : Fin 3, fderiv ℝ (heatRegTest η) v a i * a i =
      (heatRegSq η v ^ (1 / 2 : ℝ) - η) * ∑ i : Fin 3, a i ^ 2 +
        heatRegSq η v ^ (-(1 / 2 : ℝ)) * heatRegDot v a * heatRegDot v a := by
    simp only [heatRegTest_fderiv_apply_component hη, heatRegDot]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsum, mul_assoc]
  exact le_add_of_nonneg_right (mul_nonneg hρ0 (mul_self_nonneg _))

/-- The squared response `q = ∑ Z_i²` has a `(1 + |x|)^{-6}` bound, uniformly in
time. -/
theorem response_sq_decay {g : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ}
    (hg : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (g i j)) (hgc : ∀ i j, HasCompactSupport (g i j)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ p : Vec3 × ℝ,
      vec3EuclideanNorm (responseVec g p) ≤ M ∧
      ∑ i : Fin 3, (responseVec g p i) ^ 2 ≤ M / (1 + vec3EuclideanNorm p.1) ^ 6 := by
  obtain ⟨M, hM, hdec⟩ := vecTimeDiv_response_decay hg hgc
  refine ⟨3 * M + 3 * M ^ 2, by positivity, fun p => ?_⟩
  set w : ℝ := (1 + vec3EuclideanNorm p.1) ^ 3
  have hw : 1 ≤ w := one_le_pow₀ (by
    have := vec3EuclideanNorm_nonneg p.1
    linarith only [this])
  have hwpos : 0 < w := lt_of_lt_of_le zero_lt_one hw
  have hcomp (i : Fin 3) : |responseVec g p i| ≤ M / w := (hdec i i i p).1
  constructor
  · refine (vec3EuclideanNorm_le_sum_abs _).trans ?_
    calc
      ∑ i : Fin 3, |responseVec g p i| ≤ ∑ _i : Fin 3, M := Finset.sum_le_sum fun i _ =>
        (hcomp i).trans (div_le_self hM hw)
      _ = 3 * M := by simp
      _ ≤ 3 * M + 3 * M ^ 2 := le_add_of_nonneg_right (by positivity)
  · rw [show (1 + vec3EuclideanNorm p.1) ^ 6 = w * w by simp only [w]; ring]
    calc
      ∑ i : Fin 3, (responseVec g p i) ^ 2 ≤ ∑ _i : Fin 3, M ^ 2 / (w * w) := by
        apply Finset.sum_le_sum
        intro i _
        have h := pow_le_pow_left₀ (abs_nonneg _) (hcomp i) 2
        rw [sq_abs, div_pow] at h
        simpa [sq] using h
      _ = 3 * M ^ 2 / (w * w) := by simp; ring
      _ ≤ (3 * M + 3 * M ^ 2) / (w * w) :=
        div_le_div_of_nonneg_right (le_add_of_nonneg_left (by positivity)) (by positivity)

/-- Over a time window the regularized entropy at every time and the
dissipation are bounded by `Y = ∫∫ |Z| |g|²`. -/
theorem response_critical_window_bounds {g : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ}
    (hg : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (g i j)) (hgc : ∀ i j, HasCompactSupport (g i j))
    (hgpos : ∀ i j, tsupport (g i j) ⊆ {p | 0 < p.2}) {η : ℝ} (hη : 0 < η)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    (∀ t ∈ Icc 0 τ, ∫ x, heatRegEnergy η (responseVec g (x, t)) ≤
      ∫ p, vec3EuclideanNorm (responseVec g p) * ∑ i : Fin 3, ∑ j : Fin 3, (g i j p) ^ 2
        ∂((volume : Measure Vec3).prod (volume.restrict (Ioc 0 τ)))) ∧
    ∫ p, ∑ j : Fin 3, ∑ i : Fin 3,
        fderiv ℝ (heatRegTest η) (responseVec g p) (responseGrad g j p) i *
          responseGrad g j p i
        ∂((volume : Measure Vec3).prod (volume.restrict (Ioc 0 τ))) ≤
      2 * ∫ p, vec3EuclideanNorm (responseVec g p) * ∑ i : Fin 3, ∑ j : Fin 3, (g i j p) ^ 2
        ∂((volume : Measure Vec3).prod (volume.restrict (Ioc 0 τ))) := by
  obtain ⟨_, _, hF3⟩ := response_critical_integrable hg hgc hη 0 τ
  have hF3nonneg (p : Vec3 × ℝ) : 0 ≤ vec3EuclideanNorm (responseVec g p) *
      ∑ i : Fin 3, ∑ j : Fin 3, (g i j p) ^ 2 :=
    mul_nonneg (vec3EuclideanNorm_nonneg _)
      (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)
  have hF2nonneg (p : Vec3 × ℝ) : 0 ≤ ∑ j : Fin 3, ∑ i : Fin 3,
      fderiv ℝ (heatRegTest η) (responseVec g p) (responseGrad g j p) i *
        responseGrad g j p i :=
    Finset.sum_nonneg fun j _ => (mul_nonneg (sub_nonneg.mpr (heatReg_root_ge_eta hη _))
      (Finset.sum_nonneg fun i _ => sq_nonneg _)).trans
      (heatRegTest_dissipation_ge hη _ _)
  have hE0 (t : ℝ) : 0 ≤ ∫ x, heatRegEnergy η (responseVec g (x, t)) :=
    integral_nonneg fun x => heatRegEnergy_nonneg hη _
  constructor
  · intro t ht
    have h := response_critical_energy_le hg hgc hgpos hη ht.1
    have hD : 0 ≤ ∫ p, ∑ j : Fin 3, ∑ i : Fin 3,
        fderiv ℝ (heatRegTest η) (responseVec g p) (responseGrad g j p) i *
          responseGrad g j p i ∂((volume : Measure Vec3).prod (volume.restrict (Ioc 0 t))) :=
      integral_nonneg hF2nonneg
    have hmono := window_integral_mono ht.2 hF3 hF3nonneg
    linarith only [h, hD, hmono]
  · have h := response_critical_energy_le hg hgc hgpos hη hτ
    linarith only [h, hE0 τ]

/-- At each time, the Gagliardo–Nirenberg inequality for the regularized
critical profile: its `L^{10/3}` norm is controlled by the regularized entropy
and the entropy dissipation. -/
theorem response_critical_slice_gn {g : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ}
    (hg : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (g i j)) (hgc : ∀ i j, HasCompactSupport (g i j))
    {η : ℝ} (hη : 0 < η) (t : ℝ) :
    ∫ x, |heatRegG η (responseVec g (x, t))| ^ (10 / 3 : ℝ) ≤
      gagliardoNirenbergSobolevConstant.toReal ^ 2 *
        (27 * ∫ x, heatRegEnergy η (responseVec g (x, t))) ^ (2 / 3 : ℝ) *
        ((9 / 2 : ℝ) * ∫ x, ∑ j : Fin 3, ∑ i : Fin 3,
          fderiv ℝ (heatRegTest η) (responseVec g (x, t)) (responseGrad g j (x, t)) i *
            responseGrad g j (x, t) i) := by
  let U : Fin 3 → Vec3 × ℝ → ℝ := fun k => causalHeatConv (vecTimeDiv g k)
  have hU (k : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (U k) :=
    causalHeatConv_contDiff (vecTimeDiv_contDiff hg k) (vecTimeDiv_hasCompactSupport hgc k)
  have hsl : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec3 => ((y, t) : Vec3 × ℝ)) :=
    contDiff_id.prodMk contDiff_const
  have hZs : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec3 => responseVec g (y, t)) :=
    contDiff_pi.2 fun k => (hU k).comp hsl
  let f : Vec3 → ℝ := fun x => heatRegG η (responseVec g (x, t))
  have hf : ContDiff ℝ 1 f := ((heatRegG_contDiff hη).comp hZs).of_le (by simp)
  obtain ⟨M, hM, hq⟩ := response_sq_decay hg hgc
  have hT : ContDiff ℝ 1 (heatRegTest η) := (heatRegTest_contDiff hη).of_le (by simp)
  obtain ⟨A, hA, hat⟩ := response_atom_bounds hg hgc hT (heatRegTest_zero η)
  obtain ⟨hZc, hGc, hDc⟩ := response_continuity hg hgc hT
  have hsc : Continuous (fun x : Vec3 => ((x, t) : Vec3 × ℝ)) :=
    continuous_id.prodMk continuous_const
  set q : Vec3 → ℝ := fun x => ∑ i : Fin 3, (responseVec g (x, t) i) ^ 2 with hqdef
  have hqc : Continuous q := continuous_finsetSum _ fun i _ =>
    ((continuous_apply i).comp (hZc.comp hsc)).pow 2
  have hq0 (x : Vec3) : 0 ≤ q x := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hqint : Integrable q := integrable_of_abs_le_decay_six' hM hqc fun x => by
    rw [abs_of_nonneg (hq0 x)]
    exact (hq (x, t)).2
  set c : ℝ := (3 * η + 2 * M) / 6 with hc
  have hc0 : 0 ≤ c := by positivity
  have hEle (x : Vec3) : heatRegEnergy η (responseVec g (x, t)) ≤ c * q x :=
    heatRegEnergy_le_mul_sum_sq hη hM _ (hq (x, t)).1
  have hEc : Continuous (fun x => heatRegEnergy η (responseVec g (x, t))) :=
    (heatRegEnergy_contDiff hη).continuous.comp (hZc.comp hsc)
  have hEint : Integrable (fun x => heatRegEnergy η (responseVec g (x, t))) :=
    (hqint.const_mul c).mono' hEc.aestronglyMeasurable (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (heatRegEnergy_nonneg hη _)]
      exact hEle x)
  -- the dissipation slice
  let D : Fin 3 → Vec3 → ℝ := fun j x => ∑ i : Fin 3,
    fderiv ℝ (heatRegTest η) (responseVec g (x, t)) (responseGrad g j (x, t)) i *
      responseGrad g j (x, t) i
  have hDcont (j : Fin 3) : Continuous (D j) := continuous_finsetSum _ fun i _ =>
    (((continuous_apply i).comp (hDc j)).comp hsc).mul
      (((continuous_apply i).comp (hGc j)).comp hsc)
  have hDint (j : Fin 3) : Integrable (D j) :=
    integrable_of_abs_le_decay_six' (C := 3 * (A * A)) (by positivity) (hDcont j) fun x => by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc
        ∑ i : Fin 3, |fderiv ℝ (heatRegTest η) (responseVec g (x, t))
            (responseGrad g j (x, t)) i * responseGrad g j (x, t) i| ≤
            ∑ _i : Fin 3, A * A / (1 + vec3EuclideanNorm x) ^ 6 :=
          Finset.sum_le_sum fun i _ =>
            abs_mul_le_decay_six hA (hat (x, t) i j).2.2.2.2 (hat (x, t) i j).2.1
        _ = 3 * (A * A) / (1 + vec3EuclideanNorm x) ^ 6 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring
  have hD0 (j : Fin 3) (x : Vec3) : 0 ≤ D j x :=
    (mul_nonneg (sub_nonneg.mpr (heatReg_root_ge_eta hη _))
      (Finset.sum_nonneg fun i _ => sq_nonneg _)).trans (heatRegTest_dissipation_ge hη _ _)
  -- derivative of the profile
  have hDf (j : Fin 3) (x : Vec3) : fderiv ℝ f x (CKN.basisVec j) =
      fderiv ℝ (heatRegG η) (responseVec g (x, t)) (responseGrad g j (x, t)) :=
    fderiv_scalar_comp_slice_apply ((heatRegG_contDiff hη).differentiable (by simp))
      (fun k => (hU k).differentiable (by simp)) x t (CKN.basisVec j)
  have hDfsq (j : Fin 3) (x : Vec3) :
      (fderiv ℝ f x (CKN.basisVec j)) ^ 2 ≤ (9 / 2 : ℝ) * D j x := by
    rw [hDf]
    refine (heatReg_gradient_bound hη _ _).trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (heatRegTest_dissipation_ge hη _ _) (by norm_num)
  have hDfc (j : Fin 3) : Continuous (fun x => fderiv ℝ f x (CKN.basisVec j)) :=
    (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hDfint (j : Fin 3) : Integrable (fun x => (fderiv ℝ f x (CKN.basisVec j)) ^ 2) :=
    ((hDint j).const_mul (9 / 2 : ℝ)).mono' ((hDfc j).pow 2).aestronglyMeasurable
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact hDfsq j x)
  -- the profile and its powers
  have hfsq (x : Vec3) : f x ^ 2 ≤ 27 * heatRegEnergy η (responseVec g (x, t)) :=
    heatRegG_sq_le_energy hη _
  have hf2int : Integrable (fun x => f x ^ 2) :=
    (hEint.const_mul 27).mono' (hf.continuous.pow 2).aestronglyMeasurable
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact hfsq x)
  have hf103 (x : Vec3) : |f x| ^ (10 / 3 : ℝ) ≤ (M ^ 2) ^ (3 / 2 : ℝ) * q x := by
    obtain ⟨hG0, hGle⟩ := heatRegG_nonneg_le_rpow hη (responseVec g (x, t))
    have hqM : q x ≤ M ^ 2 := by
      have hn := (hq (x, t)).1
      have hsq := vec3EuclideanNorm_sq (responseVec g (x, t))
      nlinarith only [hn, hsq, vec3EuclideanNorm_nonneg (responseVec g (x, t))]
    calc
      |f x| ^ (10 / 3 : ℝ) ≤ (q x ^ (3 / 4 : ℝ)) ^ (10 / 3 : ℝ) := by
        rw [abs_of_nonneg hG0]
        exact Real.rpow_le_rpow hG0 hGle (by norm_num)
      _ = q x ^ (1 : ℝ) * q x ^ (3 / 2 : ℝ) := by
        rw [← Real.rpow_mul (hq0 x), ← Real.rpow_add' (hq0 x) (by norm_num)]
        norm_num
      _ ≤ q x * (M ^ 2) ^ (3 / 2 : ℝ) := by
        rw [Real.rpow_one]
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (hq0 x) hqM (by norm_num)) (hq0 x)
      _ = (M ^ 2) ^ (3 / 2 : ℝ) * q x := by ring
  have hf103int : Integrable (fun x => |f x| ^ (10 / 3 : ℝ)) :=
    (hqint.const_mul _).mono'
      ((hf.continuous.abs.rpow_const fun _ => Or.inr (by norm_num)).aestronglyMeasurable)
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact hf103 x)
  have hGN := integral_rpow_tenThirds_le hf hf2int hDfint hf103int
  refine hGN.trans ?_
  have hint2 : ∫ x, f x ^ 2 ≤ 27 * ∫ x, heatRegEnergy η (responseVec g (x, t)) := by
    rw [← integral_const_mul]
    exact integral_mono hf2int (hEint.const_mul 27) hfsq
  have hintD : ∫ x, ∑ j : Fin 3, (fderiv ℝ f x (CKN.basisVec j)) ^ 2 ≤
      (9 / 2 : ℝ) * ∫ x, ∑ j : Fin 3, D j x := by
    rw [← integral_const_mul]
    refine integral_mono (integrable_finsetSum _ fun j _ => hDfint j)
      ((integrable_finsetSum _ fun j _ => hDint j).const_mul _) fun x => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => hDfsq j x
  have hf20 : 0 ≤ ∫ x, f x ^ 2 := integral_nonneg fun x => sq_nonneg _
  have hDf0 : 0 ≤ ∫ x, ∑ j : Fin 3, (fderiv ℝ f x (CKN.basisVec j)) ^ 2 :=
    integral_nonneg fun x => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hE0 : 0 ≤ 27 * ∫ x, heatRegEnergy η (responseVec g (x, t)) :=
    mul_nonneg (by norm_num) (integral_nonneg fun x => heatRegEnergy_nonneg hη _)
  exact mul_le_mul (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hf20 hint2 (by norm_num))
    (by positivity)) hintD hDf0 (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hE0 _))

end ESS

end
