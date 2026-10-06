/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.ForcedHeatEnergyIdentity

/-!
# The energy estimate for the smooth forced heat response

Testing the forced heat equation with the response itself gives, for every
`t₁ ≥ 0`,
`‖Z(t₁)‖₂² + ∫₀^{t₁} ‖∇Z‖₂² ≤ ∫₀^{t₁} ‖g‖₂²`,
the smooth-data form of `eq:pv-stokes-energy` in `lem:pv-stokes`.
-/

public section

open MeasureTheory Set Filter
open CKN.Foundation.Heat CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The quadratic entropy `½ |v|²`. -/
@[expose] def halfSq (v : Vec3) : ℝ := (1 / 2 : ℝ) * ∑ i : Fin 3, v i * v i

private theorem halfSq_contDiff : ContDiff ℝ 1 halfSq := by
  unfold halfSq
  fun_prop

private theorem halfSq_fderiv (v w : Vec3) :
    fderiv ℝ halfSq v w = ∑ i : Fin 3, v i * w i := by
  have hsq (i : Fin 3) : HasFDerivAt (fun u : Vec3 => u i * u i)
      (v i • ContinuousLinearMap.proj i + v i • ContinuousLinearMap.proj i) v :=
    (hasFDerivAt_apply (𝕜 := ℝ) i v).mul (hasFDerivAt_apply (𝕜 := ℝ) i v)
  have hsum : HasFDerivAt (fun u : Vec3 => ∑ i : Fin 3, u i * u i)
      (∑ i : Fin 3, (v i • ContinuousLinearMap.proj i + v i • ContinuousLinearMap.proj i)) v :=
    HasFDerivAt.fun_sum fun i _ => hsq i
  have hhalf := hsum.const_mul (1 / 2 : ℝ)
  rw [show halfSq = fun u : Vec3 => (1 / 2 : ℝ) * ∑ i : Fin 3, u i * u i from rfl,
    hhalf.fderiv]
  simp only [smul_apply, FunLike.coe_sum, Finset.sum_apply,
    add_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The response and its spatial gradient have space-time integrable squares on
each finite window, and the squared tensor is integrable there. -/
theorem response_sq_window_integrable {g : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ}
    (hg : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (g i j)) (hgc : ∀ i j, HasCompactSupport (g i j))
    (a b : ℝ) :
    Integrable (fun p : Vec3 × ℝ => ∑ i : Fin 3, ∑ j : Fin 3, (responseGrad g j p i) ^ 2)
      ((volume : Measure Vec3).prod (volume.restrict (Ioc a b))) ∧
    Integrable (fun p : Vec3 × ℝ => ∑ i : Fin 3, ∑ j : Fin 3, (g i j p) ^ 2)
      ((volume : Measure Vec3).prod (volume.restrict (Ioc a b))) ∧
    Integrable (fun p : Vec3 × ℝ => ∑ i : Fin 3, ∑ j : Fin 3,
        responseGrad g j p i * (responseGrad g j p i + g i j p))
      ((volume : Measure Vec3).prod (volume.restrict (Ioc a b))) := by
  obtain ⟨M, hM, hdec⟩ := vecTimeDiv_response_decay hg hgc
  have hU (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (causalHeatConv (vecTimeDiv g i)) :=
    causalHeatConv_contDiff (vecTimeDiv_contDiff hg i) (vecTimeDiv_hasCompactSupport hgc i)
  have hGr (i j : Fin 3) : Continuous (fun p => responseGrad g j p i) :=
    ((hU i).continuous_fderiv (by simp)).clm_apply continuous_const
  have hsqb {f : Vec3 × ℝ → ℝ} (hf : ∀ p, |f p| ≤ M / (1 + vec3EuclideanNorm p.1) ^ 3)
      (p : Vec3 × ℝ) : f p ^ 2 ≤ M ^ 2 / (1 + vec3EuclideanNorm p.1) ^ 6 := by
    have h := pow_le_pow_left₀ (abs_nonneg _) (hf p) 2
    rw [sq_abs, div_pow, ← pow_mul] at h
    exact h
  have hsumb {F : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ} {c : ℝ}
      (hF : ∀ i j p, |F i j p| ≤ c / (1 + vec3EuclideanNorm p.1) ^ 6) (p : Vec3 × ℝ) :
      |∑ i : Fin 3, ∑ j : Fin 3, F i j p| ≤ (9 * c) / (1 + vec3EuclideanNorm p.1) ^ 6 := by
    calc
      _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, |F i j p| :=
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, c / (1 + vec3EuclideanNorm p.1) ^ 6 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hF i j p
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring
  have hc1 : Continuous (fun p : Vec3 × ℝ => ∑ i : Fin 3, ∑ j : Fin 3,
      (responseGrad g j p i) ^ 2) :=
    continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => (hGr i j).pow 2
  have hc2 : Continuous (fun p : Vec3 × ℝ => ∑ i : Fin 3, ∑ j : Fin 3, (g i j p) ^ 2) :=
    continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      (hg i j).continuous.pow 2
  have hc3 : Continuous (fun p : Vec3 × ℝ => ∑ i : Fin 3, ∑ j : Fin 3,
      responseGrad g j p i * (responseGrad g j p i + g i j p)) :=
    continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      (hGr i j).mul ((hGr i j).add (hg i j).continuous)
  refine ⟨?_, ?_, ?_⟩
  · refine integrable_window_of_decay hc1 (by positivity)
      (fun x t _ => hsumb (c := M ^ 2) (F := fun i j p => (responseGrad g j p i) ^ 2)
        (fun i j p => ?_) (x, t))
    rw [abs_of_nonneg (sq_nonneg _)]
    exact hsqb (f := fun p => responseGrad g j p i) (fun p => (hdec i j j p).2.1) p
  · refine integrable_window_of_decay hc2 (by positivity)
      (fun x t _ => hsumb (c := M ^ 2) (F := fun i j p => (g i j p) ^ 2)
        (fun i j p => ?_) (x, t))
    rw [abs_of_nonneg (sq_nonneg _)]
    exact hsqb (f := fun p => g i j p) (fun p => (hdec i j j p).2.2.2.2.1) p
  · refine integrable_window_of_decay hc3 (by positivity)
      (fun x t _ => hsumb (c := M * (2 * M))
        (F := fun i j p => responseGrad g j p i * (responseGrad g j p i + g i j p))
        (fun i j p => ?_) (x, t))
    have hw : 0 < (1 + vec3EuclideanNorm p.1) ^ 3 := by
      have := vec3EuclideanNorm_nonneg p.1
      positivity
    have h1 := (hdec i j j p).2.1
    have h2 : |responseGrad g j p i + g i j p| ≤ 2 * M / (1 + vec3EuclideanNorm p.1) ^ 3 :=
      (abs_add_le _ _).trans (by
        have := (hdec i j j p).2.2.2.2.1
        rw [show 2 * M / (1 + vec3EuclideanNorm p.1) ^ 3 =
          M / (1 + vec3EuclideanNorm p.1) ^ 3 + M / (1 + vec3EuclideanNorm p.1) ^ 3 by ring]
        exact add_le_add h1 this)
    rw [abs_mul, show (1 + vec3EuclideanNorm p.1) ^ 6 =
      (1 + vec3EuclideanNorm p.1) ^ 3 * (1 + vec3EuclideanNorm p.1) ^ 3 by ring,
      ← div_mul_div_comm]
    exact mul_le_mul h1 h2 (abs_nonneg _) (div_nonneg hM hw.le)

/-- The energy estimate for the smooth forced heat response: for every `t₁ ≥ 0`,
`‖Z(t₁)‖₂² + ∫_{(0,t₁]} ‖∇Z‖₂² ≤ ∫_{(0,t₁]} ‖g‖₂²`. -/
theorem response_energy_le {g : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ}
    (hg : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (g i j)) (hgc : ∀ i j, HasCompactSupport (g i j))
    (hgpos : ∀ i j, tsupport (g i j) ⊆ {p | 0 < p.2}) {t₁ : ℝ} (ht₁ : 0 ≤ t₁) :
    (∫ x, ∑ i : Fin 3, (responseVec g (x, t₁) i) ^ 2) +
      ∫ p, ∑ i : Fin 3, ∑ j : Fin 3, (responseGrad g j p i) ^ 2
        ∂((volume : Measure Vec3).prod (volume.restrict (Ioc 0 t₁))) ≤
      ∫ p, ∑ i : Fin 3, ∑ j : Fin 3, (g i j p) ^ 2
        ∂((volume : Measure Vec3).prod (volume.restrict (Ioc 0 t₁))) := by
  have hT : ContDiff ℝ 1 (fun v : Vec3 => v) := contDiff_id
  have hid := response_entropy_identity hg hgc hgpos halfSq_contDiff hT halfSq_fderiv
    (by simp [halfSq]) rfl ht₁
  simp only [fderiv_fun_id, ContinuousLinearMap.id_apply] at hid
  obtain ⟨hA, hB, hAB⟩ := response_sq_window_integrable hg hgc 0 t₁
  set μ := (volume : Measure Vec3).prod (volume.restrict (Ioc (0 : ℝ) t₁))
  have hpoint (p : Vec3 × ℝ) :
      -(∑ i : Fin 3, ∑ j : Fin 3, responseGrad g j p i * (responseGrad g j p i + g i j p)) ≤
        (1 / 2 : ℝ) * (∑ i : Fin 3, ∑ j : Fin 3, (g i j p) ^ 2) -
          (1 / 2 : ℝ) * ∑ i : Fin 3, ∑ j : Fin 3, (responseGrad g j p i) ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro i _
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro j _
    nlinarith only [sq_nonneg (responseGrad g j p i + g i j p)]
  have hmono := integral_mono (μ := μ)
    (f := fun p => -(∑ i : Fin 3, ∑ j : Fin 3,
      responseGrad g j p i * (responseGrad g j p i + g i j p)))
    (g := fun p => (1 / 2 : ℝ) * (∑ i : Fin 3, ∑ j : Fin 3, (g i j p) ^ 2) -
      (1 / 2 : ℝ) * ∑ i : Fin 3, ∑ j : Fin 3, (responseGrad g j p i) ^ 2)
    hAB.neg ((hB.const_mul _).sub (hA.const_mul _)) hpoint
  rw [integral_neg, integral_sub (hB.const_mul _) (hA.const_mul _), integral_const_mul,
    integral_const_mul] at hmono
  have hhalf : ∫ x, halfSq (responseVec g (x, t₁)) =
      (1 / 2 : ℝ) * ∫ x, ∑ i : Fin 3, (responseVec g (x, t₁) i) ^ 2 := by
    rw [← integral_const_mul]
    congr 1
    funext x
    simp only [halfSq, sq]
  rw [hhalf] at hid
  linarith only [hid, hmono]

end ESS

end
