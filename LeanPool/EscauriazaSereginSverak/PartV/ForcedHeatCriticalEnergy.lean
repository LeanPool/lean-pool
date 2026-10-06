/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.ForcedHeatCriticalCore

/-!
# The critical energy inequality for the smooth forced heat response

For the regularized entropy `heatRegEnergy η` with gradient `heatRegTest η`,
the whole-space identity and the pointwise absorption of the forcing give

`∫ E_η(Z(t₁)) + ½ ∫₀^{t₁} ∑_j D_j ≤ ∫₀^{t₁} ∫ |Z| |g|²`,

the regularized form of the critical inequality in `lem:pv-stokes`.
-/

public section

open MeasureTheory Set Filter
open CKN.Foundation.Heat CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- A product of two quantities with `(1 + |x|)^{-3}` bounds has a
`(1 + |x|)^{-6}` bound. -/
theorem abs_mul_le_decay_six {x y A B : ℝ} {z : Vec3} (hA : 0 ≤ A)
    (hx : |x| ≤ A / (1 + vec3EuclideanNorm z) ^ 3)
    (hy : |y| ≤ B / (1 + vec3EuclideanNorm z) ^ 3) :
    |x * y| ≤ A * B / (1 + vec3EuclideanNorm z) ^ 6 := by
  have hw : 0 < (1 + vec3EuclideanNorm z) ^ 3 := by
    have := vec3EuclideanNorm_nonneg z
    positivity
  rw [abs_mul, show (1 + vec3EuclideanNorm z) ^ 6 =
    (1 + vec3EuclideanNorm z) ^ 3 * (1 + vec3EuclideanNorm z) ^ 3 by ring,
    ← div_mul_div_comm]
  exact mul_le_mul hx hy (abs_nonneg _) (div_nonneg hA hw.le)

/-- A double sum over `Fin 3` of quantities with a common `(1 + |x|)^{-6}`
bound. -/
theorem abs_double_sum_le_decay_six {F : Fin 3 → Fin 3 → ℝ} {C : ℝ} {z : Vec3}
    (hF : ∀ i j, |F i j| ≤ C / (1 + vec3EuclideanNorm z) ^ 6) :
    |∑ i : Fin 3, ∑ j : Fin 3, F i j| ≤ (9 * C) / (1 + vec3EuclideanNorm z) ^ 6 := by
  calc
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, |F i j| :=
      (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, C / (1 + vec3EuclideanNorm z) ^ 6 :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hF i j
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      ring

/-- The regularized entropy has the regularized critical test as its gradient. -/
theorem heatRegEnergy_fderiv_eq_sum {η : ℝ} (hη : 0 < η) (v w : Vec3) :
    fderiv ℝ (heatRegEnergy η) v w = ∑ i : Fin 3, heatRegTest η v i * w i := by
  rw [heatRegEnergy_fderiv hη, heatRegTest_pairing]

/-- The regularized entropy vanishes at the origin. -/
theorem heatRegEnergy_zero {η : ℝ} (hη : 0 < η) : heatRegEnergy η 0 = 0 := by
  have hroot : heatRegSq η 0 ^ (1 / 2 : ℝ) = η := by
    rw [← Real.sqrt_eq_rpow]
    have hq : heatRegSq η 0 = η ^ 2 := by simp [heatRegSq]
    rw [hq, Real.sqrt_sq hη.le]
  rw [heatRegEnergy_factor hη, hroot, sub_self]
  ring

/-- The regularized critical test vanishes at the origin. -/
theorem heatRegTest_zero (η : ℝ) : heatRegTest η 0 = 0 := by
  funext i
  simp [heatRegTest]

/-- The three integrands of the regularized critical inequality are integrable
on every finite time window. -/
theorem response_critical_integrable {g : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ}
    (hg : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (g i j)) (hgc : ∀ i j, HasCompactSupport (g i j))
    {η : ℝ} (hη : 0 < η) (a b : ℝ) :
    Integrable (fun p => ∑ i : Fin 3, ∑ j : Fin 3,
      fderiv ℝ (heatRegTest η) (responseVec g p) (responseGrad g j p) i *
        (responseGrad g j p i + g i j p))
      ((volume : Measure Vec3).prod (volume.restrict (Ioc a b))) ∧
    Integrable (fun p => ∑ j : Fin 3, ∑ i : Fin 3,
      fderiv ℝ (heatRegTest η) (responseVec g p) (responseGrad g j p) i *
        responseGrad g j p i)
      ((volume : Measure Vec3).prod (volume.restrict (Ioc a b))) ∧
    Integrable (fun p => vec3EuclideanNorm (responseVec g p) *
      ∑ i : Fin 3, ∑ j : Fin 3, (g i j p) ^ 2)
      ((volume : Measure Vec3).prod (volume.restrict (Ioc a b))) := by
  have hT : ContDiff ℝ 1 (heatRegTest η) := (heatRegTest_contDiff hη).of_le (by simp)
  set μ := (volume : Measure Vec3).prod (volume.restrict (Ioc a b))
  obtain ⟨A, hA, hat⟩ := response_atom_bounds hg hgc hT (heatRegTest_zero η)
  obtain ⟨hZc, hGc, hDc⟩ := response_continuity hg hgc hT
  let B : Fin 3 → Vec3 × ℝ → Vec3 := fun j p =>
    fderiv ℝ (heatRegTest η) (responseVec g p) (responseGrad g j p)
  have hBc (j : Fin 3) (i : Fin 3) : Continuous (fun p => B j p i) :=
    (continuous_apply i).comp (hDc j)
  have hac (j : Fin 3) (i : Fin 3) : Continuous (fun p => responseGrad g j p i) :=
    (continuous_apply i).comp (hGc j)
  have hF1 : Integrable (fun p => ∑ i : Fin 3, ∑ j : Fin 3,
      B j p i * (responseGrad g j p i + g i j p)) μ := by
    refine integrable_window_of_decay (continuous_finsetSum _ fun i _ =>
      continuous_finsetSum _ fun j _ => (hBc j i).mul ((hac j i).add (hg i j).continuous))
      (C := 9 * (A * (2 * A))) (by positivity) fun x t _ => ?_
    refine abs_double_sum_le_decay_six fun i j => abs_mul_le_decay_six hA
      (hat (x, t) i j).2.2.2.2 ?_
    refine (abs_add_le _ _).trans ?_
    rw [show 2 * A / (1 + vec3EuclideanNorm x) ^ 3 =
      A / (1 + vec3EuclideanNorm x) ^ 3 + A / (1 + vec3EuclideanNorm x) ^ 3 by ring]
    exact add_le_add (hat (x, t) i j).2.1 (hat (x, t) i j).2.2.1
  have hF2 : Integrable (fun p => ∑ j : Fin 3, ∑ i : Fin 3,
      B j p i * responseGrad g j p i) μ := by
    refine integrable_window_of_decay (continuous_finsetSum _ fun j _ =>
      continuous_finsetSum _ fun i _ => (hBc j i).mul (hac j i))
      (C := 9 * (A * A)) (by positivity) fun x t _ => ?_
    exact abs_double_sum_le_decay_six fun j i => abs_mul_le_decay_six hA
      (hat (x, t) i j).2.2.2.2 (hat (x, t) i j).2.1
  have hF3 : Integrable (fun p => vec3EuclideanNorm (responseVec g p) *
      ∑ i : Fin 3, ∑ j : Fin 3, (g i j p) ^ 2) μ := by
    refine integrable_window_of_decay ((continuous_vec3EuclideanNorm.comp hZc).mul
      (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
        (hg i j).continuous.pow 2)) (C := 3 * A * (9 * (A * A))) (by positivity)
      fun x t _ => ?_
    have hw1 : 1 ≤ (1 + vec3EuclideanNorm x) ^ 3 := one_le_pow₀ (by
      have := vec3EuclideanNorm_nonneg x
      linarith only [this])
    have hn : |vec3EuclideanNorm (responseVec g (x, t))| ≤
        3 * A / (1 + vec3EuclideanNorm x) ^ 3 := by
      rw [abs_of_nonneg (vec3EuclideanNorm_nonneg _)]
      refine (vec3EuclideanNorm_le_sum_abs _).trans ?_
      calc
        ∑ i : Fin 3, |responseVec g (x, t) i| ≤
            ∑ _i : Fin 3, A / (1 + vec3EuclideanNorm x) ^ 3 :=
          Finset.sum_le_sum fun i _ => (hat (x, t) i i).1
        _ = 3 * A / (1 + vec3EuclideanNorm x) ^ 3 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring
    have hsq : |∑ i : Fin 3, ∑ j : Fin 3, (g i j (x, t)) ^ 2| ≤
        9 * (A * A) / (1 + vec3EuclideanNorm x) ^ 3 := by
      refine (abs_double_sum_le_decay_six (C := A * A) (z := x) fun i j => ?_).trans ?_
      · rw [sq]
        exact abs_mul_le_decay_six hA (hat (x, t) i j).2.2.1 (hat (x, t) i j).2.2.1
      · apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        rw [show (1 + vec3EuclideanNorm x) ^ 6 =
          (1 + vec3EuclideanNorm x) ^ 3 * (1 + vec3EuclideanNorm x) ^ 3 by ring]
        exact le_mul_of_one_le_left (by positivity) hw1
    exact abs_mul_le_decay_six (by positivity) hn hsq
  exact ⟨hF1, hF2, hF3⟩

/-- The critical energy inequality for the forced heat response, regularized
at level `η > 0`. -/
theorem response_critical_energy_le {g : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ}
    (hg : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (g i j)) (hgc : ∀ i j, HasCompactSupport (g i j))
    (hgpos : ∀ i j, tsupport (g i j) ⊆ {p | 0 < p.2}) {η : ℝ} (hη : 0 < η)
    {t₁ : ℝ} (ht₁ : 0 ≤ t₁) :
    (∫ x, heatRegEnergy η (responseVec g (x, t₁))) +
      (1 / 2 : ℝ) * ∫ p, ∑ j : Fin 3, ∑ i : Fin 3,
        fderiv ℝ (heatRegTest η) (responseVec g p) (responseGrad g j p) i *
          responseGrad g j p i
        ∂((volume : Measure Vec3).prod (volume.restrict (Ioc 0 t₁))) ≤
      ∫ p, vec3EuclideanNorm (responseVec g p) * ∑ i : Fin 3, ∑ j : Fin 3, (g i j p) ^ 2
        ∂((volume : Measure Vec3).prod (volume.restrict (Ioc 0 t₁))) := by
  have hT : ContDiff ℝ 1 (heatRegTest η) := (heatRegTest_contDiff hη).of_le (by simp)
  have hΦ : ContDiff ℝ 1 (heatRegEnergy η) := (heatRegEnergy_contDiff hη).of_le (by simp)
  have hid := response_entropy_identity hg hgc hgpos hΦ hT (heatRegEnergy_fderiv_eq_sum hη)
    (heatRegEnergy_zero hη) (heatRegTest_zero η) ht₁
  set μ := (volume : Measure Vec3).prod (volume.restrict (Ioc (0 : ℝ) t₁))
  obtain ⟨hF1, hF2, hF3⟩ := response_critical_integrable hg hgc hη 0 t₁
  let B : Fin 3 → Vec3 × ℝ → Vec3 := fun j p =>
    fderiv ℝ (heatRegTest η) (responseVec g p) (responseGrad g j p)
  -- pointwise absorption
  have hpoint (p : Vec3 × ℝ) :
      -(∑ i : Fin 3, ∑ j : Fin 3, B j p i * (responseGrad g j p i + g i j p)) ≤
        -(1 / 2 : ℝ) * (∑ j : Fin 3, ∑ i : Fin 3, B j p i * responseGrad g j p i) +
          vec3EuclideanNorm (responseVec g p) * ∑ i : Fin 3, ∑ j : Fin 3, (g i j p) ^ 2 := by
    rw [Finset.sum_comm (f := fun i j => B j p i * (responseGrad g j p i + g i j p)),
      Finset.sum_comm (f := fun i j => (g i j p) ^ 2), Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j _
    exact heatRegTest_forcing_absorb hη (responseVec g p) (responseGrad g j p)
      (fun i => g i j p)
  have hmono := integral_mono (μ := μ)
    (f := fun p => -(∑ i : Fin 3, ∑ j : Fin 3, B j p i * (responseGrad g j p i + g i j p)))
    (g := fun p => -(1 / 2 : ℝ) * (∑ j : Fin 3, ∑ i : Fin 3, B j p i * responseGrad g j p i) +
          vec3EuclideanNorm (responseVec g p) * ∑ i : Fin 3, ∑ j : Fin 3, (g i j p) ^ 2)
    hF1.neg ((hF2.const_mul _).add hF3) hpoint
  rw [integral_neg, integral_add (hF2.const_mul _) hF3, integral_const_mul] at hmono
  change ∫ x, heatRegEnergy η (responseVec g (x, t₁)) =
    -∫ p, ∑ i : Fin 3, ∑ j : Fin 3, B j p i * (responseGrad g j p i + g i j p) ∂μ at hid
  change (∫ x, heatRegEnergy η (responseVec g (x, t₁))) +
      (1 / 2 : ℝ) * ∫ p, ∑ j : Fin 3, ∑ i : Fin 3, B j p i * responseGrad g j p i ∂μ ≤ _
  linarith only [hid, hmono]

end ESS

end
