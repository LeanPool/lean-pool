/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.LocalSobolevCalculus
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingSobolevEmbedding

/-!
# Uniform limits of smooth functions and their ordered derivatives

If smooth functions on `ℝ³` converge uniformly together with all ordered
derivatives up to order `k`, the limit is `C^k` and its ordered derivatives are
the limits (`lem:lps-Bochner-joint-smooth`).
-/

public section

open MeasureTheory Set Filter Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The first-order derivative along `j` of a `C¹` function is the value of its
Fréchet derivative on the `j`th basis vector. -/
theorem lps_spatialDeriv_eq_of_hasFDerivAt {f : Vec3 → ℝ} {f' : Vec3 → Vec3 →L[ℝ] ℝ}
    (h : ∀ x, HasFDerivAt f (f' x) x) (j : Fin 3) :
    spatialDeriv f j = fun x => f' x (basisVec j) := by
  funext x
  simp only [spatialDeriv, (h x).fderiv]

/-- Uniform limits of smooth functions whose ordered derivatives up to order `k`
converge uniformly are `C^k`, with the limit of the derivatives as derivatives
(`lem:lps-Bochner-joint-smooth`). -/
theorem lps_uniform_limit_contDiff (k : ℕ) :
    ∀ (g : ℕ → Vec3 → ℝ), (∀ n, ContDiff ℝ (⊤ : ℕ∞) (g n)) →
      (∀ α : List (Fin 3), α.length ≤ k →
        ∃ h : Vec3 → ℝ, TendstoUniformly (fun n => wordDeriv α (g n)) h atTop) →
      ∃ f : Vec3 → ℝ, ContDiff ℝ k f ∧ ∀ α : List (Fin 3), α.length ≤ k →
        TendstoUniformly (fun n => wordDeriv α (g n)) (wordDeriv α f) atTop := by
  induction k with
  | zero =>
      intro g hg hconv
      obtain ⟨f, hf⟩ := hconv [] (by simp)
      refine ⟨f, ?_, ?_⟩
      · refine contDiff_zero.mpr ?_
        exact hf.continuous (Eventually.of_forall fun n => (hg n).continuous).frequently
      · intro α hα
        have : α = [] := List.length_eq_zero_iff.mp (by omega)
        subst this
        simpa only [wordDeriv] using hf
  | succ k ih =>
      intro g hg hconv
      -- the derivative sequences satisfy the hypothesis at order `k`
      have hdg (j : Fin 3) (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv (g n) j) :=
        contDiff_spatialDeriv_smooth (hg n) j
      have hdconv (j : Fin 3) (α : List (Fin 3)) (hα : α.length ≤ k) :
          ∃ h : Vec3 → ℝ,
            TendstoUniformly (fun n => wordDeriv α (spatialDeriv (g n) j)) h atTop := by
        obtain ⟨h, hh⟩ := hconv (j :: α) (by simp only [List.length_cons]; omega)
        exact ⟨h, by simpa only [wordDeriv] using hh⟩
      choose fj hfjC hfjT using fun j => ih (fun n => spatialDeriv (g n) j) (hdg j) (hdconv j)
      obtain ⟨f, hf⟩ := hconv [] (by simp)
      simp only [wordDeriv] at hf
      let g' : Vec3 → Vec3 →L[ℝ] ℝ := fun x =>
        ∑ j : Fin 3, fj j x • (ContinuousLinearMap.proj j : Vec3 →L[ℝ] ℝ)
      have hg'C : ContDiff ℝ k g' := by
        refine ContDiff.sum fun j _ => ?_
        exact (hfjC j).smul contDiff_const
      have hfder (n : ℕ) (x : Vec3) :
          fderiv ℝ (g n) x = ∑ j : Fin 3, spatialDeriv (g n) j x •
            (ContinuousLinearMap.proj j : Vec3 →L[ℝ] ℝ) := by
        ext v
        simp only [sum_apply, smul_apply,
          ContinuousLinearMap.proj_apply, smul_eq_mul]
        have hv : v = ∑ j : Fin 3, v j • basisVec j := by
          simpa using (CKN.sum_smul_basisVec v).symm
        conv_lhs => rw [hv]
        rw [map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_smul, smul_eq_mul, mul_comm]
        rfl
      have hunif : TendstoUniformly (fun n x => fderiv ℝ (g n) x) g' atTop := by
        rw [Metric.tendstoUniformly_iff]
        intro ε hε
        have h3 : ∀ j : Fin 3, ∀ᶠ n in atTop, ∀ x, dist (fj j x)
            (spatialDeriv (g n) j x) < ε / 4 := by
          intro j
          have := (Metric.tendstoUniformly_iff.mp (by simpa only [wordDeriv] using
            (hfjT j [] (by simp)))) (ε / 4) (by positivity)
          filter_upwards [this] with n hn x
          exact hn x
        have hall : ∀ᶠ n in atTop, ∀ j : Fin 3, ∀ x, dist (fj j x)
            (spatialDeriv (g n) j x) < ε / 4 := by
          rw [eventually_all]
          exact h3
        filter_upwards [hall] with n hn x
        rw [dist_comm, dist_eq_norm, hfder n x]
        change ‖(∑ j : Fin 3, spatialDeriv (g n) j x •
            (ContinuousLinearMap.proj j : Vec3 →L[ℝ] ℝ)) - g' x‖ < ε
        have hsub : (∑ j : Fin 3, spatialDeriv (g n) j x •
            (ContinuousLinearMap.proj j : Vec3 →L[ℝ] ℝ)) - g' x =
            ∑ j : Fin 3, (spatialDeriv (g n) j x - fj j x) •
              (ContinuousLinearMap.proj j : Vec3 →L[ℝ] ℝ) := by
          simp only [g']
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun j _ => (sub_smul _ _ _).symm
        rw [hsub]
        calc ‖∑ j : Fin 3, (spatialDeriv (g n) j x - fj j x) •
              (ContinuousLinearMap.proj j : Vec3 →L[ℝ] ℝ)‖
            ≤ ∑ j : Fin 3, ‖(spatialDeriv (g n) j x - fj j x) •
              (ContinuousLinearMap.proj j : Vec3 →L[ℝ] ℝ)‖ := norm_sum_le _ _
          _ ≤ ∑ j : Fin 3, ε / 4 := by
              refine Finset.sum_le_sum fun j _ => ?_
              rw [norm_smul]
              have hproj : ‖(ContinuousLinearMap.proj j : Vec3 →L[ℝ] ℝ)‖ ≤ 1 := by
                refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
                simpa only [ContinuousLinearMap.proj_apply, one_mul, Real.norm_eq_abs] using
                  norm_le_pi_norm v j
              have hd := hn j x
              rw [dist_comm, Real.dist_eq] at hd
              calc ‖spatialDeriv (g n) j x - fj j x‖ * ‖(ContinuousLinearMap.proj j :
                    Vec3 →L[ℝ] ℝ)‖ ≤ ‖spatialDeriv (g n) j x - fj j x‖ * 1 :=
                    mul_le_mul_of_nonneg_left hproj (norm_nonneg _)
                _ ≤ ε / 4 := by
                    rw [mul_one, Real.norm_eq_abs]
                    exact hd.le
          _ < ε := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
              norm_num
              linarith only [hε]
      have hderiv : ∀ x, HasFDerivAt f (g' x) x := by
        intro x
        refine hasFDerivAt_of_tendstoUniformly (f := g) hunif ?_ ?_ x
        · intro n y
          exact (((hg n).differentiable (by simp)).differentiableAt).hasFDerivAt
        · intro y
          exact hf.tendsto_at y
      refine ⟨f, ?_, ?_⟩
      · exact contDiff_succ_iff_hasFDerivAt.mpr ⟨g', hg'C, hderiv⟩
      · intro α hα
        cases α with
        | nil => simpa only [wordDeriv] using hf
        | cons j α =>
            have hj : spatialDeriv f j = fj j := by
              rw [lps_spatialDeriv_eq_of_hasFDerivAt hderiv j]
              funext x
              simp only [g', sum_apply,
                smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
                basisVec, Pi.single_apply]
              simp
            change TendstoUniformly (fun n => wordDeriv α (spatialDeriv (g n) j))
              (wordDeriv α (spatialDeriv f j)) atTop
            rw [hj]
            exact hfjT j α (by simp only [List.length_cons] at hα; omega)

end ESS
