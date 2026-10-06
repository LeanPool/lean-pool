/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.LocalStrongRegProduct
public import LeanPool.EscauriazaSereginSverak.LPS.RegularisedH1IBP

/-!
# The gradient of the smooth pressure against the transport term

For a smooth square-integrable pressure whose weak equation
`∫ P Δψ = -∑ ∫ F_ij ∂_i∂_j ψ` holds against every smooth compactly supported test function, the
pressure equation `ΔP = -∑ ∂_i c_i` holds pointwise, where `c_i = ∑_j ∂_j F_ji` is the divergence of
the tensor. Consequently `‖∇P‖² = -⟨c, ∇P⟩`, the orthogonality behind the pressure gradient bound in
the time derivative estimate of `prop:lps-local-strong`.
-/

public section

open MeasureTheory Set Filter Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS.LPS

/-- Integration by parts of a smooth function against a smooth compactly supported one. -/
theorem lps_ibp_compactSupport {F g : Vec3 → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g) (j : Fin 3) :
    (∫ x, spatialDeriv F j x * g x) = -∫ x, F x * spatialDeriv g j x := by
  have hFd : Continuous (spatialDeriv F j) := (contDiff_spatialDeriv_smooth hF j).continuous
  have hgd : Continuous (spatialDeriv g j) := (contDiff_spatialDeriv_smooth hg j).continuous
  have hgdc : HasCompactSupport (spatialDeriv g j) := by
    have h := hgc.fderiv_apply (𝕜 := ℝ) (basisVec j)
    exact h
  have hleft : Integrable (fun x => spatialDeriv g j x * F x) volume :=
    (hgd.mul hF.continuous).integrable_of_hasCompactSupport (hgdc.mul_right)
  have hright : Integrable (fun x => g x * spatialDeriv F j x) volume :=
    (hg.continuous.mul hFd).integrable_of_hasCompactSupport (hgc.mul_right)
  have hcross : Integrable (fun x => g x * F x) volume :=
    (hg.continuous.mul hF.continuous).integrable_of_hasCompactSupport (hgc.mul_right)
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := volume) (f := g) (g := F) (v := basisVec j)
    hleft hright hcross
    (fun x _ => hg.differentiable (by simp) x)
    (fun x _ => hF.differentiable (by simp) x)
  simp only [spatialDeriv] at hgd hFd ⊢
  calc (∫ x, (fderiv ℝ F x) (basisVec j) * g x)
      = ∫ x, g x * (fderiv ℝ F x) (basisVec j) := by congr 1; funext x; ring
    _ = -∫ x, (fderiv ℝ g x) (basisVec j) * F x := h
    _ = -∫ x, F x * (fderiv ℝ g x) (basisVec j) := by congr 1; congr 1; funext x; ring

/-- The pressure equation holds pointwise for a smooth square-integrable pressure satisfying its
weak form: `ΔP = -∑ᵢ ∂ᵢ cᵢ` with `cᵢ = ∑ⱼ ∂ⱼ F_ji` (`prop:lps-local-strong`). -/
theorem lps_pressure_laplacian_eq_neg_divergence
    {P : Vec3 → ℝ} {F : Fin 3 → Fin 3 → Vec3 → ℝ}
    (hP : ContDiff ℝ (⊤ : ℕ∞) P) (hF : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (F i j))
    (hP0 : MemLp P 2 volume) (hP1 : ∀ k, MemLp (spatialDeriv P k) 2 volume)
    (hP2 : ∀ k, MemLp (spatialDeriv (spatialDeriv P k) k) 2 volume)
    (hc0 : ∀ i, MemLp (fun x => ∑ j : Fin 3, spatialDeriv (F j i) j x) 2 volume)
    (hc1 : ∀ i, MemLp (spatialDeriv (fun x => ∑ j : Fin 3, spatialDeriv (F j i) j x) i) 2 volume)
    (hweak : ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      (∫ x, P x * spatialLaplacian ψ x) =
        -∑ i : Fin 3, ∑ j : Fin 3, ∫ x, F i j x * mixedSecond ψ i j x) (x : Vec3) :
    spatialLaplacian P x +
      ∑ i : Fin 3, spatialDeriv (fun y => ∑ j : Fin 3, spatialDeriv (F j i) j y) i x = 0 := by
  set c : Fin 3 → Vec3 → ℝ := fun i y => ∑ j : Fin 3, spatialDeriv (F j i) j y with hcdef
  have hcs : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (c i) := fun i =>
    ContDiff.sum fun j _ => contDiff_spatialDeriv_smooth (hF j i) j
  have hG : Continuous (fun y => spatialLaplacian P y +
      ∑ i : Fin 3, spatialDeriv (c i) i y) := by
    refine Continuous.add ?_ (continuous_finsetSum _ fun i _ =>
      (contDiff_spatialDeriv_smooth (hcs i) i).continuous)
    exact continuous_finsetSum _ fun i _ =>
      (contDiff_spatialDeriv_smooth (contDiff_spatialDeriv_smooth hP i) i).continuous
  have hae : ∀ᵐ y ∂(volume : Measure Vec3), spatialLaplacian P y +
      ∑ i : Fin 3, spatialDeriv (c i) i y = 0 := by
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hG.locallyIntegrable fun g hg hgc => ?_
    have hg2 : MemLp g 2 volume := hg.continuous.memLp_of_hasCompactSupport hgc
    have hgd : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv g k) := fun k =>
      contDiff_spatialDeriv_smooth hg k
    have hgd2 : ∀ k, MemLp (spatialDeriv g k) 2 volume := fun k =>
      (hgd k).continuous.memLp_of_hasCompactSupport (hgc.fderiv_apply (𝕜 := ℝ) (basisVec k))
    have hgdd2 : ∀ k, MemLp (spatialDeriv (spatialDeriv g k) k) 2 volume := fun k =>
      (contDiff_spatialDeriv_smooth (hgd k) k).continuous.memLp_of_hasCompactSupport
        ((hgc.fderiv_apply (𝕜 := ℝ) (basisVec k)).fderiv_apply (𝕜 := ℝ) (basisVec k))
    -- ∫ g ΔP = ∫ P Δg
    have h1 : (∫ y, g y * spatialLaplacian P y) = ∫ y, P y * spatialLaplacian g y := by
      rw [lps_pairing_laplacian hg hP hg2 hgd2 hP1 hP2,
        lps_pairing_laplacian hP hg hP0 hP1 hgd2 hgdd2]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      congr 1; funext y; ring
    -- ∫ g ∂ᵢ cᵢ
    have h2 : ∀ i, (∫ y, g y * spatialDeriv (c i) i y) =
        ∑ j : Fin 3, ∫ y, F j i y * mixedSecond g j i y := by
      intro i
      rw [lps_divergence_pairing_direction hg (hcs i) i hg2 (hgd2 i) (hc0 i) (hc1 i)]
      have hexp : (∫ y, spatialDeriv g i y * c i y) =
          ∑ j : Fin 3, ∫ y, spatialDeriv g i y * spatialDeriv (F j i) j y := by
        rw [← integral_finsetSum]
        · congr 1; funext y; simp [hcdef, Finset.mul_sum]
        · intro j _
          have hc : Continuous fun y => spatialDeriv g i y * spatialDeriv (F j i) j y :=
            (hgd i).continuous.mul (contDiff_spatialDeriv_smooth (hF j i) j).continuous
          exact hc.integrable_of_hasCompactSupport
            ((hgc.fderiv_apply (𝕜 := ℝ) (basisVec i)).mul_right)
      rw [hexp, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      have := lps_ibp_compactSupport (hF j i) (hgd i)
        (hgc.fderiv_apply (𝕜 := ℝ) (basisVec i)) j
      rw [show (fun y => spatialDeriv g i y * spatialDeriv (F j i) j y) =
        fun y => spatialDeriv (F j i) j y * spatialDeriv g i y from funext fun y => mul_comm _ _,
        this, neg_neg]
      rfl
    have hLapP : MemLp (spatialLaplacian P) 2 volume := by
      unfold spatialLaplacian
      exact memLp_finsetSum _ fun j _ => hP2 j
    have hint1 : Integrable (fun y => g y * spatialLaplacian P y) volume :=
      hg2.integrable_mul hLapP
    have hint2 : ∀ i ∈ (Finset.univ : Finset (Fin 3)),
        Integrable (fun y => g y * spatialDeriv (c i) i y) volume :=
      fun i _ => hg2.integrable_mul (hc1 i)
    calc (∫ y, g y • (spatialLaplacian P y + ∑ i : Fin 3, spatialDeriv (c i) i y))
        = ∫ y, (g y * spatialLaplacian P y + ∑ i : Fin 3, g y * spatialDeriv (c i) i y) := by
          congr 1; funext y; simp only [smul_eq_mul, mul_add, Finset.mul_sum]
      _ = (∫ y, g y * spatialLaplacian P y) +
          ∑ i : Fin 3, ∫ y, g y * spatialDeriv (c i) i y := by
          rw [integral_add hint1 (integrable_finsetSum _ hint2),
            integral_finsetSum _ hint2]
      _ = 0 := by
          rw [h1, hweak g hg hgc]
          simp only [h2]
          rw [neg_add_eq_zero]
          exact Finset.sum_comm
  have hzero := (Continuous.ae_eq_iff_eq (μ := (volume : Measure Vec3)) hG
    continuous_const).1 (by filter_upwards [hae] with y hy; exact hy)
  exact congrFun hzero x

/-- The pressure gradient is bounded in `L²` by the divergence of the tensor:
`∑ᵢ ‖∂ᵢ P‖² ≤ ∑ᵢ ‖cᵢ‖²` (`prop:lps-local-strong`). -/
theorem lps_pressure_gradient_sq_le
    {P : Vec3 → ℝ} {F : Fin 3 → Fin 3 → Vec3 → ℝ}
    (hP : ContDiff ℝ (⊤ : ℕ∞) P) (hF : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (F i j))
    (hP0 : MemLp P 2 volume) (hP1 : ∀ k, MemLp (spatialDeriv P k) 2 volume)
    (hP2 : ∀ k, MemLp (spatialDeriv (spatialDeriv P k) k) 2 volume)
    (hc0 : ∀ i, MemLp (fun x => ∑ j : Fin 3, spatialDeriv (F j i) j x) 2 volume)
    (hc1 : ∀ i, MemLp (spatialDeriv (fun x => ∑ j : Fin 3, spatialDeriv (F j i) j x) i) 2 volume)
    (hweak : ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      (∫ x, P x * spatialLaplacian ψ x) =
        -∑ i : Fin 3, ∑ j : Fin 3, ∫ x, F i j x * mixedSecond ψ i j x) :
    (∑ i : Fin 3, ∫ x, spatialDeriv P i x ^ 2) ≤
      ∑ i : Fin 3, ∫ x, (∑ j : Fin 3, spatialDeriv (F j i) j x) ^ 2 := by
  set c : Fin 3 → Vec3 → ℝ := fun i y => ∑ j : Fin 3, spatialDeriv (F j i) j y with hcdef
  have hcs : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (c i) := fun i =>
    ContDiff.sum fun j _ => contDiff_spatialDeriv_smooth (hF j i) j
  have hpt := lps_pressure_laplacian_eq_neg_divergence hP hF hP0 hP1 hP2 hc0 hc1 hweak
  have hLapP : MemLp (spatialLaplacian P) 2 volume := by
    unfold spatialLaplacian
    exact memLp_finsetSum _ fun j _ => hP2 j
  have hA : (∫ x, P x * spatialLaplacian P x) = -∑ j : Fin 3, ∫ x, spatialDeriv P j x ^ 2 := by
    rw [lps_pairing_laplacian hP hP hP0 hP1 hP1 hP2]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1; funext x; ring
  have hB : (∫ x, P x * spatialLaplacian P x) = ∑ i : Fin 3, ∫ x, spatialDeriv P i x * c i x := by
    have : (fun x => P x * spatialLaplacian P x) =
        fun x => ∑ i : Fin 3, -(P x * spatialDeriv (c i) i x) := by
      funext x
      have h := hpt x
      rw [show spatialLaplacian P x = -∑ i : Fin 3, spatialDeriv (c i) i x by linarith only [h],
        Finset.sum_neg_distrib, mul_neg, Finset.mul_sum]
    rw [this, integral_finsetSum (f := fun i x => -(P x * spatialDeriv (c i) i x)) _
      (fun i _ => ((hP0.integrable_mul (hc1 i)).neg))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_neg, lps_divergence_pairing_direction hP (hcs i) i hP0 (hP1 i) (hc0 i) (hc1 i),
      neg_neg]
  have hG : (∑ j : Fin 3, ∫ x, spatialDeriv P j x ^ 2) =
      -∑ i : Fin 3, ∫ x, spatialDeriv P i x * c i x := by
    rw [← hB, hA, neg_neg]
  have hle : (∑ i : Fin 3, ∫ x, spatialDeriv P i x ^ 2) ≤
      (1 / 2) * ((∑ i : Fin 3, ∫ x, spatialDeriv P i x ^ 2) +
        ∑ i : Fin 3, ∫ x, c i x ^ 2) := by
    have hpt : ∀ i, (∫ x, -(spatialDeriv P i x * c i x)) ≤
        (1 / 2) * ((∫ x, spatialDeriv P i x ^ 2) + ∫ x, c i x ^ 2) := by
      intro i
      have hi1 : Integrable (fun x => spatialDeriv P i x ^ 2) volume := (hP1 i).integrable_sq
      have hi2 : Integrable (fun x => c i x ^ 2) volume := (hc0 i).integrable_sq
      rw [← integral_add hi1 hi2, ← integral_const_mul]
      refine integral_mono ((hP1 i).integrable_mul (hc0 i)).neg
        ((hi1.add hi2).const_mul _) fun x => ?_
      nlinarith only [sq_nonneg (spatialDeriv P i x + c i x)]
    calc (∑ i : Fin 3, ∫ x, spatialDeriv P i x ^ 2)
        = ∑ i : Fin 3, ∫ x, -(spatialDeriv P i x * c i x) := by
          rw [hG, ← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl fun i _ => (integral_neg _).symm
      _ ≤ ∑ i : Fin 3, (1 / 2) * ((∫ x, spatialDeriv P i x ^ 2) + ∫ x, c i x ^ 2) :=
          Finset.sum_le_sum fun i _ => hpt i
      _ = _ := by rw [← Finset.mul_sum, Finset.sum_add_distrib]
  linarith only [hle]

end ESS.LPS

end
