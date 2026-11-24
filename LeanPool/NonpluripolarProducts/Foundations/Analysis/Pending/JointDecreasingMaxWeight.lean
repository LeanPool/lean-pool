/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.JointDecreasingSmoothMax

/-! # Weighted maximum locality with two genuine decreasing branches

The complete mathematical statement and proof preceded this file.
ROOT11 is strictly excluded from the fixed C90 batch.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff ComplexOrder

namespace SGPT.Foundations.Analysis.Pending.JointDecreasingMaxWeight

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere SmoothMax BedfordTaylor

variable {n : ℕ}

/-- The actual positive gap of the joint maximum preserves the weighted mixed limit. -/
theorem integral_mul_jointMaxWeight_eq {U : Opens (ComplexModel n)}
    {u : Fin n → ComplexModel n → ℝ} (i₀ : Fin n) {g : ComplexModel n → ℝ}
    {J : ℕ → ComplexModel n → ℝ} (hg : IsDecApprox U g J) {μ μ' : Measure (ComplexModel n)}
    (hμc : μ (U : Set (ComplexModel n))ᶜ = 0) (hμf : ∀ K, IsCompact K → K ⊆ U → μ K < ⊤)
    (hμ : ∀ F, IsAdmissible n U u F → TendstoMixed U F μ)
    (hμ'c : μ' (U : Set (ComplexModel n))ᶜ = 0) (hμ'f : ∀ K, IsCompact K → K ⊆ U → μ' K < ⊤)
    (hμ' : ∀ F, IsAdmissible n U (Function.update u i₀ fun z ↦ max (u i₀ z) (g z)) F →
      TendstoMixed U F μ')
    (hex : ∃ F, IsAdmissible n U u F) {χ : ComplexModel n → ℝ} (hχ : Continuous χ)
    (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ U) :
    ∫ z, χ z * (max (u i₀ z) (g z) - g z) ∂μ =
      ∫ z, χ z * (max (u i₀ z) (g z) - g z) ∂μ' := by
  classical
  obtain ⟨F, hF⟩ := hex
  set W : ComplexModel n → ℝ := fun z ↦ max (u i₀ z) (g z) with hW_def
  set G : ℕ → ComplexModel n → ℝ := fun j ↦ scaledSmoothMax (maxScale j) (F i₀ j) (J j) with hG_def
  have hG : IsDecApprox U W G := JointDecreasingSmoothMax.isDecApprox_joint_scaledSmoothMax (hF.1
    i₀) hg
  set F' : Fin n → ℕ → ComplexModel n → ℝ := Function.update F i₀ G with hF'_def
  have hF' : IsAdmissible n U (Function.update u i₀ W) F' := by
    refine ⟨fun i ↦ ?_, fun i hi ↦ absurd i.isLt (not_lt.mpr hi)⟩
    by_cases h : i = i₀
    · subst h
      simpa [hF'_def] using hG
    · simpa [hF'_def, Function.update_of_ne h] using hF.1 i
  have hWC := wClaim_of_pClaim (pClaim_all (n := n))
  have hA := hWC U u μ hμc hμf hμ F hF W G hG χ hχ hχc hχU
  have hB := hWC U _ μ' hμ'c hμ'f hμ' F' hF' W G hG χ hχ hχc hχU
  set ψ : ComplexModel n → ℝ := fun z ↦ χ z * g z with hψ_def
  set Ψ : ℕ → ComplexModel n → ℝ := fun k z ↦ χ z * J k z with hΨ_def
  have hA2 := hWC U u μ hμc hμf hμ F hF g J hg χ hχ hχc hχU
  have hB2 := hWC U _ μ' hμ'c hμ'f hμ' F' hF' g J hg χ hχ hχc hχU
  change Tendsto (fun k ↦ ∫ z, Ψ k z * mixedDensity (fun i ↦ F i k) z)
    atTop (𝓝 (∫ z, ψ z ∂μ)) at hA2
  change Tendsto (fun k ↦ ∫ z, Ψ k z * mixedDensity (fun i ↦ F' i k) z)
    atTop (𝓝 (∫ z, ψ z ∂μ')) at hB2
  have hFs (k : ℕ) (i : Fin n) : IsSmoothPsdOn U (F i k) := (hF.1 i).1 k
  have hF's (k : ℕ) (i : Fin n) : IsSmoothPsdOn U (F' i k) := (hF'.1 i).1 k
  have hDc (k : ℕ) := continuousOn_mixedDensity fun i ↦ (hFs k i).1
  have hD'c (k : ℕ) := continuousOn_mixedDensity fun i ↦ (hF's k i).1
  -- integrability of the smooth integrands against Lebesgue measure
  have hIA (k : ℕ) : Integrable fun z ↦ χ z * G k z * mixedDensity (fun i ↦ F i k) z := by
    have := integrable_mul_of_continuousOn
      (D := fun z ↦ G k z * mixedDensity (fun i ↦ F i k) z)
      ((hG.1 k).1.continuousOn.mul (hDc k)) hχ hχc hχU
    simpa only [mul_assoc] using this
  have hIB (k : ℕ) : Integrable fun z ↦ χ z * G k z * mixedDensity (fun i ↦ F' i k) z := by
    have := integrable_mul_of_continuousOn
      (D := fun z ↦ G k z * mixedDensity (fun i ↦ F' i k) z)
      ((hG.1 k).1.continuousOn.mul (hD'c k)) hχ hχc hχU
    simpa only [mul_assoc] using this
  have hIψA (k : ℕ) : Integrable fun z ↦ Ψ k z * mixedDensity (fun i ↦ F i k) z := by
    have := integrable_mul_of_continuousOn
      (D := fun z ↦ J k z * mixedDensity (fun i ↦ F i k) z)
      ((hg.1 k).1.continuousOn.mul (hDc k)) hχ hχc hχU
    simpa only [hΨ_def, mul_assoc] using this
  have hIψB (k : ℕ) : Integrable fun z ↦ Ψ k z * mixedDensity (fun i ↦ F' i k) z := by
    have := integrable_mul_of_continuousOn
      (D := fun z ↦ J k z * mixedDensity (fun i ↦ F' i k) z)
      ((hg.1 k).1.continuousOn.mul (hD'c k)) hχ hχc hχU
    simpa only [hΨ_def, mul_assoc] using this
  have hsubA (k : ℕ) : (∫ z, χ z * G k z * mixedDensity (fun i ↦ F i k) z) -
      ∫ z, Ψ k z * mixedDensity (fun i ↦ F i k) z =
      ∫ z, χ z * (G k z - J k z) * mixedDensity (fun i ↦ F i k) z := by
    rw [← integral_sub (hIA k) (hIψA k)]
    congr 1
    funext z
    simp only [hΨ_def]
    ring
  have hsubB (k : ℕ) : (∫ z, χ z * G k z * mixedDensity (fun i ↦ F' i k) z) -
      ∫ z, Ψ k z * mixedDensity (fun i ↦ F' i k) z =
      ∫ z, χ z * (G k z - J k z) * mixedDensity (fun i ↦ F' i k) z := by
    rw [← integral_sub (hIB k) (hIψB k)]
    congr 1
    funext z
    simp only [hΨ_def]
    ring
  -- the two weighted differences have the same limit
  have hIA' (k : ℕ) : Integrable fun z ↦ χ z * (G k z - J k z) * mixedDensity (fun i ↦ F i k) z :=
    ((hIA k).sub (hIψA k)).congr
      (Eventually.of_forall fun z ↦ by simp only [Pi.sub_apply, hΨ_def]; ring)
  have hIB' (k : ℕ) : Integrable fun z ↦ χ z * (G k z - J k z) * mixedDensity (fun i ↦ F' i k) z :=
    ((hIB k).sub (hIψB k)).congr
      (Eventually.of_forall fun z ↦ by simp only [Pi.sub_apply, hΨ_def]; ring)
  have hχa : Continuous fun z ↦ |χ z| := hχ.abs
  have hχac : HasCompactSupport fun z ↦ |χ z| := hχc.abs
  have hs : Function.support (fun z ↦ |χ z|) ⊆ Function.support χ :=
    fun _ hz => abs_ne_zero.mp hz
  have hχaU : tsupport (fun z ↦ |χ z|) ⊆ U := (closure_mono hs).trans hχU
  have ha := hμ F hF _ hχa hχac hχaU
  have hb := hμ' F' hF' _ hχa hχac hχaU
  have hIa (k : ℕ) : Integrable fun z ↦ |χ z| * mixedDensity (fun i ↦ F i k) z :=
    integrable_mul_of_continuousOn (hDc k) hχa hχac hχaU
  have hIb (k : ℕ) : Integrable fun z ↦ |χ z| * mixedDensity (fun i ↦ F' i k) z :=
    integrable_mul_of_continuousOn (hD'c k) hχa hχac hχaU
  have hpt (k : ℕ) (z : ComplexModel n) :
      |χ z * (G k z - J k z) * mixedDensity (fun i ↦ F i k) z -
        χ z * (G k z - J k z) * mixedDensity (fun i ↦ F' i k) z| ≤
      maxScale k * (|χ z| * mixedDensity (fun i ↦ F i k) z +
        |χ z| * mixedDensity (fun i ↦ F' i k) z) := by
    by_cases hzU : z ∈ (U : Set (ComplexModel n))
    · have hD0 := mixedDensity_nonneg fun i ↦ (hFs k i).2 z hzU
      have hD'0 := mixedDensity_nonneg fun i ↦ (hF's k i).2 z hzU
      have hR0 : 0 ≤ maxScale k * (|χ z| * mixedDensity (fun i ↦ F i k) z +
          |χ z| * mixedDensity (fun i ↦ F' i k) z) :=
        mul_nonneg (maxScale_pos k).le (add_nonneg (mul_nonneg (abs_nonneg _) hD0)
          (mul_nonneg (abs_nonneg _) hD'0))
      by_cases hz : J k z + maxScale k < F i₀ k z
      · have hev : ∀ i, F' i k =ᶠ[𝓝 z] F i k := by
          intro i
          by_cases h : i = i₀
          · subst h
            have hc : ContinuousAt (fun y ↦ F i k y - J k y) z :=
              ((hFs k i).1.continuousOn.sub (hg.1 k).1.continuousOn).continuousAt
                (U.isOpen.mem_nhds hzU)
            filter_upwards [hc.eventually (lt_mem_nhds (show maxScale k < F i k z - J k z by
              linarith))] with y hy
            simp only [hF'_def, Function.update_self, hG_def, scaledSmoothMax]
            rw [scaledPosPart_eq_self (maxScale_pos k) hy.le]
            ring
          · simp [hF'_def, Function.update_of_ne h]
        have h0 : χ z * (G k z - J k z) * mixedDensity (fun i ↦ F i k) z -
            χ z * (G k z - J k z) * mixedDensity (fun i ↦ F' i k) z = 0 := by
          rw [mixedDensity_congr hev, sub_self]
        rw [h0, abs_zero]
        exact hR0
      · have hG0 : 0 ≤ G k z - J k z := by
          have := scaledPosPart_nonneg (maxScale_pos k).le (F i₀ k z - J k z)
          simp only [hG_def, scaledSmoothMax]
          linarith
        have hGe : G k z - J k z ≤ maxScale k := by
          have := scaledPosPart_le (maxScale_pos k)
            (show F i₀ k z - J k z ≤ maxScale k by linarith [not_lt.mp hz])
          simp only [hG_def, scaledSmoothMax]
          linarith
        rw [← mul_sub, abs_mul, abs_mul, abs_of_nonneg hG0]
        calc |χ z| * (G k z - J k z) * |mixedDensity (fun i ↦ F i k) z -
              mixedDensity (fun i ↦ F' i k) z|
            ≤ |χ z| * maxScale k * (mixedDensity (fun i ↦ F i k) z +
              mixedDensity (fun i ↦ F' i k) z) := by
              refine mul_le_mul (mul_le_mul_of_nonneg_left hGe (abs_nonneg _)) ?_
                (abs_nonneg _) (mul_nonneg (abs_nonneg _) (maxScale_pos k).le)
              rw [abs_le]; constructor <;> linarith
          _ = _ := by ring
    · have hχz : χ z = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ hzU (hχU h)
      simp [hχz]
  have hdiff : Tendsto (fun k ↦ (∫ z, χ z * (G k z - J k z) * mixedDensity (fun i ↦ F i k) z) -
      ∫ z, χ z * (G k z - J k z) * mixedDensity (fun i ↦ F' i k) z) atTop (𝓝 0) := by
    set a : ℕ → ℝ := fun k ↦ ∫ z, |χ z| * mixedDensity (fun i ↦ F i k) z
    set b : ℕ → ℝ := fun k ↦ ∫ z, |χ z| * mixedDensity (fun i ↦ F' i k) z
    refine squeeze_zero_norm (fun k ↦ ?_) (?_ : Tendsto (fun k ↦ maxScale k * (a k + b k))
      atTop (𝓝 0))
    · rw [← integral_sub (hIA' k) (hIB' k), Real.norm_eq_abs]
      refine (abs_integral_le_integral_abs).trans ?_
      rw [← integral_add (hIa k) (hIb k), ← integral_const_mul]
      exact integral_mono ((hIA' k).sub (hIB' k)).abs
        (((hIa k).add (hIb k)).const_mul _) (hpt k)
    · simpa using tendsto_maxScale.mul (ha.add hb)
  have hcomb : Tendsto (fun k ↦ (∫ z, χ z * (G k z - J k z) * mixedDensity (fun i ↦ F i k) z) -
      ∫ z, χ z * (G k z - J k z) * mixedDensity (fun i ↦ F' i k) z) atTop
      (𝓝 (((∫ z, χ z * W z ∂μ) - ∫ z, ψ z ∂μ) - ((∫ z, χ z * W z ∂μ') - ∫ z, ψ z ∂μ'))) := by
    have h := (hA.sub hA2).sub (hB.sub hB2)
    simpa only [hsubA, hsubB] using h
  have hzero := tendsto_nhds_unique hcomb hdiff
  -- rewrite both sides as differences of integrals
  have hsplit (ν : Measure (ComplexModel n)) (hνf : ∀ K, IsCompact K → K ⊆ U → ν K < ⊤) :
      ∫ z, χ z * (W z - g z) ∂ν = (∫ z, χ z * W z ∂ν) - ∫ z, ψ z ∂ν := by
    obtain ⟨A, hA0, hAbd⟩ := exists_bound_of_continuous_of_hasCompactSupport hχ hχc
    have hintweight {q : ComplexModel n → ℝ} {Q : ℕ → ComplexModel n → ℝ}
        (hQ : IsDecApprox U q Q) : Integrable (fun z ↦ χ z * q z) ν := by
      obtain ⟨B, hBbd⟩ := hQ.exists_abs_le hχc hχU
      have hqbd : ∀ z ∈ tsupport χ, |q z| ≤ B := fun z hz ↦ hQ.abs_le_of_mem hχU hBbd hz
      refine integrable_of_bounded_of_support (isClosed_tsupport χ).measurableSet
        (hνf _ hχc hχU) (stronglyMeasurable_test_mul_limit hχ hχU
          (fun k ↦ (hQ.1 k).1.continuousOn) fun z hz ↦ hQ.2.2.1 z hz)
        (C := A * max B 0) (fun z ↦ ?_) (fun z hz ↦ ?_)
      · by_cases hz : z ∈ tsupport χ
        · rw [abs_mul]
          exact mul_le_mul (hAbd z) ((hqbd z hz).trans (le_max_left _ _)) (abs_nonneg _) hA0
        · rw [image_eq_zero_of_notMem_tsupport hz, zero_mul, abs_zero]
          exact mul_nonneg hA0 (le_max_right _ _)
      · rw [image_eq_zero_of_notMem_tsupport hz, zero_mul]
    have h1 : Integrable (fun z ↦ χ z * W z) ν := hintweight hG
    have h2 : Integrable ψ ν := hintweight hg
    rw [← integral_sub h1 h2]
    congr 1
    funext z
    simp only [hψ_def]
    ring
  rw [show (fun z ↦ χ z * (max (u i₀ z) (g z) - g z)) = fun z ↦ χ z * (W z - g z) from rfl,
    hsplit μ hμf, hsplit μ' hμ'f]
  linarith [hzero]

end SGPT.Foundations.Analysis.Pending.JointDecreasingMaxWeight
