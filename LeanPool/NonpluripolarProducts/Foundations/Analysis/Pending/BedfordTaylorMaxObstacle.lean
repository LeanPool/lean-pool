/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BedfordTaylorMaxLocality

/-!
# Plurifine locality of Bedford–Taylor measures for a maximum with a smooth obstacle

Let `u' = max(u, g)` in one slot, where `g` is smooth with positive semidefinite
complex Hessian. The regularized maxima `g + ε_j P((f_j - g)/ε_j)` of decreasing
smooth approximations `f_j` of `u` are again smooth and positive semidefinite,
because `P' ∈ [0,1]` mixes the two Hessians convexly. They decrease to
`max(u, g)`, and their mixed densities agree with those of `f_j` where
`f_j > g + ε_j`, while `(g + ε_j P((f_j - g)/ε_j)) - g ≤ ε_j` elsewhere.

Unlike the constant obstacle of `BedfordTaylorMaxLocality`, the weight
`max(u, g) - g` is not plurisubharmonic, so the weighted convergence theorem is
applied to the plurisubharmonic weight `max(u, g)` and the smooth part is
removed by the unweighted convergence theorem against the test function `χ · g`.
Dividing by the positive weight on `{u > g}` then gives `μ = μ'` there.

Source: Bedford–Taylor locality in the plurifine topology, as invoked in BEGZ §1.2.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff ComplexOrder

namespace SGPT.Foundations.Analysis.Pending.BedfordTaylor

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere SmoothMax

variable {n : ℕ}

/-- The regularized maximum of `f` with the obstacle `g`, at scale `ε`. -/
def scaledSmoothMax (ε : ℝ) (f g : ComplexModel n → ℝ) : ComplexModel n → ℝ :=
  fun z ↦ g z + scaledPosPart ε (f z - g z)

theorem scaledSmoothMax_apply (ε : ℝ) (f g : ComplexModel n → ℝ) (z : ComplexModel n) :
    scaledSmoothMax ε f g z = g z + scaledPosPart ε (f z - g z) := rfl

theorem scaledSmoothMax_eq_smul {ε : ℝ} (hε : 0 < ε) (f g : ComplexModel n → ℝ) :
    scaledSmoothMax ε f g = ε • smoothMax (ε⁻¹ • f) (ε⁻¹ • g) := by
  funext z
  simp only [scaledSmoothMax, smoothMax, scaledPosPart, Pi.smul_apply, smul_eq_mul,
    div_eq_inv_mul, mul_add, ← mul_sub]
  rw [← mul_assoc, mul_inv_cancel₀ hε.ne', one_mul]

theorem contDiffAt_scaledSmoothMax {f g : ComplexModel n → ℝ} {z : ComplexModel n}
    (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z) (ε : ℝ) :
    ContDiffAt ℝ 2 (scaledSmoothMax ε f g) z := by
  have hP : ContDiffAt ℝ 2 (fun y ↦ SmoothMax.posPart ((f y - g y) / ε)) z :=
    (contDiff_posPart.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt.comp z
      ((hf.sub hg).div_const ε)
  exact hg.add (contDiffAt_const.mul hP)

/-- The regularized maximum of two functions with positive semidefinite complex
Hessians has a positive semidefinite complex Hessian. -/
theorem complexHessian_scaledSmoothMax_posSemidef {f g : ComplexModel n → ℝ}
    {z : ComplexModel n} (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z)
    (hHf : (complexHessian f z).PosSemidef) (hHg : (complexHessian g z).PosSemidef)
    {ε : ℝ} (hε : 0 < ε) : (complexHessian (scaledSmoothMax ε f g) z).PosSemidef := by
  have hf' : ContDiffAt ℝ 2 (ε⁻¹ • f) z := by simpa [Pi.smul_def] using hf.const_smul ε⁻¹
  have hg' : ContDiffAt ℝ 2 (ε⁻¹ • g) z := by simpa [Pi.smul_def] using hg.const_smul ε⁻¹
  have hHf' : (complexHessian (ε⁻¹ • f) z).PosSemidef := by
    rw [complexHessian_smul hf]
    exact hHf.smul (by exact_mod_cast (inv_pos.2 hε).le)
  have hHg' : (complexHessian (ε⁻¹ • g) z).PosSemidef := by
    rw [complexHessian_smul hg]
    exact hHg.smul (by exact_mod_cast (inv_pos.2 hε).le)
  have hsm : ContDiffAt ℝ 2 (smoothMax (ε⁻¹ • f) (ε⁻¹ • g)) z := by
    have hP : ContDiffAt ℝ 2 (SmoothMax.posPart ∘ ((ε⁻¹ • f) - (ε⁻¹ • g))) z :=
      (contDiff_posPart.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt.comp z (hf'.sub hg')
    exact hg'.add hP
  rw [scaledSmoothMax_eq_smul hε, complexHessian_smul hsm]
  exact (complexHessian_smoothMax_posSemidef hf' hg' hHf' hHg').smul
    (by exact_mod_cast hε.le)

theorem max_eq_add_max_sub (a b : ℝ) : max a b = b + max (a - b) 0 := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (by linarith), add_zero]
  · rw [max_eq_left h, max_eq_left (by linarith)]; ring

/-- The scaled regularized maxima with a smooth positive semidefinite obstacle
form a decreasing approximation of `max(w, g)`. -/
theorem IsDecApprox.scaledSmoothMax {U : Opens (ComplexModel n)} {w g : ComplexModel n → ℝ}
    {G : ℕ → ComplexModel n → ℝ} (hG : IsDecApprox U w G) (hg : IsSmoothPsdOn U g) :
    IsDecApprox U (fun z ↦ max (w z) (g z))
      (fun j ↦ scaledSmoothMax (maxScale j) (G j) g) := by
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  refine ⟨fun j ↦ ⟨?_, fun z hz ↦ ?_⟩, fun z hz j l hjl ↦ ?_, fun z hz ↦ ?_, fun K hK hKU ↦ ?_⟩
  · exact hg.1.add (contDiffOn_const.mul (contDiff_posPart.comp_contDiffOn
      (((hG.1 j).1.sub hg.1).div_const _)))
  · exact complexHessian_scaledSmoothMax_posSemidef
      (((hG.1 j).1.contDiffAt (U.isOpen.mem_nhds hz)).of_le h2)
      ((hg.1.contDiffAt (U.isOpen.mem_nhds hz)).of_le h2) ((hG.1 j).2 z hz) (hg.2 z hz)
      (maxScale_pos j)
  · change g z + scaledPosPart (maxScale l) (G l z - g z) ≤
      g z + scaledPosPart (maxScale j) (G j z - g z)
    have h := (scaledPosPart_mono_right (maxScale_pos l)
        (show G l z - g z ≤ G j z - g z by linarith [hG.2.1 z hz hjl])).trans
      (scaledPosPart_mono_left (maxScale_pos l) (maxScale_antitone hjl) (G j z - g z))
    linarith
  · have hlim : Tendsto (fun j ↦ g z + max (G j z - g z) 0) atTop (𝓝 (max (w z) (g z))) := by
      rw [max_eq_add_max_sub (w z) (g z)]
      exact tendsto_const_nhds.add (((hG.2.2.1 z hz).sub_const (g z)).max tendsto_const_nhds)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlim
      (by simpa using hlim.add tendsto_maxScale) (fun j ↦ ?_) (fun j ↦ ?_)
    · change g z + max (G j z - g z) 0 ≤ g z + scaledPosPart (maxScale j) (G j z - g z)
      have := max_le (le_scaledPosPart (maxScale_pos j) (G j z - g z))
        (scaledPosPart_nonneg (maxScale_pos j).le (G j z - g z))
      linarith
    · change g z + scaledPosPart (maxScale j) (G j z - g z) ≤
        g z + max (G j z - g z) 0 + maxScale j
      have := scaledPosPart_le_max_add (maxScale_pos j) (G j z - g z)
      linarith
  · obtain ⟨m, hm⟩ := hG.2.2.2 K hK hKU
    refine ⟨m, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact (hm ⟨z, hz, rfl⟩).trans (le_max_left _ _)

/-! ### Test functions multiplied by a function continuous on `U` -/

/-- Multiplying a test function by a function continuous on `U` gives a
continuous function. -/
theorem continuous_test_mul {U : Opens (ComplexModel n)} {χ D : ComplexModel n → ℝ}
    (hχ : Continuous χ) (hχU : tsupport χ ⊆ U) (hD : ContinuousOn D U) :
    Continuous fun z ↦ χ z * D z :=
  continuous_of_continuousOn_of_eq_zero U.isOpen (isClosed_tsupport χ) hχU
    (hχ.continuousOn.mul hD) fun z hz ↦ by simp [image_eq_zero_of_notMem_tsupport hz]

theorem tsupport_test_mul_subset {χ D : ComplexModel n → ℝ} :
    tsupport (fun z ↦ χ z * D z) ⊆ tsupport χ :=
  closure_mono fun z (hz : χ z * D z ≠ 0) ↦ fun h ↦ hz (by simp [h])

/-- A bounded strongly measurable function vanishing outside a set of finite
measure is integrable. -/
theorem integrable_of_bounded_of_support {ν : Measure (ComplexModel n)}
    {f : ComplexModel n → ℝ} {S : Set (ComplexModel n)} (hS : MeasurableSet S)
    (hνS : ν S < ⊤) (hf : StronglyMeasurable f) {C : ℝ} (hC : ∀ z, |f z| ≤ C)
    (h0 : ∀ z ∉ S, f z = 0) : Integrable f ν := by
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  have hbound : ∀ z, ‖f z‖ₑ ≤ S.indicator (fun _ ↦ ENNReal.ofReal C) z := by
    intro z
    by_cases hz : z ∈ S
    · rw [indicator_of_mem hz, Real.eNorm_eq_ofReal_abs]
      exact ENNReal.ofReal_le_ofReal (hC z)
    · rw [indicator_of_notMem hz, h0 z hz]
      simp
  refine lt_of_le_of_lt (lintegral_mono hbound) ?_
  rw [lintegral_indicator hS, setLIntegral_const]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hνS

/-- A test function times a pointwise limit of functions continuous on `U` is
strongly measurable. -/
theorem stronglyMeasurable_test_mul_limit {U : Opens (ComplexModel n)}
    {χ h : ComplexModel n → ℝ} {H : ℕ → ComplexModel n → ℝ} (hχ : Continuous χ)
    (hχU : tsupport χ ⊆ U) (hHc : ∀ k, ContinuousOn (H k) U)
    (hlim : ∀ z ∈ U, Tendsto (fun k ↦ H k z) atTop (𝓝 (h z))) :
    StronglyMeasurable fun z ↦ χ z * h z := by
  refine stronglyMeasurable_of_tendsto atTop
    (f := fun k z ↦ χ z * H k z) (fun k ↦ (continuous_test_mul hχ hχU (hHc k)).stronglyMeasurable)
    (tendsto_pi_nhds.2 fun z ↦ ?_)
  by_cases hz : z ∈ (U : Set (ComplexModel n))
  · exact tendsto_const_nhds.mul (hlim z hz)
  · have hχz : χ z = 0 := image_eq_zero_of_notMem_tsupport fun hmem ↦ hz (hχU hmem)
    simp [hχz]

theorem exists_bound_of_continuous_of_hasCompactSupport {f : ComplexModel n → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) : ∃ C, 0 ≤ C ∧ ∀ z, |f z| ≤ C := by
  obtain ⟨C, hC⟩ := (hfc.image (continuous_abs.comp hf)).bddAbove
  refine ⟨max C 0, le_max_right _ _, fun z ↦ ?_⟩
  by_cases hz : z ∈ tsupport f
  · exact (hC ⟨z, hz, rfl⟩).trans (le_max_left _ _)
  · rw [image_eq_zero_of_notMem_tsupport hz, abs_zero]
    exact le_max_right _ _

/-- **Weighted locality for a smooth obstacle.** Replacing one slot `u i₀` by
`max(u i₀, g)`, with `g` smooth and positive semidefinite, does not change the
limit measure weighted by `max(u i₀, g) - g`. -/
theorem integral_mul_maxObstacleWeight_eq {U : Opens (ComplexModel n)}
    {u : Fin n → ComplexModel n → ℝ} (i₀ : Fin n) {g : ComplexModel n → ℝ}
    (hg : IsSmoothPsdOn U g) {μ μ' : Measure (ComplexModel n)}
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
  set G : ℕ → ComplexModel n → ℝ := fun j ↦ scaledSmoothMax (maxScale j) (F i₀ j) g with hG_def
  have hG : IsDecApprox U W G := (hF.1 i₀).scaledSmoothMax hg
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
  have hψ : Continuous ψ := continuous_test_mul hχ hχU hg.1.continuousOn
  have hψc : HasCompactSupport ψ := hχc.mul_right
  have hψU : tsupport ψ ⊆ U := tsupport_test_mul_subset.trans hχU
  have hA2 := hμ F hF ψ hψ hψc hψU
  have hB2 := hμ' F' hF' ψ hψ hψc hψU
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
  have hIψA (k : ℕ) : Integrable fun z ↦ ψ z * mixedDensity (fun i ↦ F i k) z := by
    have := integrable_mul_of_continuousOn
      (D := fun z ↦ g z * mixedDensity (fun i ↦ F i k) z)
      (hg.1.continuousOn.mul (hDc k)) hχ hχc hχU
    simpa only [hψ_def, mul_assoc] using this
  have hIψB (k : ℕ) : Integrable fun z ↦ ψ z * mixedDensity (fun i ↦ F' i k) z := by
    have := integrable_mul_of_continuousOn
      (D := fun z ↦ g z * mixedDensity (fun i ↦ F' i k) z)
      (hg.1.continuousOn.mul (hD'c k)) hχ hχc hχU
    simpa only [hψ_def, mul_assoc] using this
  have hsubA (k : ℕ) : (∫ z, χ z * G k z * mixedDensity (fun i ↦ F i k) z) -
      ∫ z, ψ z * mixedDensity (fun i ↦ F i k) z =
      ∫ z, χ z * (G k z - g z) * mixedDensity (fun i ↦ F i k) z := by
    rw [← integral_sub (hIA k) (hIψA k)]
    congr 1
    funext z
    simp only [hψ_def]
    ring
  have hsubB (k : ℕ) : (∫ z, χ z * G k z * mixedDensity (fun i ↦ F' i k) z) -
      ∫ z, ψ z * mixedDensity (fun i ↦ F' i k) z =
      ∫ z, χ z * (G k z - g z) * mixedDensity (fun i ↦ F' i k) z := by
    rw [← integral_sub (hIB k) (hIψB k)]
    congr 1
    funext z
    simp only [hψ_def]
    ring
  -- the two weighted differences have the same limit
  have hIA' (k : ℕ) : Integrable fun z ↦ χ z * (G k z - g z) * mixedDensity (fun i ↦ F i k) z :=
    ((hIA k).sub (hIψA k)).congr
      (Eventually.of_forall fun z ↦ by simp only [Pi.sub_apply, hψ_def]; ring)
  have hIB' (k : ℕ) : Integrable fun z ↦ χ z * (G k z - g z) * mixedDensity (fun i ↦ F' i k) z :=
    ((hIB k).sub (hIψB k)).congr
      (Eventually.of_forall fun z ↦ by simp only [Pi.sub_apply, hψ_def]; ring)
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
      |χ z * (G k z - g z) * mixedDensity (fun i ↦ F i k) z -
        χ z * (G k z - g z) * mixedDensity (fun i ↦ F' i k) z| ≤
      maxScale k * (|χ z| * mixedDensity (fun i ↦ F i k) z +
        |χ z| * mixedDensity (fun i ↦ F' i k) z) := by
    by_cases hzU : z ∈ (U : Set (ComplexModel n))
    · have hD0 := mixedDensity_nonneg fun i ↦ (hFs k i).2 z hzU
      have hD'0 := mixedDensity_nonneg fun i ↦ (hF's k i).2 z hzU
      have hR0 : 0 ≤ maxScale k * (|χ z| * mixedDensity (fun i ↦ F i k) z +
          |χ z| * mixedDensity (fun i ↦ F' i k) z) :=
        mul_nonneg (maxScale_pos k).le (add_nonneg (mul_nonneg (abs_nonneg _) hD0)
          (mul_nonneg (abs_nonneg _) hD'0))
      by_cases hz : g z + maxScale k < F i₀ k z
      · have hev : ∀ i, F' i k =ᶠ[𝓝 z] F i k := by
          intro i
          by_cases h : i = i₀
          · subst h
            have hc : ContinuousAt (fun y ↦ F i k y - g y) z :=
              ((hFs k i).1.continuousOn.sub hg.1.continuousOn).continuousAt
                (U.isOpen.mem_nhds hzU)
            filter_upwards [hc.eventually (lt_mem_nhds (show maxScale k < F i k z - g z by
              linarith))] with y hy
            simp only [hF'_def, Function.update_self, hG_def, scaledSmoothMax]
            rw [scaledPosPart_eq_self (maxScale_pos k) hy.le]
            ring
          · simp [hF'_def, Function.update_of_ne h]
        have h0 : χ z * (G k z - g z) * mixedDensity (fun i ↦ F i k) z -
            χ z * (G k z - g z) * mixedDensity (fun i ↦ F' i k) z = 0 := by
          rw [mixedDensity_congr hev, sub_self]
        rw [h0, abs_zero]
        exact hR0
      · have hG0 : 0 ≤ G k z - g z := by
          have := scaledPosPart_nonneg (maxScale_pos k).le (F i₀ k z - g z)
          simp only [hG_def, scaledSmoothMax]
          linarith
        have hGe : G k z - g z ≤ maxScale k := by
          have := scaledPosPart_le (maxScale_pos k)
            (show F i₀ k z - g z ≤ maxScale k by linarith [not_lt.mp hz])
          simp only [hG_def, scaledSmoothMax]
          linarith
        rw [← mul_sub, abs_mul, abs_mul, abs_of_nonneg hG0]
        calc |χ z| * (G k z - g z) * |mixedDensity (fun i ↦ F i k) z -
              mixedDensity (fun i ↦ F' i k) z|
            ≤ |χ z| * maxScale k * (mixedDensity (fun i ↦ F i k) z +
              mixedDensity (fun i ↦ F' i k) z) := by
              refine mul_le_mul (mul_le_mul_of_nonneg_left hGe (abs_nonneg _)) ?_
                (abs_nonneg _) (mul_nonneg (abs_nonneg _) (maxScale_pos k).le)
              rw [abs_le]; constructor <;> linarith
          _ = _ := by ring
    · have hχz : χ z = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ hzU (hχU h)
      simp [hχz]
  have hdiff : Tendsto (fun k ↦ (∫ z, χ z * (G k z - g z) * mixedDensity (fun i ↦ F i k) z) -
      ∫ z, χ z * (G k z - g z) * mixedDensity (fun i ↦ F' i k) z) atTop (𝓝 0) := by
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
  have hcomb : Tendsto (fun k ↦ (∫ z, χ z * (G k z - g z) * mixedDensity (fun i ↦ F i k) z) -
      ∫ z, χ z * (G k z - g z) * mixedDensity (fun i ↦ F' i k) z) atTop
      (𝓝 (((∫ z, χ z * W z ∂μ) - ∫ z, ψ z ∂μ) - ((∫ z, χ z * W z ∂μ') - ∫ z, ψ z ∂μ'))) := by
    have h := (hA.sub hA2).sub (hB.sub hB2)
    simpa only [hsubA, hsubB] using h
  have hzero := tendsto_nhds_unique hcomb hdiff
  -- rewrite both sides as differences of integrals
  have hsplit (ν : Measure (ComplexModel n)) (hνf : ∀ K, IsCompact K → K ⊆ U → ν K < ⊤) :
      ∫ z, χ z * (W z - g z) ∂ν = (∫ z, χ z * W z ∂ν) - ∫ z, ψ z ∂ν := by
    obtain ⟨A, hA0, hAbd⟩ := exists_bound_of_continuous_of_hasCompactSupport hχ hχc
    obtain ⟨B, hBbd⟩ := hG.exists_abs_le hχc hχU
    have hWbd : ∀ z ∈ tsupport χ, |W z| ≤ B := fun z hz ↦ hG.abs_le_of_mem hχU hBbd hz
    have h1 : Integrable (fun z ↦ χ z * W z) ν := by
      refine integrable_of_bounded_of_support (isClosed_tsupport χ).measurableSet
        (hνf _ hχc hχU) (stronglyMeasurable_test_mul_limit hχ hχU
          (fun k ↦ (hG.1 k).1.continuousOn) fun z hz ↦ hG.2.2.1 z hz)
        (C := A * max B 0) (fun z ↦ ?_) (fun z hz ↦ ?_)
      · by_cases hz : z ∈ tsupport χ
        · rw [abs_mul]
          exact mul_le_mul (hAbd z) ((hWbd z hz).trans (le_max_left _ _)) (abs_nonneg _) hA0
        · rw [image_eq_zero_of_notMem_tsupport hz, zero_mul, abs_zero]
          exact mul_nonneg hA0 (le_max_right _ _)
      · rw [image_eq_zero_of_notMem_tsupport hz, zero_mul]
    have h2 : Integrable ψ ν := by
      obtain ⟨C, hC0, hCbd⟩ := exists_bound_of_continuous_of_hasCompactSupport hψ hψc
      refine integrable_of_bounded_of_support (isClosed_tsupport χ).measurableSet
        (hνf _ hχc hχU) hψ.stronglyMeasurable hCbd fun z hz ↦ ?_
      simp [hψ_def, image_eq_zero_of_notMem_tsupport hz]
    rw [← integral_sub h1 h2]
    congr 1
    funext z
    simp only [hψ_def]
    ring
  rw [show (fun z ↦ χ z * (max (u i₀ z) (g z) - g z)) = fun z ↦ χ z * (W z - g z) from rfl,
    hsplit μ hμf, hsplit μ' hμ'f]
  linarith [hzero]

/-- The strict superlevel set over a smooth obstacle is measurable. -/
theorem IsDecApprox.measurableSet_lt_obstacle {U : Opens (ComplexModel n)}
    {w g : ComplexModel n → ℝ} {G : ℕ → ComplexModel n → ℝ} (hG : IsDecApprox U w G)
    (hg : ContinuousOn g U) : MeasurableSet {z | z ∈ U ∧ g z < w z} := by
  have heq : {z | z ∈ U ∧ g z < w z} =
      ⋃ m : ℕ, ⋂ k : ℕ, ((U : Set (ComplexModel n)) ∩
        (fun z ↦ G k z - g z) ⁻¹' Ioi (1 / ((m : ℝ) + 1))) := by
    ext z
    simp only [mem_ofPred_eq, mem_iUnion, mem_iInter, mem_inter_iff, mem_preimage, mem_Ioi]
    constructor
    · rintro ⟨hzU, hz⟩
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt (sub_pos.2 hz)
      exact ⟨m, fun k ↦ ⟨hzU, by linarith [hG.le_of_mem hzU k]⟩⟩
    · rintro ⟨m, hm⟩
      obtain ⟨hzU, -⟩ := hm 0
      have hpos : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
      refine ⟨hzU, ?_⟩
      have := ge_of_tendsto' ((hG.2.2.1 z hzU).sub_const (g z)) fun k ↦ (hm k).2.le
      linarith
  rw [heq]
  exact MeasurableSet.iUnion fun m ↦ MeasurableSet.iInter fun k ↦
    (((hG.1 k).1.continuousOn.sub hg).isOpen_inter_preimage U.isOpen isOpen_Ioi).measurableSet

/-- **Locality for one slot over a smooth obstacle.** On `{u i₀ > g}` the limit
measures for `u` and for `u` with `max(u i₀, g)` in slot `i₀` coincide. -/
theorem restrict_eq_of_max_slot_obstacle {U : Opens (ComplexModel n)}
    {u : Fin n → ComplexModel n → ℝ} (i₀ : Fin n) {g : ComplexModel n → ℝ}
    (hg : IsSmoothPsdOn U g) {μ μ' : Measure (ComplexModel n)}
    (hμc : μ (U : Set (ComplexModel n))ᶜ = 0) (hμf : ∀ K, IsCompact K → K ⊆ U → μ K < ⊤)
    (hμ : ∀ F, IsAdmissible n U u F → TendstoMixed U F μ)
    (hμ'c : μ' (U : Set (ComplexModel n))ᶜ = 0) (hμ'f : ∀ K, IsCompact K → K ⊆ U → μ' K < ⊤)
    (hμ' : ∀ F, IsAdmissible n U (Function.update u i₀ fun z ↦ max (u i₀ z) (g z)) F →
      TendstoMixed U F μ')
    (hex : ∃ F, IsAdmissible n U u F) :
    μ.restrict {z | z ∈ U ∧ g z < u i₀ z} = μ'.restrict {z | z ∈ U ∧ g z < u i₀ z} := by
  classical
  obtain ⟨F, hF⟩ := id hex
  have hGw := hF.1 i₀
  set P := {z | z ∈ U ∧ g z < u i₀ z}
  have hPm : MeasurableSet P := hGw.measurableSet_lt_obstacle hg.1.continuousOn
  have hUm := U.isOpen.measurableSet
  set f : ComplexModel n → ENNReal := fun z ↦ ENNReal.ofReal (max (u i₀ z) (g z) - g z)
  have hfm (ν : Measure (ComplexModel n)) : AEMeasurable f (ν.restrict U) := by
    refine (aemeasurable_of_tendsto_metrizable_ae atTop
      (f := fun j z ↦ max (F i₀ j z) (g z) - g z) (fun j ↦ ?_) ?_).ennreal_ofReal
    · exact (((hGw.1 j).1.continuousOn.sup hg.1.continuousOn).sub
        hg.1.continuousOn).aemeasurable hUm
    · filter_upwards [ae_restrict_mem hUm] with z hz
      exact ((hGw.2.2.1 z hz).max tendsto_const_nhds).sub_const (g z)
  refine restrict_eq_of_max_weight_test_integral_eq hPm hfm ?_ ?_ hμf hμ'f ?_
  · intro K hK hKU
    obtain ⟨C, hC⟩ := hGw.exists_abs_le hK hKU
    exact ⟨C, fun _ hz => hGw.abs_le_of_mem hKU hC hz⟩
  · intro K hK hKU
    obtain ⟨D, hD⟩ := hK.exists_bound_of_continuousOn (hg.1.continuousOn.mono hKU)
    exact ⟨D, fun z hz => by simpa only [Real.norm_eq_abs] using hD z hz⟩
  · intro φ
    exact integral_mul_maxObstacleWeight_eq i₀ hg hμc hμf hμ hμ'c hμ'f hμ' hex
      φ.continuous φ.hasCompactSupport φ.tsupport_subset

theorem IsSmoothPsdOn.mono {U V : Opens (ComplexModel n)} {g : ComplexModel n → ℝ}
    (hg : IsSmoothPsdOn U g) (hVU : V ≤ U) : IsSmoothPsdOn V g :=
  ⟨hg.1.mono hVU, fun z hz ↦ hg.2 z (hVU hz)⟩

/-- The tuple with `max(·, g i)` applied in the slots of index below `k`. -/
def maxTupleObstacle (u g : Fin n → ComplexModel n → ℝ) (k : ℕ) :
    Fin n → ComplexModel n → ℝ :=
  fun i ↦ if i.val < k then fun z ↦ max (u i z) (g i z) else u i

theorem maxTupleObstacle_zero (u g : Fin n → ComplexModel n → ℝ) :
    maxTupleObstacle u g 0 = u := by
  funext i; simp [maxTupleObstacle]

theorem maxTupleObstacle_succ (u g : Fin n → ComplexModel n → ℝ) {k : ℕ} (hk : k < n) :
    maxTupleObstacle u g (k + 1) =
      Function.update (maxTupleObstacle u g k) ⟨k, hk⟩
        (fun z ↦ max (maxTupleObstacle u g k ⟨k, hk⟩ z) (g ⟨k, hk⟩ z)) := by
  funext i
  by_cases h : i = ⟨k, hk⟩
  · subst h; simp [maxTupleObstacle]
  · have hik : i.val ≠ k := fun h' ↦ h (Fin.ext h')
    simp only [maxTupleObstacle, Function.update_of_ne h]
    by_cases hlt : i.val < k
    · simp [hlt, show i.val < k + 1 by omega]
    · simp [hlt, show ¬ i.val < k + 1 by omega]

theorem maxTupleObstacle_apply_self (u g : Fin n → ComplexModel n → ℝ) {k : ℕ} (hk : k < n) :
    maxTupleObstacle u g k ⟨k, hk⟩ = u ⟨k, hk⟩ := by
  simp [maxTupleObstacle]

theorem exists_isAdmissible_maxTupleObstacle {U : Opens (ComplexModel n)}
    {u g : Fin n → ComplexModel n → ℝ} {F : Fin n → ℕ → ComplexModel n → ℝ}
    (hF : IsAdmissible n U u F) (hg : ∀ i, IsSmoothPsdOn U (g i)) (k : ℕ) :
    ∃ F', IsAdmissible n U (maxTupleObstacle u g k) F' := by
  classical
  refine ⟨fun i ↦ if i.val < k then
    (fun j ↦ scaledSmoothMax (maxScale j) (F i j) (g i)) else F i,
    fun i ↦ ?_, fun i hi ↦ absurd i.isLt (not_lt.mpr hi)⟩
  by_cases h : i.val < k
  · simpa [maxTupleObstacle, h] using (hF.1 i).scaledSmoothMax (hg i)
  · simpa [maxTupleObstacle, h] using hF.1 i

/-- **Locality in all slots over smooth obstacles, on a relatively compact set.** -/
theorem restrict_eq_maxTupleObstacle {U : Opens (ComplexModel n)}
    {u g : Fin n → ComplexModel n → ℝ} (hg : ∀ i, IsSmoothPsdOn U (g i))
    {μ : Measure (ComplexModel n)} (hμf : ∀ K, IsCompact K → K ⊆ U → μ K < ⊤)
    (hμ : ∀ F, IsAdmissible n U u F → TendstoMixed U F μ)
    (hex : ∃ F, IsAdmissible n U u F) :
    ∀ k, k ≤ n → ∀ μ' : Measure (ComplexModel n), μ' (U : Set (ComplexModel n))ᶜ = 0 →
      (∀ K, IsCompact K → K ⊆ U → μ' K < ⊤) →
      (∀ F, IsAdmissible n U (maxTupleObstacle u g k) F → TendstoMixed U F μ') →
      μ'.restrict {z | z ∈ U ∧ ∀ i, g i z < u i z} =
        μ.restrict {z | z ∈ U ∧ ∀ i, g i z < u i z} := by
  obtain ⟨F, hF⟩ := id hex
  set P := {z | z ∈ U ∧ ∀ i, g i z < u i z} with hP_def
  have hPU : P ⊆ U := fun z hz ↦ hz.1
  intro k
  induction k with
  | zero =>
    intro _ μ' _ hμ'f hμ'
    rw [maxTupleObstacle_zero] at hμ'
    have h := restrict_eq_of_claims le_rfl hμ'f hμf hμ' hμ hex
    rw [← Measure.restrict_restrict_of_subset hPU, h, Measure.restrict_restrict_of_subset hPU]
  | succ k ih =>
    intro hk μ' hμ'c hμ'f hμ'
    have hkn : k < n := hk
    obtain ⟨μk, hμkc, hμkf, hμkT⟩ := pClaim_all (n := n) U (maxTupleObstacle u g k)
    have hIH := ih hkn.le μk hμkc hμkf hμkT
    rw [maxTupleObstacle_succ u g hkn] at hμ'
    have hslot := restrict_eq_of_max_slot_obstacle (u := maxTupleObstacle u g k) ⟨k, hkn⟩
      (hg ⟨k, hkn⟩) hμkc hμkf hμkT hμ'c hμ'f hμ'
      (exists_isAdmissible_maxTupleObstacle hF hg k)
    have hPS : P ⊆ {z | z ∈ U ∧ g ⟨k, hkn⟩ z < maxTupleObstacle u g k ⟨k, hkn⟩ z} := fun z hz ↦
      ⟨hz.1, by rw [maxTupleObstacle_apply_self]; exact hz.2 _⟩
    rw [← hIH, ← Measure.restrict_restrict_of_subset hPS, ← hslot,
      Measure.restrict_restrict_of_subset hPS]

/-- **Max-obstacle locality on an open set.** Replacing every slot `v i` by
`max(v i, g i)`, with each `g i` smooth and positive semidefinite, does not
change the measure on the set where every slot strictly exceeds its obstacle. -/
theorem restrict_eq_of_max_obstacle {Ω : Opens (ComplexModel n)}
    {v w g : Fin n → ComplexModel n → ℝ} (hg : ∀ i, IsSmoothPsdOn Ω (g i))
    {μ ν : Measure (ComplexModel n)}
    (hμf : ∀ K, IsCompact K → K ⊆ Ω → μ K < ⊤) (hνf : ∀ K, IsCompact K → K ⊆ Ω → ν K < ⊤)
    (hμT : ∀ U, RelativelyCompactIn U Ω → ∃ F, IsAdmissible n U v F ∧ TendstoMixed U F μ)
    (hνT : ∀ U, RelativelyCompactIn U Ω → ∃ F, IsAdmissible n U w F ∧ TendstoMixed U F ν)
    (hmax : ∀ i, EqOn (w i) (fun z ↦ max (v i z) (g i z)) Ω) :
    ν.restrict {z | z ∈ Ω ∧ ∀ i, g i z < v i z} =
      μ.restrict {z | z ∈ Ω ∧ ∀ i, g i z < v i z} := by
  obtain ⟨U, -, hUrc, hUabs⟩ := exists_exhaustion Ω
  have hUΩ (m : ℕ) : U m ≤ Ω := subset_closure.trans (hUrc m).2
  have hQ : {z | z ∈ Ω ∧ ∀ i, g i z < v i z} =
      ⋃ m, {z | z ∈ U m ∧ ∀ i, g i z < v i z} := by
    ext z
    simp only [mem_ofPred_eq, mem_iUnion]
    constructor
    · rintro ⟨hzΩ, hz⟩
      obtain ⟨m, hm⟩ := hUabs {z} isCompact_singleton (singleton_subset_iff.2 hzΩ)
      exact ⟨m, hm rfl, hz⟩
    · rintro ⟨m, hzm, hz⟩
      exact ⟨hUΩ m hzm, hz⟩
  rw [hQ, Measure.restrict_iUnion_congr]
  intro m
  set V := U m
  set P := {z | z ∈ V ∧ ∀ i, g i z < v i z}
  have hPV : P ⊆ V := fun z hz ↦ hz.1
  have hgV (i : Fin n) : IsSmoothPsdOn V (g i) := (hg i).mono (hUΩ m)
  have hfinV (ρ : Measure (ComplexModel n)) (hρ : ∀ K, IsCompact K → K ⊆ Ω → ρ K < ⊤) :
      ∀ K, IsCompact K → K ⊆ V → ρ K < ⊤ := fun K hK hKV ↦ hρ K hK (hKV.trans (hUΩ m))
  obtain ⟨F, hF, hFT⟩ := hμT V (hUrc m)
  obtain ⟨μV, -, hμVf, hμVT⟩ := pClaim_all (n := n) V v
  have e1 : μ.restrict V = μV.restrict V :=
    restrict_eq_of_testFunction_integral_eq (hfinV μ hμf) hμVf fun φ ↦
      tendsto_nhds_unique (hFT φ φ.continuous φ.hasCompactSupport φ.tsupport_subset)
        (hμVT F hF φ φ.continuous φ.hasCompactSupport φ.tsupport_subset)
  obtain ⟨G, hG, hGT⟩ := hνT V (hUrc m)
  have hG' : IsAdmissible n V (maxTupleObstacle v g n) G := by
    refine ⟨fun i ↦ (hG.1 i).congr fun z hz ↦ ?_, fun i hi ↦ absurd i.isLt (not_lt.mpr hi)⟩
    simpa [maxTupleObstacle] using hmax i (hUΩ m hz)
  obtain ⟨νV, hνVc, hνVf, hνVT⟩ := pClaim_all (n := n) V (maxTupleObstacle v g n)
  have e2 : ν.restrict V = νV.restrict V :=
    restrict_eq_of_testFunction_integral_eq (hfinV ν hνf) hνVf fun φ ↦
      tendsto_nhds_unique (hGT φ φ.continuous φ.hasCompactSupport φ.tsupport_subset)
        (hνVT G hG' φ φ.continuous φ.hasCompactSupport φ.tsupport_subset)
  have hchain := restrict_eq_maxTupleObstacle hgV hμVf hμVT ⟨F, hF⟩ n le_rfl νV hνVc hνVf hνVT
  rw [← Measure.restrict_restrict_of_subset hPV, e2, Measure.restrict_restrict_of_subset hPV,
    hchain, ← Measure.restrict_restrict_of_subset hPV, ← e1,
    Measure.restrict_restrict_of_subset hPV]

/-- **Scalar max-obstacle locality** for bounded Bedford–Taylor measures. -/
theorem IsLocalBedfordTaylorMeasure.restrict_max_obstacle
    {Ω : Opens (ComplexModel n)} {v w g : ComplexModel n → ℝ}
    {μ ν : Measure (ComplexModel n)}
    (hμ : IsLocalBedfordTaylorMeasure Ω v μ)
    (hν : IsLocalBedfordTaylorMeasure Ω w ν) (hg : IsSmoothPsdOn Ω g)
    (hmax : EqOn w (fun z ↦ max (v z) (g z)) Ω) :
    ν.restrict {z | z ∈ Ω ∧ g z < v z} = μ.restrict {z | z ∈ Ω ∧ g z < v z} := by
  have h := restrict_eq_of_max_obstacle (v := fun _ ↦ v) (w := fun _ ↦ w) (g := fun _ ↦ g)
    (fun _ ↦ hg) hμ.2.2.1 hν.2.2.1
    (fun _ hU ↦ IsLocalBedfordTaylorMeasure.exists_isAdmissible_tendstoMixed hμ hU)
    (fun _ hU ↦ IsLocalBedfordTaylorMeasure.exists_isAdmissible_tendstoMixed hν hU) fun _ ↦ hmax
  have hS : {z | z ∈ Ω ∧ g z < v z} ⊆ {z | z ∈ Ω ∧ ∀ _ : Fin n, g z < v z} :=
    fun z hz ↦ ⟨hz.1, fun _ ↦ hz.2⟩
  rw [← Measure.restrict_restrict_of_subset hS, h, Measure.restrict_restrict_of_subset hS]

/-- **Mixed max-obstacle locality** for bounded Bedford–Taylor measures. -/
theorem IsLocalMixedBedfordTaylorMeasure.restrict_max_obstacle
    {Ω : Opens (ComplexModel n)} {v w g : Fin n → ComplexModel n → ℝ}
    {μ ν : Measure (ComplexModel n)}
    (hμ : IsLocalMixedBedfordTaylorMeasure Ω v μ)
    (hν : IsLocalMixedBedfordTaylorMeasure Ω w ν) (hg : ∀ i, IsSmoothPsdOn Ω (g i))
    (hmax : ∀ i, EqOn (w i) (fun z ↦ max (v i z) (g i z)) Ω) :
    ν.restrict {z | z ∈ Ω ∧ ∀ i, g i z < v i z} =
      μ.restrict {z | z ∈ Ω ∧ ∀ i, g i z < v i z} :=
  restrict_eq_of_max_obstacle hg hμ.2.2.1 hν.2.2.1
    (fun _ hU ↦ IsLocalMixedBedfordTaylorMeasure.exists_isAdmissible_tendstoMixed hμ hU)
    (fun _ hU ↦ IsLocalMixedBedfordTaylorMeasure.exists_isAdmissible_tendstoMixed hν hU) hmax

end SGPT.Foundations.Analysis.Pending.BedfordTaylor

end
