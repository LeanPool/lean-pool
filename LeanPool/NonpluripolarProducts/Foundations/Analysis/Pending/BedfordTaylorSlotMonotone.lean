/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BedfordTaylorGauge

/-!
# Monotonicity of Bedford–Taylor limits under smooth positive slot increments

Adding a smooth function with positive semidefinite complex Hessian to one slot
does not decrease the Bedford–Taylor limit against nonnegative tests: the mixed
density is linear in the slot, and the extra term has only positive
semidefinite slots.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff ComplexOrder

namespace SGPT.Foundations.Analysis.Pending.BedfordTaylor

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere

variable {n : ℕ}

theorem IsDecApprox.add_smoothPsd {U : Opens (ComplexModel n)} {w : ComplexModel n → ℝ}
    {G : ℕ → ComplexModel n → ℝ} (hG : IsDecApprox U w G) {s : ComplexModel n → ℝ}
    (hs : IsSmoothPsdOn U s) :
    IsDecApprox U (fun z ↦ w z + s z) (fun k z ↦ G k z + s z) := by
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  refine ⟨fun k ↦ ⟨(hG.1 k).1.add hs.1, fun z hz ↦ ?_⟩, fun z hz k l hkl ↦ ?_,
    fun z hz ↦ (hG.2.2.1 z hz).add_const _, fun K hK hKU ↦ ?_⟩
  · change (complexHessian (G k + s) z).PosSemidef
    rw [complexHessian_add (((hG.1 k).1.contDiffAt (U.isOpen.mem_nhds hz)).of_le h2)
        ((hs.1.contDiffAt (U.isOpen.mem_nhds hz)).of_le h2)]
    exact ((hG.1 k).2 z hz).add (hs.2 z hz)
  · simpa using hG.2.1 z hz hkl
  · obtain ⟨m, hm⟩ := hG.2.2.2 K hK hKU
    obtain ⟨m', hm'⟩ := (hK.image_of_continuousOn (hs.1.continuousOn.mono hKU)).bddBelow
    exact ⟨m + m', by
      rintro _ ⟨z, hz, rfl⟩
      exact add_le_add (hm ⟨z, hz, rfl⟩) (hm' ⟨z, hz, rfl⟩)⟩

/-- **Slot monotonicity.** -/
theorem IsBTLimit.integral_le_add_smoothPsd {Ω : Opens (ComplexModel n)}
    {u : Fin n → ComplexModel n → ℝ} {μ ν : Measure (ComplexModel n)} (hμ : IsBTLimit Ω u μ)
    (i₀ : Fin n) {s : ComplexModel n → ℝ} (hs : IsSmoothPsdOn Ω s)
    (hν : IsBTLimit Ω (Function.update u i₀ fun z ↦ u i₀ z + s z) ν)
    {φ : ComplexModel n → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hφΩ : tsupport φ ⊆ Ω) (hφ0 : ∀ z, 0 ≤ φ z) :
    ∫ z, φ z ∂μ ≤ ∫ z, φ z ∂ν := by
  classical
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  obtain ⟨V, hVo, hKV, hVΩ, hVc⟩ :=
    exists_open_between_and_isCompact_closure hφc Ω.isOpen hφΩ
  set U : Opens (ComplexModel n) := ⟨V, hVo⟩
  have hU : RelativelyCompactIn U Ω := ⟨hVc, hVΩ⟩
  have hUΩ : U ≤ Ω := subset_closure.trans hVΩ
  have hsU : IsSmoothPsdOn U s := ⟨hs.1.mono hUΩ, fun z hz ↦ hs.2 z (hUΩ hz)⟩
  obtain ⟨F, hF, hFT⟩ := hμ.2.2 U hU
  set F' : Fin n → ℕ → ComplexModel n → ℝ :=
    Function.update F i₀ (fun k z ↦ F i₀ k z + s z) with hF'_def
  have hF' : IsAdmissible n U (Function.update u i₀ fun z ↦ u i₀ z + s z) F' := by
    refine ⟨fun i ↦ ?_, fun i hi ↦ absurd i.isLt (not_lt.mpr hi)⟩
    by_cases h : i = i₀
    · subst h
      simpa [hF'_def] using (hF.1 i).add_smoothPsd hsU
    · simpa [hF'_def, Function.update_of_ne h] using hF.1 i
  have hT' := hν.tendstoMixed hU hF'
  have hDcF (k : ℕ) := continuousOn_mixedDensity fun i ↦ ((hF.1 i).1 k).1
  have hDcF' (k : ℕ) := continuousOn_mixedDensity fun i ↦ ((hF'.1 i).1 k).1
  refine le_of_tendsto_of_tendsto (hFT φ hφ hφc hKV) (hT' φ hφ hφc hKV)
    (Eventually.of_forall fun k ↦ ?_)
  refine integral_mono (integrable_mul_of_continuousOn (hDcF k) hφ hφc hKV)
    (integrable_mul_of_continuousOn (hDcF' k) hφ hφc hKV) fun z ↦ ?_
  by_cases hz : z ∈ (U : Set (ComplexModel n))
  · refine mul_le_mul_of_nonneg_left ?_ (hφ0 z)
    have hslots : (fun i ↦ F' i k) =
        Function.update (fun i ↦ F i k) i₀ (fun y ↦ F i₀ k y + 1 * s y) := by
      funext i
      by_cases h : i = i₀
      · subst h; simp [hF'_def]
      · simp [hF'_def, Function.update_of_ne h]
    have ha := (((hF.1 i₀).1 k).1.contDiffAt (U.isOpen.mem_nhds hz)).of_le h2
    have hb := (hsU.1.contDiffAt (U.isOpen.mem_nhds hz)).of_le h2
    rw [hslots, mixedDensity_update_add_smul i₀ ha hb, Function.update_eq_self, one_mul]
    have hnn : 0 ≤ mixedDensity (Function.update (fun i ↦ F i k) i₀ s) z := by
      refine mixedDensity_nonneg fun i ↦ ?_
      by_cases h : i = i₀
      · subst h; simpa using hsU.2 z hz
      · simpa [Function.update_of_ne h] using ((hF.1 i).1 k).2 z hz
    linarith
  · simp [image_eq_zero_of_notMem_tsupport fun h ↦ hz (hKV h)]

end SGPT.Foundations.Analysis.Pending.BedfordTaylor
