/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BedfordTaylorSlotAdd

/-!
# Positive homogeneity of the mixed Bedford–Taylor measure in one slot

If one slot of the tuple is a nonnegative multiple `s * a` of a locally bounded
plurisubharmonic function, the mixed Bedford–Taylor measure is `s` times the
measure obtained by putting `a` in that slot. Scaling a smooth approximation of
`a` by `s` gives an admissible family for `s * a`, and the mixed densities are
linear in each slot, so the weak limit is scaled by `s`; uniqueness of
Bedford–Taylor limits then identifies the two measures.

This is the measure-level form of slot homogeneity in the algebra of bounded
Bedford–Taylor products (BEGZ §1.2, Demailly III.3).
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff ComplexOrder

namespace SGPT.Foundations.Analysis.Pending.BedfordTaylor

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere

variable {n : ℕ}

/-- Nonnegative multiples of decreasing smooth approximations approximate the
multiple. -/
theorem IsDecApprox.const_mul {U : Opens (ComplexModel n)} {a : ComplexModel n → ℝ}
    {A : ℕ → ComplexModel n → ℝ} (hA : IsDecApprox U a A) {s : ℝ} (hs : 0 ≤ s) :
    IsDecApprox U (fun z ↦ s * a z) (fun k z ↦ s * A k z) := by
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  refine ⟨fun k ↦ ⟨contDiffOn_const.mul (hA.1 k).1, fun z hz ↦ ?_⟩, fun z hz k l hkl ↦ ?_,
    fun z hz ↦ (hA.2.2.1 z hz).const_mul s, fun K hK hKU ↦ ?_⟩
  · have hAz : ContDiffAt ℝ 2 (A k) z := ((hA.1 k).1.contDiffAt (U.isOpen.mem_nhds hz)).of_le h2
    change (complexHessian (s • A k) z).PosSemidef
    rw [complexHessian_smul hAz]
    exact ((hA.1 k).2 z hz).smul (Complex.zero_le_real.mpr hs)
  · exact mul_le_mul_of_nonneg_left (hA.2.1 z hz hkl) hs
  · obtain ⟨m, hm⟩ := hA.2.2.2 K hK hKU
    refine ⟨s * m, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact mul_le_mul_of_nonneg_left (hm ⟨z, hz, rfl⟩) hs

/-- The mixed density is homogeneous in the chosen slot. -/
theorem mixedDensity_update_const_mul {f : Fin n → ComplexModel n → ℝ} (i₀ : Fin n)
    {a : ComplexModel n → ℝ} {z : ComplexModel n} (ha : ContDiffAt ℝ 2 a z) (s : ℝ) :
    mixedDensity (Function.update f i₀ fun y ↦ s * a y) z =
      s * mixedDensity (Function.update f i₀ a) z := by
  have h := mixedDensity_update_add_smul (f := f) i₀ ha ha (s - 1)
  have hfun : (fun y ↦ a y + (s - 1) * a y) = fun y ↦ s * a y := by funext y; ring
  rw [hfun] at h
  rw [h]
  ring

/-- **Existence under scaling a slot.** If `μa` is the Bedford–Taylor limit for
the tuple with `a` in slot `i₀`, then `s • μa` is the limit for the tuple with
`s * a` in that slot, for every `s ≥ 0`. -/
theorem IsBTLimit.const_mul_slot {Ω : Opens (ComplexModel n)} {v : Fin n → ComplexModel n → ℝ}
    (i₀ : Fin n) {a : ComplexModel n → ℝ} {s : ℝ} (hs : 0 ≤ s) {μa : Measure (ComplexModel n)}
    (hμa : IsBTLimit Ω (Function.update v i₀ a) μa) :
    IsBTLimit Ω (Function.update v i₀ fun z ↦ s * a z) (ENNReal.ofReal s • μa) := by
  classical
  refine ⟨?_, fun K hK hKΩ ↦ ?_, fun U hU ↦ ?_⟩
  · rw [smul_apply, hμa.1, smul_zero]
  · rw [smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hμa.2.1 K hK hKΩ)
  obtain ⟨F, hF, hFT⟩ := hμa.2.2 U hU
  have hA : IsDecApprox U a (F i₀) := by simpa using hF.1 i₀
  set F' : Fin n → ℕ → ComplexModel n → ℝ :=
    Function.update F i₀ (fun k z ↦ s * F i₀ k z) with hF'_def
  have hF' : IsAdmissible n U (Function.update v i₀ fun z ↦ s * a z) F' := by
    refine ⟨fun i ↦ ?_, fun i hi ↦ absurd i.isLt (not_lt.mpr hi)⟩
    by_cases h : i = i₀
    · subst h; simpa [hF'_def] using hA.const_mul hs
    · simpa [hF'_def, Function.update_of_ne h] using hF.1 i
  refine ⟨F', hF', fun φ hφc hφs hφU ↦ ?_⟩
  have hdens (k : ℕ) (z : ComplexModel n) (hz : z ∈ (U : Set (ComplexModel n))) :
      mixedDensity (fun i ↦ F' i k) z = s * mixedDensity (fun i ↦ F i k) z := by
    have h2' : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
    have hAz : ContDiffAt ℝ 2 (F i₀ k) z :=
      ((hA.1 k).1.contDiffAt (U.isOpen.mem_nhds hz)).of_le h2'
    have hupd : (fun i ↦ F' i k) =
        Function.update (fun i ↦ F i k) i₀ (fun y ↦ s * F i₀ k y) := by
      funext i
      by_cases h : i = i₀
      · subst h; simp [hF'_def]
      · simp [hF'_def, Function.update_of_ne h]
    have hmul := mixedDensity_update_const_mul (f := fun i ↦ F i k) i₀ hAz s
    rw [Function.update_eq_self] at hmul
    rw [hupd, hmul]
  have hint (k : ℕ) : ∫ z, φ z * mixedDensity (fun i ↦ F' i k) z =
      s * ∫ z, φ z * mixedDensity (fun i ↦ F i k) z := by
    rw [← integral_const_mul]
    congr 1
    funext z
    by_cases hz : z ∈ (U : Set (ComplexModel n))
    · rw [hdens k z hz]; ring
    · simp [image_eq_zero_of_notMem_tsupport fun h ↦ hz (hφU h)]
  rw [integral_smul_measure, ENNReal.toReal_ofReal hs, smul_eq_mul]
  simpa only [hint] using (hFT φ hφc hφs hφU).const_mul s

/-- **Slot homogeneity of Bedford–Taylor limits.** The limit for the tuple with
`s * a` in slot `i₀` is `s` times the limit for `a` in that slot. -/
theorem IsBTLimit.smul_slot {Ω : Opens (ComplexModel n)} {v : Fin n → ComplexModel n → ℝ}
    (i₀ : Fin n) {a : ComplexModel n → ℝ} {s : ℝ} (hs : 0 < s) {μ μa : Measure (ComplexModel n)}
    (hμ : IsBTLimit Ω (Function.update v i₀ fun z ↦ s * a z) μ)
    (hμa : IsBTLimit Ω (Function.update v i₀ a) μa) :
    μ = ENNReal.ofReal s • μa :=
  hμ.unique (hμa.const_mul_slot i₀ hs.le)

end SGPT.Foundations.Analysis.Pending.BedfordTaylor

end
