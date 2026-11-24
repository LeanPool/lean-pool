/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.JointDecreasingMaxWeight

/-! # Strict-superlevel maximum locality with two genuinely approximated branches

The complete mathematical statements and entire proofs preceded this file.
ROOT12 is strictly excluded from the fixed C90 batch.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff ComplexOrder

namespace SGPT.Foundations.Analysis.Pending.JointDecreasingMaxLocality

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere SmoothMax BedfordTaylor

variable {n : ℕ}

/-- Borel strict comparison is constructed from the original two finite limits. -/
theorem measurableSet_lt_of_joint_decApprox {U : Opens (ComplexModel n)}
    {u v : ComplexModel n → ℝ} {F G : ℕ → ComplexModel n → ℝ}
    (hF : IsDecApprox U u F) (hG : IsDecApprox U v G) :
    MeasurableSet {z | z ∈ U ∧ v z < u z} := by
  classical
  have hmeas {w : ComplexModel n → ℝ} {H : ℕ → ComplexModel n → ℝ}
      (hH : IsDecApprox U w H) :
      Measurable ((U : Set (ComplexModel n)).piecewise w (fun _ ↦ 0)) := by
    refine measurable_of_tendsto_metrizable
      (f := fun j ↦ (U : Set (ComplexModel n)).piecewise (H j) (fun _ ↦ 0))
      (fun j ↦ ((hH.1 j).1.continuousOn).measurable_piecewise
        continuousOn_const U.isOpen.measurableSet) (tendsto_pi_nhds.2 fun z ↦ ?_)
    by_cases hz : z ∈ (U : Set (ComplexModel n))
    · simpa only [Set.piecewise, ite_eq_left hz] using hH.2.2.1 z hz
    · simp only [Set.piecewise, ite_eq_right hz]
      exact tendsto_const_nhds
  have hlt := measurableSet_lt (hmeas hG) (hmeas hF)
  have heq : {z | z ∈ U ∧ v z < u z} = (U : Set (ComplexModel n)) ∩
      {z | (U : Set (ComplexModel n)).piecewise v (fun _ ↦ 0) z <
        (U : Set (ComplexModel n)).piecewise u (fun _ ↦ 0) z} := by
    ext z
    change (z ∈ (U : Set (ComplexModel n)) ∧ v z < u z) ↔
      (z ∈ (U : Set (ComplexModel n)) ∧
        (U : Set (ComplexModel n)).piecewise v (fun _ ↦ 0) z <
          (U : Set (ComplexModel n)).piecewise u (fun _ ↦ 0) z)
    by_cases hz : z ∈ (U : Set (ComplexModel n)) <;> simp [hz]
  rw [heq]
  exact U.isOpen.measurableSet.inter hlt

/-- The original positive comparison gap internally yields maximum slot locality. -/
theorem restrict_eq_of_joint_max_slot {U : Opens (ComplexModel n)}
    {u : Fin n → ComplexModel n → ℝ} (i₀ : Fin n) {g : ComplexModel n → ℝ}
    {J : ℕ → ComplexModel n → ℝ} (hg : IsDecApprox U g J) {μ μ' : Measure (ComplexModel n)}
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
  set P := {z | z ∈ U ∧ g z < u i₀ z} with hP_def
  have hPm : MeasurableSet P := measurableSet_lt_of_joint_decApprox hGw hg
  have hPU : P ⊆ U := fun z hz ↦ hz.1
  have hUm := U.isOpen.measurableSet
  set f : ComplexModel n → ENNReal := fun z ↦ ENNReal.ofReal (max (u i₀ z) (g z) - g z)
    with hf_def
  have hfm (ν : Measure (ComplexModel n)) : AEMeasurable f (ν.restrict U) := by
    refine (aemeasurable_of_tendsto_metrizable_ae atTop
      (f := fun j z ↦ max (F i₀ j z) (J j z) - J j z) (fun j ↦ ?_) ?_).ennreal_ofReal
    · exact (((hGw.1 j).1.continuousOn.sup (hg.1 j).1.continuousOn).sub
        (hg.1 j).1.continuousOn).aemeasurable hUm
    · filter_upwards [ae_restrict_mem hUm] with z hz
      exact ((hGw.2.2.1 z hz).max (hg.2.2.1 z hz)).sub (hg.2.2.1 z hz)
  set ρ := (μ.restrict U).withDensity f
  set ρ' := (μ'.restrict U).withDensity f
  have hfin (ν : Measure (ComplexModel n)) (hνf : ∀ K, IsCompact K → K ⊆ U → ν K < ⊤) :
      ∀ K, IsCompact K → K ⊆ U → (ν.restrict U).withDensity f K < ⊤ := by
    intro K hK hKU
    obtain ⟨C, hC⟩ := hGw.exists_abs_le hK hKU
    obtain ⟨D, hD⟩ := hg.exists_abs_le hK hKU
    rw [withDensity_apply _ hK.measurableSet]
    calc ∫⁻ z in K, f z ∂ν.restrict U ≤ ∫⁻ z in K, ENNReal.ofReal (C + D) ∂ν.restrict U := by
          refine setLIntegral_mono_ae measurable_const.aemeasurable ?_
          refine Eventually.of_forall fun z hz ↦ ENNReal.ofReal_le_ofReal ?_
          have h1 := hGw.abs_le_of_mem hKU hC hz
          have h2 := hg.abs_le_of_mem hKU hD hz
          have h1' := le_abs_self (u i₀ z)
          have h2' := neg_abs_le (g z)
          have h1n := abs_nonneg (u i₀ z)
          have h2n := abs_nonneg (g z)
          rcases le_total (u i₀ z) (g z) with h | h
          · rw [max_eq_right h, sub_self]
            linarith
          · rw [max_eq_left h]
            linarith
      _ = ENNReal.ofReal (C + D) * ν.restrict U K := by rw [setLIntegral_const]
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          ((Measure.restrict_apply_le _ _).trans_lt (hνf K hK hKU))
  have hint (ν : Measure (ComplexModel n)) (φ : ComplexModel n → ℝ)
      (hφU : tsupport φ ⊆ U) :
      ∫ z, φ z ∂(ν.restrict U).withDensity f = ∫ z, φ z * (max (u i₀ z) (g z) - g z) ∂ν := by
    rw [integral_withDensity_eq_integral_toReal_smul₀ (hfm ν)
      (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz ↦ by
      simp [image_eq_zero_of_notMem_tsupport fun h ↦ hz (hφU h)]]
    congr 1; funext z
    rw [ENNReal.toReal_ofReal (sub_nonneg.2 (le_max_right _ _)), smul_eq_mul, mul_comm]
  have hρ : ρ.restrict U = ρ'.restrict U :=
    restrict_eq_of_testFunction_integral_eq (hfin μ hμf) (hfin μ' hμ'f) fun φ ↦ by
      rw [hint μ φ φ.tsupport_subset, hint μ' φ φ.tsupport_subset]
      exact JointDecreasingMaxWeight.integral_mul_jointMaxWeight_eq i₀ hg hμc hμf hμ hμ'c hμ'f hμ'
        hex φ.continuous
        φ.hasCompactSupport φ.tsupport_subset
  have hself (ν : Measure (ComplexModel n)) :
      ((ν.restrict U).withDensity f).restrict U = (ν.restrict U).withDensity f := by
    rw [restrict_withDensity hUm, Measure.restrict_restrict hUm, inter_self]
  rw [hself, hself] at hρ
  have hinv (ν : Measure (ComplexModel n)) :
      ν.restrict P = (((ν.restrict U).withDensity f).restrict P).withDensity
        fun z ↦ (f z)⁻¹ := by
    rw [restrict_withDensity hPm, withDensity_inv_same₀ ((hfm ν).mono_measure
      Measure.restrict_le_self)]
    · rw [Measure.restrict_restrict_of_subset hPU]
    · filter_upwards [ae_restrict_mem hPm] with z hz
      simp only [hf_def, ne_eq, ENNReal.ofReal_eq_zero, not_le, sub_pos]
      exact lt_max_of_lt_left hz.2
    · exact Eventually.of_forall fun _ ↦ ENNReal.ofReal_ne_top
  rw [hinv μ, hinv μ', hρ]

end SGPT.Foundations.Analysis.Pending.JointDecreasingMaxLocality
