/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BedfordTaylorMaxObstacle

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
  set P := {z | z ∈ U ∧ g z < u i₀ z}
  have hPm : MeasurableSet P := measurableSet_lt_of_joint_decApprox hGw hg
  have hUm := U.isOpen.measurableSet
  set f : ComplexModel n → ENNReal := fun z ↦ ENNReal.ofReal (max (u i₀ z) (g z) - g z)
  have hfm (ν : Measure (ComplexModel n)) : AEMeasurable f (ν.restrict U) := by
    refine (aemeasurable_of_tendsto_metrizable_ae atTop
      (f := fun j z ↦ max (F i₀ j z) (J j z) - J j z) (fun j ↦ ?_) ?_).ennreal_ofReal
    · exact (((hGw.1 j).1.continuousOn.sup (hg.1 j).1.continuousOn).sub
        (hg.1 j).1.continuousOn).aemeasurable hUm
    · filter_upwards [ae_restrict_mem hUm] with z hz
      exact ((hGw.2.2.1 z hz).max (hg.2.2.1 z hz)).sub (hg.2.2.1 z hz)
  refine BedfordTaylor.restrict_eq_of_max_weight_test_integral_eq hPm hfm ?_ ?_ hμf hμ'f ?_
  · intro K hK hKU
    obtain ⟨C, hC⟩ := hGw.exists_abs_le hK hKU
    exact ⟨C, fun _ hz => hGw.abs_le_of_mem hKU hC hz⟩
  · intro K hK hKU
    obtain ⟨D, hD⟩ := hg.exists_abs_le hK hKU
    exact ⟨D, fun _ hz => hg.abs_le_of_mem hKU hD hz⟩
  · intro φ
    exact JointDecreasingMaxWeight.integral_mul_jointMaxWeight_eq i₀ hg hμc hμf hμ hμ'c hμ'f hμ' hex
      φ.continuous φ.hasCompactSupport φ.tsupport_subset

end SGPT.Foundations.Analysis.Pending.JointDecreasingMaxLocality
