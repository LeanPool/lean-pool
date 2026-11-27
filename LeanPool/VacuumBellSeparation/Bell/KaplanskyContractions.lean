/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.KaplanskyEffects
public import LeanPool.VacuumBellSeparation.Bell.Cells

/-! # Actual selfadjoint contraction approximation through effects -/

@[expose] public section

namespace VacuumBellSeparation

open Filter Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem two_smul_effect_sub_one_contraction {E : H →L[ℂ] H} (hE : 0 ≤ E) (hE1 : E ≤ 1) :
    IsSelfAdjoint ((2 : ℝ) • E - 1) ∧ ‖(2 : ℝ) • E - 1‖ ≤ 1 := by
  have he : cfc (fun x : ℝ => 2 * x - 1) E = (2 : ℝ) • E - 1 := by
    rw [cfc_sub (fun x : ℝ => 2 * x) (fun _ : ℝ => 1) E
      (continuous_const.mul continuous_id).continuousOn continuous_const.continuousOn,
      cfc_const_mul_id 2 E hE.isSelfAdjoint, cfc_const_one ℝ E hE.isSelfAdjoint]
  rw [← he]
  refine ⟨cfc_predicate _ _, norm_cfc_le zero_le_one ?_⟩
  intro x hx
  have hb := effect_spectrum_bounds hE hE1 hx
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ⟨by linarith [hb.1], by linarith [hb.2]⟩

theorem half_one_add_contraction_effect {A : H →L[ℂ] H} (hA : IsSelfAdjoint A) (hn : ‖A‖ ≤ 1) :
    0 ≤ (1 / 2 : ℝ) • (1 + A) ∧ (1 / 2 : ℝ) • (1 + A) ≤ 1 := by
  have hp := ContinuousLinearMap.nonneg_iff_isPositive.mpr
    (isPositive_one_add_of_saContraction hA hn)
  have hm := ContinuousLinearMap.nonneg_iff_isPositive.mpr
    (isPositive_one_sub_of_saContraction hA hn)
  refine ⟨smul_nonneg (by norm_num) hp, sub_nonneg.mp ?_⟩
  have he : 1 - (1 / 2 : ℝ) • (1 + A) = (1 / 2 : ℝ) • (1 - A) := by module
  rw [he]
  exact smul_nonneg (by norm_num) hm

theorem exists_saContraction_strong_approximation
    (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (hfc : ∀ (f : ℝ → ℝ) (A : H →L[ℂ] H), A ∈ S → cfc f A ∈ S)
    {A : H →L[ℂ] H} (hA : A ∈ generatedVNA (S : Set (H →L[ℂ] H)))
    (hsa : IsSelfAdjoint A) (hn : ‖A‖ ≤ 1) :
    ∃ As : (Finset H × ℕ) → (H →L[ℂ] H),
      (∀ i, As i ∈ S ∧ IsSelfAdjoint (As i) ∧ ‖As i‖ ≤ 1) ∧
        ∀ x : H, Tendsto (fun i => As i x) atTop (𝓝 (A x)) := by
  let E := (1 / 2 : ℝ) • (1 + A)
  have hE : E ∈ generatedVNA (S : Set (H →L[ℂ] H)) :=
    starSubalgebra_real_smul_mem (generatedVNA (S : Set (H →L[ℂ] H))).toStarSubalgebra
      (add_mem (one_mem _) hA) _
  have hb := half_one_add_contraction_effect hsa hn
  obtain ⟨Es, hEs, hlim⟩ := exists_effect_strong_approximation S hfc hE hb.1 hb.2
  refine ⟨fun i => (2 : ℝ) • Es i - 1, ?_, ?_⟩
  · intro i
    exact ⟨S.sub_mem (starSubalgebra_real_smul_mem S (hEs i).1 2) S.one_mem,
      two_smul_effect_sub_one_contraction (hEs i).2.1 (hEs i).2.2⟩
  · intro x
    have he : (2 : ℝ) • E - 1 = A := by dsimp only [E]; module
    have ht := ((hlim x).const_smul (2 : ℝ)).sub (tendsto_const_nhds (x := x))
    change Tendsto (fun i => ((2 : ℝ) • Es i - 1) x) atTop (𝓝 (((2 : ℝ) • E - 1) x)) at ht
    simpa only [he] using ht

end VacuumBellSeparation
