/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Collar

/-!
# Joining two collars

Three nested closed discs in a surface must share one radius coordinate. Keep the collar of the
inner disc on radii at most two, and on radii from two to three use the collar of the middle disc
after subtracting one from the radius.
The change of radius uses a denominator bounded below by two, so it gives a continuous map of the
plane, also at zero. The collars agree along their common circle.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Metric

/-- The outer-annulus change of radius used to join two collars. -/
noncomputable def collarOuterStep (z : ℂ) : ℂ :=
  ((max 2 ‖z‖ - 1) / max 2 ‖z‖ : ℝ) • z

theorem continuous_collarOuterStep : Continuous collarOuterStep := by
  have hf : Continuous (fun z : ℂ => (max 2 ‖z‖ - 1) / max 2 ‖z‖) := by
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro z
      have h : (0 : ℝ) < max 2 ‖z‖ := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
      exact h.ne'
  exact hf.smul continuous_id

theorem collarOuterStep_norm {z : ℂ} (hz : 2 ≤ ‖z‖) :
    ‖collarOuterStep z‖ = ‖z‖ - 1 := by
  have hn : 0 < ‖z‖ := lt_of_lt_of_le (by norm_num) hz
  rw [collarOuterStep, max_eq_right hz, norm_smul, Real.norm_eq_abs,
    abs_of_pos (div_pos (by linarith) hn), div_mul_cancel₀ _ hn.ne']

theorem collarOuterStep_injOn : InjOn collarOuterStep {z : ℂ | 2 ≤ ‖z‖} := by
  intro z hz w hw heq
  change 2 ≤ ‖z‖ at hz
  change 2 ≤ ‖w‖ at hw
  have hnorm : ‖z‖ = ‖w‖ := by
    have h := congrArg norm heq
    rw [collarOuterStep_norm hz, collarOuterStep_norm hw] at h
    linarith
  have hscale : (‖z‖ - 1) / ‖z‖ ≠ 0 := by
    apply ne_of_gt
    exact div_pos (by linarith [hz]) (by linarith [hz])
  simp only [collarOuterStep, max_eq_right hz, ← hnorm] at heq
  exact (smul_right_injective _ hscale) heq

theorem collarOuterStep_two {z : ℂ} (hz : ‖z‖ = 2) :
    collarOuterStep z = (1 / 2 : ℝ) • z := by
  simp only [collarOuterStep, hz, max_self]
  norm_num

/-- The inverse radius change on the outer annulus. -/
theorem exists_collarOuterStep_preimage {w : ℂ} (hw : 1 ≤ ‖w‖) :
    ∃ z : ℂ, ‖z‖ = ‖w‖ + 1 ∧ collarOuterStep z = w := by
  have hn : 0 < ‖w‖ := lt_of_lt_of_le zero_lt_one hw
  let z : ℂ := ((‖w‖ + 1) / ‖w‖ : ℝ) • w
  have hz : ‖z‖ = ‖w‖ + 1 := by
    rw [show z = ((‖w‖ + 1) / ‖w‖ : ℝ) • w from rfl, norm_smul, Real.norm_eq_abs,
      abs_of_pos (div_pos (by linarith) hn), div_mul_cancel₀ _ hn.ne']
  refine ⟨z, hz, ?_⟩
  have hz2 : 2 ≤ ‖z‖ := by rw [hz]; linarith
  rw [collarOuterStep, max_eq_right hz2, hz]
  dsimp only [z]
  rw [smul_smul]
  have heq : (‖w‖ + 1 - 1) / (‖w‖ + 1) * ((‖w‖ + 1) / ‖w‖) = 1 := by
    field_simp
    ring
  rw [heq, one_smul]

/-- Join two compatible collars into coordinates in which the three
nested discs have radii one, two, and three. -/
theorem exists_joined_collar_coordinates
    {S : Type*} [TopologicalSpace S] {A B E : Set S}
    (c₁ c₂ : ℂ → S)
    (hc₁ : ContinuousOn c₁ (closedBall 0 2)) (hi₁ : InjOn c₁ (closedBall 0 2))
    (hc₂ : ContinuousOn c₂ (closedBall 0 2)) (hi₂ : InjOn c₂ (closedBall 0 2))
    (hA : c₁ '' closedBall 0 1 = A) (hB₁ : c₁ '' closedBall 0 2 = B)
    (hB₂ : c₂ '' closedBall 0 1 = B) (hE : c₂ '' closedBall 0 2 = E)
    (hbd : c₂ '' sphere 0 2 = discBd E)
    (hcompat : ∀ z : ℂ, ‖z‖ = 2 → c₁ z = c₂ (collarOuterStep z)) :
    ∃ c : ℂ → S, ContinuousOn c (closedBall 0 3) ∧ InjOn c (closedBall 0 3) ∧
      c '' closedBall 0 1 = A ∧ c '' closedBall 0 2 = B ∧
      c '' closedBall 0 3 = E ∧ c '' sphere 0 3 = discBd E := by
  classical
  let c : ℂ → S := fun z => if ‖z‖ ≤ 2 then c₁ z else c₂ (collarOuterStep z)
  have hcinner : ∀ z, ‖z‖ ≤ 2 → c z = c₁ z := fun z hz => ite_eq_left hz
  have hcouter : ∀ z, 2 ≤ ‖z‖ → c z = c₂ (collarOuterStep z) := by
    intro z hz
    rcases eq_or_lt_of_le hz with heq | hlt
    · rw [hcinner z heq.ge]
      exact hcompat z heq.symm
    · exact ite_eq_right (not_le.mpr hlt)
  have hJ : ∀ z, 2 ≤ ‖z‖ → ‖z‖ ≤ 3 → collarOuterStep z ∈ closedBall 0 2 := by
    intro z hlo hhi
    rw [mem_closedBall_zero_iff, collarOuterStep_norm hlo]
    linarith
  have hBc₂ : ∀ w ∈ closedBall (0 : ℂ) 2, c₂ w ∈ B → ‖w‖ ≤ 1 := by
    intro w hw hBw
    obtain ⟨v, hv, heq⟩ := hB₂.symm ▸ hBw
    have hvw := hi₂ (closedBall_subset_closedBall (by norm_num) hv) hw heq
    exact hvw ▸ mem_closedBall_zero_iff.mp hv
  have hccont : ContinuousOn c (closedBall 0 3) := by
    let R : Set ℂ := closedBall 0 3 ∩ {z | 2 ≤ ‖z‖}
    have hR : IsClosed R := isClosed_closedBall.inter (isClosed_le continuous_const continuous_norm)
    have hcontinner : ContinuousOn c (closedBall 0 2) :=
      hc₁.congr (fun z hz => hcinner z (mem_closedBall_zero_iff.mp hz))
    have hcontouter : ContinuousOn c R := by
      have hmap : MapsTo collarOuterStep R (closedBall 0 2) := fun z hz =>
        hJ z hz.2 (mem_closedBall_zero_iff.mp hz.1)
      exact (hc₂.comp continuous_collarOuterStep.continuousOn hmap).congr
        (fun z hz => hcouter z hz.2)
    have hcover : closedBall (0 : ℂ) 2 ∪ R = closedBall 0 3 := by
      ext z
      constructor
      · rintro (hz | hz)
        · exact closedBall_subset_closedBall (by norm_num) hz
        · exact hz.1
      · intro hz
        by_cases hz2 : ‖z‖ ≤ 2
        · exact Or.inl (mem_closedBall_zero_iff.mpr hz2)
        · exact Or.inr ⟨hz, (le_of_not_ge hz2)⟩
    exact hcover ▸ hcontinner.union_of_isClosed hcontouter isClosed_closedBall hR
  have hcB : c '' closedBall 0 2 = B := by
    rw [← hB₁]
    exact image_congr (fun z hz => hcinner z (mem_closedBall_zero_iff.mp hz))
  have hcA : c '' closedBall 0 1 = A := by
    rw [← hA]
    exact image_congr (fun z hz => hcinner z ((mem_closedBall_zero_iff.mp hz).trans (by norm_num)))
  have hcEsub : c '' closedBall 0 3 ⊆ E := by
    rintro _ ⟨z, hz, rfl⟩
    by_cases hz2 : ‖z‖ ≤ 2
    · rw [hcinner z hz2]
      have hzB : c₁ z ∈ B := hB₁ ▸ mem_image_of_mem c₁ (mem_closedBall_zero_iff.mpr hz2)
      obtain ⟨w, hw, heq⟩ := hB₂.symm ▸ hzB
      rw [← heq]
      exact hE ▸ mem_image_of_mem c₂ (closedBall_subset_closedBall (by norm_num) hw)
    · rw [hcouter z (le_of_not_ge hz2)]
      exact hE ▸ mem_image_of_mem c₂ (hJ z (le_of_not_ge hz2) (mem_closedBall_zero_iff.mp hz))
  have hcEsurj : E ⊆ c '' closedBall 0 3 := by
    intro x hx
    obtain ⟨w, hw, rfl⟩ := hE.symm ▸ hx
    by_cases hw1 : ‖w‖ ≤ 1
    · have hwB : c₂ w ∈ B := hB₂ ▸ mem_image_of_mem c₂ (mem_closedBall_zero_iff.mpr hw1)
      obtain ⟨z, hz, heq⟩ := hcB.symm ▸ hwB
      exact ⟨z, closedBall_subset_closedBall (by norm_num) hz, heq⟩
    · obtain ⟨z, hzn, hzJ⟩ := exists_collarOuterStep_preimage (le_of_not_ge hw1)
      have hz2 : 2 ≤ ‖z‖ := by rw [hzn]; linarith [le_of_not_ge hw1]
      refine ⟨z, mem_closedBall_zero_iff.mpr ?_, ?_⟩
      · rw [hzn]
        linarith [mem_closedBall_zero_iff.mp hw]
      · rw [hcouter z hz2, hzJ]
  have hci : InjOn c (closedBall 0 3) := by
    intro z hz w hw heq
    by_cases hz2 : ‖z‖ ≤ 2
    · by_cases hw2 : ‖w‖ ≤ 2
      · rw [hcinner z hz2, hcinner w hw2] at heq
        exact hi₁ (mem_closedBall_zero_iff.mpr hz2) (mem_closedBall_zero_iff.mpr hw2) heq
      · have hwlo : 2 ≤ ‖w‖ := le_of_not_ge hw2
        have hzB : c z ∈ B := hcB ▸ mem_image_of_mem c (mem_closedBall_zero_iff.mpr hz2)
        rw [heq, hcouter w hwlo] at hzB
        have hn := hBc₂ _ (hJ w hwlo (mem_closedBall_zero_iff.mp hw)) hzB
        rw [collarOuterStep_norm hwlo] at hn
        exact False.elim (hw2 (by linarith))
    · have hzlo : 2 ≤ ‖z‖ := le_of_not_ge hz2
      by_cases hw2 : ‖w‖ ≤ 2
      · have hwB : c w ∈ B := hcB ▸ mem_image_of_mem c (mem_closedBall_zero_iff.mpr hw2)
        rw [← heq, hcouter z hzlo] at hwB
        have hn := hBc₂ _ (hJ z hzlo (mem_closedBall_zero_iff.mp hz)) hwB
        rw [collarOuterStep_norm hzlo] at hn
        exact False.elim (hz2 (by linarith))
      · have hwlo : 2 ≤ ‖w‖ := le_of_not_ge hw2
        rw [hcouter z hzlo, hcouter w hwlo] at heq
        exact collarOuterStep_injOn hzlo hwlo
          (hi₂ (hJ z hzlo (mem_closedBall_zero_iff.mp hz))
            (hJ w hwlo (mem_closedBall_zero_iff.mp hw)) heq)
  refine ⟨c, hccont, hci, hcA, hcB, hcEsub.antisymm hcEsurj, ?_⟩
  rw [← hbd]
  apply Set.Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    have hzn : ‖z‖ = 3 := mem_sphere_zero_iff_norm.mp hz
    have hz2 : 2 ≤ ‖z‖ := by rw [hzn]; norm_num
    refine ⟨collarOuterStep z, ?_, (hcouter z hz2).symm⟩
    rw [mem_sphere_zero_iff_norm, collarOuterStep_norm hz2, hzn]
    norm_num
  · rintro _ ⟨w, hw, rfl⟩
    have hwn : ‖w‖ = 2 := mem_sphere_zero_iff_norm.mp hw
    obtain ⟨z, hzn, hzJ⟩ := exists_collarOuterStep_preimage (by rw [hwn]; norm_num)
    have hz3 : ‖z‖ = 3 := by rw [hzn, hwn]; norm_num
    refine ⟨z, mem_sphere_zero_iff_norm.mpr hz3, ?_⟩
    rw [hcouter z (by rw [hz3]; norm_num), hzJ]

end GraphMinor.Surface
