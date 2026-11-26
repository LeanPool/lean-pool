/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
public import Mathlib.Analysis.Complex.Norm
import LeanPool.GraphMinor.GM11.RadialChord
import Mathlib.Analysis.Complex.Basic

/-!
# Radial lines in the unit disc

For the stars in the feasibility discs of XII (3.1), page 245,
join the origin to each prescribed point of the unit circle. Norms
recover the parameter on each line. Thus distinct lines meet only
at the origin, and each meets the unit circle only at its endpoint.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- The closed radial line from the origin to a complex point. -/
@[expose] noncomputable def radialLine (z : ℂ) : Set ℂ :=
  range (fun t : unitInterval => t.val • z)

private theorem radialLine_norm {z : ℂ} (hz : ‖z‖ = 1) (t : unitInterval) :
    ‖t.val • z‖ = t.val := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg t.property.1, hz, mul_one]

/-- A radius to a unit-circle point is a line with the stated ends. -/
theorem isLineWithEnds_radialLine {z : ℂ} (hz : ‖z‖ = 1) :
    IsLineWithEnds (radialLine z) 0 z := by
  have hc : Continuous (fun t : unitInterval => t.val • z) := continuous_subtype_val.smul
    continuous_const
  have hi : Function.Injective (fun t : unitInterval => t.val • z) := by
    intro t s he
    apply Subtype.ext
    have hn := congrArg norm he
    rwa [radialLine_norm hz, radialLine_norm hz] at hn
  simpa only [radialLine, Set.Icc.coe_zero, Set.Icc.coe_one, zero_smul, one_smul]
    using GM11.isLine_range hc hi

/-- The radial line stays in the closed unit disc. -/
theorem radialLine_subset_unitDisc {z : ℂ} (hz : ‖z‖ = 1) :
    radialLine z ⊆ Metric.closedBall 0 1 := by
  rintro x ⟨t, rfl⟩
  rw [mem_closedBall_zero_iff, radialLine_norm hz]
  exact t.property.2

/-- A radial line meets the unit circle only at its outer endpoint. -/
theorem radialLine_inter_unitCircle {z : ℂ} (hz : ‖z‖ = 1) :
    radialLine z ∩ Metric.sphere 0 1 = {z} := by
  apply Subset.antisymm
  · rintro x ⟨⟨t, rfl⟩, hx⟩
    have ht : t.val = 1 := by
      have hn := mem_sphere_zero_iff_norm.mp hx
      rwa [radialLine_norm hz] at hn
    simpa only [ht, one_smul] using (mem_singleton z)
  · intro x hx
    rw [show x = z from hx]
    exact ⟨⟨1, one_smul ℝ z⟩, mem_sphere_zero_iff_norm.mpr hz⟩

/-- Distinct unit-circle endpoints give radial lines intersecting
exactly at their common centre. -/
theorem radialLine_inter_radialLine {z w : ℂ} (hz : ‖z‖ = 1) (hw : ‖w‖ = 1)
    (hzw : z ≠ w) : radialLine z ∩ radialLine w = {0} := by
  apply Subset.antisymm
  · rintro x ⟨⟨t, rfl⟩, ⟨s, he⟩⟩
    have hst : s.val = t.val := by
      have hn := congrArg norm he
      rwa [radialLine_norm hw, radialLine_norm hz] at hn
    have hst' : s = t := Subtype.ext hst
    cases hst'
    by_cases ht : t.val = 0
    · simpa only [ht, zero_smul] using (mem_singleton (0 : ℂ))
    · have hinv := congrArg (fun x : ℂ => t.val⁻¹ • x) he
      have hwz : w = z := by
        simpa only [smul_smul, inv_mul_cancel₀ ht, one_smul] using hinv
      exact False.elim (hzw hwz.symm)
  · rintro x rfl
    exact ⟨⟨0, zero_smul ℝ z⟩, ⟨0, zero_smul ℝ w⟩⟩

end GraphMinor.GM12
