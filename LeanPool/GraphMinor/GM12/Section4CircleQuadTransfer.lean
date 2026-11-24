/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section4CircleQuad
import LeanPool.GraphMinor.GM19.CircleLift
import LeanPool.GraphMinor.GM12.Section4DiscTwist

/-!
# Matching a transported crossing quadruple

For XII (4.5), claim (1), page 253, an ambient disc match may
keep or reverse the boundary direction. After either case,
a boundary twist preserving direction can send its four
crossing marks to the prescribed four marks, allowing the
second and fourth marks to exchange places. Both choices
preserve the two opposite pairs. Use the increasing or
decreasing lift of the inverse circle map to distinguish
the cases, then apply the ordered four-point adjustment.
-/

public section

namespace GraphMinor.GM12

open Surface

private theorem inv_ee (t : ℝ) : (ee t)⁻¹ = ee (-t) := by
  unfold ee
  rw [← Circle.exp_neg]
  congr 1
  ring

private theorem inv_ee_quarter : (ee (1 / 4))⁻¹ = ee (3 / 4) := by
  rw [inv_ee]
  apply ee_eq_iff.mpr
  exact ⟨-1, by norm_num⟩

private theorem inv_ee_half : (ee (1 / 2))⁻¹ = ee (1 / 2) := by
  rw [inv_ee]
  apply ee_eq_iff.mpr
  exact ⟨-1, by norm_num⟩

private theorem inv_ee_three_quarters : (ee (3 / 4))⁻¹ = ee (1 / 4) := by
  rw [inv_ee]
  apply ee_eq_iff.mpr
  exact ⟨-1, by norm_num⟩

/-- A circle homeomorphism's transported quarter-turn marks
can be matched to four ordered marks by a direction-preserving
map, either in the stated order or with the second and fourth
exchanged. This is the opposite-pair matching needed in
XII (4.5), claim (1), page 253. -/
theorem exists_circle_quad_transfer (τ : Circle ≃ₜ Circle)
    {b₀ b₁ b₂ b₃ : ℝ} (hb₀₁ : b₀ < b₁) (hb₁₂ : b₁ < b₂)
    (hb₂₃ : b₂ < b₃) (hb₃ : b₃ < b₀ + 1) :
    ∃ g : Circle ≃ₜ Circle, PreservesCircleOrientation g ∧
      ((g (τ (ee 0)) = ee b₀ ∧ g (τ (ee (1 / 4))) = ee b₁ ∧
        g (τ (ee (1 / 2))) = ee b₂ ∧ g (τ (ee (3 / 4))) = ee b₃) ∨
       (g (τ (ee 0)) = ee b₀ ∧ g (τ (ee (1 / 4))) = ee b₃ ∧
        g (τ (ee (1 / 2))) = ee b₂ ∧ g (τ (ee (3 / 4))) = ee b₁)) := by
  obtain ⟨ψ, hψ, hψ0, hψ1, hψ2, hψ3⟩ := exists_circle_four_point_move
    (a₀ := 0) (a₁ := 1 / 4) (a₂ := 1 / 2) (a₃ := 3 / 4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hb₀₁ hb₁₂ hb₂₃ hb₃
  obtain ⟨L, hLc, hLm, hLe⟩ := GM19.exists_circle_lift τ.symm
  rcases hLm with hmono | hanti
  · have hbase : PreservesCircleOrientation τ.symm := ⟨L, hLc, hmono, hLe⟩
    refine ⟨τ.symm.trans ψ, PreservesCircleOrientation.comp hψ hbase, Or.inl ?_⟩
    change ψ (τ.symm (τ (ee 0))) = _ ∧ ψ (τ.symm (τ (ee (1 / 4)))) = _ ∧
      ψ (τ.symm (τ (ee (1 / 2)))) = _ ∧ ψ (τ.symm (τ (ee (3 / 4)))) = _
    simpa only [τ.symm_apply_apply] using And.intro hψ0 (And.intro hψ1 (And.intro hψ2 hψ3))
  · let base := τ.symm.trans (Homeomorph.inv Circle)
    have hbase : PreservesCircleOrientation base := by
      refine ⟨(fun t => -L t), hLc.neg, (fun a b hab => neg_lt_neg (hanti hab)), ?_⟩
      intro t
      change (τ.symm (Circle.exp t))⁻¹ = Circle.exp (-L t)
      rw [hLe, Circle.exp_neg]
    refine ⟨base.trans ψ, PreservesCircleOrientation.comp hψ hbase, Or.inr ?_⟩
    change ψ ((τ.symm (τ (ee 0)))⁻¹) = _ ∧ ψ ((τ.symm (τ (ee (1 / 4))))⁻¹) = _ ∧
      ψ ((τ.symm (τ (ee (1 / 2))))⁻¹) = _ ∧ ψ ((τ.symm (τ (ee (3 / 4))))⁻¹) = _
    simp only [τ.symm_apply_apply, inv_ee_quarter, inv_ee_half, inv_ee_three_quarters]
    have h0 : (ee 0)⁻¹ = ee 0 := by simp [ee]
    rw [h0]
    exact ⟨hψ0, hψ3, hψ2, hψ1⟩

end GraphMinor.GM12
