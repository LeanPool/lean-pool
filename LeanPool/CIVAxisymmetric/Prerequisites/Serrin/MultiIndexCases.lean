/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Statements.MultiPartial
public import LeanPool.CIVAxisymmetric.Identities.Vorticity

/-!
# Spatial multi-indices of order at most two

A spatial multi-index derivative of order at most two is the function itself, a single spatial
partial, or an iterated partial; and the antisymmetric part of a velocity gradient is a signed
vorticity component. Both are used in the interior estimates of the proof of `lem:aniso:annulus`.
-/

public section

open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV



/-- A spatial multi-index derivative of order at most two is the function itself, one partial,
or an iterated partial. -/
theorem multiPartial_cases_of_order_le_two (g : ParabolicPoint → ℝ) (α : Fin 3 → ℕ)
    (hα : α 0 + α 1 + α 2 ≤ 2) :
    multiPartial g α = g ∨ (∃ j : Fin 3, multiPartial g α = spatialPartial g j) ∨
      ∃ j l : Fin 3,
        multiPartial g α = fun z => spatialPartial (fun w => spatialPartial g j w) l z := by
  have h0 : α 0 ≤ 2 := by omega
  have h1 : α 1 ≤ 2 := by omega
  have h2 : α 2 ≤ 2 := by omega
  unfold multiPartial
  generalize ha0 : α 0 = a0 at *
  generalize ha1 : α 1 = a1 at *
  generalize ha2 : α 2 = a2 at *
  interval_cases a0 <;> interval_cases a1 <;> interval_cases a2 <;>
    first
    | omega
    | exact Or.inl rfl
    | exact Or.inr (Or.inl ⟨0, rfl⟩)
    | exact Or.inr (Or.inl ⟨1, rfl⟩)
    | exact Or.inr (Or.inl ⟨2, rfl⟩)
    | exact Or.inr (Or.inr ⟨0, 0, rfl⟩)
    | exact Or.inr (Or.inr ⟨1, 0, rfl⟩)
    | exact Or.inr (Or.inr ⟨2, 0, rfl⟩)
    | exact Or.inr (Or.inr ⟨1, 1, rfl⟩)
    | exact Or.inr (Or.inr ⟨2, 1, rfl⟩)
    | exact Or.inr (Or.inr ⟨2, 2, rfl⟩)

/-- The antisymmetric part of the velocity gradient is a signed vorticity component. -/
theorem spatialPartial_antisymm_eq_smul_curlComp (u : ParabolicPoint → Vec3) (i j : Fin 3) :
    ∃ m : Fin 3, ∃ σ : ℝ, |σ| ≤ 1 ∧ ∀ z : ParabolicPoint,
      spatialPartial (fun w => u w i) j z - spatialPartial (fun w => u w j) i z =
        σ * curlComp u m z := by
  fin_cases i <;> fin_cases j
  · exact ⟨0, 0, by norm_num, fun z => by simp⟩
  · refine ⟨2, -1, by norm_num, fun z => ?_⟩
    simp [curlComp]
  · refine ⟨1, 1, by norm_num, fun z => ?_⟩
    simp [curlComp]
  · refine ⟨2, 1, by norm_num, fun z => ?_⟩
    simp [curlComp]
  · exact ⟨0, 0, by norm_num, fun z => by simp⟩
  · refine ⟨0, -1, by norm_num, fun z => ?_⟩
    simp [curlComp]
  · refine ⟨1, -1, by norm_num, fun z => ?_⟩
    simp [curlComp]
  · refine ⟨0, 1, by norm_num, fun z => ?_⟩
    simp [curlComp]
  · exact ⟨0, 0, by norm_num, fun z => by simp⟩

end CIV
