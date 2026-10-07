/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Statements.UnitCylinder
public import LeanPool.CIVAxisymmetric.Statements.GlobalEnergyClass
public import LeanPool.CIVAxisymmetric.Statements.ForceC2Bounded
public import LeanPool.CIVAxisymmetric.Analysis.SobolevSix
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Energy Class Lemmas

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open MeasureTheory Set Filter Topology
open scoped ENNReal
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV

theorem lintegral_gradSq_lt_top {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} (h : GlobalEnergyClass u Du p) :
    ∫⁻ z in unitCylinder, ‖Du z‖ₑ ^ (2 : ℝ) < ⊤ := by
  rcases h with ⟨_, hInt, _⟩
  refine lt_of_le_of_lt (lintegral_mono ?_) hInt
  intro z
  have h_nonneg : 0 ≤ ‖u z‖ₑ ^ (2 : ℝ) := by positivity
  exact le_add_of_nonneg_left h_nonneg

/-- A `C²`-bounded force is bounded in Euclidean norm on the unit cylinder. -/
theorem exists_bound_of_forceC2Bounded {f : ParabolicPoint → Vec3} (h : ForceC2Bounded f) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ unitCylinder, vec3EuclideanNorm (f z) ≤ M := by
  rcases h with ⟨M, hM⟩
  let M' : ℝ := max M 0
  have hM'_nonneg : 0 ≤ M' := le_max_right _ _
  refine ⟨Real.sqrt 3 * M', by
    have h_sqrt_nonneg : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
    exact mul_nonneg h_sqrt_nonneg hM'_nonneg, fun z hz => ?_⟩
  have h_bound : ∀ i : Fin 3, |f z i| ≤ M' := by
    intro i
    have h0 : (fun _ : Fin 3 => 0) 0 + (fun _ : Fin 3 => 0) 1 + (fun _ : Fin 3 => 0) 2 ≤ 2 := by
      norm_num
    have h_abs : |multiPartial (fun w => f w i) (fun _ => 0) z| ≤ M :=
      hM z hz i (fun _ => 0) h0
    have h_multiPartial_zero : multiPartial (fun w => f w i) (fun _ => 0) = fun w => f w i := by
      ext w
      simp [multiPartial]
    rw [h_multiPartial_zero] at h_abs
    exact h_abs.trans (le_max_left _ _)
  have h_sq_sum : (∑ i : Fin 3, (|f z i|) ^ 2) ≤ 3 * (M') ^ 2 := by
    calc
      (∑ i : Fin 3, (|f z i|) ^ 2) ≤ (∑ _i : Fin 3, (M') ^ 2) :=
        Finset.sum_le_sum fun i _ => by
          have h_abs_i : |f z i| ≤ M' := h_bound i
          gcongr
      _ = ((Finset.univ : Finset (Fin 3)).card : ℝ) * (M') ^ 2 := by
        simp
      _ = 3 * (M') ^ 2 := by norm_num
  have h_sq_sum' : (∑ i : Fin 3, (f z i) ^ 2) ≤ 3 * (M') ^ 2 := by
    refine le_trans ?_ h_sq_sum
    refine Finset.sum_le_sum fun i _ => ?_
    have h_abs_i : |f z i| ≤ M' := h_bound i
    have h_sq : (f z i) ^ 2 ≤ (|f z i|) ^ 2 := by
      rw [sq_abs]
    exact h_sq
  rw [vec3EuclideanNorm]
  calc
    Real.sqrt (∑ i : Fin 3, (f z i) ^ 2) ≤ Real.sqrt (3 * (M') ^ 2) :=
      Real.sqrt_le_sqrt h_sq_sum'
    _ = Real.sqrt 3 * Real.sqrt ((M') ^ 2) := by
      rw [Real.sqrt_mul (by norm_num : 0 ≤ (3 : ℝ))]
    _ = Real.sqrt 3 * |M'| := by rw [Real.sqrt_sq_eq_abs]
    _ = Real.sqrt 3 * M' := by rw [abs_of_nonneg hM'_nonneg]

/-- A `C²`-bounded force is bounded componentwise on the unit cylinder. -/
theorem exists_component_bound_of_forceC2Bounded {f : ParabolicPoint → Vec3}
    (h : ForceC2Bounded f) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ unitCylinder, ∀ i : Fin 3, |f z i| ≤ M := by
  rcases h with ⟨M, hM⟩
  let M' : ℝ := max M 0
  have hM'_nonneg : 0 ≤ M' := le_max_right _ _
  refine ⟨M', hM'_nonneg, fun z hz i => ?_⟩
  have h0 : (fun _ : Fin 3 => 0) 0 + (fun _ : Fin 3 => 0) 1 + (fun _ : Fin 3 => 0) 2 ≤ 2 := by
    norm_num
  have h_abs : |multiPartial (fun w => f w i) (fun _ => 0) z| ≤ M :=
    hM z hz i (fun _ => 0) h0
  have h_multiPartial_zero : multiPartial (fun w => f w i) (fun _ => 0) = fun w => f w i := by
    ext w
    simp [multiPartial]
  rw [h_multiPartial_zero] at h_abs
  exact h_abs.trans (le_max_left _ _)

end CIV
