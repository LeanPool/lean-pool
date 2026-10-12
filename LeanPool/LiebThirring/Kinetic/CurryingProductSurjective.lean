/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Kinetic.CurryingProductMap

/-!
# Surjectivity of product L² currying

Product currying is onto when the target is complete.  The proof puts finite-measure
outer indicators in the range by an explicit product-space representative, then uses
density of L² simple functions and closedness of the range of an isometry.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace LiebThirring

variable {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  {μ : Measure α} {ν : Measure β} [SFinite ν]
  [SecondCountableTopology (Lp E 2 ν)]

/-- Every iterated L² class is the curry of a product-space L² class. -/
theorem l2CurryLinearIsometry_surjective : Function.Surjective
    (l2CurryLinearIsometry (μ := μ) (ν := ν) (E := E)) := by
  classical
  intro g
  apply Lp.induction (p := (2 : ℝ≥0∞)) (μ := μ) (by norm_num)
    (fun g => g ∈ Set.range (l2CurryLinearIsometry (μ := μ) (ν := ν) (E := E)))
  · intro h A hA hμA
    let F : α × β → E := (A ×ˢ Set.univ).indicator (fun z => h z.2)
    have hFsm : StronglyMeasurable F := by
      exact ((Lp.stronglyMeasurable h).comp_measurable measurable_snd).indicator
        (hA.prod MeasurableSet.univ)
    have hmass : (∫⁻ z, ‖F z‖ₑ ^ 2 ∂(μ.prod ν)) = μ A * ‖h‖ₑ ^ 2 := by
      rw [lintegral_prod _ (hFsm.enorm.pow_const 2).aemeasurable]
      simp only [F, Set.indicator_apply, apply_ite, enorm_zero]
      simp only [Set.mem_prod, Set.mem_univ, and_true]
      rw [show (fun x => ∫⁻ y, (if x ∈ A then ‖h y‖ₑ else 0) ^ 2 ∂ν) =
          A.indicator (fun _ => ‖h‖ₑ ^ 2) by
        funext x
        by_cases hx : x ∈ A
        · simp only [hx, ↓reduceIte, Set.indicator_of_mem]
          exact lintegral_l2_enorm_sq h
        · simp [hx]]
      rw [lintegral_indicator hA, setLIntegral_const]
      exact mul_comm _ _
    have hFLp : MemLp F 2 (μ.prod ν) := by
      apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
        (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
        hFsm.aestronglyMeasurable).mpr
      simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two, hmass]
      exact ENNReal.mul_lt_top hμA (ENNReal.pow_lt_top (by finiteness))
    refine ⟨hFLp.toLp F, ?_⟩
    change l2Curry (hFLp.toLp F) = indicatorConstLp 2 hA hμA.ne h
    apply Lp.ext
    have hprod := Measure.ae_ae_of_ae_prod hFLp.coeFn_toLp
    have hi0 : ((indicatorConstLp 2 hA hμA.ne h : Lp (Lp E 2 ν) 2 μ) :
        α → Lp E 2 ν) =ᵐ[μ] A.indicator (fun _ => h) := indicatorConstLp_coeFn
    filter_upwards [l2Curry_ae (hFLp.toLp F), hi0, hprod] with x hx hi hp
    apply Lp.ext
    filter_upwards [hx, hp, Lp.coeFn_zero E 2 ν] with y hxy hprod hz
    rw [hxy, hprod, hi]
    by_cases hxA : x ∈ A
    · simp [F, hxA]
    · rw [Set.indicator_of_notMem hxA]
      dsimp only [F]
      rw [Set.indicator_of_notMem (by simp [hxA]), hz]
      rfl
  · intro f g hf hg hd ⟨u, hu⟩ ⟨v, hv⟩
    refine ⟨u + v, ?_⟩
    rw [map_add, hu, hv]
  · exact (l2CurryLinearIsometry (μ := μ) (ν := ν) (E :=
    E)).isometry.isUniformInducing.isComplete_range.isClosed

/-- Product L² and iterated L² are canonically complex-linearly isometric. -/
@[expose] noncomputable def l2CurryLinearIsometryEquiv :
    Lp E 2 (μ.prod ν) ≃ₗᵢ[ℂ] Lp (Lp E 2 ν) 2 μ :=
  LinearIsometryEquiv.ofSurjective l2CurryLinearIsometry l2CurryLinearIsometry_surjective

/-- The equivalence has the expected nested representative formula. -/
theorem l2CurryLinearIsometryEquiv_apply_ae (f : Lp E 2 (μ.prod ν)) :
    ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, l2CurryLinearIsometryEquiv f x y = f (x, y) := by
  exact l2Curry_ae f

end LiebThirring

end
