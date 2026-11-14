/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Kinetic.CurryingProductBasic
import LeanPool.LiebThirring.Kinetic.CurryingMeasurable

/-!
# Existence and uniqueness of the outer L² class

Uniqueness of an outer L² class from its nested a.e. representative formula.

A strongly measurable product L² function has a uniquely characterized outer L² class. The
target separability is used only to establish measurability.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace LiebThirring

variable {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [NormedAddCommGroup E] {μ : Measure α} {ν : Measure β}

/-- Uniqueness of an outer L² class from its nested a.e. representative formula. -/
theorem l2_curry_unique (f : α × β → E) (c d : Lp (Lp E 2 ν) 2 μ)
    (hc : ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, c x y = f (x, y))
    (hd : ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, d x y = f (x, y)) : c = d := by
  apply Lp.ext
  filter_upwards [hc, hd] with x hx hy
  apply Lp.ext
  exact Filter.EventuallyEq.trans hx (Filter.EventuallyEq.symm hy)

variable [SFinite ν] [SecondCountableTopology (Lp E 2 ν)]

/-- A strongly measurable product L² function has a uniquely characterized
outer L² class. The target separability is used only to establish measurability. -/
theorem existsUnique_l2_curry (f : α × β → E) (hf : StronglyMeasurable f)
    (hLp : MemLp f 2 (μ.prod ν)) :
    ∃! c : Lp (Lp E 2 ν) 2 μ, ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, c x y = f (x, y) := by
  classical
  borelize ↥(Lp E 2 ν)
  let g : α → Lp E 2 ν := fun x =>
    if hx : MemLp (fun y => f (x, y)) 2 ν then hx.toLp _ else 0
  have hgood : MeasurableSet {x | MemLp (fun y => f (x, y)) 2 ν} :=
    measurableSet_lt (measurable_l2_slice_eLpNorm f hf) measurable_const
  have hdist (h : Lp E 2 ν) : Measurable (fun x => dist (g x) h) := by
    have hF : StronglyMeasurable (fun z : α × β => f z - h z.2) :=
      hf.sub ((Lp.stronglyMeasurable h).comp_measurable measurable_snd)
    have hnorm : Measurable (fun x =>
        (eLpNorm (fun y => f (x, y) - h y) 2 ν).toReal) :=
      (measurable_l2_slice_eLpNorm _ hF).ennreal_toReal
    have heq : (fun x => dist (g x) h) = fun x =>
        if MemLp (fun y => f (x, y)) 2 ν then
          (eLpNorm (fun y => f (x, y) - h y) 2 ν).toReal else dist 0 h := by
      funext x
      dsimp only [g]
      split_ifs with hx
      · rw [Lp.dist_def]
        apply congrArg ENNReal.toReal
        apply eLpNorm_congr_ae
        exact hx.coeFn_toLp.sub Filter.EventuallyEq.rfl
      · rfl
    rw [heq]
    exact Measurable.ite hgood hnorm measurable_const
  have hg : StronglyMeasurable g :=
    (measurable_of_dist_functions g hdist).stronglyMeasurable
  have hax := memLp_l2_slice_ae f hf hLp
  have hmass : (∫⁻ x, ‖g x‖ₑ ^ 2 ∂μ) =
      ∫⁻ z, ‖f z‖ₑ ^ 2 ∂(μ.prod ν) := by
    calc
      _ = ∫⁻ x, ∫⁻ y, ‖f (x, y)‖ₑ ^ 2 ∂ν ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hax] with x hx
        dsimp only [g]
        rw [dite_eq_left hx, ← lintegral_l2_enorm_sq]
        exact lintegral_congr_ae (hx.coeFn_toLp.mono
          (fun _ hy => congrArg (fun u : E => ‖u‖ₑ ^ 2) hy))
      _ = _ := (lintegral_prod _ (hf.enorm.pow_const 2).aemeasurable).symm
  have hgLp : MemLp g 2 μ := by
    apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
      hg.aestronglyMeasurable).mpr
    simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
    rw [hmass]
    simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_two] using
      lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
        (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hLp
  have hc : ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, (hgLp.toLp g) x y = f (x, y) := by
    filter_upwards [hgLp.coeFn_toLp, hax] with x hx hxLp
    rw [hx]
    dsimp only [g]
    rw [dite_eq_left hxLp]
    exact hxLp.coeFn_toLp
  refine ⟨hgLp.toLp g, hc, ?_⟩
  intro d hd
  exact l2_curry_unique f d _ hd hc

end LiebThirring

end
