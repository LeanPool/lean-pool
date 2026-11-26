/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
import LeanPool.GraphMinor.Surface.Collar
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# A circle contains no proper circle

For the circle case of the schismatic definition used by XII (3.1),
page 245, a circle has no proper subset which is a circle. A continuous
injection of the standard circle into itself is onto: if it omitted
a point, rotate that point to minus one and use the continuous argument
as an injective real coordinate. The proved no-embedding theorem for
the circle and the line excludes that coordinate.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface

/-- A continuous injective self-map of the circle is onto. Omitting
one point would give a continuous injective argument coordinate in the line. -/
theorem circle_surjective_of_continuous_injective
    {f : Circle → Circle} (hf : Continuous f) (hi : Function.Injective f) : Function.Surjective f
      := by
  classical
  by_contra hn
  obtain ⟨c, hc⟩ : ∃ c : Circle, ∀ z, f z ≠ c := by
    simpa only [Function.Surjective, not_forall, not_exists] using hn
  let ρ : Circle := -c⁻¹
  have hρc : ρ * c = -1 := by simp [ρ]
  have hneg : ∀ z, ρ * f z ≠ -1 := by
    intro z he
    exact hc z (mul_left_cancel (he.trans hρc.symm))
  have hslit : ∀ z, ((ρ * f z : Circle) : ℂ) ∈ Complex.slitPlane := by
    intro z
    rw [Complex.mem_slitPlane_iff_arg]
    refine ⟨?_, Circle.coe_ne_zero _⟩
    intro he
    apply hneg z
    apply Circle.injective_arg
    simpa only [Circle.coe_neg, Circle.coe_one, Complex.arg_neg_one] using he
  let k : Circle → ℝ := fun z => Complex.arg ((ρ * f z : Circle) : ℂ)
  have hmul : Continuous (fun z => ((ρ * f z : Circle) : ℂ)) :=
    continuous_subtype_val.comp (continuous_const.mul hf)
  have hargc : ContinuousOn Complex.arg Complex.slitPlane :=
    fun z hz => (Complex.continuousAt_arg hz).continuousWithinAt
  have hk : Continuous k := continuousOn_univ.mp
    (hargc.comp hmul.continuousOn (fun z _ => hslit z))
  have hki : Function.Injective k := by
    intro z w he
    exact hi (mul_left_cancel (Circle.injective_arg he))
  exact not_injective_circle_real hk hki

/-- A circle contained in another circle is equal to it. -/
theorem oArc_eq_of_subset
    {S : Type*} [TopologicalSpace S] {Z F : Set S}
    (hZ : IsOArc Z) (hF : IsOArc F) (hZF : Z ⊆ F) : Z = F := by
  obtain ⟨φZ⟩ := hZ
  obtain ⟨φF⟩ := hF
  let k : Circle → Circle := fun z => φF.symm ⟨(φZ z).val, hZF (φZ z).property⟩
  have hk : Continuous k := φF.symm.continuous.comp
    ((continuous_subtype_val.comp φZ.continuous).subtype_mk _)
  have hki : Function.Injective k := by
    intro z w he
    have hv := congrArg φF he
    change φF (φF.symm _) = φF (φF.symm _) at hv
    simp only [Homeomorph.apply_symm_apply] at hv
    have hvS : (φZ z).val = (φZ w).val := congrArg (Subtype.val : F → S) hv
    exact φZ.injective (Subtype.ext hvS)
  have hks := circle_surjective_of_continuous_injective hk hki
  apply Subset.antisymm hZF
  intro x hxF
  obtain ⟨z, hz⟩ := hks (φF.symm ⟨x, hxF⟩)
  have hv := congrArg φF hz
  change φF (φF.symm _) = φF (φF.symm _) at hv
  simp only [Homeomorph.apply_symm_apply] at hv
  have hval : (φZ z).val = x := congrArg (Subtype.val : F → S) hv
  exact hval ▸ (φZ z).property

end GraphMinor.GM12
