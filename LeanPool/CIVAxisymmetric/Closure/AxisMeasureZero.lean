/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Closure.PolarREqZero
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# The vertical axis is Lebesgue-null

The vertical axis `{x ∈ Vec3 | x₀ = x₁ = 0}` — equivalently `{polarR x = 0}` — is a proper
linear subspace of `Vec3`, hence Lebesgue-null by the general Haar-measure fact for strict
subspaces.  This is the "axis Lebesgue-null" step needed to integrate the off-axis pointwise
vortex-stretching identity `stretching_eq_stretchGTerm` against a cutoff weight `χ²` over the
whole ball (see `lem:aniso:closure` in the paper, arXiv:2609.20803).
-/

public section

open MeasureTheory Set
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV



/-- The vertical axis `{x : Vec3 | x 0 = 0 ∧ x 1 = 0}` has Lebesgue measure zero. -/
theorem volume_axis_eq_zero : volume {x : Vec3 | x 0 = 0 ∧ x 1 = 0} = 0 := by
  set s : Submodule ℝ Vec3 :=
    { carrier := {x : Vec3 | x 0 = 0 ∧ x 1 = 0}
      zero_mem' := by simp
      add_mem' := fun {a b} ha hb => ⟨by simp [ha.1, hb.1], by simp [ha.2, hb.2]⟩
      smul_mem' := fun c {a} ha => ⟨by simp [ha.1], by simp [ha.2]⟩ }
  with hs_def
  have hne : s ≠ ⊤ := by
    intro htop
    have hmem : (basisVec 0 : Vec3) ∈ s := htop ▸ Submodule.mem_top
    have h0 : (basisVec 0 : Vec3) 0 = 0 := hmem.1
    simp at h0
  have hvol := MeasureTheory.Measure.addHaar_submodule (volume : Measure Vec3) s hne
  simpa [hs_def] using hvol

/-- The set `{x : Vec3 | polarR x = 0}` has Lebesgue measure zero. -/
theorem volume_setOf_polarR_eq_zero_eq_zero : volume {x : Vec3 | polarR x = 0} = 0 := by
  have hset : {x : Vec3 | polarR x = 0} = {x : Vec3 | x 0 = 0 ∧ x 1 = 0} := by
    ext x; exact polarR_eq_zero_iff x
  rw [hset]
  exact volume_axis_eq_zero

/-- Almost every point (with respect to Lebesgue measure) has `polarR x ≠ 0`. -/
theorem ae_polarR_ne_zero : ∀ᵐ x : Vec3 ∂volume, polarR x ≠ 0 := by
  rw [ae_iff]
  have : {x : Vec3 | ¬ polarR x ≠ 0} = {x : Vec3 | polarR x = 0} := by
    ext x; simp
  rw [this]
  simpa using volume_setOf_polarR_eq_zero_eq_zero

end CIV
