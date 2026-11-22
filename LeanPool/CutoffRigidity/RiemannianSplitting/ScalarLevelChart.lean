/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.RegularScalarChart

/-! # Restricting genuine scalar product coordinates to their level
The zero-level chart is constructed from the actual implicit-function chart.
-/

@[expose] public section
open Set
open scoped Topology

namespace CutoffRigidity

variable {A F : Type*} [TopologicalSpace A] [TopologicalSpace F]

/-- Restrict a genuine scalar product chart to its actual zero level. -/
noncomputable def scalarLevelChart (f : A → ℝ) (e : OpenPartialHomeomorph A (ℝ × F))
    (hfirst : ∀ x ∈ e.source, (e x).1 = f x) (x₀ : {x : A // f x = 0}) :
    OpenPartialHomeomorph {x : A // f x = 0} F := by
  classical
  let inverse : F → {x : A // f x = 0} := fun y ↦
    if hy : (0, y) ∈ e.target then
      ⟨e.symm (0, y), by
        rw [← hfirst _ (e.map_target hy), e.right_inv hy]⟩
    else x₀
  have hinv (y : F) (hy : (0, y) ∈ e.target) :
      (inverse y).val = e.symm (0, y) := by simp only [inverse, dite_eq_left hy]
  have hpair (x : {x : A // f x = 0}) (hx : x.val ∈ e.source) : (0, (e x.val).2) = e x.val := by
    ext
    · exact (hfirst x.val hx).trans x.property |>.symm
    · rfl
  refine
    { toFun := fun x ↦ (e x.val).2
      invFun := inverse
      source := Subtype.val ⁻¹' e.source
      target := (fun y : F ↦ (0, y)) ⁻¹' e.target
      map_source' := ?_
      map_target' := ?_
      left_inv' := ?_
      right_inv' := ?_
      continuousOn_toFun := ?_
      continuousOn_invFun := ?_
      open_source := e.open_source.preimage continuous_subtype_val
      open_target := e.open_target.preimage (continuous_const.prodMk continuous_id) }
  · intro x hx
    change (0, (e x.val).2) ∈ e.target
    rw [hpair x hx]
    exact e.map_source hx
  · intro y hy
    change (inverse y).val ∈ e.source
    rw [hinv y hy]
    exact e.map_target hy
  · intro x hx
    apply Subtype.ext
    have hy : (0, (e x.val).2) ∈ e.target := by rw [hpair x hx]; exact e.map_source hx
    rw [hinv _ hy, hpair x hx]
    exact e.left_inv hx
  · intro y hy
    rw [hinv y hy, e.right_inv hy]
  · exact continuous_snd.comp_continuousOn
      (e.continuousOn.comp continuous_subtype_val.continuousOn fun _ hx ↦ hx)
  · have hsub : Topology.IsInducing (Subtype.val : {x : A // f x = 0} → A) :=
      @Topology.IsInducing.subtypeVal A _ {x | f x = 0}
    apply hsub.continuousOn_iff.mpr
    exact (e.continuousOn_symm.comp
      (continuous_const.prodMk continuous_id).continuousOn fun _ hy ↦ hy).congr
      (fun y hy ↦ hinv y hy)

@[simp] theorem scalarLevelChart_apply (f : A → ℝ) (e : OpenPartialHomeomorph A (ℝ × F))
    (hfirst : ∀ x ∈ e.source, (e x).1 = f x) (x₀ : {x : A // f x = 0})
    (x : {x : A // f x = 0}) : scalarLevelChart f e hfirst x₀ x = (e x.val).2 := rfl

@[simp] theorem scalarLevelChart_source (f : A → ℝ) (e : OpenPartialHomeomorph A (ℝ × F))
    (hfirst : ∀ x ∈ e.source, (e x).1 = f x) (x₀ : {x : A // f x = 0}) :
    (scalarLevelChart f e hfirst x₀).source = Subtype.val ⁻¹' e.source := rfl

@[simp] theorem scalarLevelChart_target (f : A → ℝ) (e : OpenPartialHomeomorph A (ℝ × F))
    (hfirst : ∀ x ∈ e.source, (e x).1 = f x) (x₀ : {x : A // f x = 0}) :
    (scalarLevelChart f e hfirst x₀).target = (fun y : F ↦ (0, y)) ⁻¹' e.target := rfl

/-- On the actual coordinate target, the level-chart inverse is the original
product-chart inverse evaluated at scalar coordinate zero. -/
theorem scalarLevelChart_symm_val (f : A → ℝ) (e : OpenPartialHomeomorph A (ℝ × F))
    (hfirst : ∀ x ∈ e.source, (e x).1 = f x) (x₀ : {x : A // f x = 0})
    (y : F) (hy : (0, y) ∈ e.target) :
    ((scalarLevelChart f e hfirst x₀).symm y).val = e.symm (0, y) := by
  simp [scalarLevelChart, OpenPartialHomeomorph.coe_mk_symm, hy]

end CutoffRigidity
