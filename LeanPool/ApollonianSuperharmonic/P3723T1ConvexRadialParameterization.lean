/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Topology.MetricSpace.Pseudo.Real

public import Mathlib.Analysis.Convex.Topology

/-!
# P3723T1ConvexRadialParameterization

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

open Set

-- [TABLET NODE: P3723T1ConvexRadialParameterization]
theorem P3723T1ConvexRadialParameterization
    (K : Set (Real × Real)) (hK : Convex Real K) (hclosed : IsClosed K)
    (x y : Real × Real) (hx : x ∈ interior K) (hy : y ∈ frontier K) :
    ∃ h : Icc (0 : Real) 1 ≃ₜ segment Real x y,
      ((h ⟨0, by norm_num⟩ : segment Real x y) : Real × Real) = x ∧
      ((h ⟨1, by norm_num⟩ : segment Real x y) : Real × Real) = y ∧
      segment Real x y ⊆ interior K ∪ {y} ∧
      ∀ t : Icc (0 : Real) 1,
        ((h t : segment Real x y) : Real × Real) =
          (1 - (t : Real)) • x + (t : Real) • y := by
-- BODY
  have hxy : x ≠ y := by
    intro he
    exact hy.2 (he ▸ hx)
  let f : Icc (0 : Real) 1 → segment Real x y := fun t =>
    ⟨(1 - (t : Real)) • x + (t : Real) • y,
      by rw [segment_eq_image]; exact ⟨t, t.property, rfl⟩⟩
  have hfc : Continuous f := by
    apply Continuous.subtype_mk
    exact ((continuous_const.sub continuous_subtype_val).smul continuous_const).add
      (continuous_subtype_val.smul continuous_const)
  have hfi : Function.Injective f := by
    intro s t hst
    apply Subtype.ext
    apply AffineMap.lineMap_injective Real hxy
    simpa only [AffineMap.lineMap_apply_module] using congrArg Subtype.val hst
  have hfs : Function.Surjective f := by
    intro q
    have hq := q.property
    simp only [segment_eq_image] at hq
    obtain ⟨t, ht, heq⟩ := hq
    exact ⟨⟨t, ht⟩, Subtype.ext heq⟩
  let h : Icc (0 : Real) 1 ≃ₜ segment Real x y :=
    (isHomeomorph_iff_continuous_bijective.mpr ⟨hfc, hfi, hfs⟩).homeomorph
  refine ⟨h, by simp [h, f], by simp [h, f], ?_, ?_⟩
  · intro q hq
    rw [segment_eq_image] at hq
    obtain ⟨t, ht, rfl⟩ := hq
    by_cases ht1 : t = 1
    · simp [ht1]
    · exact Or.inl (hK.combo_interior_self_mem_interior hx
        (hclosed.frontier_subset hy) (sub_pos.mpr (lt_of_le_of_ne ht.2 ht1)) ht.1
          (by ring))
  · intro t
    rfl

end ApollonianSuperharmonic

end
