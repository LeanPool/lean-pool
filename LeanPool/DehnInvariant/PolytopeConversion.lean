/-
Copyright (c) 2026 Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Pool contributors
-/
module

public import LeanPool.DehnInvariant.Polytope
public import LeanPool.Polytopes.Polytope
import LeanPool.Polytopes.MainTheorem
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Conversions for the Lean Pool polytope API

Normalize the nonzero face functionals to identify bounded H-polytopes with
the sets used in the Dehn invariant. The polytope theorem then gives the
corresponding description by finite convex hulls.
-/

public section

open scoped RealInnerProductSpace
open Set

namespace DehnCanon.Library

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- A bounded H-polytope satisfies the half-space predicate for the Dehn invariant. -/
theorem IsPoly.of_Hpolytope {H : Set (Halfspace E)} (hH : H.Finite)
    (hb : Bornology.IsBounded (Hpolytope hH)) : IsPoly (Hpolytope hH) := by
  classical
  let normal (part : Halfspace E) : E := (InnerProductSpace.toDual ℝ E).symm part.f.1
  refine ⟨hb, H, hH.fintype, fun part => normal part.1, fun part => part.1.α, ?_⟩
  ext x
  rw [mem_Hpolytope]
  have evaluation (part : Halfspace E) : ⟪normal part, x⟫ = part.f.1 x := by
    simpa only [normal, InnerProductSpace.toDual_apply_apply] using
      congrArg (fun functional : StrongDual ℝ E => functional x)
        (LinearIsometryEquiv.apply_symm_apply (InnerProductSpace.toDual ℝ E) part.f.1)
  constructor
  · intro hx part
    change ⟪normal part.1, x⟫ ≤ part.1.α
    exact (evaluation part.1).le.trans (hx part.1 part.2)
  · intro hx part hpart
    exact (evaluation part).ge.trans (hx ⟨part, hpart⟩)

/-- Any bounded intersection of finitely many closed half-spaces is an H-polytope. -/
theorem IsPoly.exists_Hpolytope [Nontrivial E] {P : Set E} (hP : IsPoly P) :
    ∃ (H : Set (Halfspace E)) (hH : H.Finite), Hpolytope hH = P := by
  classical
  obtain ⟨_, indices, _, normals, offsets, rfl⟩ := hP
  by_cases impossible : ∃ index, normals index = 0 ∧ offsets index < 0
  · obtain ⟨index, hzero, hnegative⟩ := impossible
    have empty : sol normals offsets = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have h := hx index
      rw [hzero, inner_zero_left] at h
      exact hnegative.not_ge h
    rw [empty]
    exact empty_Hpolytope
  let Nonzero := {index : indices // normals index ≠ 0}
  let halfspace (index : Nonzero) : Halfspace E :=
    ⟨⟨innerSL ℝ (‖normals index.1‖⁻¹ • normals index.1), by
          have positive := norm_pos_iff.mpr index.2
          rw [innerSL_apply_norm, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr positive),
            inv_mul_cancel₀ positive.ne']⟩,
      ‖normals index.1‖⁻¹ * offsets index.1⟩
  refine ⟨Set.range halfspace, Set.finite_range halfspace, ?_⟩
  ext x
  rw [mem_Hpolytope]
  have equivalent (index : Nonzero) :
      (halfspace index).f.1 x ≤ (halfspace index).α ↔ ⟪normals index.1, x⟫ ≤ offsets index.1 := by
    change ⟪‖normals index.1‖⁻¹ • normals index.1, x⟫ ≤ ‖normals index.1‖⁻¹ * offsets index.1 ↔ _
    rw [real_inner_smul_left, mul_le_mul_iff_right₀ (inv_pos.mpr (norm_pos_iff.mpr index.2))]
  constructor
  · intro hx index
    by_cases hzero : normals index = 0
    · rw [hzero, inner_zero_left]
      exact le_of_not_gt fun hnegative => impossible ⟨index, hzero, hnegative⟩
    · exact (equivalent ⟨index, hzero⟩).mp (hx _ ⟨⟨index, hzero⟩, rfl⟩)
  · rintro hx _ ⟨index, rfl⟩
    exact (equivalent index).mpr (hx index.1)

/-- In finite dimension, the Dehn invariant's polytopes are exactly the finite convex hulls. -/
theorem isPoly_iff_exists_Vpolytope [Nontrivial E] [FiniteDimensional ℝ E] (P : Set E) :
    IsPoly P ↔ ∃ (S : Set E) (hS : S.Finite), Vpolytope hS = P := by
  constructor
  · intro hP
    obtain ⟨H, hH, rfl⟩ := hP.exists_Hpolytope
    have compact := Metric.isCompact_iff_isClosed_bounded.mpr ⟨hP.isClosed, hP.1⟩
    obtain ⟨S, hS, equality⟩ := (MainTheoremOfPolytopes (E := E)).2 hH compact
    exact ⟨S, hS, equality.symm⟩
  · rintro ⟨S, hS, rfl⟩
    obtain ⟨H, hH, equality⟩ := (MainTheoremOfPolytopes (E := E)).1 S hS
    rw [← equality]
    exact IsPoly.of_Hpolytope hH (equality ▸ (Compact_Vpolytope hS)).isBounded

end DehnCanon.Library
