/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
import LeanPool.GraphMinor.GM11.Section3
import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic

/-!
# Two homotopic arcs bound a null-homotopic circle

The uniqueness part of the entry-edge definition in XII, page 243,
compares the paths along two spokes. If the paths are homotopic and
otherwise disjoint, their union is a null-homotopic circle. This file
proves the path-to-circle step. It uses the usual traversal of the first
arc followed by the reverse of the second, with its endpoints identified.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- Two injective arcs with common ends and no other intersection
form a closed traversal with no repeated parameter except its ends. -/
theorem joined_loop_eq {X : Type*} [TopologicalSpace X] {a b : X}
    (p q : Path a b) (hp : Function.Injective p) (hq : Function.Injective q)
    (hcross : ∀ s t, p s = q t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1))
    {s t : unitInterval} (heq : (p.trans q.symm) s = (p.trans q.symm) t) :
    s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0) := by
  by_cases hs : (s : ℝ) ≤ 1 / 2 <;> by_cases ht : (t : ℝ) ≤ 1 / 2
  · simp only [Path.trans_apply, hs, ht, ↓reduceDIte] at heq
    have h := congrArg Subtype.val (hp heq)
    left
    apply Subtype.ext
    dsimp only at h
    linarith
  · simp only [Path.trans_apply, hs, ht, ↓reduceDIte, Path.symm_apply] at heq
    rcases hcross _ _ heq with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · have h₁' := congrArg Subtype.val h₁
      have h₂' := congrArg Subtype.val h₂
      simp only [unitInterval.coe_symm_eq, Icc.coe_zero] at h₁' h₂'
      right; left
      constructor
      · apply Subtype.ext
        change (s : ℝ) = 0
        linarith
      · apply Subtype.ext
        change (t : ℝ) = 1
        linarith
    · have h₁' := congrArg Subtype.val h₁
      have h₂' := congrArg Subtype.val h₂
      simp only [unitInterval.coe_symm_eq, Icc.coe_one] at h₁' h₂'
      left
      apply Subtype.ext
      linarith
  · simp only [Path.trans_apply, hs, ht, ↓reduceDIte, Path.symm_apply] at heq
    rcases hcross _ _ heq.symm with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · have h₁' := congrArg Subtype.val h₁
      have h₂' := congrArg Subtype.val h₂
      simp only [unitInterval.coe_symm_eq, Icc.coe_zero] at h₁' h₂'
      right; right
      constructor
      · apply Subtype.ext
        change (s : ℝ) = 1
        linarith
      · apply Subtype.ext
        change (t : ℝ) = 0
        linarith
    · have h₁' := congrArg Subtype.val h₁
      have h₂' := congrArg Subtype.val h₂
      simp only [unitInterval.coe_symm_eq, Icc.coe_one] at h₁' h₂'
      left
      apply Subtype.ext
      linarith
  · simp only [Path.trans_apply, hs, ht, ↓reduceDIte, Path.symm_apply] at heq
    have h := congrArg Subtype.val (hq heq)
    simp only [unitInterval.coe_symm_eq] at h
    left
    apply Subtype.ext
    linarith

/-- The union of two injective homotopic paths with common ends and no
other intersections is a null-homotopic `O`-arc. This is the homotopy
step used to distinguish entry spokes in XII, page 243. -/
theorem nullHomotopic_union_of_homotopic_arcs {X : Type*}
    [TopologicalSpace X] [T2Space X] {a b : X} (p q : Path a b)
    (hp : Function.Injective p) (hq : Function.Injective q)
    (hcross : ∀ s t, p s = q t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1))
    (hh : p.Homotopic q) : IsNullHomotopicOArcIn univ (range p ∪ range q) := by
  let loop := p.trans q.symm
  let γ : C(Circle, X) := loopLift 1 loop.toContinuousMap (by simp)
  have hγi : Function.Injective γ := by
    intro z w heq
    obtain ⟨s, rfl⟩ := arcParam_surjective 1 z
    obtain ⟨t, rfl⟩ := arcParam_surjective 1 w
    have hst := heq
    simp only [γ, loopLift_apply] at hst
    change (p.trans q.symm) s = (p.trans q.symm) t at hst
    rcases joined_loop_eq p q hp hq hcross hst with h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact congrArg (arcParam 1) h
    · simp only [arcParam_zero, arcParam_one]
    · simp only [arcParam_zero, arcParam_one]
  have hrange : range γ = range p ∪ range q := by
    have heq : range γ = range loop := by
      ext x
      constructor
      · rintro ⟨z, rfl⟩
        obtain ⟨s, rfl⟩ := arcParam_surjective 1 z
        exact ⟨s, (loopLift_apply 1 _ _ s).symm⟩
      · rintro ⟨s, rfl⟩
        exact ⟨arcParam 1 s, loopLift_apply 1 _ _ s⟩
    rw [heq, Path.trans_range, Path.symm_range]
  have hnull : ClosedCurveIsNullHomotopicIn univ γ := by
    obtain ⟨H⟩ := (hh.hcomp (Path.Homotopic.refl q.symm)).trans (Path.Homotopic.trans_symm q)
    let F : C(unitInterval × unitInterval, X) := ⟨fun z => H (z.2, z.1), by fun_prop⟩
    have hends : ∀ t, F (0, t) = F (1, t) := by intro t; simp [F]
    refine ⟨a, mem_univ _, cylinderLift 1 F hends, fun _ => mem_univ _, ?_, ?_⟩
    · intro z
      obtain ⟨s, rfl⟩ := arcParam_surjective 1 z
      rw [cylinderLift_apply]
      change H (0, s) = loopLift 1 loop.toContinuousMap _ (arcParam 1 s)
      rw [H.apply_zero, loopLift_apply]
    · intro z
      obtain ⟨s, rfl⟩ := arcParam_surjective 1 z
      rw [cylinderLift_apply]
      change H (1, s) = a
      simp
  let φ : Circle ≃ₜ (range p ∪ range q : Set X) :=
    (γ.continuous.isClosedEmbedding hγi).isEmbedding.toHomeomorph.trans
      (Homeomorph.setCongr hrange)
  refine ⟨φ, ?_⟩
  have heq : (⟨fun z => (φ z).val, continuous_subtype_val.comp φ.continuous⟩ : C(Circle, X)) = γ
    := by
    ext z
    rfl
  rw [heq]
  exact hnull

/-- Map a null-homotopic circle through a topological embedding. This
lets path homotopies in a subspace be used in the ambient surface. -/
theorem nullHomotopic_oArc_image {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
    {f : X → Y} (hf : IsEmbedding f) {Z F : Set X}
    (hF : IsNullHomotopicOArcIn Z F) :
    IsNullHomotopicOArcIn (f '' Z) (f '' F) := by
  obtain ⟨φ, c, hc, H, hHZ, hH0, hH1⟩ := hF
  let γ : C(Circle, Y) := ⟨fun z => f (φ z).val,
    hf.continuous.comp (continuous_subtype_val.comp φ.continuous)⟩
  have hγi : Function.Injective γ :=
    (hf.comp (IsEmbedding.subtypeVal.comp φ.isEmbedding)).injective
  have hrange : range γ = f '' F := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨(φ z).val, (φ z).property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨φ.symm ⟨x, hx⟩, by simp [γ]⟩
  let e : Circle ≃ₜ (f '' F : Set Y) :=
    (γ.continuous.isClosedEmbedding hγi).isEmbedding.toHomeomorph.trans
      (Homeomorph.setCongr hrange)
  refine ⟨e, f c, ⟨c, hc, rfl⟩, ?_, ?_, ?_, ?_⟩
  · exact ⟨fun z => f (H z), hf.continuous.comp H.continuous⟩
  · intro z
    exact ⟨H z, hHZ z, rfl⟩
  · intro z
    change f (H (z, 0)) = γ z
    exact congrArg f (hH0 z)
  · intro z
    exact congrArg f (hH1 z)

end GraphMinor.GM12
