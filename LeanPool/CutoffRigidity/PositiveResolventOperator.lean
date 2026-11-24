/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import LeanPool.CutoffRigidity.SymmetricOperatorDenseRange

/-! # The self-adjoint operator recovered from an injective symmetric resolvent -/

public section

namespace CutoffRigidity

open scoped LinearPMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The actual graph of the operator `R⁻¹-I`. -/
@[expose] noncomputable def positiveResolventGraph (R : H →L[ℝ] H) : Submodule ℝ (H × H) :=
  (R.toLinearMap.prod (LinearMap.id - R.toLinearMap)).range

omit [CompleteSpace H] in
theorem mem_positiveResolventGraph (R : H →L[ℝ] H) (x y : H) :
    (x, y) ∈ positiveResolventGraph R ↔ ∃ f : H, R f = x ∧ f - R f = y := by
  change (∃ f, (R f, f - R f) = (x, y)) ↔ _
  simp only [Prod.mk.injEq]

omit [CompleteSpace H] in
theorem positiveResolventGraph_singleValued (R : H →L[ℝ] H) (hR : Function.Injective R) :
    ∀ x : H × H, x ∈ positiveResolventGraph R → x.1 = 0 → x.2 = 0 := by
  rintro ⟨x, y⟩ hxy hx
  obtain ⟨f, hf, hfy⟩ := (mem_positiveResolventGraph R x y).mp hxy
  have hf0 : f = 0 := hR (by simpa only [map_zero] using hf.trans hx)
  simpa only [hf0, map_zero, sub_zero] using hfy.symm

/-- Genuine unbounded operator recovered from its injective resolvent. -/
@[expose] noncomputable def positiveResolventOperator (R : H →L[ℝ] H) : H →ₗ.[ℝ] H :=
  (positiveResolventGraph R).toLinearPMap

omit [CompleteSpace H] in
theorem positiveResolventOperator_graph (R : H →L[ℝ] H) (hR : Function.Injective R) :
    (positiveResolventOperator R).graph = positiveResolventGraph R :=
  Submodule.toLinearPMap_graph_eq _ (positiveResolventGraph_singleValued R hR)

omit [CompleteSpace H] in
/-- The graph equation for `R⁻¹-I` is equivalent to the shifted resolvent equation. -/
theorem mem_positiveResolventOperator_graph_iff (R : H →L[ℝ] H) (hR : Function.Injective R)
    (u g : H) : (u, g) ∈ (positiveResolventOperator R).graph ↔ R (u + g) = u := by
  rw [positiveResolventOperator_graph R hR, mem_positiveResolventGraph]
  constructor
  · rintro ⟨f, hf, hg⟩
    have hsum : u + g = f := by rw [← hf, ← hg]; abel
    simpa only [hsum] using hf
  · intro h
    exact ⟨u + g, h, by rw [h]; abel⟩

omit [CompleteSpace H] in
theorem positiveResolventOperator_mem_domain (R : H →L[ℝ] H) (hR : Function.Injective R)
    (x : H) : x ∈ (positiveResolventOperator R).domain ↔ ∃ f, R f = x := by
  rw [LinearPMap.mem_domain_iff, positiveResolventOperator_graph R hR]
  constructor
  · rintro ⟨y, hxy⟩
    obtain ⟨f, hf, _⟩ := (mem_positiveResolventGraph R x y).mp hxy
    exact ⟨f, hf⟩
  · rintro ⟨f, rfl⟩
    exact ⟨f - R f, (mem_positiveResolventGraph R _ _).mpr ⟨f, rfl, rfl⟩⟩

omit [CompleteSpace H] in
theorem positiveResolventOperator_apply (R : H →L[ℝ] H) (hR : Function.Injective R)
    (f : H) (hx : R f ∈ (positiveResolventOperator R).domain) :
    positiveResolventOperator R ⟨R f, hx⟩ = f - R f := by
  apply ((positiveResolventOperator R).image_iff hx).mpr ?_ |>.symm
  rw [positiveResolventOperator_graph R hR]
  exact (mem_positiveResolventGraph R _ _).mpr ⟨f, rfl, rfl⟩

/-- The constructed operator has actual dense domain. -/
theorem positiveResolventOperator_dense_domain (R : H →L[ℝ] H) (hR : Function.Injective R)
    (hsym : ∀ x y, inner ℝ (R x) y = inner ℝ x (R y)) :
    Dense ((positiveResolventOperator R).domain : Set H) := by
  apply (denseRange_of_injective_symmetric R hR hsym).mono
  rintro x ⟨f, rfl⟩
  exact (positiveResolventOperator_mem_domain R hR _).mpr ⟨f, rfl⟩

omit [CompleteSpace H] in
/-- The inverse-resolvent operator is symmetric on its actual domain. -/
theorem positiveResolventOperator_formalAdjoint (R : H →L[ℝ] H) (hR : Function.Injective R)
    (hsym : ∀ x y, inner ℝ (R x) y = inner ℝ x (R y)) :
    (positiveResolventOperator R).IsFormalAdjoint (positiveResolventOperator R) := by
  intro x y
  obtain ⟨f, hf⟩ := (positiveResolventOperator_mem_domain R hR x).mp x.property
  obtain ⟨g, hg⟩ := (positiveResolventOperator_mem_domain R hR y).mp y.property
  have hAx : positiveResolventOperator R x = f - R f := by
    have hx := positiveResolventOperator_apply R hR f (hf ▸ x.property)
    simpa only [hf] using hx
  have hAy : positiveResolventOperator R y = g - R g := by
    have hy := positiveResolventOperator_apply R hR g (hg ▸ y.property)
    simpa only [hg] using hy
  rw [hAx, hAy, ← hf, ← hg, inner_sub_left, inner_sub_right, hsym]
  rw [hsym f g]

/-- Surjectivity of `I+A` makes the symmetric inverse-resolvent operator
self-adjoint, proved directly from the defining Hilbert-adjoint pairing. -/
theorem positiveResolventOperator_selfAdjoint (R : H →L[ℝ] H) (hR : Function.Injective R)
    (hsym : ∀ x y, inner ℝ (R x) y = inner ℝ x (R y)) :
    IsSelfAdjoint (positiveResolventOperator R) := by
  let A := positiveResolventOperator R
  have hd := positiveResolventOperator_dense_domain R hR hsym
  have hle : A ≤ A.adjoint :=
    (positiveResolventOperator_formalAdjoint R hR hsym).le_adjoint hd
  apply le_antisymm ?_ hle
  constructor
  · intro y hy
    let w := A.adjoint ⟨y, hy⟩
    have hrep : R (w + y) = y := by
      apply ext_inner_right ℝ
      intro f
      have hx := (positiveResolventOperator_mem_domain R hR (R f)).mpr ⟨f, rfl⟩
      have hp := LinearPMap.adjoint_isFormalAdjoint hd ⟨y, hy⟩ ⟨R f, hx⟩
      change inner ℝ w (R f) = inner ℝ y (positiveResolventOperator R ⟨R f, hx⟩) at hp
      rw [positiveResolventOperator_apply R hR f hx] at hp
      rw [hsym, inner_add_left, inner_sub_right] at *
      linarith
    exact (positiveResolventOperator_mem_domain R hR y).mpr ⟨w + y, hrep⟩
  · intro x y hxy
    exact ((LinearPMap.adjoint_apply_eq hd x (x₀ := A y)) (fun v => by
      have hp := positiveResolventOperator_formalAdjoint R hR hsym y v
      simpa only [hxy] using hp))

end CutoffRigidity
