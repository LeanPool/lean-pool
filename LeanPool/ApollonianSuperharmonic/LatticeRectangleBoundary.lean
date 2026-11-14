/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.LatticeVertexBoundary

/-!
# LatticeRectangleBoundary

A coordinate description of the vertex boundary, including degenerate rectangles.
Adapted from Wesley Pegden's Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
-/

@[expose] public section

namespace ApollonianSuperharmonic

/-- Boundary vertices of an integer rectangle lie on one of its four sides. -/
theorem LatticeVertexBoundary.rectangle :
    ∀ (l : ℤ), ∀ (r : ℤ), ∀ (d : ℤ), ∀ (u : ℤ), ∀ (z : GaussianInt), z ∈ LatticeVertexBoundary {w
        : GaussianInt | l ≤ w.re ∧ w.re ≤ r ∧ d ≤ w.im ∧ w.im ≤ u} ↔ (l ≤ z.re ∧ z.re ≤ r ∧ d ≤
        z.im ∧ z.im ≤ u) ∧ (z.re = l ∨ z.re = r ∨ z.im = d ∨ z.im = u) := by
  classical
  intro l r d u z
  constructor
  · rintro ⟨hz, y, hy, hyr, hyi⟩
    refine ⟨hz, ?_⟩
    change l ≤ z.re ∧ z.re ≤ r ∧ d ≤ z.im ∧ z.im ≤ u at hz
    change ¬(l ≤ y.re ∧ y.re ≤ r ∧ d ≤ y.im ∧ y.im ≤ u) at hy
    omega
  · rintro ⟨hz, he⟩
    refine ⟨hz, ?_⟩
    rcases he with he | he | he | he
    · refine ⟨⟨z.re - 1, z.im⟩, ?_, ?_, ?_⟩ <;>
        simp only [Set.mem_ofPred_eq] <;> omega
    · refine ⟨⟨z.re + 1, z.im⟩, ?_, ?_, ?_⟩ <;>
        simp only [Set.mem_ofPred_eq] <;> omega
    · refine ⟨⟨z.re, z.im - 1⟩, ?_, ?_, ?_⟩ <;>
        simp only [Set.mem_ofPred_eq] <;> omega
    · refine ⟨⟨z.re, z.im + 1⟩, ?_, ?_, ?_⟩ <;>
        simp only [Set.mem_ofPred_eq] <;> omega

end ApollonianSuperharmonic

end
