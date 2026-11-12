/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.Preamble
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Tactic.Linarith

-- [TABLET NODE: P4793T1SupportingFace]

/-!
# P4793T1SupportingFace

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4793T1SupportingFace {E : Type*} [AddCommGroup E] [Module Real E]
    (S : Set E) (f : E →ᵃ[Real] Real) (hf : ∀ x ∈ S, 0 ≤ f x) :
    (∀ x ∈ convexHull Real S, 0 ≤ f x) ∧
    convexHull Real S ∩ {x | f x = 0} = convexHull Real (S ∩ {x | f x = 0}) := by
-- BODY
  have hmap (x y : E) (a b : Real) (hab : a + b = 1) :
      f (a • x + b • y) = a * f x + b * f y := by
    rw [AffineMap.decomp f]
    simp only [Pi.add_apply, map_add, map_smul, smul_eq_mul]
    nlinarith only [show (a+b) * f 0 = f 0 by rw [hab]; ring]
  let C := convexHull Real (S ∩ {x | f x = 0})
  have h : convexHull Real S ⊆ {x | 0 ≤ f x ∧ (f x = 0 → x ∈ C)} := by
    apply convexHull_min
    · intro x hx
      exact ⟨hf x hx, fun hzero => subset_convexHull Real _ ⟨hx, hzero⟩⟩
    · intro x hx y hy a b ha hb hab
      change 0 ≤ f (a • x + b • y) ∧ (f (a • x + b • y) = 0 → _)
      rw [hmap x y a b hab]
      refine ⟨add_nonneg (mul_nonneg ha hx.1) (mul_nonneg hb hy.1), ?_⟩
      intro hz
      by_cases ha0 : a = 0
      · have hb1 : b = 1 := by linarith
        simpa [ha0, hb1] using hy.2 (by simpa [ha0, hb1] using hz)
      by_cases hb0 : b = 0
      · have ha1 : a = 1 := by linarith
        simpa [hb0, ha1] using hx.2 (by simpa [hb0, ha1] using hz)
      have hfx : f x = 0 := by
        have hz' : a * f x = 0 := by nlinarith [mul_nonneg hb hy.1, mul_nonneg ha hx.1]
        exact (mul_eq_zero.mp hz').resolve_left ha0
      have hfy : f y = 0 := by
        have hz' : b * f y = 0 := by nlinarith [mul_nonneg hb hy.1, mul_nonneg ha hx.1]
        exact (mul_eq_zero.mp hz').resolve_left hb0
      exact (convex_convexHull Real _) (hx.2 hfx) (hy.2 hfy) ha hb hab
  refine ⟨fun x hx => (h hx).1, Set.Subset.antisymm ?_ ?_⟩
  · intro x hx
    exact (h hx.1).2 hx.2
  · apply convexHull_min
    · intro x hx
      exact ⟨subset_convexHull Real S hx.1, hx.2⟩
    · apply (convex_convexHull Real S).inter
      intro x hx y hy a b ha hb hab
      change f (a • x + b • y) = 0
      rw [hmap x y a b hab, hx, hy]
      ring

end ApollonianSuperharmonic

end
