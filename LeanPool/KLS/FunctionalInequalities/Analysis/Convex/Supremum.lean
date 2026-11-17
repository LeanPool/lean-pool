/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Algebra.Order.Archimedean.Real.Hom

/-!
# Finite real suprema of convex families

A pointwise bounded-above nonempty family of real-valued convex functions has
convex conditional supremum on its common convex domain. This pure ordered
vector-space tool is shared by compact affine-support extensions and the
Dirichlet subsolution envelope supporting Letwin arXiv:2607.24164v1, Lemma 2.2.
-/

@[expose] public section

namespace FunctionalInequalities.Analysis
open Set

/-- Convexity of a finite real conditional supremum, with the nonempty family
and its pointwise upper bounds explicit. No topology or dimension is required. -/
theorem convexOn_sSup_image_of_bddAbove {E ι : Type*} [AddCommMonoid E] [Module ℝ E] {D : Set E}
    (hD : Convex ℝ D) {S : Set ι} (hS : S.Nonempty) (F : ι → E → ℝ)
    (hF : ∀ i ∈ S, ConvexOn ℝ D (F i)) (hB : ∀ x ∈ D, BddAbove ((fun i => F i x) '' S)) :
    ConvexOn ℝ D (fun x => sSup ((fun i => F i x) '' S)) := by
  refine ⟨hD, ?_⟩
  intro x hx y hy a b ha hb hab
  apply csSup_le (hS.image _)
  rintro _ ⟨i, hi, rfl⟩
  calc
    F i (a • x + b • y) ≤ a • F i x + b • F i y := (hF i hi).2 hx hy ha hb hab
    _ ≤ a • sSup ((fun i => F i x) '' S) + b • sSup ((fun i => F i y) '' S) :=
      add_le_add (smul_le_smul_of_nonneg_left (le_csSup (hB x hx) ⟨i, hi, rfl⟩) ha)
        (smul_le_smul_of_nonneg_left (le_csSup (hB y hy) ⟨i, hi, rfl⟩) hb)

end FunctionalInequalities.Analysis
