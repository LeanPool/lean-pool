/-
Copyright (c) 2026 Lukas Liehr, Mitchell A. Taylor, Peiyang Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Liehr, Mitchell A. Taylor, Peiyang Yu
-/
module

public import LeanPool.GrothendieckBessel.MainTheorem


/-!
# Grothendieck's theorem for Bessel sequences

Source: arxiv:2608.12280, url:https://github.com/lukasliehr/GrothendieckBessel/tree/f1ad1c7680bce2b1ab4218a02bddd694fb57062a
Authors: Lukas Liehr, Mitchell A. Taylor, Peiyang Yu
Status: verified
Main declarations: `GrothendieckBessel.main`
Tags: functional-analysis, bessel-sequences, gram-matrices
MSC: 46B15, 46B25, 46C05
-/



/-!
# Countable Grothendieck--Bessel Gram representation, with proofs

Proof-carrying counterpart to the declaration in `Showcase.lean`.
Adapted for Lean Pool from the Apache-2.0 upstream formalization, with module-system,
Mathlib API, and compilation changes.
-/

@[expose] public section


noncomputable section

open MeasureTheory
open scoped BigOperators ComplexConjugate InnerProductSpace

namespace GrothendieckBessel

theorem main_withProof
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (x : ℕ → H) (hx : BesselSequenceBoundOne x) :
    ∃ f : ℕ → ℝ → ℂ,
      (∀ j, AEStronglyMeasurable (f j) μ) ∧
      (∀ j t, t ∈ unitInterval → ‖f j t‖ ≤ 1) ∧
      ∀ j k,
        ⟪x k, x j⟫_ℂ =
          ∫ t in unitInterval, f j t * star (f k t) := by
  exact main_proof H x hx

/--
Comparator-facing proved counterpart to `GrothendieckBessel.main` in
`Showcase.lean`. The existing `main_withProof` entry point is retained.
-/
theorem main
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (x : ℕ → H) (hx : BesselSequenceBoundOne x) :
    ∃ f : ℕ → ℝ → ℂ,
      (∀ j, AEStronglyMeasurable (f j) μ) ∧
      (∀ j t, t ∈ unitInterval → ‖f j t‖ ≤ 1) ∧
      ∀ j k,
        ⟪x k, x j⟫_ℂ =
          ∫ t in unitInterval, f j t * star (f k t) := by
  exact main_withProof H x hx

end GrothendieckBessel
