/-
Copyright (c) 2026 Lukas Liehr, Mitchell A. Taylor, Peiyang Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Liehr, Mitchell A. Taylor, Peiyang Yu
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Countable Gram-kernel conventions
Adapted for Lean Pool from the Apache-2.0 upstream formalization, with module-system,
Mathlib API, and compilation changes.
-/

@[expose] public section


noncomputable section

open MeasureTheory
open scoped BigOperators ComplexConjugate ENNReal

namespace GrothendieckBessel

/-- The unit interval `[0,1]`. -/
def unitInterval : Set ℝ :=
  Set.Icc (0 : ℝ) 1

/-- Lebesgue measure restricted to `[0,1]`. -/
abbrev μ : Measure ℝ :=
  volume.restrict unitInterval

/--
A Bessel sequence in a complex Hilbert space with bound `1`, expressed by
the standard inequality for all finitely supported coefficient families.
-/
def BesselSequenceBoundOne
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (x : ℕ → H) : Prop :=
    ∀ (F : Finset ℕ) (c : ℕ → ℂ),
      ‖∑ j ∈ F, c j • x j‖ ^ 2 ≤ ∑ j ∈ F, ‖c j‖ ^ 2

/-- Lebesgue measure restricted to a measurable set. -/
abbrev μOn (S : Set ℝ) : Measure ℝ :=
  volume.restrict S

/-- The linear-in-the-first `L²` correlation on a measurable set. -/
def l2InnerOn (S : Set ℝ) (f g : ℝ → ℂ) : ℂ :=
  ∫ t, f t * star (g t) ∂μOn S

/--
Every finite quadratic form of the kernel is nonnegative and bounded above by
the coefficient `ℓ²` norm.  This is the finite positive-contraction condition
used in the compactness argument.
-/
def FiniteHermitianPositiveContraction {J : Type*} (h : J → J → ℂ) : Prop :=
  (∀ j k, h k j = star (h j k)) ∧
    ∀ F : Finset J, ∀ c : J → ℂ,
      0 ≤ (F.sum (fun j => F.sum (fun k => c j * star (c k) * h j k))).re ∧
        (F.sum (fun j => F.sum (fun k => c j * star (c k) * h j k))).re ≤
          F.sum (fun j => ‖c j‖ ^ 2)

end GrothendieckBessel
