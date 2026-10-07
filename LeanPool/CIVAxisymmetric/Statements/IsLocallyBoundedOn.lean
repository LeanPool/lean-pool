/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Ambient.Basic
public import Mathlib.Data.Set.Prod
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Is Locally Bounded On

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open MeasureTheory Set
open CKN


noncomputable section

namespace CIV

/-- `q ∈ L^∞_loc(I; L^∞(ℝ^m))`. -/
@[expose] def IsLocallyBoundedOn (m : ℕ) (I : Set ℝ) (q : Vec m × ℝ → ℝ) : Prop :=
  AEStronglyMeasurable q (volume.restrict (univ ×ˢ I)) ∧
    ∀ J : Set ℝ, IsCompact J → J ⊆ I → ∃ M : ℝ, ∀ᵐ z ∂(volume.restrict (univ ×ˢ J)), |q z| ≤ M

end CIV
