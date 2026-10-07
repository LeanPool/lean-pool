/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Ambient.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Data.Set.Prod

/-!
# Test Functions

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open Set
open CKN


noncomputable section

namespace CIV

/-- Test functions on `Vec m × ℝ` supported in `Vec m × I`. -/
@[expose] def testFunctions (m : ℕ) (I : Set ℝ) : Set (Vec m × ℝ → ℝ) :=
  {φ | ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ univ ×ˢ I}

end CIV
