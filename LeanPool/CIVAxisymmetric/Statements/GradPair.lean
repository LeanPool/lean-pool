/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Ambient.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
# Grad Pair

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open CKN


noncomputable section

namespace CIV

/-- The spatial gradient of a test function paired with a vector. -/
@[expose] def gradPair (m : ℕ) (φ : Vec m × ℝ → ℝ) (z : Vec m × ℝ) (v : Vec m) : ℝ :=
  fderiv ℝ (fun x : Vec m => φ (x, z.2)) z.1 v

end CIV
