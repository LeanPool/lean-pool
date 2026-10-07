/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Setting.Derivatives
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Topology
public import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Coordinate directional derivative on a time slice

`axisDeriv j` is the directional derivative along the `j`-th coordinate axis on a
spatial slice `{t}` fixed.  The lemmas below transport the repository's
`spatialPartial` / `multiPartial` derivatives — which are functions of a full
`ParabolicPoint` — to iterated Fréchet derivatives of the spatial restriction
`h(·, t)`.  This is the form consumed by the analyticity criterion
(`thm:analytic:interior`).
-/

public section

open Set
open CKN.Foundation.Parabolic CKN

noncomputable section



namespace CIV

/-- The directional derivative of a function of the space variable along a coordinate axis. -/
@[expose] def axisDeriv (j : Fin 3) (G : Vec3 → ℝ) : Vec3 → ℝ := fun x => fderiv ℝ G x (basisVec j)

/-- Iterating `spatialPartial` on a time slice produces iterated `axisDeriv` on the spatial
restriction. -/
theorem slice_spatialPartial_iterate (h : ParabolicPoint → ℝ) (j : Fin 3) (m : ℕ) (t : ℝ) :
    (fun x : Vec3 => ((fun k => spatialPartial k j)^[m] h) (x, t)) =
      (axisDeriv j)^[m] (fun x : Vec3 => h (x, t)) := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact congrArg (axisDeriv j) ih

/-- The multi-index spatial derivative on a time slice factors as iterated
`axisDeriv` applied in coordinate order. -/
theorem multiPartial_slice (h : ParabolicPoint → ℝ) (α : Fin 3 → ℕ) (t : ℝ) :
    (fun x : Vec3 => multiPartial h α (x, t)) =
      (axisDeriv 0)^[α 0] ((axisDeriv 1)^[α 1] ((axisDeriv 2)^[α 2]
        (fun x : Vec3 => h (x, t)))) := by
  rw [show (fun x : Vec3 => multiPartial h α (x, t)) =
      (fun x : Vec3 => ((fun k => spatialPartial k 0)^[α 0]
        ((fun k => spatialPartial k 1)^[α 1]
          ((fun k => spatialPartial k 2)^[α 2] h))) (x, t)) from rfl,
    slice_spatialPartial_iterate, slice_spatialPartial_iterate, slice_spatialPartial_iterate]

end CIV
