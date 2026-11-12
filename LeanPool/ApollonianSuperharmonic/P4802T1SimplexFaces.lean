/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import Mathlib.Basic.Real.Basic

public import Mathlib.Analysis.Convex.Combination

-- [TABLET NODE: P4802T1SimplexFaces]

/-!
# P4802T1SimplexFaces

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4802T1SimplexFaces {E : Type*} [AddCommGroup E] [Module Real E]
    (V : Set E) (hV : V.Finite) (hi : AffineIndependent Real (fun x : V => (x : E)))
    (S T : Set E) (hS : S ⊆ V) (hT : T ⊆ V) :
    convexHull Real S ∩ convexHull Real T = convexHull Real (S ∩ T) := by
-- BODY
  classical
  have hs := hV.subset hS
  have ht := hV.subset hT
  have hh : AffineIndependent Real (fun x : hV.toFinset => (x : E)) := by
    change AffineIndependent Real (fun x : (hV.toFinset : Set E) => (x : E))
    rw [hV.coe_toFinset]
    exact hi
  have he := hh.convexHull_inter (hs.toFinset_subset_toFinset.mpr hS)
    (ht.toFinset_subset_toFinset.mpr hT)
  simpa only [hs.coe_toFinset, ht.coe_toFinset] using he.symm

end ApollonianSuperharmonic

end
