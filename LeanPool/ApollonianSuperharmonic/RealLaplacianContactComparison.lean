/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.RealFourNeighborLaplacian

-- [TABLET NODE: RealLaplacianContactComparison]

/-!
# RealLaplacianContactComparison

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem RealLaplacianContactComparison :
    (forall (u v : GaussianInt -> Real) (x : GaussianInt),
      u x = v x ->
      (forall y, y = x + 1 ∨ y = x - 1 ∨ y = x + ⟨0, 1⟩ ∨
        y = x - ⟨0, 1⟩ -> u y <= v y) ->
      RealFourNeighborLaplacian u x <= RealFourNeighborLaplacian v x) /\
    (forall (F : Nat -> GaussianInt -> Real) (g : GaussianInt -> Real)
      (M : Real) (x : GaussianInt),
      (forall i, RealFourNeighborLaplacian (F i) x <= M) ->
      (exists i, g x = F i x /\
        forall y, y = x + 1 ∨ y = x - 1 ∨ y = x + ⟨0, 1⟩ ∨
          y = x - ⟨0, 1⟩ -> g y <= F i y) ->
      RealFourNeighborLaplacian g x <= M) /\
    (forall (F : Nat -> GaussianInt -> Real) (g : GaussianInt -> Real)
      (M : Real) (x : GaussianInt),
      (forall i, M <= RealFourNeighborLaplacian (F i) x) ->
      (exists i, g x = F i x /\
        forall y, y = x + 1 ∨ y = x - 1 ∨ y = x + ⟨0, 1⟩ ∨
          y = x - ⟨0, 1⟩ -> F i y <= g y) ->
      M <= RealFourNeighborLaplacian g x) := by
-- BODY
  constructor
  · intro u v x hcenter hneighbors
    unfold RealFourNeighborLaplacian
    have hright := hneighbors (x + 1) (Or.inl rfl)
    have hleft := hneighbors (x - 1) (Or.inr (Or.inl rfl))
    have hup := hneighbors (x + ⟨0, 1⟩) (Or.inr (Or.inr (Or.inl rfl)))
    have hdown := hneighbors (x - ⟨0, 1⟩) (Or.inr (Or.inr (Or.inr rfl)))
    linarith
  constructor
  · intro F g M x hbound hattained
    obtain ⟨i, hvalue, hcontact⟩ := hattained
    have hcomparison := (show
        RealFourNeighborLaplacian g x <= RealFourNeighborLaplacian (F i) x from
      (by
        unfold RealFourNeighborLaplacian
        have hright := hcontact (x + 1) (Or.inl rfl)
        have hleft := hcontact (x - 1) (Or.inr (Or.inl rfl))
        have hup := hcontact (x + ⟨0, 1⟩) (Or.inr (Or.inr (Or.inl rfl)))
        have hdown := hcontact (x - ⟨0, 1⟩) (Or.inr (Or.inr (Or.inr rfl)))
        linarith))
    linarith [hbound i]
  · intro F g M x hbound hattained
    obtain ⟨i, hvalue, hcontact⟩ := hattained
    have hcomparison := (show
        RealFourNeighborLaplacian (F i) x <= RealFourNeighborLaplacian g x from
      (by
        unfold RealFourNeighborLaplacian
        have hright := hcontact (x + 1) (Or.inl rfl)
        have hleft := hcontact (x - 1) (Or.inr (Or.inl rfl))
        have hup := hcontact (x + ⟨0, 1⟩) (Or.inr (Or.inr (Or.inl rfl)))
        have hdown := hcontact (x - ⟨0, 1⟩) (Or.inr (Or.inr (Or.inr rfl)))
        linarith [hvalue]))
    linarith [hbound i]

end ApollonianSuperharmonic

end
