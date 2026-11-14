/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.PeriodicTileCore

-- [TABLET NODE: P3723T1ContactStabilizer]

/-!
# P3723T1ContactStabilizer

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P3723T1ContactStabilizer {ι : Type} (P : PeriodicTileCore ι)
    (u : P.lattice) (a b : ι)
    (h : ({P.shift u a, P.shift u b} : Set ι) = {a, b}) : u = 0 := by
-- BODY
  have pairzero (p q w : Real × Real)
      (h : ({p + w, q + w} : Set (Real × Real)) = {p, q}) : w = 0 := by
    have hp : p + w = p ∨ p + w = q := by
      have hm : p + w ∈ ({p, q} : Set (Real × Real)) := by
        rw [← h]
        simp
      simpa using hm
    have hq : q + w = p ∨ q + w = q := by
      have hm : q + w ∈ ({p, q} : Set (Real × Real)) := by
        rw [← h]
        simp
      simpa using hm
    rcases hp with hp | hp
    · have h1 := congrArg Prod.fst hp
      have h2 := congrArg Prod.snd hp
      change p.1 + w.1 = p.1 at h1
      change p.2 + w.2 = p.2 at h2
      apply Prod.ext <;> change _ = (0 : Real) <;> linarith
    · rcases hq with hq | hq
      · have h1 := congrArg Prod.fst hp
        have h2 := congrArg Prod.snd hp
        have h3 := congrArg Prod.fst hq
        have h4 := congrArg Prod.snd hq
        change p.1 + w.1 = q.1 at h1
        change p.2 + w.2 = q.2 at h2
        change q.1 + w.1 = p.1 at h3
        change q.2 + w.2 = p.2 at h4
        apply Prod.ext <;> change _ = (0 : Real) <;> linarith
      · have h1 := congrArg Prod.fst hq
        have h2 := congrArg Prod.snd hq
        change q.1 + w.1 = q.1 at h1
        change q.2 + w.2 = q.2 at h2
        apply Prod.ext <;> change _ = (0 : Real) <;> linarith
  have hpos :
      ({P.plane.position a + GaussianRealPoint u,
        P.plane.position b + GaussianRealPoint u} : Set (Real × Real)) =
        {P.plane.position a, P.plane.position b} := by
    have himage := congrArg (fun s : Set ι => P.plane.position '' s) h
    simpa only [Set.image_insert_eq, Set.image_singleton,
      P.position_periodic] using himage
  have hz := pairzero _ _ _ hpos
  apply Subtype.ext
  ext
  · have h1 := congrArg Prod.fst hz
    change (((u : GaussianInt).re : Int) : Real) = 0 at h1
    change (u : GaussianInt).re = 0
    exact_mod_cast h1
  · have h2 := congrArg Prod.snd hz
    change (((u : GaussianInt).im : Int) : Real) = 0 at h2
    change (u : GaussianInt).im = 0
    exact_mod_cast h2

end ApollonianSuperharmonic

end
