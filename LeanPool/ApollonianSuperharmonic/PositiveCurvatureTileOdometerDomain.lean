/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.TileOdometer

-- [TABLET NODE: PositiveCurvatureTileOdometerDomain]

/-!
# PositiveCurvatureTileOdometerDomain

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem PositiveCurvatureTileOdometerDomain :
    ∀ (C : CircleCoordinates), ∀ (T : ProtoTile), ∀ (h : PartialOdometer), (0 < C.1) →
        ((TileOdometer C T h) → ((h.domain : Set GaussianInt) = FootprintVertices T)) := by
  intro C T h hC hO
-- BODY
  have domain_from_odo : ∀ (c : CircleCoordinates) (U : ProtoTile) (k : PartialOdometer),
      TileOdometer c U k → (k.domain : Set GaussianInt) = FootprintVertices U := by
    intro c U k ho
    induction ho with
    | line w x hw k hdom =>
        simp [hdom, FootprintVertices]
    | unit z x U k hU hdom htrans =>
        exact hdom
    | @decompose q hq S U hs k hU hsub hcells hfoot hcentroid hdom hvalue hcompat hslope ih =>
        ext y
        change (y ∈ k.domain) ↔ y ∈ FootprintVertices U
        rw [hdom]
        have child (i : Fin 3) (s : Bool) :
            (hs i s).domain = FootprintVertices (S i s) :=
          ih i s
        change (∃ i s, y ∈ (hs i s).domain) ↔ y ∈ FootprintVertices U
        have union : (∃ i s, y ∈ (hs i s).domain) ↔
            ∃ i s, y ∈ FootprintVertices (S i s) := by
          constructor
          · rintro ⟨i, s, hy⟩
            exact ⟨i, s, (Set.ext_iff.mp (child i s) y).mp hy⟩
          · rintro ⟨i, s, hy⟩
            exact ⟨i, s, (Set.ext_iff.mp (child i s) y).mpr hy⟩
        rw [union]
        clear hq hU hsub hcentroid hvalue hcompat hslope ih child union
        classical
        simp only [FootprintVertices]
        constructor
        · rintro ⟨i, s, hy⟩
          exact hfoot i s hy
        · intro hy
          by_cases hu : U.cells.Nonempty
          · simp only [ite_eq_left hu, Set.mem_ofPred_eq] at hy
            rcases hy with ⟨x, hx, hv⟩
            rcases (hcells x).mp hx with ⟨i, s, hxs⟩
            have hs : (S i s).cells.Nonempty := ⟨x, hxs⟩
            refine ⟨i, s, ?_⟩
            simp only [ite_eq_left hs, Set.mem_ofPred_eq]
            exact ⟨x, hxs, hv⟩
          · have hs_empty : ∀ i s, ¬ (S i s).cells.Nonempty := by
              intro i s hs
              rcases hs with ⟨x, hx⟩
              apply hu
              exact ⟨x, (hcells x).mpr ⟨i, s, hx⟩⟩
            have ha : (S 0 false).anchor = U.anchor := by
              have hh := hfoot 0 false
              rw [FootprintVertices, ite_eq_right (hs_empty 0 false),
                FootprintVertices, ite_eq_right hu] at hh
              have hm := hh (Set.mem_singleton _)
              simpa using hm
            simp only [ite_eq_right hu, Set.mem_singleton_iff] at hy
            refine ⟨0, false, ?_⟩
            simp only [ite_eq_right (hs_empty 0 false), Set.mem_singleton_iff]
            simpa [ha] using hy
  exact domain_from_odo C T h hO

end ApollonianSuperharmonic

end
