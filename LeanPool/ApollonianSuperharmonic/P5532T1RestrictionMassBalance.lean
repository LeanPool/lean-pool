/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandCanonicalPeriodicExtension
public import LeanPool.ApollonianSuperharmonic.PeriodicTileTotalIndegree

-- [TABLET NODE: P5532T1RestrictionMassBalance]

/-!
# P5532T1RestrictionMassBalance

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5532T1RestrictionMassBalance
    (c : CircleCoordinates) (U : ProtoTile) (k : PartialOdometer)
    (g : IntegerLatticeFunction) (ho : TileOdometer c U k)
    (hdom : (k.domain : Set GaussianInt) = FootprintVertices U)
    (hext : GlobalOdometerExtends g k) :
    let I := k.domain.filter fun x =>
      @decide (x ∉ BoundaryFootprintVertices U) (Classical.propDecidable _)
    (∑ x ∈ I, (2 + FourNeighborLaplacian g x)) =
      ((((I.product I).filter fun e => @decide (FourNeighborAdjacent e.1 e.2)
        (Classical.propDecidable _)).card / 2 : ℕ) : ℤ) := by
-- BODY
  classical
  cases ho with
  | line w x hw k hk =>
    have hempty : (k.domain.filter fun y =>
        @decide (y ∉ BoundaryFootprintVertices (⟨∅, x⟩ : ProtoTile))
          (Classical.propDecidable _)) = ∅ := by
      ext y
      simp [hk, BoundaryFootprintVertices]
    dsimp only
    rw [hempty]
    simp [Finset.product_eq_sprod]
  | unit z x U k hcell hdomain htrans =>
    have hne : U.cells.Nonempty := by rw [hcell]; simp
    have bottom : {x, x + 1} ∈ BoundaryFootprintEdges U := by
      refine ⟨x, Or.inl ⟨rfl, Or.inl ⟨?_, ?_⟩⟩⟩
      · simp [hcell]
      · simp only [hcell, Finset.mem_singleton]
        intro hh
        have hh' := congrArg Zsqrtd.im hh
        simp at hh'
    have left : {x, x + ⟨0, 1⟩} ∈ BoundaryFootprintEdges U := by
      refine ⟨x, Or.inr ⟨rfl, Or.inl ⟨?_, ?_⟩⟩⟩
      · simp [hcell]
      · simp only [hcell, Finset.mem_singleton]
        intro hh
        have hh' := congrArg Zsqrtd.re hh
        simp at hh'
    have right : {x + 1, x + 1 + ⟨0, 1⟩} ∈ BoundaryFootprintEdges U := by
      refine ⟨x + 1, Or.inr ⟨rfl, Or.inr ⟨?_, ?_⟩⟩⟩
      · simp only [hcell, Finset.mem_singleton]
        intro hh
        have hh' := congrArg Zsqrtd.re hh
        simp at hh'
      · simp [hcell]
    have hb0 : x ∈ BoundaryFootprintVertices U := by
      rw [BoundaryFootprintVertices, ite_eq_left hne]
      exact ⟨{x, x + 1}, bottom, by simp⟩
    have hb1 : x + 1 ∈ BoundaryFootprintVertices U := by
      rw [BoundaryFootprintVertices, ite_eq_left hne]
      exact ⟨{x, x + 1}, bottom, by simp⟩
    have hbi : x + ⟨0, 1⟩ ∈ BoundaryFootprintVertices U := by
      rw [BoundaryFootprintVertices, ite_eq_left hne]
      exact ⟨{x, x + ⟨0, 1⟩}, left, by simp⟩
    have hb1i : x + 1 + ⟨0, 1⟩ ∈ BoundaryFootprintVertices U := by
      rw [BoundaryFootprintVertices, ite_eq_left hne]
      exact ⟨{x + 1, x + 1 + ⟨0, 1⟩}, right, by simp⟩
    have hempty : (k.domain.filter fun y =>
        @decide (y ∉ BoundaryFootprintVertices U) (Classical.propDecidable _)) = ∅ := by
      ext y
      simp only [Finset.mem_filter, decide_eq_true_eq, Finset.notMem_empty, iff_false]
      rintro ⟨hy, hnb⟩
      have hyfoot : y ∈ FootprintVertices U := by rw [← hdom]; exact hy
      simp only [FootprintVertices, ite_eq_left hne, Set.mem_ofPred_eq] at hyfoot
      obtain ⟨a, ha, hv⟩ := hyfoot
      have hax : a = x := by simpa [hcell] using ha
      subst a
      rcases hv with hv | hv | hv | hv
      · rw [hv] at hnb; exact hnb hb0
      · rw [hv] at hnb; exact hnb hb1
      · rw [hv] at hnb; exact hnb hbi
      · rw [hv] at hnb; exact hnb hb1i
    dsimp only
    rw [hempty]
    simp [Finset.product_eq_sprod]
  | @decompose p hp S U hs k hU hsub hcells hfoot hcentroid hdomain
      hvalue hcompat hslope =>
    have hk : TileOdometer (p 0) U k := TileOdometer.decompose hp hU hsub
      hcells hfoot hcentroid hdomain hvalue hcompat hslope
    have hpos : 0 < (p 0).1 := (ProperBandCurvatureStructure p hp).1
    let C : BandCircle := ⟨⟨p 0, Or.inl hpos, p, hp.1, 0, rfl⟩, hpos⟩
    obtain ⟨G, hG, hlat, htile, hweb, hperiod, hlap⟩ :=
      BandCanonicalPeriodicExtension C p hp rfl U k g hU hk hdom hext
    have hm := PeriodicTileTotalIndegree C U k G hdom hU hlat htile hweb hperiod
    dsimp only at hm ⊢
    rw [← hm]
    apply Finset.sum_congr rfl
    intro x hx
    have hx' := Finset.mem_filter.mp hx
    have hnb : x ∉ BoundaryFootprintVertices U :=
      @of_decide_eq_true _ (Classical.propDecidable _) hx'.2
    rw [hlap x hx'.1 hnb]

end ApollonianSuperharmonic

end
