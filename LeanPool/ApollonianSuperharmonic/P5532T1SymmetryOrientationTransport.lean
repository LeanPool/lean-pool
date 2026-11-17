/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P5532T1OrientationPullback
public import LeanPool.ApollonianSuperharmonic.P5686T1UniformGlobalOdometerTransport
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryTileOdometerCovariance
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryPartialOdometerAction
public import LeanPool.ApollonianSuperharmonic.BandPackingSymmetryTileAction
public import LeanPool.ApollonianSuperharmonic.GlobalOdometerExtends

-- [TABLET NODE: P5532T1SymmetryOrientationTransport]

/-!
# P5532T1SymmetryOrientationTransport

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5532T1SymmetryOrientationTransport
    (s : BandPackingSymmetry) (c : CircleCoordinates) (T : ProtoTile)
    (h : PartialOdometer) (g : IntegerLatticeFunction)
    (ho : TileOdometer c T h) (hext : GlobalOdometerExtends g h) :
    ∃ g' : IntegerLatticeFunction,
      GlobalOdometerExtends g' (BandPackingSymmetryPartialOdometerAction s h) ∧
      let D := h.domain.filter fun x =>
        @decide (x ∉ BoundaryFootprintVertices T) (Classical.propDecidable _)
      let E := (BandPackingSymmetryPartialOdometerAction s h).domain.filter fun x =>
        @decide (x ∉ BoundaryFootprintVertices (BandPackingSymmetryTileAction s T))
          (Classical.propDecidable _)
      (Nonempty (AcyclicIndegreeOrientation D (fun x => 2 + FourNeighborLaplacian g x)) ↔
        Nonempty (AcyclicIndegreeOrientation E (fun x => 2 + FourNeighborLaplacian g' x))) := by
-- BODY
  classical
  obtain ⟨g', he', hlap⟩ :=
    P5686T1UniformGlobalOdometerTransport s g h hext
  have grid : ∀ a : BandPackingSymmetry,
      Function.Bijective (BandPackingSymmetryVectorAction a) ∧
      (∀ x y, FourNeighborAdjacent x y ↔
        FourNeighborAdjacent (BandPackingSymmetryVectorAction a x)
          (BandPackingSymmetryVectorAction a y)) ∧
      ∀ V, BoundaryFootprintVertices (BandPackingSymmetryTileAction a V) =
        BandPackingSymmetryVectorAction a '' BoundaryFootprintVertices V := by
    intro a
    induction a with
    | identity =>
      refine ⟨Function.bijective_id, fun _ _ => Iff.rfl, ?_⟩
      intro V
      simp [BandPackingSymmetryTileAction, BandPackingSymmetryVectorAction]
    | shift w =>
      refine ⟨Function.bijective_id, fun _ _ => Iff.rfl, ?_⟩
      intro V
      simp [BandPackingSymmetryTileAction, BandPackingSymmetryVectorAction]
    | negate =>
      have inv (x : GaussianInt) : GaussianQuarterTurn (-GaussianQuarterTurn x) = x := by
        ext <;> simp [GaussianQuarterTurn]
      have inv' (x : GaussianInt) : -GaussianQuarterTurn (GaussianQuarterTurn x) = x := by
        ext <;> simp [GaussianQuarterTurn]
      refine ⟨⟨?_, fun x => ⟨-GaussianQuarterTurn x, inv x⟩⟩, ?_, ?_⟩
      · intro x y hxy
        simpa only [BandPackingSymmetryVectorAction, inv'] using
          congrArg (fun z => -GaussianQuarterTurn z) hxy
      · intro x y
        simp [BandPackingSymmetryVectorAction, FourNeighborAdjacent,
          GaussianQuarterTurn, Zsqrtd.ext_iff]
        omega
      · intro V
        exact (TileQuarterTurnFormulas V).2.2.2.2.2.2.2.1
    | conjugate =>
      have inv (x : GaussianInt) : -GaussianReflection (-GaussianReflection x) = x := by
        ext <;> simp [GaussianReflection]
      refine ⟨⟨?_, fun x => ⟨-GaussianReflection x, inv x⟩⟩, ?_, ?_⟩
      · intro x y hxy
        simpa only [BandPackingSymmetryVectorAction, inv] using
          congrArg (fun z => -GaussianReflection z) hxy
      · intro x y
        simp [BandPackingSymmetryVectorAction, FourNeighborAdjacent,
          GaussianReflection, Zsqrtd.ext_iff]
        omega
      · intro V
        rw [BandPackingSymmetryTileAction,
          (TileQuarterTurnFormulas _).2.2.2.2.2.2.2.1,
          (TileQuarterTurnFormulas _).2.2.2.2.2.2.2.1,
          (TileReflectionFormulas _).2.2.2.2.2.2.2.1]
        simp only [Set.image_image]
        congr 1
    | comp a b iha ihb =>
      refine ⟨iha.1.comp ihb.1, ?_, ?_⟩
      · intro x y
        exact (ihb.2.1 x y).trans (iha.2.1 _ _)
      · intro V
        simp only [BandPackingSymmetryTileAction, iha.2.2, ihb.2.2,
          BandPackingSymmetryVectorAction, Set.image_image]
  let L := BandPackingSymmetryVectorAction s
  let D := h.domain.filter fun x =>
    @decide (x ∉ BoundaryFootprintVertices T) (Classical.propDecidable _)
  let E := (BandPackingSymmetryPartialOdometerAction s h).domain.filter fun x =>
    @decide (x ∉ BoundaryFootprintVertices (BandPackingSymmetryTileAction s T))
      (Classical.propDecidable _)
  have hdomain := (BandPackingSymmetryTileOdometerCovariance s c T h ho).2.1
  have hboundary := (grid s).2.2 T
  have hE : E = D.image L := by
    ext y
    simp only [E, D, Finset.mem_filter, decide_eq_true_eq, Finset.mem_image]
    constructor
    · rintro ⟨hy, hnb⟩
      have hy' : y ∈ BandPackingSymmetryVectorAction s '' (h.domain : Set GaussianInt) := by
        rw [← hdomain]
        exact hy
      obtain ⟨x, hx, rfl⟩ := hy'
      refine ⟨x, ⟨hx, ?_⟩, rfl⟩
      intro hb
      apply hnb
      rw [hboundary]
      exact Set.mem_image_of_mem L hb
    · rintro ⟨x, ⟨hx, hnb⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · change L x ∈ ((BandPackingSymmetryPartialOdometerAction s h).domain : Set GaussianInt)
        rw [hdomain]
        exact ⟨x, hx, rfl⟩
      · intro hb
        rw [hboundary] at hb
        obtain ⟨y, hy, hyx⟩ := hb
        exact hnb ((grid s).1.1 hyx ▸ hy)
  let e : GaussianInt ≃ GaussianInt := Equiv.ofBijective L (grid s).1
  have hD : D = E.image e.symm := by
    rw [hE, Finset.image_image]
    have hf : e.symm ∘ L = id := by
      funext x
      exact e.symm_apply_apply x
    rw [hf]
    simp
  refine ⟨g', he', ?_⟩
  change Nonempty (AcyclicIndegreeOrientation D (fun x => 2 + FourNeighborLaplacian g x)) ↔
    Nonempty (AcyclicIndegreeOrientation E (fun x => 2 + FourNeighborLaplacian g' x))
  constructor
  · rintro ⟨o⟩
    apply P5532T1OrientationPullback E D
      (fun x => 2 + FourNeighborLaplacian g' x)
      (fun x => 2 + FourNeighborLaplacian g x) e.symm hD e.symm.injective
      (fun x y => ?_) (fun x hx => ?_) o
    · have ha := (grid s).2.1 (e.symm x) (e.symm y)
      change FourNeighborAdjacent (e.symm x) (e.symm y) ↔
        FourNeighborAdjacent (e (e.symm x)) (e (e.symm y)) at ha
      simpa only [e.apply_symm_apply] using ha.symm
    · have hl := hlap (e.symm x)
      change FourNeighborLaplacian g' (e (e.symm x)) =
        FourNeighborLaplacian g (e.symm x) at hl
      rw [e.apply_symm_apply] at hl
      rw [hl]
  · rintro ⟨o⟩
    exact P5532T1OrientationPullback D E
      (fun x => 2 + FourNeighborLaplacian g x)
      (fun x => 2 + FourNeighborLaplacian g' x) L hE (grid s).1.1 (grid s).2.1
      (fun x hx => by rw [hlap x]) o

end ApollonianSuperharmonic

end
