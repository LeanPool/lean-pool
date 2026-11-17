/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P5432T1Normalization
public import LeanPool.ApollonianSuperharmonic.P5432T1EdgeLedger
public import LeanPool.ApollonianSuperharmonic.P4062T1OrientationTransport
public import LeanPool.ApollonianSuperharmonic.DiamondLaplacianTable

-- [TABLET NODE: DiamondTileAcyclicIndegree]

/-!
# DiamondTileAcyclicIndegree

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem DiamondTileAcyclicIndegree :
    ∀ (K : DiamondParameter), ∀ (T : ProtoTile), ∀ (h : PartialOdometer), ∀ (g :
        IntegerLatticeFunction), (BandPrototile ((DiamondRecursiveQuadruple K) 0) T) →
        ((TileOdometer ((DiamondRecursiveQuadruple K) 0) T h) → (((h.domain : Set GaussianInt) =
        FootprintVertices T) → ((GlobalOdometerExtends g h) → (
    let D := h.domain.filter fun x =>
      @decide (x ∉ BoundaryFootprintVertices T) (Classical.propDecidable _)
    Nonempty (AcyclicIndegreeOrientation D
      (fun x => 2 + FourNeighborLaplacian g x)))))) := by
  intro K T h g hT hodo hdom hext
-- BODY
  classical
  let D := h.domain.filter fun x =>
    @decide (x ∉ BoundaryFootprintVertices T) (Classical.propDecidable _)
  change Nonempty (AcyclicIndegreeOrientation D (fun x => 2 + FourNeighborLaplacian g x))
  obtain ⟨u, hinterior, hlap⟩ := P5432T1Normalization K T h g hodo hdom hext
  have hm (x : GaussianInt) : x ∈ D ↔ x-u ∈ DiamondVertexDomains K true := by
    simpa only [D, Finset.mem_filter, decide_eq_true_eq] using hinterior x
  let E := D.image (fun x => x-u)
  have hE (x : GaussianInt) : x ∈ E ↔ x ∈ DiamondVertexDomains K true := by
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      exact (hm y).mp hy
    · intro hx
      exact Finset.mem_image.mpr ⟨x+u, (hm _).mpr (by simpa using hx), by simp⟩
  let edge := fun x y : GaussianInt =>
    x ∈ E ∧ y ∈ E ∧ FourNeighborAdjacent x y ∧
      (x.re.natAbs < y.re.natAbs ∨
        (x.re = y.re ∧ ¬ Even (x.re+x.im) ∧ Even (y.re+y.im)))
  let rank := fun x : GaussianInt =>
    2 * x.re.natAbs + if Even (x.re+x.im) then 1 else 0
  obtain ⟨hsupported, horiented, hincreasing, hcount⟩ := P5432T1EdgeLedger K E hE
  let o : AcyclicIndegreeOrientation E
      (fun x => 2 + FourNeighborLaplacian (DiamondOdometer K) x) := {
    edge := edge
    edgeDecidable := fun _ _ => Classical.propDecidable _
    rank := rank
    supported := hsupported
    oriented := horiented
    increasing := hincreasing
    indegree := by
      intro x hx
      rw [hcount x hx, (DiamondLaplacianTable K).2.2 x ((hE x).mp hx)]
      split_ifs <;> norm_num }
  have hDE : D = E.image (fun x => x+u) := by
    simp [E, Finset.image_image, Function.comp_def]
  have hsigma : ∀ x ∈ D, 2 + FourNeighborLaplacian g x =
      2 + FourNeighborLaplacian (DiamondOdometer K) (x-u) := by
    intro x hx
    rw [hlap x ((hm x).mp hx)]
  obtain ⟨transported, _, _⟩ := P4062T1OrientationTransport E D
    (fun x => 2 + FourNeighborLaplacian (DiamondOdometer K) x)
    (fun x => 2 + FourNeighborLaplacian g x) u hDE hsigma o
  exact ⟨transported⟩

end ApollonianSuperharmonic

end
