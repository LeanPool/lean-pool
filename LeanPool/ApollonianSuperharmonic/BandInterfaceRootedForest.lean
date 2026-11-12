/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandOdometerInteriorTable
public import LeanPool.ApollonianSuperharmonic.PeriodicTileTotalIndegree
public import LeanPool.ApollonianSuperharmonic.P4250T2InterfaceCycleExclusion
public import LeanPool.ApollonianSuperharmonic.P4250T2PrecursorRootSeparation
public import LeanPool.ApollonianSuperharmonic.P4250T2InterfaceNeighborCount
public import LeanPool.ApollonianSuperharmonic.P4250T2IndegreeSubtraction
public import LeanPool.ApollonianSuperharmonic.P4250T2FiniteForestCompletion

-- [TABLET NODE: BandInterfaceRootedForest]

/-!
# BandInterfaceRootedForest

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem BandInterfaceRootedForest
    (C : BandCircle) (q : Fin 4 → CircleCoordinates)
    (cfg : BandOrderedGeneralConfiguration q) (T : ProtoTile)
    (cert : BandOrderedGeneralLayoutCertificate q cfg C T)
    (h : PartialOdometer) (hs : Fin 3 → Bool → PartialOdometer)
    (g : IntegerLatticeFunction)
    (hT : BandPrototile (q 0) T)
    (hlat : LatticeTile T)
    (hodo : TileOdometer (q 0) T h)
    (hdom : (h.domain : Set GaussianInt) = FootprintVertices T)
    (hsub : ∀ i s, TileOdometer (q i.succ) (cert.P i s) (hs i s))
    (hsdom : ∀ i s, ((hs i s).domain : Set GaussianInt) =
      FootprintVertices (cert.P i s))
    (hext : GlobalOdometerExtends g h)
    (hrest : ∀ i s, GlobalOdometerExtends g (hs i s))
    (htile : ExactTileTiling (RegularTileFamily T (TilingLattice C)))
    (hweb : ∀ x, x ∈ BoundaryFootprintVertices T →
      FourNeighborLaplacian g x = 1)
    (hperiod : ∃ b : ℝ × ℝ, ∀ v, v ∈ TilingLattice C → ∀ x,
      (g (x + v) : ℝ) - LatticeQuadraticForm (CircleMatrix C) (x + v) -
          (b.1 * (x + v).re + b.2 * (x + v).im) =
        (g x : ℝ) - LatticeQuadraticForm (CircleMatrix C) x -
          (b.1 * x.re + b.2 * x.im))
    (hPorient :
      let D := h.domain.filter fun x =>
        @decide (x ∉ BoundaryFootprintVertices T) (Classical.propDecidable _)
      let P := D.filter fun x =>
        @decide (∃ i s, x ∈ (hs i s).domain ∧
          x ∉ BoundaryFootprintVertices (cert.P i s)) (Classical.propDecidable _)
      Nonempty (AcyclicIndegreeOrientation P
        (fun x => 2 + FourNeighborLaplacian g x))) :
    let D := h.domain.filter fun x =>
      @decide (x ∉ BoundaryFootprintVertices T) (Classical.propDecidable _)
    let P := D.filter fun x =>
      @decide (∃ i s, x ∈ (hs i s).domain ∧
        x ∉ BoundaryFootprintVertices (cert.P i s)) (Classical.propDecidable _)
    let W := D \ P
    ∃ R : Finset GaussianInt,
      RootedFourNeighborForest W R ∧ R.card ≤ 2 ∧
      ∀ x ∈ W,
        (2 + FourNeighborLaplacian g x) -
            (((P.filter fun y => @decide (FourNeighborAdjacent y x)
              (Classical.propDecidable _)).card : ℕ) : ℤ) =
          1 - if x ∈ R then 1 else 0 := by
-- BODY
  classical
  let D := h.domain.filter fun x =>
    @decide (x ∉ BoundaryFootprintVertices T) (Classical.propDecidable _)
  let P := D.filter fun x =>
    @decide (∃ i s, x ∈ (hs i s).domain ∧
      x ∉ BoundaryFootprintVertices (cert.P i s)) (Classical.propDecidable _)
  let W := D \ P
  let R : Finset GaussianInt := {cert.precursor_boundary.a, cert.precursor_boundary.b}
  have hD : ∀ x, x ∈ D ↔
      x ∈ FootprintVertices T ∧ x ∉ BoundaryFootprintVertices T := by
    intro x
    have hmem : x ∈ h.domain ↔ x ∈ FootprintVertices T := by
      change x ∈ (h.domain : Set GaussianInt) ↔ _
      rw [hdom]
    simp only [D, Finset.mem_filter, decide_eq_true_eq, hmem]
  have hP : ∀ x, x ∈ P ↔ x ∈ D ∧ ∃ i s,
      x ∈ FootprintVertices (cert.P i s) ∧
        x ∉ BoundaryFootprintVertices (cert.P i s) := by
    intro x
    have hmem : ∀ i s, x ∈ (hs i s).domain ↔
        x ∈ FootprintVertices (cert.P i s) := by
      intro i s
      change x ∈ ((hs i s).domain : Set GaussianInt) ↔ _
      rw [hsdom]
    simp only [P, Finset.mem_filter, decide_eq_true_eq, hmem]
  have hPD : P ⊆ D := Finset.filter_subset _ _
  obtain ⟨hattach, hcycle⟩ :=
    P4250T2InterfaceCycleExclusion C q cfg T cert hT hlat D P hD hP
  obtain ⟨hRW, hprecursor, hrootType, hcentral, hseparate⟩ :=
    P4250T2PrecursorRootSeparation C q cfg T cert hT hlat D P hD hP hattach
  have hneighbors := P4250T2InterfaceNeighborCount
    C q cfg T cert hT hlat D P hD hP hprecursor hcentral
  have residual : ∀ x ∈ W,
      (2 + FourNeighborLaplacian g x) -
        ((P.filter fun y => @decide (FourNeighborAdjacent y x)
          (Classical.propDecidable _)).card : ℤ) =
        1 - if x ∈ R then 1 else 0 := by
    intro x hx
    have hxT := (hD x).mp (Finset.mem_sdiff.mp hx).1
    have table := BandOdometerInteriorTable q cfg.proper T cert.P h hs g
      hT hodo hext cert.outer_occurrence cert.outer_union hsub hrest x hxT.1 hxT.2
    have neighbors := hneighbors x hx
    dsimp only at table neighbors
    by_cases hr : x ∈ R
    · obtain ⟨hk, hc⟩ := hrootType x hr
      have hn := neighbors.2 hr
      by_cases ho : cert.O.cells = ∅
      · have hl := table.2.1 hk (hc.mpr ho)
        rw [ite_eq_left ho] at hn
        simp only [hl, hn, ite_eq_left hr]
        norm_num
      · have hnc : GaussianRealPoint x ≠ TileCentroid T :=
          fun hcenter => ho (hc.mp hcenter)
        have hl := table.1 hk hnc
        rw [ite_eq_right ho] at hn
        simp only [hl, hn, ite_eq_left hr]
        norm_num
    · obtain ⟨hn, hk, hnc⟩ := neighbors.1 hr
      rcases hk with hk | hk
      · have hl := table.1 hk hnc
        rw [hl, ite_eq_right hr]
        omega
      · have hl := table.2.2.1 hk
        rw [hl, ite_eq_right hr]
        omega
  have hTC : BandPrototile C.1.1 T := cert.child_eq ▸ hT
  have total := PeriodicTileTotalIndegree C T h g hdom hTC hlat htile hweb hperiod
  have subtracted := P4250T2IndegreeSubtraction D P
    (fun x => 2 + FourNeighborLaplacian g x) hPD hPorient total
  have hcount : (∑ x ∈ W, (1 - if x ∈ R then (1 : ℤ) else 0)) =
      ((((W.product W).filter fun e => @decide (FourNeighborAdjacent e.1 e.2)
        (Classical.propDecidable _)).card / 2 : ℕ) : ℤ) := by
    calc
      _ = ∑ x ∈ W, ((2 + FourNeighborLaplacian g x) -
          ((P.filter fun y => @decide (FourNeighborAdjacent y x)
            (Classical.propDecidable _)).card : ℤ)) :=
        Finset.sum_congr rfl (fun x hx => (residual x hx).symm)
      _ = _ := subtracted
  exact ⟨R, P4250T2FiniteForestCompletion W R hRW hcycle hseparate hcount,
    Finset.card_le_two, residual⟩

end ApollonianSuperharmonic

end
