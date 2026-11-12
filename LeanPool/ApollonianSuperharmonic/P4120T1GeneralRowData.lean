/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralOdometerRowData
public import LeanPool.ApollonianSuperharmonic.BandPrototileCentroidUnique
public import LeanPool.ApollonianSuperharmonic.ProtoTileObservableExtensionality
public import LeanPool.ApollonianSuperharmonic.TileOdometerBandPrototile
public import LeanPool.ApollonianSuperharmonic.TileOdometerReindexedDecomposition

-- [TABLET NODE: P4120T1GeneralRowData]

/-!
# P4120T1GeneralRowData

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4120T1GeneralRowData
    (q : Fin 4 → CircleCoordinates) (cfg : BandOrderedGeneralConfiguration q)
    (C : BandCircle) (T : ProtoTile)
    (cert : BandOrderedGeneralLayoutCertificate q cfg C T)
    (h : PartialOdometer) (g : IntegerLatticeFunction)
    (hodo : TileOdometer (q 0) T h) (hext : GlobalOdometerExtends g h) :
    ∃ (P : Fin 3 → Bool → ProtoTile) (r : Fin 3 → Bool → PartialOdometer)
      (Q S : Fin 3 → Bool → ProtoTile)
      (u v : Fin 3 → Bool → PartialOdometer),
      BandOrderedGeneralOdometerRowData q cfg C T cert h P r Q S u v g := by
-- BODY
  obtain ⟨P, r, hPband, hP, hPcells, hPfoot, hPcent, hPdom,
      hPvalue, hPcompat, hPslope⟩ :=
    TileOdometerReindexedDecomposition q cfg.proper T h
      (by linarith [cfg.childLarge]) hodo
  have hfirst : 1 < (cfg.firstPredecessor 0).1 := by
    rw [cfg.firstChild]
    linarith [cfg.order12, cfg.secondLarge]
  have hQroot : TileOdometer (cfg.firstPredecessor 0) (P 0 true) (r 0 true) := by
    rw [cfg.firstChild]
    exact hP 0 true
  have hSroot : TileOdometer (cfg.firstPredecessor 0) (P 0 false) (r 0 false) := by
    rw [cfg.firstChild]
    exact hP 0 false
  obtain ⟨Q, u, hQband, hQ, hQcells, hQfoot, hQcent, hQdom,
      hQvalue, hQcompat, hQslope⟩ :=
    TileOdometerReindexedDecomposition cfg.firstPredecessor cfg.firstProper
      (P 0 true) (r 0 true) hfirst hQroot
  obtain ⟨S, v, hSband, hS, hScells, hSfoot, hScent, hSdom,
      hSvalue, hScompat, hSslope⟩ :=
    TileOdometerReindexedDecomposition cfg.firstPredecessor cfg.firstProper
      (P 0 false) (r 0 false) hfirst hSroot
  obtain ⟨c, hc⟩ := hext
  have extP : ∀ i s z, z ∈ (r i s).domain → g z = (r i s).value z + c := by
    intro i s z hz
    rw [hc z ((hPdom z).mpr ⟨i, s, hz⟩), hPvalue i s z hz]
  have extQ : ∀ i s z, z ∈ (u i s).domain → g z = (u i s).value z + c := by
    intro i s z hz
    rw [extP 0 true z ((hQdom z).mpr ⟨i, s, hz⟩), hQvalue i s z hz]
  have extS : ∀ i s z, z ∈ (v i s).domain → g z = (v i s).value z + c := by
    intro i s z hz
    rw [extP 0 false z ((hSdom z).mpr ⟨i, s, hz⟩), hSvalue i s z hz]
  have compare (D : CircleCoordinates) (U V : ProtoTile)
      (hU : BandPrototile D U) (hV : BandPrototile D V)
      (hcent : TileCentroid U = TileCentroid V) :
      U.cells = V.cells ∧ FootprintVertices U = FootprintVertices V ∧
        BoundaryFootprintVertices U = BoundaryFootprintVertices V ∧
        TileCentroid U = TileCentroid V := by
    obtain ⟨hcell, hanchor⟩ := BandPrototileCentroidUnique D U V hU hV hcent
    have obs := ProtoTileObservableExtensionality U V hcell hanchor
    exact ⟨hcell, obs.1, obs.2.1, hcent⟩
  have obsP : ∀ i s,
      (P i s).cells = (cert.P i s).cells ∧
      FootprintVertices (P i s) = FootprintVertices (cert.P i s) ∧
      BoundaryFootprintVertices (P i s) = BoundaryFootprintVertices (cert.P i s) ∧
      TileCentroid (P i s) = TileCentroid (cert.P i s) := by
    intro i s
    apply compare _ _ _ (TileOdometerBandPrototile _ _ _ (hP i s))
      (cert.outer_occurrence i s).1
    exact sub_left_injective ((hPcent i s).trans (cert.outer_occurrence i s).2.2.symm)
  have obsQ : ∀ i s,
      (Q i s).cells = (cert.Q i s).cells ∧
      FootprintVertices (Q i s) = FootprintVertices (cert.Q i s) ∧
      BoundaryFootprintVertices (Q i s) = BoundaryFootprintVertices (cert.Q i s) ∧
      TileCentroid (Q i s) = TileCentroid (cert.Q i s) := by
    intro i s
    apply compare _ _ _ (TileOdometerBandPrototile _ _ _ (hQ i s))
      (cert.plus_occurrence i s).1
    have hh := hQcent i s
    rw [(obsP 0 true).2.2.2] at hh
    exact sub_left_injective (hh.trans (cert.plus_occurrence i s).2.2.symm)
  have obsS : ∀ i s,
      (S i s).cells = (cert.S i s).cells ∧
      FootprintVertices (S i s) = FootprintVertices (cert.S i s) ∧
      BoundaryFootprintVertices (S i s) = BoundaryFootprintVertices (cert.S i s) ∧
      TileCentroid (S i s) = TileCentroid (cert.S i s) := by
    intro i s
    apply compare _ _ _ (TileOdometerBandPrototile _ _ _ (hS i s))
      (cert.minus_occurrence i s).1
    have hh := hScent i s
    rw [(obsP 0 false).2.2.2] at hh
    exact sub_left_injective (hh.trans (cert.minus_occurrence i s).2.2.symm)
  refine ⟨P, r, Q, S, u, v, ?_⟩
  refine {
    hroot := hodo, hPband := hPband, hP := hP, hPcells := hPcells,
    hPfoot := hPfoot, hPcent := hPcent, hPdom := hPdom,
    hPvalue := hPvalue, hPcompat := hPcompat, hPslope := hPslope,
    hQroot := hQroot, hSroot := hSroot, hQband := hQband, hSband := hSband,
    hQ := hQ, hS := hS, hQcells := hQcells, hScells := hScells,
    hQfoot := hQfoot, hSfoot := hSfoot, hQcent := hQcent, hScent := hScent,
    hQdom := hQdom, hSdom := hSdom, hQvalue := hQvalue, hSvalue := hSvalue,
    hQcompat := hQcompat, hScompat := hScompat, hQslope := hQslope,
    hSslope := hSslope, hextP := fun i s => ⟨c, extP i s⟩,
    hextQ := fun i s => ⟨c, extQ i s⟩, hextS := fun i s => ⟨c, extS i s⟩,
    hcompat := ?_, hobsP := obsP, hobsQ := obsQ, hobsS := obsS }
  intro a b ha hb
  have common : ∀ a : PartialOdometer,
      (∃ i s, a = r i s ∨ a = u i s ∨ a = v i s) →
      ∀ z, z ∈ a.domain → g z = a.value z + c := by
    intro a ha
    rcases ha with ⟨i, s, rfl | rfl | rfl⟩
    · exact extP i s
    · exact extQ i s
    · exact extS i s
  right
  refine ⟨0, ?_⟩
  intro z hza hzb
  have ha' := common a ha z hza
  have hb' := common b hb z hzb
  omega

end ApollonianSuperharmonic

end
