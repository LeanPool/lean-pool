/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BandInterfaceRootedForest
public import LeanPool.ApollonianSuperharmonic.AcyclicIndegreeOrientation
public import LeanPool.ApollonianSuperharmonic.BandCircle
public import LeanPool.ApollonianSuperharmonic.BoundaryFootprintVertices
public import LeanPool.ApollonianSuperharmonic.DiamondTileAcyclicIndegree
public import LeanPool.ApollonianSuperharmonic.FordTileAcyclicIndegree
public import LeanPool.ApollonianSuperharmonic.FourNeighborLaplacian
public import LeanPool.ApollonianSuperharmonic.GlobalOdometerExtends
public import LeanPool.ApollonianSuperharmonic.TileOdometer
public import LeanPool.ApollonianSuperharmonic.P5532T1SymmetryOrientationTransport
public import LeanPool.ApollonianSuperharmonic.P5532T1RestrictionMassBalance
public import LeanPool.ApollonianSuperharmonic.P5532T1ParentInteriorGeometry
public import LeanPool.ApollonianSuperharmonic.P5532T1OverlapNoEntry
public import LeanPool.ApollonianSuperharmonic.P5532T1FiniteOrientationGluing
public import LeanPool.ApollonianSuperharmonic.P5532T1ForestAttachment

-- [TABLET NODE: BandTileAcyclicIndegree]

/-!
# BandTileAcyclicIndegree

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace BandAcyclicIndegreeGeometry

private theorem emptyOrientation :
    (by
      classical
      exact
        ∀ (σ : GaussianInt → ℤ), Nonempty (AcyclicIndegreeOrientation (∅ : Finset GaussianInt) σ)
            ) := by
  classical
  intro σ
  exact ⟨{
    edge := fun _ _ => False
    edgeDecidable := fun _ _ => Classical.propDecidable _
    rank := fun _ => 0
    supported := by intro x y he; cases he
    oriented := by simp
    increasing := by intro x y he; cases he
    indegree := by simp }⟩

private theorem hemptyAt200 :
    (by
      classical
      exact
        ∀ (k : PartialOdometer), ∀ (x : GaussianInt), (k.domain = {x}) → ((k.domain.filter fun y
            => @decide (y ∉ BoundaryFootprintVertices (⟨∅, x⟩ : ProtoTile))
            (Classical.propDecidable _)) = ∅) ) := by
  classical
  intro k x hk
  ext y
  simp [hk, BoundaryFootprintVertices]

private theorem bottom :
    (by
      classical
      exact
        ∀ (U : ProtoTile), ∀ (x : GaussianInt), (U.cells = {x}) → ({x, x + 1} ∈
            BoundaryFootprintEdges U) ) := by
  classical
  intro U x hcell
  refine ⟨x, Or.inl ⟨rfl, Or.inl ⟨?_, ?_⟩⟩⟩
  · simp [hcell]
  · simp only [hcell, Finset.mem_singleton]
    intro hh
    have hh' := congrArg Zsqrtd.im hh
    simp at hh'

private theorem left :
    (by
      classical
      exact
        ∀ (U : ProtoTile), ∀ (x : GaussianInt), (U.cells = {x}) → ({x, x + ⟨0, 1⟩} ∈
            BoundaryFootprintEdges U) ) := by
  classical
  intro U x hcell
  refine ⟨x, Or.inr ⟨rfl, Or.inl ⟨?_, ?_⟩⟩⟩
  · simp [hcell]
  · simp only [hcell, Finset.mem_singleton]
    intro hh
    have hh' := congrArg Zsqrtd.re hh
    simp at hh'

private theorem right :
    (by
      classical
      exact
        ∀ (U : ProtoTile), ∀ (x : GaussianInt), (U.cells = {x}) → ({x + 1, x + 1 + ⟨0, 1⟩} ∈
            BoundaryFootprintEdges U) ) := by
  classical
  intro U x hcell
  refine ⟨x + 1, Or.inr ⟨rfl, Or.inr ⟨?_, ?_⟩⟩⟩
  · simp only [hcell, Finset.mem_singleton]
    intro hh
    have hh' := congrArg Zsqrtd.re hh
    simp at hh'
  · simp [hcell]

private theorem hb0 :
    (by
      classical
      exact
        ∀ (U : ProtoTile), ∀ (x : GaussianInt), (U.cells.Nonempty) → (({x, x + 1} ∈
            BoundaryFootprintEdges U) → (x ∈ BoundaryFootprintVertices U)) ) := by
  classical
  intro U x hne bottom
  rw [BoundaryFootprintVertices, ite_eq_left hne]
  exact ⟨{x, x + 1}, bottom, by simp⟩

private theorem hb1 :
    (by
      classical
      exact
        ∀ (U : ProtoTile), ∀ (x : GaussianInt), (U.cells.Nonempty) → (({x, x + 1} ∈
            BoundaryFootprintEdges U) → (x + 1 ∈ BoundaryFootprintVertices U)) ) := by
  classical
  intro U x hne bottom
  rw [BoundaryFootprintVertices, ite_eq_left hne]
  exact ⟨{x, x + 1}, bottom, by simp⟩

private theorem hbi :
    (by
      classical
      exact
        ∀ (U : ProtoTile), ∀ (x : GaussianInt), (U.cells.Nonempty) → (({x, x + ⟨0, 1⟩} ∈
            BoundaryFootprintEdges U) → (x + ⟨0, 1⟩ ∈ BoundaryFootprintVertices U)) ) := by
  classical
  intro U x hne left
  rw [BoundaryFootprintVertices, ite_eq_left hne]
  exact ⟨{x, x + ⟨0, 1⟩}, left, by simp⟩

private theorem hb1i :
    (by
      classical
      exact
        ∀ (U : ProtoTile), ∀ (x : GaussianInt), (U.cells.Nonempty) → (({x + 1, x + 1 + ⟨0, 1⟩} ∈
            BoundaryFootprintEdges U) → (x + 1 + ⟨0, 1⟩ ∈ BoundaryFootprintVertices U)) ) := by
  classical
  intro U x hne right
  rw [BoundaryFootprintVertices, ite_eq_left hne]
  exact ⟨{x + 1, x + 1 + ⟨0, 1⟩}, right, by simp⟩

private theorem hemptyAt243 :
    (by
      classical
      exact
        ∀ (U : ProtoTile), ∀ (k : PartialOdometer), ((↑k.domain : Set GaussianInt) =
            FootprintVertices U) → (∀ (x : GaussianInt), (U.cells = {x}) → ((U.cells.Nonempty) →
            ((x ∈ BoundaryFootprintVertices U) → ((x + 1 ∈ BoundaryFootprintVertices U) → ((x +
            ⟨0, 1⟩ ∈ BoundaryFootprintVertices U) → ((x + 1 + ⟨0, 1⟩ ∈ BoundaryFootprintVertices
            U) → ((k.domain.filter fun y => @decide (y ∉ BoundaryFootprintVertices U)
            (Classical.propDecidable _)) = ∅))))))) ) := by
  classical
  intro U k hd x hcell hne hb0 hb1 hbi hb1i
  ext y
  simp only [Finset.mem_filter, decide_eq_true_eq, Finset.notMem_empty, iff_false]
  rintro ⟨hy, hnb⟩
  have hyfoot : y ∈ FootprintVertices U := by rw [← hd]; exact hy
  simp only [FootprintVertices, ite_eq_left hne, Set.mem_ofPred_eq] at hyfoot
  obtain ⟨a, ha, hv⟩ := hyfoot
  have hax : a = x := by simpa [hcell] using ha
  subst a
  rcases hv with hv | hv | hv | hv
  · rw [hv] at hnb; exact hnb hb0
  · rw [hv] at hnb; exact hnb hb1
  · rw [hv] at hnb; exact hnb hbi
  · rw [hv] at hnb; exact hnb hb1i

private theorem hcurv :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (r : Fin (3 : ℕ)), ∀ (s : BandPackingSymmetry),
        let qr : Fin 4 → CircleCoordinates :=
          ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        let p := BandPackingSymmetryQuadrupleAction s qr
        (p 0 = BandPackingSymmetryCircleAction s (q 0)) → ((p 0).1 = (q 0).1) ) := by
  classical
  intro q r s qr p hp0
  rw [hp0]
  exact (BandPackingSymmetryCovariance s).1 _

private theorem hV :
    (by
      classical
      exact
        ∀ (U : ProtoTile), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), (BandPrototile (q (0 : Fin (4
            : ℕ))) U) → (∀ (r : Fin (3 : ℕ)), ∀ (s : BandPackingSymmetry),
        let qr : Fin 4 → CircleCoordinates :=
          ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        let p := BandPackingSymmetryQuadrupleAction s qr
        let V := BandPackingSymmetryTileAction s U
        (p 0 = BandPackingSymmetryCircleAction s (q 0)) → (BandPrototile (p 0) V)) ) := by
  classical
  intro U q hU r s qr p V hp0
  rw [hp0]
  exact ((BandPackingSymmetryCovariance s).2.1 _ _).mp hU

private theorem hl :
    (by
      classical
      exact
        ∀ (U : ProtoTile), ∀ (k : PartialOdometer), ∀ (q : Fin (4 : ℕ) → CircleCoordinates),
            (TileOdometer (q 0) U k) → (∀ (r : Fin (3 : ℕ)), ∀ (s : BandPackingSymmetry),
        let qr : Fin 4 → CircleCoordinates :=
          ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        let p := BandPackingSymmetryQuadrupleAction s qr
        let V := BandPackingSymmetryTileAction s U
        let l := BandPackingSymmetryPartialOdometerAction s k
        (p 0 = BandPackingSymmetryCircleAction s (q 0)) → (TileOdometer (p 0) V l)) ) := by
  classical
  intro U k q hodo r s qr p V l hp0
  rw [hp0]
  exact (BandPackingSymmetryTileOdometerCovariance s _ _ _ hodo).1

private theorem hroot :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (r : Fin (3 : ℕ)), ∀ (s : BandPackingSymmetry),
        let qr : Fin 4 → CircleCoordinates :=
          ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        let p := BandPackingSymmetryQuadrupleAction s qr
        ∀ (F : FordFareyParameter), (p = FordRecursiveQuadruple F) → (p 0 = FordCircleCoordinate
            F.p F.q) ) := by
  classical
  intro q r s qr p F hpF
  rw [hpF]
  rfl

private theorem restrict_dom :
    (by
      classical
      exact
        ∀ (U : ProtoTile), ∀ (k : PartialOdometer), ∀ (s : BandPackingSymmetry),
        let V := BandPackingSymmetryTileAction s U
        let l := BandPackingSymmetryPartialOdometerAction s k
        ((l.domain : Set GaussianInt) = FootprintVertices V) → (
        let restrict (W : ProtoTile) : PartialOdometer :=
          let d := l.domain.filter fun x => decide (x ∈ FootprintVertices W)
          { domain := d
            value := fun x => if x ∈ d then l.value x else 0
            value_outside := by intro x hx; exact ite_eq_right hx }
        ∀ (W : ProtoTile), (FootprintVertices W ⊆ FootprintVertices V) → (((restrict W).domain :
            Set GaussianInt) = FootprintVertices W))) := by
  classical
  intro U k s V l hldom restrict W hW
  ext x
  simp only [restrict, Finset.mem_coe, Finset.mem_filter, decide_eq_true_eq]
  constructor
  · exact And.right
  · intro hx
    exact ⟨(Set.ext_iff.mp hldom x).mpr (hW hx), hx⟩

private theorem hls :
    (by
      classical
      exact
        ∀ (U : ProtoTile), ∀ (k : PartialOdometer), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (r
            : Fin (3 : ℕ)), ∀ (s : BandPackingSymmetry),
        let qr : Fin 4 → CircleCoordinates :=
          ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        let p := BandPackingSymmetryQuadrupleAction s qr
        let V := BandPackingSymmetryTileAction s U
        let l := BandPackingSymmetryPartialOdometerAction s k
        ∀ (hp : ProperBandQuadruple p), ∀ (hpos : 0 < (p 0).1), (BandPrototile (p 0) V) →
            ((TileOdometer (p 0) V l) → (∀ (cfg : BandOrderedGeneralConfiguration p),
        let B : BandCircle := ⟨⟨p 0, Or.inl hpos, p, hp.1, 0, rfl⟩, hpos⟩
        ∀ (cert : BandOrderedGeneralLayoutCertificate p cfg B V),
        let restrict (W : ProtoTile) : PartialOdometer :=
          let d := l.domain.filter fun x => decide (x ∈ FootprintVertices W)
          { domain := d
            value := fun x => if x ∈ d then l.value x else 0
            value_outside := by intro x hx; exact ite_eq_right hx }
        let ls := fun i s => restrict (cert.P i s)
        (∀ i, ∀ s, ((ls i s).domain : Set GaussianInt) = FootprintVertices (cert.P i s)) → ((∀ i,
            ∀ s, ∀ x, x ∈ (ls i s).domain → x ∈ l.domain ∧ l.value x = (ls i s).value x) → (∀ i,
            ∀ s, TileOdometer (p i.succ) (cert.P i s) (ls i s)))))) := by
  classical
  intro U k q r s qr p V l hp hpos hV hl cfg B cert restrict ls hlsdom hlrest i s
  apply AncestorOdometerRestriction _ _ _ _ _ l
  refine ⟨hl, ?_, hlsdom i s, ?_, ?_⟩
  · exact Relation.ReflTransGen.single
      ⟨p, i, s, hp, rfl, rfl, hV, cert.outer_occurrence i s⟩
  · intro x hx
    exact (hlrest i s x hx).1
  · intro x hx
    exact (hlrest i s x hx).2.symm

private theorem hOS :
    (by
      classical
      exact
        ∀ (U : ProtoTile), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (r : Fin (3 : ℕ)), ∀ (s :
            BandPackingSymmetry),
        let qr : Fin 4 → CircleCoordinates :=
          ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        let p := BandPackingSymmetryQuadrupleAction s qr
        let V := BandPackingSymmetryTileAction s U
        ∀ (hp : ProperBandQuadruple p), ∀ (hpos : 0 < (p 0).1), ∀ (cfg :
            BandOrderedGeneralConfiguration p),
        let B : BandCircle := ⟨⟨p 0, Or.inl hpos, p, hp.1, 0, rfl⟩, hpos⟩
        ∀ (cert : BandOrderedGeneralLayoutCertificate p cfg B V), FootprintVertices cert.O =
            FootprintVertices (cert.S 0 true) ) := by
  classical
  intro U q r s qr p V hp hpos cfg B cert
  by_cases hn : cert.O.cells.Nonempty
  · have hs : (cert.S 0 true).cells.Nonempty := by
      rw [← cert.precursor_cells]
      exact hn
    simp only [FootprintVertices, ite_eq_left hn, ite_eq_left hs]
    rw [cert.precursor_cells]
  · have he : cert.O.cells = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    have hs : ¬ (cert.S 0 true).cells.Nonempty := by
      rw [← cert.precursor_cells]
      exact hn
    simp only [FootprintVertices, ite_eq_right hn, ite_eq_right hs]
    rw [cert.precursor_anchor he]

private theorem hOparent :
    (by
      classical
      exact
        ∀ (U : ProtoTile), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (r : Fin (3 : ℕ)), ∀ (s :
            BandPackingSymmetry),
        let qr : Fin 4 → CircleCoordinates :=
          ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        let p := BandPackingSymmetryQuadrupleAction s qr
        let V := BandPackingSymmetryTileAction s U
        ∀ (hp : ProperBandQuadruple p), ∀ (hpos : 0 < (p 0).1), ∀ (cfg :
            BandOrderedGeneralConfiguration p),
        let B : BandCircle := ⟨⟨p 0, Or.inl hpos, p, hp.1, 0, rfl⟩, hpos⟩
        ∀ (cert : BandOrderedGeneralLayoutCertificate p cfg B V), (FootprintVertices cert.O =
            FootprintVertices (cert.S 0 true)) → (∀ s, FootprintVertices cert.O ⊆
            FootprintVertices (cert.P 0 s)) ) := by
  classical
  intro U q r s qr p V hp hpos cfg B cert hOS s
  cases s
  · rw [hOS]
    exact (cert.minus_occurrence 0 true).2.1
  · rw [cert.precursor_eq]
    exact (cert.plus_occurrence 0 false).2.1

private theorem hkrest :
    (by
      classical
      exact
        ∀ (U : ProtoTile), ∀ (k : PartialOdometer), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (r
            : Fin (3 : ℕ)), ∀ (s : BandPackingSymmetry),
        let qr : Fin 4 → CircleCoordinates :=
          ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        let p := BandPackingSymmetryQuadrupleAction s qr
        let V := BandPackingSymmetryTileAction s U
        let l := BandPackingSymmetryPartialOdometerAction s k
        ∀ (hp : ProperBandQuadruple p), ∀ (hpos : 0 < (p 0).1), ∀ (cfg :
            BandOrderedGeneralConfiguration p),
        let B : BandCircle := ⟨⟨p 0, Or.inl hpos, p, hp.1, 0, rfl⟩, hpos⟩
        ∀ (cert : BandOrderedGeneralLayoutCertificate p cfg B V),
        let restrict (W : ProtoTile) : PartialOdometer :=
          let d := l.domain.filter fun x => decide (x ∈ FootprintVertices W)
          { domain := d
            value := fun x => if x ∈ d then l.value x else 0
            value_outside := by intro x hx; exact ite_eq_right hx }
        (∀ (W : ProtoTile), ∀ (x : GaussianInt), (x ∈ (restrict W).domain) → (x ∈ l.domain ∧
            l.value x = (restrict W).value x)) → (
        let ls := fun i s => restrict (cert.P i s)
        (∀ i, ∀ s, ((ls i s).domain : Set GaussianInt) = FootprintVertices (cert.P i s)) → ((∀ i,
            ∀ s, ∀ x, x ∈ (ls i s).domain → x ∈ l.domain ∧ l.value x = (ls i s).value x) → ((∀ s,
            FootprintVertices cert.O ⊆ FootprintVertices (cert.P 0 s)) → (
        let ks := fun _ : Bool => restrict cert.O
        (∀ s, ((ks s).domain : Set GaussianInt) = FootprintVertices cert.O) → (∀ s, ∀ x, x ∈ (ks
            s).domain → x ∈ (ls 0 s).domain ∧ (ls 0 s).value x = (ks s).value x))))) ) := by
  classical
  intro U k q r s qr p V l hp hpos cfg B cert restrict restrict_rest ls hlsdom hlrest hOparent ks
      hksdom s x hx
  have hxp : x ∈ (ls 0 s).domain := by
    exact (Set.ext_iff.mp (hlsdom 0 s) x).mpr
      (hOparent s ((Set.ext_iff.mp (hksdom s) x).mp hx))
  exact ⟨hxp, (hlrest 0 s x hxp).2.symm.trans (restrict_rest _ x hx).2⟩

private theorem hOancestor :
    (by
      classical
      exact
        ∀ (U : ProtoTile), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (r : Fin (3 : ℕ)), ∀ (s :
            BandPackingSymmetry),
        let qr : Fin 4 → CircleCoordinates :=
          ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        let p := BandPackingSymmetryQuadrupleAction s qr
        let V := BandPackingSymmetryTileAction s U
        ∀ (hp : ProperBandQuadruple p), ∀ (hpos : 0 < (p 0).1), ∀ (cfg :
            BandOrderedGeneralConfiguration p),
        let B : BandCircle := ⟨⟨p 0, Or.inl hpos, p, hp.1, 0, rfl⟩, hpos⟩
        ∀ (cert : BandOrderedGeneralLayoutCertificate p cfg B V), AncestorTile
            (cfg.firstPredecessor 1) (p 1) cert.O (cert.P 0 true) ) := by
  classical
  intro U q r s qr p V hp hpos cfg B cert
  rw [cert.precursor_eq]
  exact Relation.ReflTransGen.single
    ⟨cfg.firstPredecessor, 0, false, cfg.firstProper, cfg.firstChild, rfl,
      (cert.outer_occurrence 0 true).1, cert.plus_occurrence 0 false⟩

private theorem hks :
    (by
      classical
      exact
        ∀ (U : ProtoTile), ∀ (k : PartialOdometer), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (r
            : Fin (3 : ℕ)), ∀ (s : BandPackingSymmetry),
        let qr : Fin 4 → CircleCoordinates :=
          ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        let p := BandPackingSymmetryQuadrupleAction s qr
        let V := BandPackingSymmetryTileAction s U
        let l := BandPackingSymmetryPartialOdometerAction s k
        ∀ (hp : ProperBandQuadruple p), ∀ (hpos : 0 < (p 0).1), ∀ (cfg :
            BandOrderedGeneralConfiguration p),
        let B : BandCircle := ⟨⟨p 0, Or.inl hpos, p, hp.1, 0, rfl⟩, hpos⟩
        ∀ (cert : BandOrderedGeneralLayoutCertificate p cfg B V),
        let restrict (W : ProtoTile) : PartialOdometer :=
          let d := l.domain.filter fun x => decide (x ∈ FootprintVertices W)
          { domain := d
            value := fun x => if x ∈ d then l.value x else 0
            value_outside := by intro x hx; exact ite_eq_right hx }
        let ls := fun i s => restrict (cert.P i s)
        (∀ i, ∀ s, TileOdometer (p i.succ) (cert.P i s) (ls i s)) → (
        let ks := fun _ : Bool => restrict cert.O
        (∀ s, ((ks s).domain : Set GaussianInt) = FootprintVertices cert.O) → ((∀ s, ∀ x, x ∈ (ks
            s).domain → x ∈ (ls 0 s).domain ∧ (ls 0 s).value x = (ks s).value x) → ((AncestorTile
            (cfg.firstPredecessor 1) (p 1) cert.O (cert.P 0 true)) → (∀ s, TileOdometer
            (cfg.firstPredecessor 1) cert.O (ks s))))) ) := by
  classical
  intro U k q r s qr p V l hp hpos cfg B cert restrict ls hls ks hksdom hkrest hOancestor s
  exact AncestorOdometerRestriction _ _ _ _ _ (ls 0 true)
    ⟨hls 0 true, hOancestor, hksdom s,
      (fun x hx => (hkrest true x hx).1),
      (fun x hx => (hkrest true x hx).2.symm)⟩

private theorem hrest :
    (by
      classical
      exact
        ∀ (U : ProtoTile), ∀ (k : PartialOdometer), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (r
            : Fin (3 : ℕ)), ∀ (s : BandPackingSymmetry),
        let qr : Fin 4 → CircleCoordinates :=
          ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        let p := BandPackingSymmetryQuadrupleAction s qr
        let V := BandPackingSymmetryTileAction s U
        let l := BandPackingSymmetryPartialOdometerAction s k
        ∀ (hp : ProperBandQuadruple p), ∀ (hpos : 0 < (p 0).1), ∀ (cfg :
            BandOrderedGeneralConfiguration p),
        let B : BandCircle := ⟨⟨p 0, Or.inl hpos, p, hp.1, 0, rfl⟩, hpos⟩
        ∀ (cert : BandOrderedGeneralLayoutCertificate p cfg B V),
        let restrict (W : ProtoTile) : PartialOdometer :=
          let d := l.domain.filter fun x => decide (x ∈ FootprintVertices W)
          { domain := d
            value := fun x => if x ∈ d then l.value x else 0
            value_outside := by intro x hx; exact ite_eq_right hx }
        let ls := fun i s => restrict (cert.P i s)
        (∀ i, ∀ s, ∀ x, x ∈ (ls i s).domain → x ∈ l.domain ∧ l.value x = (ls i s).value x) → (∀
            (G : IntegerLatticeFunction), (GlobalOdometerExtends G l) → (∀ i, ∀ t,
            GlobalOdometerExtends G (ls i t))) ) := by
  classical
  intro U k q r s qr p V l hp hpos cfg B cert restrict ls hlrest G heG i t
  obtain ⟨b, hb⟩ := heG
  refine ⟨b, ?_⟩
  intro x hx
  rw [hb x (hlrest i t x hx).1, (hlrest i t x hx).2]

private theorem hkext :
    (by
      classical
      exact
        ∀ (U : ProtoTile), ∀ (k : PartialOdometer), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (r
            : Fin (3 : ℕ)), ∀ (s : BandPackingSymmetry),
        let qr : Fin 4 → CircleCoordinates :=
          ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        let p := BandPackingSymmetryQuadrupleAction s qr
        let V := BandPackingSymmetryTileAction s U
        let l := BandPackingSymmetryPartialOdometerAction s k
        ∀ (hp : ProperBandQuadruple p), ∀ (hpos : 0 < (p 0).1), ∀ (cfg :
            BandOrderedGeneralConfiguration p),
        let B : BandCircle := ⟨⟨p 0, Or.inl hpos, p, hp.1, 0, rfl⟩, hpos⟩
        ∀ (cert : BandOrderedGeneralLayoutCertificate p cfg B V),
        let restrict (W : ProtoTile) : PartialOdometer :=
          let d := l.domain.filter fun x => decide (x ∈ FootprintVertices W)
          { domain := d
            value := fun x => if x ∈ d then l.value x else 0
            value_outside := by intro x hx; exact ite_eq_right hx }
        let ls := fun i s => restrict (cert.P i s)
        let ks := fun _ : Bool => restrict cert.O
        (∀ s, ∀ x, x ∈ (ks s).domain → x ∈ (ls 0 s).domain ∧ (ls 0 s).value x = (ks s).value x) →
            (∀ (G : IntegerLatticeFunction), (∀ i, ∀ t, GlobalOdometerExtends G (ls i t)) →
            (GlobalOdometerExtends G (ks true))) ) := by
  classical
  intro U k q r s qr p V l hp hpos cfg B cert restrict ls ks hkrest G hrest
  obtain ⟨b, hb⟩ := hrest 0 true
  refine ⟨b, ?_⟩
  intro x hx
  rw [hb x (hkrest true x hx).1, (hkrest true x hx).2]

private theorem kids :
    (by
      classical
      exact
        ∀ (n : ℕ), ∀ (U : ProtoTile), ∀ (s : BandPackingSymmetry),
        let V := BandPackingSymmetryTileAction s U
        ∀ (k : PartialOdometer),
        let l := BandPackingSymmetryPartialOdometerAction s k
        ∀ (ih : ∀ m < n,
      ∀ (c : CircleCoordinates), ∀ (U : ProtoTile), ∀ (k : PartialOdometer), ∀ (f :
          IntegerLatticeFunction), c.1.toNat = m →
          TileOdometer c U k →
            (↑k.domain : Set GaussianInt) = FootprintVertices U →
              GlobalOdometerExtends f k →
        let D := k.domain.filter fun x =>
          @decide (x ∉ BoundaryFootprintVertices U) (Classical.propDecidable _);
                Nonempty (AcyclicIndegreeOrientation D fun (x : GaussianInt) => (2 : ℤ) +
                    FourNeighborLaplacian f x)), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (hn :
                    (q (0 : Fin (4 : ℕ))).1.toNat = n), ∀ (r : Fin (3 : ℕ)),
        let qr : Fin 4 → CircleCoordinates :=
          ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        let p := BandPackingSymmetryQuadrupleAction s qr
        ∀ (hp : ProperBandQuadruple p), ∀ (hcurv : (p 0).1 = (q 0).1), ∀ (hpos : 0 < (p 0).1), ∀
            (cfg : BandOrderedGeneralConfiguration p),
        let B : BandCircle := ⟨⟨p 0, Or.inl hpos, p, hp.1, 0, rfl⟩, hpos⟩
        ∀ (cert : BandOrderedGeneralLayoutCertificate p cfg B V),
        let restrict (W : ProtoTile) : PartialOdometer :=
          let d := l.domain.filter fun x => decide (x ∈ FootprintVertices W)
          { domain := d
            value := fun x => if x ∈ d then l.value x else 0
            value_outside := by intro x hx; exact ite_eq_right hx }
        let ls := fun i s => restrict (cert.P i s)
        (∀ i, ∀ s, ((ls i s).domain : Set GaussianInt) = FootprintVertices (cert.P i s)) → ((∀ i,
            ∀ s, TileOdometer (p i.succ) (cert.P i s) (ls i s)) → (∀ (G :
            IntegerLatticeFunction), (∀ i, ∀ t, GlobalOdometerExtends G (ls i t)) → (
        let A := fun a : Fin 3 × Bool => (ls a.1 a.2).domain.filter fun x =>
          @decide (x ∉ BoundaryFootprintVertices (cert.P a.1 a.2))
            (Classical.propDecidable _)
        let σ := fun x => 2 + FourNeighborLaplacian G x
        ∀ a, Nonempty (AcyclicIndegreeOrientation (A a) σ)))) ) := by
  classical
  intro n U s V k l ih q hn r qr p hp hcurv hpos cfg B cert restrict ls hlsdom hls G hrest A σ a
  let D := l.domain.filter fun x =>
    @decide (x ∉ BoundaryFootprintVertices V) (Classical.propDecidable _)
  have hsmall : (p a.1.succ).1.toNat < n := by
    rw [← hn, ← hcurv]
    exact (Int.toNat_lt_toNat hpos).mpr (hp.2 a.1)
  exact ih _ hsmall _ (cert.P a.1 a.2) (ls a.1 a.2) G rfl
    (hls a.1 a.2) (hlsdom a.1 a.2) (hrest a.1 a.2)

private theorem closed :
    (by
      classical
      exact
        ∀ (U : ProtoTile), ∀ (k : PartialOdometer), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (r
            : Fin (3 : ℕ)), ∀ (s : BandPackingSymmetry),
        let qr : Fin 4 → CircleCoordinates :=
          ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        let p := BandPackingSymmetryQuadrupleAction s qr
        let V := BandPackingSymmetryTileAction s U
        let l := BandPackingSymmetryPartialOdometerAction s k
        ∀ (hp : ProperBandQuadruple p), ∀ (hpos : 0 < (p 0).1), ∀ (cfg :
            BandOrderedGeneralConfiguration p),
        let B : BandCircle := ⟨⟨p 0, Or.inl hpos, p, hp.1, 0, rfl⟩, hpos⟩
        ∀ (cert : BandOrderedGeneralLayoutCertificate p cfg B V),
        let restrict (W : ProtoTile) : PartialOdometer :=
          let d := l.domain.filter fun x => decide (x ∈ FootprintVertices W)
          { domain := d
            value := fun x => if x ∈ d then l.value x else 0
            value_outside := by intro x hx; exact ite_eq_right hx }
        let ls := fun i s => restrict (cert.P i s)
        let ks := fun _ : Bool => restrict cert.O
        ∀ (G : IntegerLatticeFunction),
        let A := fun a : Fin 3 × Bool => (ls a.1 a.2).domain.filter fun x =>
          @decide (x ∉ BoundaryFootprintVertices (cert.P a.1 a.2))
            (Classical.propDecidable _)
        let I := (ks true).domain.filter fun x =>
          @decide (x ∉ BoundaryFootprintVertices cert.O) (Classical.propDecidable _)
        let σ := fun x => 2 + FourNeighborLaplacian G x
        ∀ (kids : ∀ a, Nonempty (AcyclicIndegreeOrientation (A a) σ)),
        let os := fun a => Classical.choice (kids a)
        ((∑ x ∈ I, σ x) =
          (((I.product I).filter fun e =>
            @decide (FourNeighborAdjacent e.1 e.2) (Classical.propDecidable _)).card / 2 : ℕ)) →
        ((∀ (a b : Fin 3 × Bool), a ≠ b →
          A a ∩ A b = if a.1 = 0 ∧ b.1 = 0 then I else ∅) → (∀ a, ∀ b, ∀ x ∈ A a ∩ A b, ∀ y ∈
            A a, (os a).edge y x → y ∈ A b)) ) := by
  classical
  intro U k q r s qr p V l hp hpos cfg B cert restrict ls ks G A I σ kids os mass hpair a b x hx
      y hy hexy
  by_cases hab : a = b
  · simpa [← hab] using hy
  by_cases hz : a.1 = 0 ∧ b.1 = 0
  · have hm : (∑ x ∈ A a ∩ A b, σ x) =
        (((((A a ∩ A b).product (A a ∩ A b)).filter fun e =>
          @decide (FourNeighborAdjacent e.1 e.2) (Classical.propDecidable _)).card
            / 2 : ℕ) : ℤ) := by
      rw [hpair a b hab, ite_eq_left hz]
      exact mass
    exact (Finset.mem_inter.mp (P5532T1OverlapNoEntry (A a) (A a ∩ A b)
      σ Finset.inter_subset_left (os a) hm x hx y hy hexy)).2
  · have hempty : A a ∩ A b = ∅ := by
      rw [hpair a b hab, ite_eq_right hz]
    simp [hempty] at hx

private theorem hPo :
    (by
      classical
      exact
        ∀ (U : ProtoTile), ∀ (k : PartialOdometer), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (r
            : Fin (3 : ℕ)), ∀ (s : BandPackingSymmetry),
        let qr : Fin 4 → CircleCoordinates :=
          ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        let p := BandPackingSymmetryQuadrupleAction s qr
        let V := BandPackingSymmetryTileAction s U
        let l := BandPackingSymmetryPartialOdometerAction s k
        ∀ (hp : ProperBandQuadruple p), ∀ (hpos : 0 < (p 0).1), ∀ (cfg :
            BandOrderedGeneralConfiguration p),
        let B : BandCircle := ⟨⟨p 0, Or.inl hpos, p, hp.1, 0, rfl⟩, hpos⟩
        ∀ (cert : BandOrderedGeneralLayoutCertificate p cfg B V),
        let restrict (W : ProtoTile) : PartialOdometer :=
          let d := l.domain.filter fun x => decide (x ∈ FootprintVertices W)
          { domain := d
            value := fun x => if x ∈ d then l.value x else 0
            value_outside := by intro x hx; exact ite_eq_right hx }
        let ls := fun i s => restrict (cert.P i s)
        ∀ (G : IntegerLatticeFunction),
        let D := l.domain.filter fun x =>
          @decide (x ∉ BoundaryFootprintVertices V) (Classical.propDecidable _)
        let A := fun a : Fin 3 × Bool => (ls a.1 a.2).domain.filter fun x =>
          @decide (x ∉ BoundaryFootprintVertices (cert.P a.1 a.2))
            (Classical.propDecidable _)
        let σ := fun x => 2 + FourNeighborLaplacian G x
        (AcyclicIndegreeOrientation (Finset.univ.biUnion A) σ) → (
        let P := D.filter fun x => @decide (∃ i t, x ∈ (ls i t).domain ∧
          x ∉ BoundaryFootprintVertices (cert.P i t)) (Classical.propDecidable _)
        (Finset.univ.biUnion A = P) → (Nonempty (AcyclicIndegreeOrientation P σ))) ) := by
  classical
  intro U k q r s qr p V l hp hpos cfg B cert restrict ls G D A σ oUnion P hUnion
  rw [← hUnion]
  exact ⟨oUnion⟩

end BandAcyclicIndegreeGeometry

theorem BandTileAcyclicIndegree :
    ∀ (C : BandCircle), ∀ (T : ProtoTile), ∀ (h : PartialOdometer), ∀ (g :
        IntegerLatticeFunction), (BandPrototile C.1.1 T) → ((TileOdometer C.1.1 T h) →
        (((h.domain : Set GaussianInt) = FootprintVertices T) → ((GlobalOdometerExtends g h) → (
    let D := h.domain.filter fun x =>
      @decide (x ∉ BoundaryFootprintVertices T) (Classical.propDecidable _)
    Nonempty (AcyclicIndegreeOrientation D
      (fun x => 2 + FourNeighborLaplacian g x)))))) := by
  intro C T h g hT hodo hdom hext
-- BODY
  classical
  have emptyOrientation := BandAcyclicIndegreeGeometry.emptyOrientation
  have main : ∀ n : ℕ, ∀ (c : CircleCoordinates) (U : ProtoTile)
      (k : PartialOdometer) (f : IntegerLatticeFunction),
      c.1.toNat = n → TileOdometer c U k →
      (k.domain : Set GaussianInt) = FootprintVertices U →
      GlobalOdometerExtends f k →
      let D := k.domain.filter fun x =>
        @decide (x ∉ BoundaryFootprintVertices U) (Classical.propDecidable _)
      Nonempty (AcyclicIndegreeOrientation D
        (fun x => 2 + FourNeighborLaplacian f x)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro c U k f hn ho hd he
      cases ho with
      | line w x hw k hk =>
        have hempty : (k.domain.filter fun y =>
            @decide (y ∉ BoundaryFootprintVertices (⟨∅, x⟩ : ProtoTile))
              (Classical.propDecidable _)) = ∅ := BandAcyclicIndegreeGeometry.hemptyAt200 k x hk
        dsimp only
        rw [hempty]
        exact emptyOrientation _
      | unit z x U k hcell hdomain htrans =>
        have hne : U.cells.Nonempty := by rw [hcell]; simp
        have bottom := BandAcyclicIndegreeGeometry.bottom U x hcell
        have hempty : (k.domain.filter fun y =>
            @decide (y ∉ BoundaryFootprintVertices U) (Classical.propDecidable _)) = ∅ :=
                BandAcyclicIndegreeGeometry.hemptyAt243 U k hd x hcell hne
                (BandAcyclicIndegreeGeometry.hb0 U x hne bottom) (BandAcyclicIndegreeGeometry.hb1
                U x hne bottom) (BandAcyclicIndegreeGeometry.hbi U x hne
                (BandAcyclicIndegreeGeometry.left U x hcell)) (BandAcyclicIndegreeGeometry.hb1i U
                x hne (BandAcyclicIndegreeGeometry.right U x hcell))
        dsimp only
        rw [hempty]
        exact emptyOrientation _
      | @decompose q hq S U hs k hU hsub hcells hfoot hcentroid hdomain
          hvalue hcompat hslope =>
        have hodo : TileOdometer (q 0) U k := TileOdometer.decompose hq hU hsub
          hcells hfoot hcentroid hdomain hvalue hcompat hslope
        obtain ⟨r, s, hregime⟩ := BandRegimeClassification q hq
        let qr : Fin 4 → CircleCoordinates :=
          ![q 0, q r.succ, q (r + 1).succ, q (r + 2).succ]
        let p := BandPackingSymmetryQuadrupleAction s qr
        let V := BandPackingSymmetryTileAction s U
        let l := BandPackingSymmetryPartialOdometerAction s k
        have hqr : ProperBandQuadruple qr :=
          (BandParentRotationOccurrenceCovariance q hq r U hU S
            (fun i t => ⟨TileOdometerBandPrototile _ _ _ (hsub i t),
              hfoot i t, hcentroid i t⟩) hcells).1
        have hp : ProperBandQuadruple p := BandPackingSymmetryProperCovariance s qr hqr
        have hp0 : p 0 = BandPackingSymmetryCircleAction s (q 0) := by
          simp [p, qr, BandPackingSymmetryQuadrupleAction]
        have hcurv := BandAcyclicIndegreeGeometry.hcurv q r s hp0
        have hpos : 0 < (p 0).1 := (ProperBandCurvatureStructure p hp).1
        have hV : BandPrototile (p 0) V := BandAcyclicIndegreeGeometry.hV U q hU r s hp0
        have hl : TileOdometer (p 0) V l := BandAcyclicIndegreeGeometry.hl U k q hodo r s hp0
        have hldom : (l.domain : Set GaussianInt) = FootprintVertices V :=
          PositiveCurvatureTileOdometerDomain _ _ _ hpos hl
        obtain ⟨f', he', htransport⟩ :=
          P5532T1SymmetryOrientationTransport s (q 0) U k f hodo he
        apply htransport.mpr
        change Nonempty (AcyclicIndegreeOrientation
          (l.domain.filter fun x => @decide (x ∉ BoundaryFootprintVertices V)
            (Classical.propDecidable _)) (fun x => 2 + FourNeighborLaplacian f' x))
        change Xor (∃ F : FordFareyParameter, 1 < F.q ∧ p = FordRecursiveQuadruple F)
          (Xor (∃ K : DiamondParameter, 1 < K.1 ∧ p = DiamondRecursiveQuadruple K)
            (Nonempty (BandOrderedGeneralConfiguration p))) at hregime
        rcases hregime with ⟨⟨F, hF, hpF⟩, _⟩ | ⟨hregime, _⟩
        · have hroot : p 0 = FordCircleCoordinate F.p F.q := BandAcyclicIndegreeGeometry.hroot q
            r s F hpF
          exact FordTileAcyclicIndegree F V l f' (hroot ▸ hV) (hroot ▸ hl) hldom he'
        rcases hregime with ⟨⟨K, hK, hpK⟩, _⟩ | ⟨⟨cfg⟩, _⟩
        · exact DiamondTileAcyclicIndegree K V l f'
            (congrFun hpK 0 ▸ hV) (congrFun hpK 0 ▸ hl) hldom he'
        let B : BandCircle := ⟨⟨p 0, Or.inl hpos, p, hp.1, 0, rfl⟩, hpos⟩
        obtain ⟨cert⟩ := BandOrderedGeneralLayout p cfg B rfl V hV
          (by
            intro t W Z ht hW hZ hcov hsmall
            have htall := BandTileSimultaneousInduction t ht W hW
            exact ⟨htall.1, htall.2.1, htall.2.2.1 Z hZ hcov⟩)
          (by
            intro c W hW hsmall
            cases hW with
            | line w a hw => exact (P4564T2ElementaryQuarterTurn 0 a).1
            | unit z a anchor => exact (P4564T2ElementaryQuarterTurn a anchor).2
            | @decompose t ht Z W hZ hcov hfo hce =>
              exact (BandTileSimultaneousInduction t ht W
                (BandPrototile.decompose ht hZ hcov hfo hce)).2.2.2.1)
          (by
            intro t W Z ht hW hsmall hlarge i hZ hce
            exact (BandTileSimultaneousInduction t ht W hW).2.2.2.2.2.1
              hlarge i Z hZ hce)
          (by
            intro t W Z Z' ht hW hsmall i hZ hZ' hce hce'
            exact (BandTileSimultaneousInduction t ht W hW).2.2.2.2.2.2.1
              i Z Z' hZ hZ' hce hce')
        let restrict (W : ProtoTile) : PartialOdometer :=
          let d := l.domain.filter fun x => decide (x ∈ FootprintVertices W)
          { domain := d
            value := fun x => if x ∈ d then l.value x else 0
            value_outside := by intro x hx; exact ite_eq_right hx }
        have restrict_dom := BandAcyclicIndegreeGeometry.restrict_dom U k s hldom
        have restrict_rest (W : ProtoTile) (x : GaussianInt)
            (hx : x ∈ (restrict W).domain) :
            x ∈ l.domain ∧ l.value x = (restrict W).value x :=
          ⟨(Finset.mem_filter.mp hx).1, (ite_eq_left hx).symm⟩
        let ls := fun i s => restrict (cert.P i s)
        have hlsdom : ∀ i s, ((ls i s).domain : Set GaussianInt) =
            FootprintVertices (cert.P i s) := fun i s =>
          restrict_dom _ (cert.outer_occurrence i s).2.1
        have hlrest : ∀ i s x, x ∈ (ls i s).domain →
            x ∈ l.domain ∧ l.value x = (ls i s).value x := fun i s x hx =>
          restrict_rest _ x hx
        have hls := BandAcyclicIndegreeGeometry.hls U k q r s hp hpos hV hl cfg cert hlsdom hlrest
        have hOparent := BandAcyclicIndegreeGeometry.hOparent U q r s hp hpos cfg cert
            (BandAcyclicIndegreeGeometry.hOS U q r s hp hpos cfg cert)
        let ks := fun _ : Bool => restrict cert.O
        have hksdom : ∀ s, ((ks s).domain : Set GaussianInt) =
            FootprintVertices cert.O := fun _ =>
          restrict_dom _ ((hOparent true).trans (cert.outer_occurrence 0 true).2.1)
        have hkrest := BandAcyclicIndegreeGeometry.hkrest U k q r s hp hpos cfg cert
            restrict_rest hlsdom hlrest hOparent hksdom
        have hks := BandAcyclicIndegreeGeometry.hks U k q r s hp hpos cfg cert hls hksdom hkrest
            (BandAcyclicIndegreeGeometry.hOancestor U q r s hp hpos cfg cert)
        obtain ⟨G, heG, hlat, htile, hweb, hperiod, hlap⟩ :=
          BandCanonicalPeriodicExtension B p hp rfl V l f' hV hl hldom he'
        have hrest := BandAcyclicIndegreeGeometry.hrest U k q r s hp hpos cfg cert hlrest G heG
        let D := l.domain.filter fun x =>
          @decide (x ∉ BoundaryFootprintVertices V) (Classical.propDecidable _)
        let A := fun a : Fin 3 × Bool => (ls a.1 a.2).domain.filter fun x =>
          @decide (x ∉ BoundaryFootprintVertices (cert.P a.1 a.2))
            (Classical.propDecidable _)
        let I := (ks true).domain.filter fun x =>
          @decide (x ∉ BoundaryFootprintVertices cert.O) (Classical.propDecidable _)
        let σ := fun x => 2 + FourNeighborLaplacian G x
        have kids := BandAcyclicIndegreeGeometry.kids n U s k ih q hn r hp hcurv hpos cfg cert
            hlsdom hls G hrest
        let os := fun a => Classical.choice (kids a)
        have mass := P5532T1RestrictionMassBalance (cfg.firstPredecessor 1)
          cert.O (ks true) G (hks true) (hksdom true) (BandAcyclicIndegreeGeometry.hkext U k q r
              s hp hpos cfg cert hkrest G hrest)
        obtain ⟨hAD, hpair, hcross, hUnion⟩ := P5532T1ParentInteriorGeometry
          B p cfg V cert l ls (ks true) hlat hldom hlsdom (hksdom true)
        have closed := BandAcyclicIndegreeGeometry.closed U k q r s hp hpos cfg cert G kids mass
            hpair
        obtain ⟨oUnion, _⟩ := P5532T1FiniteOrientationGluing A σ os hcross closed
        let P := D.filter fun x => @decide (∃ i t, x ∈ (ls i t).domain ∧
          x ∉ BoundaryFootprintVertices (cert.P i t)) (Classical.propDecidable _)
        change Finset.univ.biUnion A = P at hUnion
        have hPo := BandAcyclicIndegreeGeometry.hPo U k q r s hp hpos cfg cert G oUnion hUnion
        obtain ⟨R, hf, hcard, hres⟩ := BandInterfaceRootedForest B p cfg V cert l ls G
          hV hlat hl hldom hls hlsdom heG hrest htile hweb hperiod hPo
        obtain ⟨oD, _⟩ := P5532T1ForestAttachment D P R σ (Finset.filter_subset _ _)
          (Classical.choice hPo) hf hres
        exact P5532T1OrientationPullback D D
          (fun x => 2 + FourNeighborLaplacian f' x) σ id (by simp) (fun _ _ h => h)
          (fun _ _ => Iff.rfl)
          (by
            intro x hx
            have hx' := Finset.mem_filter.mp hx
            have hnb : x ∉ BoundaryFootprintVertices V :=
              @of_decide_eq_true _ (Classical.propDecidable _) hx'.2
            dsimp [σ]
            rw [hlap x hx'.1 hnb]) oD
  exact main _ C.1.1 T h g rfl hodo hdom hext

end ApollonianSuperharmonic

end
