/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.AffineTriangularStrip
public import LeanPool.ApollonianSuperharmonic.BandCircle
public import LeanPool.ApollonianSuperharmonic.BandPrototile
public import LeanPool.ApollonianSuperharmonic.BandPrototileCentroidUnique
public import LeanPool.ApollonianSuperharmonic.BandPrototileCentralSymmetry
public import LeanPool.ApollonianSuperharmonic.BandPrototileTranslation
public import LeanPool.ApollonianSuperharmonic.ClosedSquareRealization
public import LeanPool.ApollonianSuperharmonic.GaussianRealPoint
public import LeanPool.ApollonianSuperharmonic.ProperBandCurvatureStructure
public import LeanPool.ApollonianSuperharmonic.RegularTileFamily
public import LeanPool.ApollonianSuperharmonic.TileHalfTurnFormulas
public import LeanPool.ApollonianSuperharmonic.TileRealization
public import LeanPool.ApollonianSuperharmonic.TileString
public import LeanPool.ApollonianSuperharmonic.TileStringCoordinateTransport
public import LeanPool.ApollonianSuperharmonic.TileStringCentralCovariance
public import LeanPool.ApollonianSuperharmonic.TileTranslationFormulas
public import LeanPool.ApollonianSuperharmonic.TriangularLatticeAdjacent
public import LeanPool.ApollonianSuperharmonic.TriangularMaxIncrement
public import LeanPool.ApollonianSuperharmonic.TriangularSignedHeight
public import LeanPool.ApollonianSuperharmonic.TriangularStripSegment

-- [TABLET NODE: TileStringRegularFamilyCentralCovariance]

/-!
# TileStringRegularFamilyCentralCovariance

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace RegularStringCentralGeometry

private theorem coordinate_value :
    (by
      classical
      exact
        ∀ (base : ProtoTile), ∀ (a : GaussianInt), ∀ (b : GaussianInt),
        let tileAt := fun z : Int × Int =>
          TileTranslation base ((z.1 : GaussianInt) * a + (z.2 : GaussianInt) * b)
        ∀ T, ∀ z, T = tileAt z → T = TileTranslation base ((z.1 : GaussianInt) * a + (z.2 :
            GaussianInt) * b) ) := by
  classical
  intro base a b tileAt T z hz
  exact hz

private theorem reflect_height :
    (by
      classical
      exact
        (GaussianInt) → ((GaussianInt) → (∀ (r : ℤ × ℤ), ∀ (s : ℤ × ℤ),
        let reflect := fun z : Int × Int => (r.1 + s.1 - z.1, r.2 + s.2 - z.2)
        ∀ z, TriangularBoundaryStrip r s z → TriangularBoundaryStrip s r (reflect z))) ) := by
  classical
  intro a b r s reflect z hz
  have hh : TriangularSignedHeight s r (reflect z) =
      TriangularSignedHeight r s z := by
    dsimp [TriangularSignedHeight, reflect]
    ring
  have hm : TriangularMaxIncrement s r = TriangularMaxIncrement r s := by
    dsimp [TriangularMaxIncrement]
    have e1 : s.1 - r.1 = -(r.1 - s.1) := by omega
    have e2 : s.2 - r.2 = -(r.2 - s.2) := by omega
    have f1 : |r.1 - s.1| = |s.1 - r.1| := by rw [e1, abs_neg]
    have f2 : |r.2 - s.2| = |s.2 - r.2| := by rw [e2, abs_neg]
    have f3 : |(r.1 - s.1) - (r.2 - s.2)| =
        |(s.1 - r.1) - (s.2 - r.2)| := by
      have e3 : (s.1 - r.1) - (s.2 - r.2) =
          -((r.1 - s.1) - (r.2 - s.2)) := by omega
      rw [e3, abs_neg]
    rw [f1, f2, f3]
  dsimp [TriangularBoundaryStrip] at hz ⊢
  rw [hh, hm]
  exact hz

private theorem reflect_sub :
    (by
      classical
      exact
        (GaussianInt) → ((GaussianInt) → (∀ (r : ℤ × ℤ), ∀ (s : ℤ × ℤ),
        let reflect := fun z : Int × Int => (r.1 + s.1 - z.1, r.2 + s.2 - z.2)
        ∀ x, ∀ y, reflect y - reflect x = -(y - x))) ) := by
  classical
  intro a b r s reflect x y
  apply Prod.ext <;> dsimp [reflect] <;> omega

private theorem reflect_adjacent :
    (by
      classical
      exact
        ∀ (r : ℤ × ℤ), ∀ (s : ℤ × ℤ),
        let reflect := fun z : Int × Int => (r.1 + s.1 - z.1, r.2 + s.2 - z.2)
        (∀ x, ∀ y, reflect y - reflect x = -(y - x)) → (∀ x, ∀ y, TriangularLatticeAdjacent x y →
            TriangularLatticeAdjacent (reflect x) (reflect y)) ) := by
  classical
  intro r s reflect reflect_sub x y hxy
  dsimp [TriangularLatticeAdjacent] at hxy ⊢
  rcases hxy with hxy | hxy | hxy | hxy | hxy | hxy
  · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
    rw [reflect_sub, hxy]
    norm_num
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
    rw [reflect_sub, hxy]
    norm_num
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))
    rw [reflect_sub, hxy]
    norm_num
  · refine Or.inl ?_
    rw [reflect_sub, hxy]
    norm_num
  · refine Or.inr (Or.inl ?_)
    rw [reflect_sub, hxy]
    norm_num
  · refine Or.inr (Or.inr (Or.inl ?_))
    rw [reflect_sub, hxy]
    norm_num

private theorem reflected_segment :
    (by
      classical
      exact
        (GaussianInt) → ((GaussianInt) → (∀ (r : ℤ × ℤ), ∀ (s : ℤ × ℤ), ∀ (coordinates : List (ℤ
            × ℤ)), (TriangularStripSegment r s coordinates) → (
        let reflect := fun z : Int × Int => (r.1 + s.1 - z.1, r.2 + s.2 - z.2)
        (∀ z, TriangularBoundaryStrip r s z → TriangularBoundaryStrip s r (reflect z)) → ((∀ x, ∀
            y, TriangularLatticeAdjacent x y → TriangularLatticeAdjacent (reflect x) (reflect y))
            → (TriangularStripSegment s r (coordinates.map reflect)))))) ) := by
  classical
  intro a b r s coordinates hsegment reflect reflect_height reflect_adjacent
  by_cases hrs : r = s
  · have heq : coordinates = [r] := by simpa [TriangularStripSegment, hrs] using hsegment
    simp [TriangularStripSegment, hrs, reflect, heq]
  · have hsseg := (show TriangularStripSegment r s coordinates from hsegment)
    have hrs' : s ≠ r := Ne.symm hrs
    dsimp [TriangularStripSegment] at hsseg
    rw [ite_eq_right hrs] at hsseg
    rcases hsseg with ⟨hfirst, hlast', hnodup, hbound, hchain'⟩
    have hfirst' : (coordinates.map reflect).head? = some s := by
      rw [List.head?_map, hfirst]
      simp only [Option.map, Option.some.injEq]
      apply Prod.ext <;> dsimp [reflect] <;> omega
    have hlast'' : (coordinates.map reflect).getLast? = some r := by
      rw [List.getLast?_map, hlast']
      simp only [Option.map, Option.some.injEq]
      apply Prod.ext <;> dsimp [reflect] <;> omega
    have hinj : Function.Injective reflect := by
      intro x y he
      have hx := congrArg Prod.fst he
      have hy := congrArg Prod.snd he
      apply Prod.ext <;> dsimp [reflect] at hx hy ⊢ <;> omega
    have hnodup' := List.Nodup.map hinj hnodup
    have hbound' : ∀ z ∈ coordinates.map reflect,
        TriangularBoundaryStrip s r z := by
      intro z hz
      rw [List.mem_map] at hz
      rcases hz with ⟨w, hw, rfl⟩
      exact reflect_height w (hbound w hw)
    have hchain'' : List.IsChain TriangularLatticeAdjacent
        (coordinates.map reflect) :=
      List.isChain_map_of_isChain reflect reflect_adjacent hchain'
    have htarget :
        (coordinates.map reflect).head? = some s ∧
        (coordinates.map reflect).getLast? = some r ∧
        (coordinates.map reflect).Nodup ∧
        (∀ z ∈ coordinates.map reflect, TriangularBoundaryStrip s r z) ∧
        List.IsChain TriangularLatticeAdjacent (coordinates.map reflect) :=
      ⟨hfirst', hlast'', hnodup', hbound', hchain''⟩
    rw [show TriangularStripSegment s r (coordinates.map reflect) =
      ((coordinates.map reflect).head? = some s ∧
        (coordinates.map reflect).getLast? = some r ∧
        (coordinates.map reflect).Nodup ∧
        (∀ z ∈ coordinates.map reflect, TriangularBoundaryStrip s r z) ∧
        List.IsChain TriangularLatticeAdjacent (coordinates.map reflect)) by
          simp [TriangularStripSegment, hrs']]
    exact htarget

private theorem reflected_corr :
    (by
      classical
      exact
        ∀ (base : ProtoTile), ∀ (tiles : List ProtoTile), ∀ (a : GaussianInt), ∀ (b :
            GaussianInt), ∀ (coordinates : List (ℤ × ℤ)), (List.Forall₂ (fun (T : ProtoTile) (z :
            ℤ × ℤ) => T = TileTranslation base ((↑z.1 : GaussianInt) * a + (↑z.2 : GaussianInt) *
            b)) tiles coordinates) → (
        let tileAt := fun z : Int × Int =>
          TileTranslation base ((z.1 : GaussianInt) * a + (z.2 : GaussianInt) * b)
        List.Forall₂ (fun T z => T = tileAt z) tiles (coordinates)) ) := by
  classical
  intro base tiles a b coordinates hcorr tileAt
  simpa [tileAt] using hcorr

private theorem reverse_corr :
    (by
      classical
      exact
        ∀ (base : ProtoTile), ∀ (a : GaussianInt), ∀ (b : GaussianInt), ∀ (r : ℤ × ℤ), ∀ (s : ℤ ×
            ℤ), ∀ (coordinates : List (ℤ × ℤ)),
        let tileAt := fun z : Int × Int =>
          TileTranslation base ((z.1 : GaussianInt) * a + (z.2 : GaussianInt) * b)
        let reflect := fun z : Int × Int => (r.1 + s.1 - z.1, r.2 + s.2 - z.2)
        let reverseTiles := coordinates.map (fun z => tileAt (reflect z))
        List.Forall₂ (fun T z => T = tileAt z) reverseTiles (coordinates.map reflect) ) := by
  classical
  intro base a b r s coordinates tileAt reflect reverseTiles
  change List.Forall₂ (fun T z => T = tileAt z)
    (coordinates.map (fun z => tileAt (reflect z))) (coordinates.map reflect)
  have map_corr : ∀ xs : List (Int × Int),
      List.Forall₂ (fun T z => T = tileAt z)
        (xs.map (fun z => tileAt (reflect z))) (xs.map reflect) := by
    intro xs
    induction xs with
    | nil => exact .nil
    | cons z zs ih => exact .cons rfl ih
  exact map_corr coordinates

private theorem reverse_string :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (R : ProtoTile), ∀ (S
            : ProtoTile), ∀ (a : GaussianInt), ∀ (b : GaussianInt), (∀ (R : ProtoTile), ∀ (S :
            ProtoTile), ∀ (tiles : List ProtoTile), ∀ (r : ℤ × ℤ), ∀ (s : ℤ × ℤ), R =
            TileTranslation base ((↑r.1 : GaussianInt) * a + (↑r.2 : GaussianInt) * b) → S =
            TileTranslation base ((↑s.1 : GaussianInt) * a + (↑s.2 : GaussianInt) * b) →
            (TileString C orientation base R S tiles ↔ ∃! coordinates : List (ℤ × ℤ),
            List.Forall₂ (fun (T : ProtoTile) (z : ℤ × ℤ) => T = TileTranslation base ((↑z.1 :
            GaussianInt) * a + (↑z.2 : GaussianInt) * b)) tiles coordinates ∧
            TriangularStripSegment r s coordinates)) → (∀ (r : ℤ × ℤ), (R = TileTranslation base
            ((↑r.1 : GaussianInt) * a + (↑r.2 : GaussianInt) * b)) → (∀ (s : ℤ × ℤ), (S =
            TileTranslation base ((↑s.1 : GaussianInt) * a + (↑s.2 : GaussianInt) * b)) → (∀
            (coordinates : List (ℤ × ℤ)),
        let tileAt := fun z : Int × Int =>
          TileTranslation base ((z.1 : GaussianInt) * a + (z.2 : GaussianInt) * b)
        let reflect := fun z : Int × Int => (r.1 + s.1 - z.1, r.2 + s.2 - z.2)
        (TriangularStripSegment s r (coordinates.map reflect)) → (
        let reverseTiles := coordinates.map (fun z => tileAt (reflect z))
        (List.Forall₂ (fun T z => T = tileAt z) reverseTiles (coordinates.map reflect)) →
            (TileString C orientation base S R reverseTiles))))) ) := by
  classical
  intro C orientation base R S a b htransport r hr s hs coordinates tileAt reflect
      reflected_segment reverseTiles reverse_corr
  apply (htransport S R reverseTiles s r hs hr).mpr
  exact ⟨coordinates.map reflect, ⟨reverse_corr, reflected_segment⟩, by
    intro other hother
    exact (AffineTriangularStrip).1 s r |>.unique hother.2 reflected_segment⟩

private theorem center_integral :
    (by
      classical
      exact
        ∀ (D : CircleCoordinates), ∀ (T : ProtoTile), BandPrototile D T → ∃ c : GaussianInt,
            GaussianRealPoint c = TileCentroid T + TileCentroid T ) := by
  classical
  intro D T hT
  induction hT with
  | line w x hw =>
      refine ⟨2 * x, ?_⟩
      simp [TileCentroid, GaussianRealPoint]
      constructor <;> ring
  | unit z x =>
      refine ⟨2 * x + 1 + ⟨0, 1⟩, ?_⟩
      simp [TileCentroid, GaussianRealPoint]
      constructor <;> ring
  | @decompose q hq S T hS hcells hfoot hcentroid ih =>
      obtain ⟨c, hc⟩ := ih 0 false
      let w := BandVectors.1 (q ((0 : Fin 3) + 2).succ)
        (q ((0 : Fin 3) + 1).succ)
      refine ⟨c + ⟨w.re + w.im, w.im - w.re⟩, ?_⟩
      have hd := hcentroid 0 false
      have hcr := congrArg Prod.fst hd
      have hci := congrArg Prod.snd hd
      have hccr := congrArg Prod.fst hc
      have hcci := congrArg Prod.snd hc
      have hcr' : (TileCentroid (S 0 false)).1 - (TileCentroid T).1 =
          -(1 / 2 : Real) * (((w.re : Int) : Real) + ((w.im : Int) : Real)) := by
        simpa [w, GaussianRealPoint] using hcr
      have hci' : (TileCentroid (S 0 false)).2 - (TileCentroid T).2 =
          -(1 / 2 : Real) * (((w.im : Int) : Real) - ((w.re : Int) : Real)) := by
        simpa [w, GaussianRealPoint] using hci
      change (c.re : Real) = _ at hccr
      change (c.im : Real) = _ at hcci
      change (c.re : Real) = (TileCentroid (S 0 false)).1 +
        (TileCentroid (S 0 false)).1 at hccr
      change (c.im : Real) = (TileCentroid (S 0 false)).2 +
        (TileCentroid (S 0 false)).2 at hcci
      apply Prod.ext
      · dsimp [GaussianRealPoint]
        push_cast
        linarith [hcr', hccr]
      · dsimp [GaussianRealPoint]
        push_cast
        linarith [hci', hcci]

private theorem hu :
    (by
      classical
      exact
        ∀ (base : ProtoTile), ∀ (R : ProtoTile), ∀ (S : ProtoTile), ∀ (a : GaussianInt), ∀ (b :
            GaussianInt), ∀ (r : ℤ × ℤ), (R = TileTranslation base ((↑r.1 : GaussianInt) * a +
            (↑r.2 : GaussianInt) * b)) → (∀ (s : ℤ × ℤ), (S = TileTranslation base ((↑s.1 :
            GaussianInt) * a + (↑s.2 : GaussianInt) * b)) → (∀ (cbase : GaussianInt),
            (GaussianRealPoint cbase = TileCentroid base + TileCentroid base) → (
        let wr : GaussianInt := (r.1 : GaussianInt) * a + (r.2 : GaussianInt) * b
        let ws : GaussianInt := (s.1 : GaussianInt) * a + (s.2 : GaussianInt) * b
        let u : GaussianInt := cbase + wr + ws
        GaussianRealPoint u = TileCentroid R + TileCentroid S))) ) := by
  classical
  intro base R S a b r hr s hs cbase hcbase wr ws u
  have hr' : TileCentroid R =
      TileCentroid base + GaussianRealPoint wr := by
    rw [hr, (TileTranslationFormulas base wr).2.2.2.2.1]
    dsimp [wr, GaussianRealPoint]
    rfl
  have hs' : TileCentroid S =
      TileCentroid base + GaussianRealPoint ws := by
    rw [hs, (TileTranslationFormulas base ws).2.2.2.2.1]
    dsimp [ws, GaussianRealPoint]
    rfl
  calc
    GaussianRealPoint u = GaussianRealPoint cbase + GaussianRealPoint wr +
        GaussianRealPoint ws := by
          dsimp [u, GaussianRealPoint]
          apply Prod.ext <;> dsimp <;> push_cast <;> ring
    _ = (TileCentroid base + TileCentroid base) +
        GaussianRealPoint wr + GaussianRealPoint ws := by rw [hcbase]
    _ = TileCentroid base + GaussianRealPoint wr +
        (TileCentroid base + GaussianRealPoint ws) := by
          apply Prod.ext <;> dsimp <;> ring
    _ = TileCentroid R + TileCentroid S := by rw [← hr', ← hs']

private theorem transformed_band :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (orientation : Bool), ∀ (base : ProtoTile), ∀ (R : ProtoTile), ∀ (S
            : ProtoTile), ∀ (tiles : List ProtoTile), ∀ (a : GaussianInt), ∀ (b : GaussianInt), ∀
            (r : ℤ × ℤ), ∀ (s : ℤ × ℤ), ∀ (cbase : GaussianInt),
        let wr : GaussianInt := (r.1 : GaussianInt) * a + (r.2 : GaussianInt) * b
        let ws : GaussianInt := (s.1 : GaussianInt) * a + (s.2 : GaussianInt) * b
        let u : GaussianInt := cbase + wr + ws
        (TileString C orientation (TileTranslation (TileHalfTurn base) u) (TileTranslation
            (TileHalfTurn R) u) (TileTranslation (TileHalfTurn S) u) (List.map (fun (T :
            ProtoTile) => TileTranslation (TileHalfTurn T) u) tiles)) → ((BandPrototile C.1.1
            (TileTranslation (TileHalfTurn base) u)) → (∀ U, U ∈ tiles → BandPrototile C.1.1
            (TileTranslation (TileHalfTurn U) u))) ) := by
  classical
  intro C orientation base R S tiles a b r s cbase wr ws u rawString rawBase U hU
  have hU' : TileTranslation (TileHalfTurn U) u ∈
      tiles.map (fun T => TileTranslation (TileHalfTurn T) u) := by
    exact List.mem_map.mpr ⟨U, hU, rfl⟩
  have hm := rawString.2.2.2.2.1 _ hU'
  rcases hm with ⟨v, hv, he⟩
  rw [he]
  exact BandPrototileTranslation C.1.1
    (TileTranslation (TileHalfTurn base) u) v rawBase

private theorem translated_band :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (base : ProtoTile), (BandPrototile C.1.1 base) → (∀ v :
            GaussianInt, v ∈ TilingLattice C → BandPrototile C.1.1 (TileTranslation base v)) ) := by
  classical
  intro C base hbase v hv
  exact BandPrototileTranslation C.1.1 base v hbase

private theorem centroid_transform :
    (by
      classical
      exact
        ∀ (a : GaussianInt), ∀ (b : GaussianInt), ∀ (r : ℤ × ℤ), ∀ (s : ℤ × ℤ), ∀ (cbase :
            GaussianInt),
        let wr : GaussianInt := (r.1 : GaussianInt) * a + (r.2 : GaussianInt) * b
        let ws : GaussianInt := (s.1 : GaussianInt) * a + (s.2 : GaussianInt) * b
        let u : GaussianInt := cbase + wr + ws
        ∀ U : ProtoTile, TileCentroid (TileTranslation (TileHalfTurn U) u) = (- (TileCentroid
            U).1 + (u.re : Int), - (TileCentroid U).2 + (u.im : Int)) ) := by
  classical
  intro a b r s cbase wr ws u U
  rw [(TileTranslationFormulas (TileHalfTurn U) u).2.2.2.2.1,
    (TileHalfTurnFormulas U).2.2.2.2.2.2.2.1]

private theorem cell_transport :
    (by
      classical
      exact
        ∀ (C : BandCircle), ∀ (base : ProtoTile), ∀ (tiles : List ProtoTile), ∀ (a :
            GaussianInt), ∀ (b : GaussianInt), (a ∈ TilingLattice C) → ((b ∈ TilingLattice C) →
            (∀ (r : ℤ × ℤ), ∀ (s : ℤ × ℤ),
        let tileAt := fun z : Int × Int =>
          TileTranslation base ((z.1 : GaussianInt) * a + (z.2 : GaussianInt) * b)
        let reflect := fun z : Int × Int => (r.1 + s.1 - z.1, r.2 + s.2 - z.2)
        ∀ (cbase : GaussianInt), (GaussianRealPoint cbase = TileCentroid base + TileCentroid
            base) → (
        let wr : GaussianInt := (r.1 : GaussianInt) * a + (r.2 : GaussianInt) * b
        let ws : GaussianInt := (s.1 : GaussianInt) * a + (s.2 : GaussianInt) * b
        let u : GaussianInt := cbase + wr + ws
        (∀ U, U ∈ tiles → BandPrototile C.1.1 (TileTranslation (TileHalfTurn U) u)) → ((∀ v :
            GaussianInt, v ∈ TilingLattice C → BandPrototile C.1.1 (TileTranslation base v)) →
            ((∀ U : ProtoTile, TileCentroid (TileTranslation (TileHalfTurn U) u) = (-
            (TileCentroid U).1 + (u.re : Int), - (TileCentroid U).2 + (u.im : Int))) → (∀ U, ∀ z,
            U ∈ tiles → U = tileAt z → (TileTranslation (TileHalfTurn U) u).cells = (tileAt
            (reflect z)).cells)))))) ) := by
  classical
  intro C base tiles a b ha hb r s tileAt reflect cbase hcbase wr ws u transformed_band
      translated_band centroid_transform U z hUm hUz
  have hVz : ((reflect z).1 : GaussianInt) * a +
      ((reflect z).2 : GaussianInt) * b ∈ TilingLattice C := by
    apply (TilingLattice C).add_mem
    · simpa using (TilingLattice C).zsmul_mem ha (reflect z).1
    · simpa using (TilingLattice C).zsmul_mem hb (reflect z).2
  have hVband : BandPrototile C.1.1 (tileAt (reflect z)) := by
    dsimp [tileAt]
    exact translated_band _ hVz
  have hUzcent : TileCentroid U = TileCentroid base +
      GaussianRealPoint ((z.1 : GaussianInt) * a + (z.2 : GaussianInt) * b) := by
    rw [hUz, (TileTranslationFormulas base _).2.2.2.2.1]
    rfl
  have hVcent : TileCentroid (tileAt (reflect z)) =
      TileCentroid base + GaussianRealPoint
        ((reflect z).1 * a + (reflect z).2 * b) := by
    dsimp [tileAt]
    rw [(TileTranslationFormulas base _).2.2.2.2.1]
    rfl
  have hcent : TileCentroid (TileTranslation (TileHalfTurn U) u) =
      TileCentroid (tileAt (reflect z)) := by
    rw [centroid_transform, hUzcent, hVcent]
    have hsum :
        ((z.1 : GaussianInt) * a + (z.2 : GaussianInt) * b) +
            (((reflect z).1 : GaussianInt) * a +
              ((reflect z).2 : GaussianInt) * b) = wr + ws := by
      dsimp [wr, ws, reflect]
      push_cast
      ring
    have hsum_re := congrArg (fun q : GaussianInt => (q.re : Real)) hsum
    have hsum_im := congrArg (fun q : GaussianInt => (q.im : Real)) hsum
    norm_num at hsum_re hsum_im
    dsimp [reflect, wr, ws] at hsum_re hsum_im
    have cast_re : ∀ n : Int, (((n : GaussianInt).re : Int) : Real) = (n : Real) := by
      intro n
      cases n <;> simp
    have cast_im : ∀ n : Int, (((n : GaussianInt).im : Int) : Real) = (0 : Real) := by
      intro n
      cases n <;> simp
    simp only [GaussianInt.toComplex_def, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      ] at hsum_re hsum_im
    norm_num at hsum_re hsum_im
    dsimp [u, reflect, GaussianRealPoint]
    have hcb_re := congrArg Prod.fst hcbase
    have hcb_im := congrArg Prod.snd hcbase
    dsimp [GaussianRealPoint] at hcb_re hcb_im
    change (cbase.re : Real) = _ at hcb_re
    change (cbase.im : Real) = _ at hcb_im
    have real_part_cast : ∀ n : Int, ((n : Complex).re) = (n : Real) := by
      intro n
      norm_num
    have imag_part_cast : ∀ n : Int, ((n : Complex).im) = (0 : Real) := by
      intro n
      norm_num
    apply Prod.ext
    · dsimp [wr, ws, reflect, GaussianRealPoint]
      push_cast
      simp only [cast_re] at hsum_re ⊢
      simp at hsum_re ⊢
      ring_nf at hsum_re ⊢
      simp only [GaussianInt.toComplex_def, Complex.add_re,
        Complex.mul_re, Complex.I_re, Complex.I_im,
        ] at ⊢
      ring_nf at ⊢
      simp only [real_part_cast, imag_part_cast] at ⊢
      ring_nf at ⊢
      nlinarith [hcb_re]
    · dsimp [wr, ws, reflect, GaussianRealPoint]
      push_cast
      simp only [cast_re, cast_im] at hsum_im ⊢
      simp at hsum_im ⊢
      ring_nf at hsum_im ⊢
      simp only [GaussianInt.toComplex_def, Complex.add_im,
        Complex.mul_im, Complex.I_re, Complex.I_im,
        ] at ⊢
      ring_nf at ⊢
      simp only [real_part_cast, imag_part_cast] at ⊢
      ring_nf at ⊢
      nlinarith [hcb_im]
  exact (BandPrototileCentroidUnique C.1.1 _ _
    (transformed_band U hUm) hVband hcent).1

private theorem endpoint_R :
    (by
      classical
      exact
        ∀ (base : ProtoTile), ∀ (R : ProtoTile), ∀ (S : ProtoTile), ∀ (tiles : List ProtoTile),
            (tiles.head? = some R) → (∀ (a : GaussianInt), ∀ (b : GaussianInt), ∀ (r : ℤ × ℤ), (R
            = TileTranslation base ((↑r.1 : GaussianInt) * a + (↑r.2 : GaussianInt) * b)) → (∀ (s
            : ℤ × ℤ), (S = TileTranslation base ((↑s.1 : GaussianInt) * a + (↑s.2 : GaussianInt)
            * b)) → (
        let tileAt := fun z : Int × Int =>
          TileTranslation base ((z.1 : GaussianInt) * a + (z.2 : GaussianInt) * b)
        let reflect := fun z : Int × Int => (r.1 + s.1 - z.1, r.2 + s.2 - z.2)
        ∀ (cbase : GaussianInt),
        let wr : GaussianInt := (r.1 : GaussianInt) * a + (r.2 : GaussianInt) * b
        let ws : GaussianInt := (s.1 : GaussianInt) * a + (s.2 : GaussianInt) * b
        let u : GaussianInt := cbase + wr + ws
        (∀ U, ∀ z, U ∈ tiles → U = tileAt z → (TileTranslation (TileHalfTurn U) u).cells =
            (tileAt (reflect z)).cells) → ((TileTranslation (TileHalfTurn R) u).cells =
            S.cells)))) ) := by
  classical
  intro base R S tiles hhead a b r hr s hs tileAt reflect cbase wr ws u cell_transport
  have h := cell_transport R r (List.mem_of_mem_head? hhead) hr
  simpa [reflect, tileAt, hs] using h

private theorem endpoint_S :
    (by
      classical
      exact
        ∀ (base : ProtoTile), ∀ (R : ProtoTile), ∀ (S : ProtoTile), ∀ (tiles : List ProtoTile),
            (tiles.getLast? = some S) → (∀ (a : GaussianInt), ∀ (b : GaussianInt), ∀ (r : ℤ × ℤ),
            (R = TileTranslation base ((↑r.1 : GaussianInt) * a + (↑r.2 : GaussianInt) * b)) → (∀
            (s : ℤ × ℤ), (S = TileTranslation base ((↑s.1 : GaussianInt) * a + (↑s.2 :
            GaussianInt) * b)) → (
        let tileAt := fun z : Int × Int =>
          TileTranslation base ((z.1 : GaussianInt) * a + (z.2 : GaussianInt) * b)
        let reflect := fun z : Int × Int => (r.1 + s.1 - z.1, r.2 + s.2 - z.2)
        ∀ (cbase : GaussianInt),
        let wr : GaussianInt := (r.1 : GaussianInt) * a + (r.2 : GaussianInt) * b
        let ws : GaussianInt := (s.1 : GaussianInt) * a + (s.2 : GaussianInt) * b
        let u : GaussianInt := cbase + wr + ws
        (∀ U, ∀ z, U ∈ tiles → U = tileAt z → (TileTranslation (TileHalfTurn U) u).cells =
            (tileAt (reflect z)).cells) → ((TileTranslation (TileHalfTurn S) u).cells =
            R.cells)))) ) := by
  classical
  intro base R S tiles hlast a b r hr s hs tileAt reflect cbase wr ws u cell_transport
  have h := cell_transport S s (List.mem_of_getLast? hlast) hs
  simpa [reflect, tileAt, hr] using h

private theorem all_cells :
    (by
      classical
      exact
        ∀ (base : ProtoTile), ∀ (tiles : List ProtoTile), ∀ (a : GaussianInt), ∀ (b :
            GaussianInt), ∀ (r : ℤ × ℤ), ∀ (s : ℤ × ℤ), ∀ (coordinates : List (ℤ × ℤ)),
            (List.Forall₂ (fun (T : ProtoTile) (z : ℤ × ℤ) => T = TileTranslation base ((↑z.1 :
            GaussianInt) * a + (↑z.2 : GaussianInt) * b)) tiles coordinates) → (
        let tileAt := fun z : Int × Int =>
          TileTranslation base ((z.1 : GaussianInt) * a + (z.2 : GaussianInt) * b)
        let reflect := fun z : Int × Int => (r.1 + s.1 - z.1, r.2 + s.2 - z.2)
        let reverseTiles := coordinates.map (fun z => tileAt (reflect z))
        ∀ (cbase : GaussianInt),
        let wr : GaussianInt := (r.1 : GaussianInt) * a + (r.2 : GaussianInt) * b
        let ws : GaussianInt := (s.1 : GaussianInt) * a + (s.2 : GaussianInt) * b
        let u : GaussianInt := cbase + wr + ws
        (∀ U, ∀ z, U ∈ tiles → U = tileAt z → (TileTranslation (TileHalfTurn U) u).cells =
            (tileAt (reflect z)).cells) → (List.Forall₂ (fun T U => (TileTranslation
            (TileHalfTurn T) u).cells = U.cells) tiles reverseTiles)) ) := by
  classical
  intro base tiles a b r s coordinates hcorr tileAt reflect reverseTiles cbase wr ws u
      cell_transport
  change List.Forall₂
    (fun T U => (TileTranslation (TileHalfTurn T) u).cells = U.cells)
    tiles (coordinates.map (fun z => tileAt (reflect z)))
  have all_cells_aux : ∀ (xs : List ProtoTile) (zs : List (Int × Int)),
      List.Forall₂ (fun T z => T = tileAt z) xs zs →
        (∀ T ∈ xs, T ∈ tiles) →
        List.Forall₂
          (fun T U => (TileTranslation (TileHalfTurn T) u).cells = U.cells)
          xs (zs.map (fun z => tileAt (reflect z))) := by
    intro xs zs h
    induction h with
    | nil => exact fun _ => .nil
    | cons hhead htail ih =>
        intro hx
        exact .cons (cell_transport _ _ (hx _ (List.mem_cons_self)) hhead)
          (ih (fun T hT => hx T (List.mem_cons_of_mem _ hT)))
  exact all_cells_aux tiles coordinates hcorr (by intro T hT; exact hT)

end RegularStringCentralGeometry

theorem TileStringRegularFamilyCentralCovariance
    (C : BandCircle) (orientation : Bool)
    (base R S : ProtoTile) (tiles : List ProtoTile)
    (hstring : TileString C orientation base R S tiles) :
    exists u : GaussianInt, exists reverseTiles : List ProtoTile,
      GaussianRealPoint u = TileCentroid R + TileCentroid S /\
      TileString C orientation base S R reverseTiles /\
      (TileTranslation (TileHalfTurn R) u).cells = S.cells /\
      (TileTranslation (TileHalfTurn S) u).cells = R.cells /\
      List.Forall₂
        (fun T U => (TileTranslation (TileHalfTurn T) u).cells = U.cells)
        tiles reverseTiles := by
-- BODY
  classical
  have original_string := hstring
  unfold TileString at hstring
  rcases hstring with ⟨hbase, hhead, hlast, hpair, hmem, hchain, hheight⟩
  obtain ⟨a, b, hdet, ha, hb, hbasis, hsource, hchart⟩ :=
    TileStringCoordinateTransport C orientation base hbase
  dsimp only at hchart
  obtain ⟨hfamily, hadjacent, hsigned, htransport⟩ := hchart
  have hRmem := hmem R (List.mem_of_mem_head? hhead)
  have hSmem := hmem S (List.mem_of_getLast? hlast)
  obtain ⟨r, hr, hr_unique⟩ := (hfamily R).mp hRmem
  obtain ⟨s, hs, hs_unique⟩ := (hfamily S).mp hSmem
  obtain ⟨coordinates, hcoords, hsegment_unique⟩ :=
    (htransport R S tiles r s hr hs).mp
      ⟨hbase, hhead, hlast, hpair, hmem, hchain, hheight⟩
  have hcorr := hcoords.1
  have hsegment := hcoords.2
  let tileAt := fun z : Int × Int =>
    TileTranslation base ((z.1 : GaussianInt) * a + (z.2 : GaussianInt) * b)
  let reflect := fun z : Int × Int => (r.1 + s.1 - z.1, r.2 + s.2 - z.2)
  have coordinate_value := RegularStringCentralGeometry.coordinate_value base a b
  have reflected_corr := RegularStringCentralGeometry.reflected_corr base tiles a b coordinates
      hcorr
  let reverseTiles := coordinates.map (fun z => tileAt (reflect z))
  have reverse_string := RegularStringCentralGeometry.reverse_string C orientation base R S a b
      htransport r hr s hs coordinates (RegularStringCentralGeometry.reflected_segment a b r s
      coordinates hsegment (RegularStringCentralGeometry.reflect_height a b r s)
      (RegularStringCentralGeometry.reflect_adjacent r s
      (RegularStringCentralGeometry.reflect_sub a b r s)))
      (RegularStringCentralGeometry.reverse_corr base a b r s coordinates)
  obtain ⟨cbase, hcbase⟩ : ∃ cbase : GaussianInt,
      GaussianRealPoint cbase = TileCentroid base + TileCentroid base := by
    exact (RegularStringCentralGeometry.center_integral) C.1.1 base hbase
  let wr : GaussianInt := (r.1 : GaussianInt) * a + (r.2 : GaussianInt) * b
  let ws : GaussianInt := (s.1 : GaussianInt) * a + (s.2 : GaussianInt) * b
  let u : GaussianInt := cbase + wr + ws
  have rawString := TileStringCentralCovariance C orientation base R S tiles u
    original_string
  have rawBase : BandPrototile C.1.1
      (TileTranslation (TileHalfTurn base) u) := rawString.1
  have cell_transport := RegularStringCentralGeometry.cell_transport C base tiles a b ha hb r s
      cbase hcbase (RegularStringCentralGeometry.transformed_band C orientation base R S tiles a
      b r s cbase rawString rawBase) (RegularStringCentralGeometry.translated_band C base hbase)
      (RegularStringCentralGeometry.centroid_transform a b r s cbase)
  exact ⟨u, reverseTiles, (RegularStringCentralGeometry.hu base R S a b r hr s hs cbase hcbase),
      reverse_string, (RegularStringCentralGeometry.endpoint_R base R S tiles hhead a b r hr s hs
      cbase cell_transport), (RegularStringCentralGeometry.endpoint_S base R S tiles hlast a b r
      hr s hs cbase cell_transport), (RegularStringCentralGeometry.all_cells base tiles a b r s
      coordinates hcorr cbase cell_transport)⟩

end ApollonianSuperharmonic

end
