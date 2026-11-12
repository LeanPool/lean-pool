/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralFinitePatches
public import LeanPool.ApollonianSuperharmonic.BandPrototileCentralSymmetry
public import LeanPool.ApollonianSuperharmonic.BandSignedOccurrenceHalfTurn
public import LeanPool.ApollonianSuperharmonic.ConsecutivePatchInterface
public import LeanPool.ApollonianSuperharmonic.ExactPatchBoundaryInterface
public import LeanPool.ApollonianSuperharmonic.FinitePatchTopology
public import LeanPool.ApollonianSuperharmonic.LatticeTileDiskUnionInterface
public import LeanPool.ApollonianSuperharmonic.ModifiedSubtileOccurrenceInterpretation
public import LeanPool.ApollonianSuperharmonic.PeriodicTileIndexedMultiplicityOne
public import LeanPool.ApollonianSuperharmonic.PeriodicTileIntersectionClassification
public import LeanPool.ApollonianSuperharmonic.PeriodicTileMultiplicityOne
public import LeanPool.ApollonianSuperharmonic.TileCellComplement
public import LeanPool.ApollonianSuperharmonic.ProtoTileObservableExtensionality
public import LeanPool.ApollonianSuperharmonic.QuarterTurnSymmetricCenteredTransport
public import LeanPool.ApollonianSuperharmonic.TileCellComplementCovariance
public import LeanPool.ApollonianSuperharmonic.TileDiskAreaCovariance
public import LeanPool.ApollonianSuperharmonic.TileTouchingCovariance

-- [TABLET NODE: TileT1DiskArea]

/-!
# TileT1DiskArea

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace DiskAreaGeometry

private theorem hadjacency :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), ∀ a, ∀ b, a ≠ b → cert.modified.plane.adjacent a b → (FootprintEdges
            (cert.modified.tile a) ∩ FootprintEdges (cert.modified.tile b)).Nonempty ) := by
  classical
  intro q cfg C₀ T cert a b hab hadj
  exact ((PeriodicTileIntersectionClassification cert.modified).1 a b hab).1.mpr hadj

private theorem hmodified :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), ∀ (whole : FiniteInducedTilePatch cert.modified.plane cert.modified.tile), (∀
            d ∈ whole.indices, ∃ (rest : FiniteInducedTilePatch cert.modified.plane
            cert.modified.tile), rest.indices = whole.indices.erase d ∧ rest.unionTile =
            TileCellComplement T (cert.modified.tile d) ∧ Nonempty (ConsecutivePatchInterface
            cert.modified.plane cert.modified.tile rest d)) → ((∀ (x : LatticeCell), ∃! a :
            PeriodicSubtileIndex, x ∈ (cert.modified.tile a).cells) → ((∀ a, ∀ b, a ≠ b →
            cert.modified.plane.adjacent a b → (FootprintEdges (cert.modified.tile a) ∩
            FootprintEdges (cert.modified.tile b)).Nonempty) → ((∀ K : FiniteInducedTilePatch
            cert.modified.plane cert.modified.tile, LatticeTile K.unionTile) → (∀ d ∈
            whole.indices, LatticeTile (TileCellComplement T (cert.modified.tile d)) ∧
            TileTouching (TileCellComplement T (cert.modified.tile d)) (cert.modified.tile d)))))
            ) := by
  classical
  intro q cfg C₀ T cert whole hdeletions hindexed hadjacency hdisk d hd
  obtain ⟨rest, hrest, hrestTile, ⟨interface⟩⟩ := hdeletions d hd
  have hUd := hdisk rest
  have hVd := cert.modified.tiles_are_disks d
  have hdisjoint : Disjoint rest.unionTile.cells (cert.modified.tile d).cells := by
    apply Finset.disjoint_left.mpr
    intro z hz hzd
    obtain ⟨b, hb, hzb⟩ := (rest.exact_union z).mp hz
    have hbd : b = d := (hindexed z).unique hzb hzd
    exact interface.exterior (hbd ▸ hb)
  have hunion : ∀ z, z ∈ whole.unionTile.cells ↔
      z ∈ rest.unionTile.cells ∨ z ∈ (cert.modified.tile d).cells := by
    intro z
    rw [whole.exact_union, rest.exact_union]
    constructor
    · rintro ⟨b, hb, hzb⟩
      by_cases hbd : b = d
      · exact Or.inr (hbd ▸ hzb)
      · exact Or.inl ⟨b, by simpa [hrest, Finset.mem_erase, hbd] using hb, hzb⟩
    · rintro (⟨b, hb, hzb⟩ | hzd)
      · exact ⟨b, Finset.mem_of_mem_erase (hrest ▸ hb), hzb⟩
      · exact ⟨d, hd, hzd⟩
  let k : Fin interface.length := ⟨0, interface.positive⟩
  obtain ⟨hb, hadj⟩ := (interface.neighbors_exact (interface.neighbor k)).mpr ⟨k, rfl⟩
  have hdb : d ≠ interface.neighbor k := by
    intro h
    exact interface.exterior (h ▸ hb)
  obtain ⟨e, hed, heb⟩ := hadjacency d (interface.neighbor k) hdb hadj
  have heU : e ∈ FootprintEdges rest.unionTile := by
    obtain ⟨z, hz, he⟩ := heb
    exact ⟨z, (rest.exact_union z).mpr ⟨interface.neighbor k, hb, hz⟩, he⟩
  obtain ⟨hfoot, ⟨x, y, hpath⟩, hedges, hvertices⟩ :=
    LatticeTileDiskUnionInterface rest.unionTile (cert.modified.tile d)
      whole.unionTile hUd hVd (hdisk whole) hdisjoint hunion ⟨e, heU, hed⟩
  obtain ⟨p, hnodup, hlength, _, _, hverts, hsteps, hpaths⟩ := hpath
  have htouch : TileTouching rest.unionTile (cert.modified.tile d) := by
    left
    refine ⟨(LatticeTileGridStructure _ hUd).1.1,
      (LatticeTileGridStructure _ hVd).1.1, hdisjoint, ?_⟩
    rw [hvertices, ← hedges]
    exact ⟨p, hnodup, hlength, hverts, hsteps, hpaths⟩
  exact ⟨hrestTile ▸ hUd, hrestTile ▸ htouch⟩

private theorem hzero :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), ∀ l : SixSubtileLabel, cert.modified.tile ⟨l, 0, 0⟩ = (match l with
              | .A => TileCellComplement (cert.P 0 true) cert.O
              | .B => cert.P 0 false
              | .C => cert.P 1 true
              | .D => cert.P 1 false
              | .E => cert.P 2 true
              | .F => cert.P 2 false) ) := by
  classical
  intro q cfg C₀ T cert l
  rw [cert.modified_tile]
  have hz : GaussianTranslation (0 : GaussianInt) = id := by
    funext z
    exact add_zero z
  simp [ModifiedSubtileOccurrenceInterpretation, TileTranslation, hz]
  rfl

private theorem horiginal :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), ∀ (whole : FiniteInducedTilePatch cert.modified.plane cert.modified.tile),
            (whole.indices = {(⟨SixSubtileLabel.A, (0 : ℤ), (0 : ℤ)⟩ : PeriodicSubtileIndex),
            (⟨SixSubtileLabel.B, (0 : ℤ), (0 : ℤ)⟩ : PeriodicSubtileIndex), (⟨SixSubtileLabel.C,
            (0 : ℤ), (0 : ℤ)⟩ : PeriodicSubtileIndex), (⟨SixSubtileLabel.D, (0 : ℤ), (0 : ℤ)⟩ :
            PeriodicSubtileIndex), (⟨SixSubtileLabel.E, (0 : ℤ), (0 : ℤ)⟩ :
            PeriodicSubtileIndex), (⟨SixSubtileLabel.F, (0 : ℤ), (0 : ℤ)⟩ :
            PeriodicSubtileIndex)}) → ((∀ d ∈ whole.indices, LatticeTile (TileCellComplement T
            (cert.modified.tile d)) ∧ TileTouching (TileCellComplement T (cert.modified.tile d))
            (cert.modified.tile d)) → ((∀ l : SixSubtileLabel, cert.modified.tile ⟨l, 0, 0⟩ =
            (match l with
              | .A => TileCellComplement (cert.P 0 true) cert.O
              | .B => cert.P 0 false
              | .C => cert.P 1 true
              | .D => cert.P 1 false
              | .E => cert.P 2 true
              | .F => cert.P 2 false)) → (∀ (i : Fin 3), ∀ (s : Bool), i ≠ 0 ∨ s = false →
                  LatticeTile
            (TileCellComplement T (cert.P i s)) ∧ TileTouching (TileCellComplement T (cert.P i
            s)) (cert.P i s)))) ) := by
  classical
  intro q cfg C₀ T cert whole hindices hmodified hzero i s h
  fin_cases i <;> cases s
  · simpa [hzero] using hmodified ⟨.B, 0, 0⟩ (by simp [hindices])
  · simp at h
  · simpa [hzero] using hmodified ⟨.D, 0, 0⟩ (by simp [hindices])
  · simpa [hzero] using hmodified ⟨.C, 0, 0⟩ (by simp [hindices])
  · simpa [hzero] using hmodified ⟨.F, 0, 0⟩ (by simp [hindices])
  · simpa [hzero] using hmodified ⟨.E, 0, 0⟩ (by simp [hindices])

private theorem harea :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), ∀ (whole : FiniteInducedTilePatch cert.modified.plane cert.modified.tile),
            (whole.indices = {(⟨SixSubtileLabel.A, (0 : ℤ), (0 : ℤ)⟩ : PeriodicSubtileIndex),
            (⟨SixSubtileLabel.B, (0 : ℤ), (0 : ℤ)⟩ : PeriodicSubtileIndex), (⟨SixSubtileLabel.C,
            (0 : ℤ), (0 : ℤ)⟩ : PeriodicSubtileIndex), (⟨SixSubtileLabel.D, (0 : ℤ), (0 : ℤ)⟩ :
            PeriodicSubtileIndex), (⟨SixSubtileLabel.E, (0 : ℤ), (0 : ℤ)⟩ :
            PeriodicSubtileIndex), (⟨SixSubtileLabel.F, (0 : ℤ), (0 : ℤ)⟩ :
            PeriodicSubtileIndex)}) → ((whole.unionTile = T) → ((∀ (x : LatticeCell), ∃! a :
            PeriodicSubtileIndex, x ∈ (cert.modified.tile a).cells) → ((∀ l : SixSubtileLabel,
            cert.modified.tile ⟨l, 0, 0⟩ = (match l with
              | .A => TileCellComplement (cert.P 0 true) cert.O
              | .B => cert.P 0 false
              | .C => cert.P 1 true
              | .D => cert.P 1 false
              | .E => cert.P 2 true
              | .F => cert.P 2 false)) → (TileArea T = Int.toNat (q 0).1)))) ) := by
  classical
  intro q cfg C₀ T cert whole hindices hwhole hindexed hzero
  have hcells : whole.indices.biUnion (fun a => (cert.modified.tile a).cells) =
      T.cells := by
    ext z
    simp only [Finset.mem_biUnion]
    simpa only [hwhole] using (whole.exact_union z).symm
  have hpair : (whole.indices : Set PeriodicSubtileIndex).PairwiseDisjoint
      (fun a => (cert.modified.tile a).cells) := by
    intro a ha b hb hab
    apply Finset.disjoint_left.mpr
    intro z hza hzb
    exact hab ((hindexed z).unique hza hzb)
  have hcard := Finset.card_biUnion hpair
  rw [hcells] at hcard
  have hsum : T.cells.card = cert.R.card := by
    rw [hcard]
    simpa [hindices, hzero, TileArea, Nat.add_assoc] using cert.orbit_area
  change T.cells.card = _
  rw [hsum, cert.representative_count, cert.child_eq]
  exact_mod_cast (Int.natAbs_of_nonneg (le_of_lt C₀.property)).trans
    (Int.toNat_of_nonneg (le_of_lt C₀.property)).symm

private theorem ht :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), ∀ (u : GaussianInt), (GaussianRealPoint u = ((TileCentroid (cert.P (0 : Fin (3
            : ℕ)) false)).1 + (TileCentroid (cert.P (0 : Fin (3 : ℕ)) false)).2, (TileCentroid
            (cert.P (0 : Fin (3 : ℕ)) false)).2 - (TileCentroid (cert.P (0 : Fin (3 : ℕ))
            false)).1)) → (
        let w := BandVectors.1 (q 3) (q 2)
        let t : GaussianInt :=
          ⟨u.re - u.im + w.re + w.im, u.re + u.im + w.im - w.re⟩
        (t.re : Real) = 2 * (TileCentroid T).1 ∧ (t.im : Real) = 2 * (TileCentroid T).2) ) := by
  classical
  intro q cfg C₀ T cert u hu w t
  have hur := congrArg Prod.fst hu
  have hui := congrArg Prod.snd hu
  have hc := (cert.outer_occurrence 0 false).2.2
  have hcr := congrArg Prod.fst hc
  have hci := congrArg Prod.snd hc
  norm_num [GaussianRealPoint] at hur hui hcr hci
  simp only [← GaussianInt.intCast_re, ← GaussianInt.intCast_im] at hur hui hcr hci
  dsimp [t, w]
  push_cast
  constructor <;> linarith

private theorem htau :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (u : GaussianInt),
        let w := BandVectors.1 (q 3) (q 2)
        let t : GaussianInt :=
          ⟨u.re - u.im + w.re + w.im, u.re + u.im + w.im - w.re⟩
        let tau : GaussianInt → GaussianInt := fun z => t - z - 1 - ⟨0, 1⟩
        Function.Involutive tau ) := by
  classical
  intro q u w t tau z
  dsimp [tau]
  abel

private theorem hHcells :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (u : GaussianInt),
        let w := BandVectors.1 (q 3) (q 2)
        let t : GaussianInt :=
          ⟨u.re - u.im + w.re + w.im, u.re + u.im + w.im - w.re⟩
        let H : ProtoTile → ProtoTile := fun U =>
          TileTranslation (TileQuarterTurn (TileQuarterTurn U)) t
        let tau : GaussianInt → GaussianInt := fun z => t - z - 1 - ⟨0, 1⟩
        ∀ U, (H U).cells = U.cells.image tau ) := by
  classical
  intro q u w t H tau U
  simp only [H, TileTranslation, TileQuarterTurn, Finset.image_image]
  apply Finset.image_congr
  intro z hz
  apply Zsqrtd.ext <;> simp [Function.comp_def, GaussianTranslation,
    GaussianQuarterTurn, tau] <;> ring

private theorem hHreal :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (T : ProtoTile), ∀ (u : GaussianInt),
        let w := BandVectors.1 (q 3) (q 2)
        let t : GaussianInt :=
          ⟨u.re - u.im + w.re + w.im, u.re + u.im + w.im - w.re⟩
        ((t.re : Real) = 2 * (TileCentroid T).1 ∧ (t.im : Real) = 2 * (TileCentroid T).2) → (
        let H : ProtoTile → ProtoTile := fun U =>
          TileTranslation (TileQuarterTurn (TileQuarterTurn U)) t
        ∀ U, TileRealization (H U) = (fun p : Real × Real => (2 * (TileCentroid T).1 - p.1, 2 *
            (TileCentroid T).2 - p.2)) '' TileRealization U) ) := by
  classical
  intro q T u w t ht H U
  dsimp only [H]
  rw [(TileTranslationFormulas _ t).2.2.2.1,
    (TileQuarterTurnFormulas (TileQuarterTurn U)).2.2.2.1,
    (TileQuarterTurnFormulas U).2.2.2.1, Set.image_image, Set.image_image]
  congr 1
  funext p
  apply Prod.ext <;> dsimp <;> simp only [ht.1, ht.2] <;> ring

private theorem hcenter :
    (by
      classical
      exact
        (Fin 4 → CircleCoordinates) → ((ProtoTile) → (∀ (U : ProtoTile), ∀ (z : GaussianInt), z ∈
            U.cells ↔ ((z.re : Real) + 1 / 2, (z.im : Real) + 1 / 2) ∈ TileRealization U)) ) := by
  classical
  intro q T U z
  constructor
  · intro hz
    simp only [TileRealization, Set.mem_iUnion]
    refine ⟨z, hz, ?_⟩
    norm_num [ClosedSquareRealization, Set.mem_Icc]
  · intro hp
    simp only [TileRealization, Set.mem_iUnion] at hp
    obtain ⟨b, hb, hbox⟩ := hp
    simp only [ClosedSquareRealization, Set.mem_Icc] at hbox
    have hr₁ : b.re < z.re + 1 := by
      exact_mod_cast (show (b.re : Real) < (z.re : Real) + 1 by linarith [hbox.1.1])
    have hr₂ : z.re < b.re + 1 := by
      exact_mod_cast (show (z.re : Real) < (b.re : Real) + 1 by linarith [hbox.2.1])
    have hi₁ : b.im < z.im + 1 := by
      exact_mod_cast (show (b.im : Real) < (z.im : Real) + 1 by linarith [hbox.1.2])
    have hi₂ : z.im < b.im + 1 := by
      exact_mod_cast (show (z.im : Real) < (b.im : Real) + 1 by linarith [hbox.2.2])
    have hbz : b = z := by apply Zsqrtd.ext <;> omega
    exact hbz ▸ hb

private theorem hreflectCells :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (T : ProtoTile), ∀ (u : GaussianInt),
        let w := BandVectors.1 (q 3) (q 2)
        let t : GaussianInt :=
          ⟨u.re - u.im + w.re + w.im, u.re + u.im + w.im - w.re⟩
        let H : ProtoTile → ProtoTile := fun U =>
          TileTranslation (TileQuarterTurn (TileQuarterTurn U)) t
        (∀ U, TileRealization (H U) = (fun p : Real × Real => (2 * (TileCentroid T).1 - p.1, 2 *
            (TileCentroid T).2 - p.2)) '' TileRealization U) → ((∀ (U : ProtoTile), ∀ (z :
            GaussianInt), z ∈ U.cells ↔ ((z.re : Real) + 1 / 2, (z.im : Real) + 1 / 2) ∈
            TileRealization U) → (∀ U, ∀ V, CentrallyReflectedAt (TileCentroid T) U V → (H
            U).cells = V.cells)) ) := by
  classical
  intro q T u w t H hHreal hcenter U V hUV
  have hreal : TileRealization (H U) = TileRealization V :=
    (hHreal U).trans hUV.symm
  ext z
  rw [hcenter, hcenter, hreal]

private theorem hHminus :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), ∀ (u : GaussianInt),
        let w := BandVectors.1 (q 3) (q 2)
        let t : GaussianInt :=
          ⟨u.re - u.im + w.re + w.im, u.re + u.im + w.im - w.re⟩
        let H : ProtoTile → ProtoTile := fun U =>
          TileTranslation (TileQuarterTurn (TileQuarterTurn U)) t
        let tau : GaussianInt → GaussianInt := fun z => t - z - 1 - ⟨0, 1⟩
        (Function.Involutive tau) → ((∀ U, (H U).cells = U.cells.image tau) → (((H (cert.P 0
            true)).cells = (cert.P 0 false).cells) → ((H (cert.P 0 false)).cells = (cert.P 0
            true).cells))) ) := by
  classical
  intro q cfg C₀ T cert u w t H tau htau hHcells hHplus
  rw [hHcells, ← hHplus, hHcells, Finset.image_image]
  simp [htau]

private theorem hHcomplement :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), ∀ (u : GaussianInt),
        let w := BandVectors.1 (q 3) (q 2)
        let t : GaussianInt :=
          ⟨u.re - u.im + w.re + w.im, u.re + u.im + w.im - w.re⟩
        let H : ProtoTile → ProtoTile := fun U =>
          TileTranslation (TileQuarterTurn (TileQuarterTurn U)) t
        ((H T).cells = T.cells) → (((H (cert.P 0 false)).cells = (cert.P 0 true).cells) → ((H
            (TileCellComplement T (cert.P 0 false))).cells = (TileCellComplement T (cert.P 0
            true)).cells)) ) := by
  classical
  intro q cfg C₀ T cert u w t H hHT hHminus
  have hc : H (TileCellComplement T (cert.P 0 false)) =
      TileCellComplement (H T) (H (cert.P 0 false)) := by
    dsimp only [H]
    rw [(TileCellComplementCovariance T (cert.P 0 false) 0).2.1,
      (TileCellComplementCovariance (TileQuarterTurn T)
        (TileQuarterTurn (cert.P 0 false)) 0).2.1,
      (TileCellComplementCovariance _ _ t).1]
  rw [hc]
  change (H T).cells \ (H (cert.P 0 false)).cells =
    T.cells \ (cert.P 0 true).cells
  rw [hHT, hHminus]

end DiskAreaGeometry

theorem TileT1DiskArea (q : Fin 4 → CircleCoordinates)
    (cfg : BandOrderedGeneralConfiguration q)
    (C₀ : BandCircle) (T : ProtoTile)
    (hT : BandPrototile (q 0) T)
    (cert : BandOrderedGeneralLayoutCertificate q cfg C₀ T) :
    LatticeTile T ∧ TileArea T = Int.toNat (q 0).1 ∧
      ∀ i s, LatticeTile (TileCellComplement T (cert.P i s)) ∧
        TileTouching (TileCellComplement T (cert.P i s)) (cert.P i s) := by
-- BODY
  classical
  obtain ⟨whole, hindices, hwhole, hA, hdeletions⟩ :=
    BandOrderedGeneralFinitePatches q cfg C₀ T cert
  have hindexed := PeriodicTileIndexedMultiplicityOne cert.modified
  have hadjacency := DiskAreaGeometry.hadjacency q cfg C₀ T cert
  have hdisk : ∀ K : FiniteInducedTilePatch
      cert.modified.plane cert.modified.tile, LatticeTile K.unionTile :=
    FinitePatchTopology cert.modified.plane cert.modified.tile
      (PeriodicTileMultiplicityOne cert.modified) hindexed hadjacency
  have hTd : LatticeTile T := hwhole ▸ hdisk whole
  have hmodified := DiskAreaGeometry.hmodified q cfg C₀ T cert whole hdeletions hindexed
      hadjacency hdisk
  have hzero := DiskAreaGeometry.hzero q cfg C₀ T cert
  have horiginal := DiskAreaGeometry.horiginal q cfg C₀ T cert whole hindices hmodified hzero
  have harea := DiskAreaGeometry.harea q cfg C₀ T cert whole hindices hwhole hindexed hzero
  refine ⟨hTd, harea, ?_⟩
  intro i s
  by_cases h : i ≠ 0 ∨ s = false
  · exact horiginal i s h
  · have hi : i = 0 := by tauto
    have hs : s = true := by cases s <;> simp_all
    subst i
    subst s
    obtain ⟨u, hu, _⟩ := QuarterTurnSymmetricCenteredTransport
      (cert.P 0 false) (cert.parent_quarter_turn 0 false)
    let w := BandVectors.1 (q 3) (q 2)
    let t : GaussianInt :=
      ⟨u.re - u.im + w.re + w.im, u.re + u.im + w.im - w.re⟩
    have ht := DiskAreaGeometry.ht q cfg C₀ T cert u hu
    let H : ProtoTile → ProtoTile := fun U =>
      TileTranslation (TileQuarterTurn (TileQuarterTurn U)) t
    let tau : GaussianInt → GaussianInt := fun z => t - z - 1 - ⟨0, 1⟩
    have htau := DiskAreaGeometry.htau q u
    have hHcells := DiskAreaGeometry.hHcells q u
    have hHreal := DiskAreaGeometry.hHreal q T u ht
    have hcenter := DiskAreaGeometry.hcenter q T
    have hreflectCells := DiskAreaGeometry.hreflectCells q T u hHreal hcenter
    have hHT : (H T).cells = T.cells :=
      hreflectCells T T (BandPrototileCentralSymmetry (q 0) T hT)
    have hsigned := BandSignedOccurrenceHalfTurn q (TileCentroid T) cert.P
      (fun i s => (cert.outer_occurrence i s).1)
      (fun i s => (cert.outer_occurrence i s).2.2) 0
    have hHplus : (H (cert.P 0 true)).cells = (cert.P 0 false).cells :=
      hreflectCells _ _ hsigned.2.2.2.2.2
    have hHminus : (H (cert.P 0 false)).cells = (cert.P 0 true).cells := DiskAreaGeometry.hHminus
        q cfg C₀ T cert u htau hHcells hHplus
    have hHcomplement :
        (H (TileCellComplement T (cert.P 0 false))).cells =
          (TileCellComplement T (cert.P 0 true)).cells := DiskAreaGeometry.hHcomplement q cfg C₀
              T cert u hHT hHminus
    obtain ⟨hminusDisk, hminusTouch⟩ := horiginal 0 false (Or.inr rfl)
    have hHDisk : LatticeTile (H (TileCellComplement T (cert.P 0 false))) :=
      (TileDiskAreaCovariance _ t).1.mp
        ((TileDiskAreaCovariance _ 0).2.1.mp
          ((TileDiskAreaCovariance _ 0).2.1.mp hminusDisk))
    have hHTouch : TileTouching (H (TileCellComplement T (cert.P 0 false)))
        (H (cert.P 0 false)) :=
      (TileTouchingCovariance _ _ t).1.mp
        ((TileTouchingCovariance _ _ 0).2.1.mp
          ((TileTouchingCovariance _ _ 0).2.1.mp hminusTouch))
    have hHcompNonempty := (LatticeTileGridStructure _ hHDisk).1.1
    have hHminusDisk : LatticeTile (H (cert.P 0 false)) :=
      (TileDiskAreaCovariance _ t).1.mp
        ((TileDiskAreaCovariance _ 0).2.1.mp
          ((TileDiskAreaCovariance _ 0).2.1.mp (cert.parent_lattice 0 false)))
    have hHminusNonempty := (LatticeTileGridStructure _ hHminusDisk).1.1
    have hcompObs := ProtoTileObservableExtensionality _ _ hHcomplement
      (fun h => False.elim (Finset.nonempty_iff_ne_empty.mp hHcompNonempty h))
    have hminusObs := ProtoTileObservableExtensionality _ _ hHminus
      (fun h => False.elim (Finset.nonempty_iff_ne_empty.mp hHminusNonempty h))
    constructor
    · change TopologicalDisk (TileRealization _)
      rw [← hcompObs.2.2.2.1]
      exact hHDisk
    · unfold TileTouching at hHTouch ⊢
      rcases hHTouch with htouch | hdegenerate | hdegenerate
      · left
        simpa only [hHcomplement, hHminus, hcompObs.2.1, hcompObs.2.2.1,
          hminusObs.2.1, hminusObs.2.2.1] using htouch
      · exact False.elim (Finset.nonempty_iff_ne_empty.mp hHcompNonempty hdegenerate.1)
      · exact False.elim (Finset.nonempty_iff_ne_empty.mp hHminusNonempty hdegenerate.1)

end ApollonianSuperharmonic

end
