/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P4456T2CrosscutIndex
public import LeanPool.ApollonianSuperharmonic.P4456T2ParentSide
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralLayoutCertificate
public import LeanPool.ApollonianSuperharmonic.BandSignedOccurrenceHalfTurn
public import LeanPool.ApollonianSuperharmonic.TileTouchingCovariance
public import LeanPool.ApollonianSuperharmonic.ProtoTileObservableExtensionality
public import LeanPool.ApollonianSuperharmonic.QuarterTurnSymmetricCenteredTransport

-- [TABLET NODE: P4456T2OrderedNoChord]

/-!
# P4456T2OrderedNoChord

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace OrderedNoChordGeometry

private theorem cycle_constant :
    (by
      classical
      exact
        ∀ (f : Fin 6 → Int), ∀ (i : Fin 6), ∀ (i' : Fin 6), (∀ j : Fin 6, f j = f (j + 1) ∨ (j =
            i ∧ j + 1 = i') ∨ (j = i' ∧ j + 1 = i)) → ∀ j, f j = f 0 ) := by
  classical
  intro f i i' h j
  have h0 : f 0 = f 1 ∨ (0 = i ∧ 1 = i') ∨ (0 = i' ∧ 1 = i) := h 0
  have h1 : f 1 = f 2 ∨ (1 = i ∧ 2 = i') ∨ (1 = i' ∧ 2 = i) := h 1
  have h2 : f 2 = f 3 ∨ (2 = i ∧ 3 = i') ∨ (2 = i' ∧ 3 = i) := h 2
  have h3 : f 3 = f 4 ∨ (3 = i ∧ 4 = i') ∨ (3 = i' ∧ 4 = i) := h 3
  have h4 : f 4 = f 5 ∨ (4 = i ∧ 5 = i') ∨ (4 = i' ∧ 5 = i) := h 4
  have h5 : f 5 = f 0 ∨ (5 = i ∧ 0 = i') ∨ (5 = i' ∧ 0 = i) := h 5
  have hall : f 1 = f 0 ∧ f 2 = f 0 ∧ f 3 = f 0 ∧ f 4 = f 0 ∧ f 5 = f 0 := by
    fin_cases i <;> fin_cases i' <;>
      norm_num [Fin.ext_iff] at h0 h1 h2 h3 h4 h5 <;> omega
  fin_cases j
  · rfl
  · exact hall.1
  · exact hall.2.1
  · exact hall.2.2.1
  · exact hall.2.2.2.1
  · exact hall.2.2.2.2

private theorem hsub :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (layout : BandOrderedGeneralLayoutCertificate q cfg
            C T), ∀ i, ∀ s, (layout.P i s).cells ⊆ T.cells ) := by
  classical
  intro q cfg C T layout i s c hc
  exact (layout.outer_union c).mpr ⟨i, s, hc⟩

private theorem ht :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (layout : BandOrderedGeneralLayoutCertificate q cfg
            C T), ∀ (u : GaussianInt), (GaussianRealPoint u = ((TileCentroid (layout.P (0 : Fin
            (3 : ℕ)) false)).1 + (TileCentroid (layout.P (0 : Fin (3 : ℕ)) false)).2,
            (TileCentroid (layout.P (0 : Fin (3 : ℕ)) false)).2 - (TileCentroid (layout.P (0 :
            Fin (3 : ℕ)) false)).1)) → (
        let w := BandVectors.1 (q 3) (q 2)
        let t : GaussianInt :=
          ⟨u.re - u.im + w.re + w.im, u.re + u.im + w.im - w.re⟩
        (t.re : Real) = 2 * (TileCentroid T).1 ∧ (t.im : Real) = 2 * (TileCentroid T).2) ) := by
  classical
  intro q cfg C T layout u hu w t
  have hur := congrArg Prod.fst hu
  have hui := congrArg Prod.snd hu
  have hc := (layout.outer_occurrence 0 false).2.2
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
        ∀ (U : ProtoTile), ∀ (z : GaussianInt), z ∈ U.cells ↔ ((z.re : Real) + 1 / 2, (z.im :
            Real) + 1 / 2) ∈ TileRealization U ) := by
  classical
  intro U z
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

private theorem hHsigned :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (layout : BandOrderedGeneralLayoutCertificate q cfg
            C T), ∀ (u : GaussianInt),
        let w := BandVectors.1 (q 3) (q 2)
        let t : GaussianInt :=
          ⟨u.re - u.im + w.re + w.im, u.re + u.im + w.im - w.re⟩
        let H : ProtoTile → ProtoTile := fun U =>
          TileTranslation (TileQuarterTurn (TileQuarterTurn U)) t
        let tau : GaussianInt → GaussianInt := fun z => t - z - 1 - ⟨0, 1⟩
        (Function.Involutive tau) → ((∀ U, (H U).cells = U.cells.image tau) → ((∀ U,
            TileRealization (H U) = (fun p : Real × Real => (2 * (TileCentroid T).1 - p.1, 2 *
            (TileCentroid T).2 - p.2)) '' TileRealization U) → ((∀ (U : ProtoTile), ∀ (z :
            GaussianInt), z ∈ U.cells ↔ ((z.re : Real) + 1 / 2, (z.im : Real) + 1 / 2) ∈
            TileRealization U) → (∀ i, ∀ s, (H (layout.P i s)).cells = (layout.P i
            (!s)).cells)))) ) := by
  classical
  intro q cfg C T layout u w t H tau htau hHcells hHreal hcenter i s
  have hsigned := BandSignedOccurrenceHalfTurn q (TileCentroid T) layout.P
    (fun i s => (layout.outer_occurrence i s).1)
    (fun i s => (layout.outer_occurrence i s).2.2) i
  have hplus : (H (layout.P i true)).cells = (layout.P i false).cells := by
    have hreal : TileRealization (H (layout.P i true)) =
        TileRealization (layout.P i false) :=
      (hHreal _).trans hsigned.2.2.2.2.2.symm
    ext z
    rw [hcenter, hcenter, hreal]
  cases s
  · change (H (layout.P i false)).cells = (layout.P i true).cells
    rw [hHcells, ← hplus, hHcells, Finset.image_image]
    simp [htau]
  · exact hplus

private theorem touch_flip :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (layout : BandOrderedGeneralLayoutCertificate q cfg
            C T), (∀ i, ∀ s, (layout.P i s).cells.Nonempty) → (∀ (u : GaussianInt),
        let w := BandVectors.1 (q 3) (q 2)
        let t : GaussianInt :=
          ⟨u.re - u.im + w.re + w.im, u.re + u.im + w.im - w.re⟩
        let H : ProtoTile → ProtoTile := fun U =>
          TileTranslation (TileQuarterTurn (TileQuarterTurn U)) t
        (∀ i, ∀ s, (H (layout.P i s)).cells = (layout.P i (!s)).cells) → (∀ i, ∀ s, ∀ j, ∀ r,
            TileTouching (layout.P i s) (layout.P j r) → TileTouching (layout.P i (!s)) (layout.P
            j (!r)))) ) := by
  classical
  intro q cfg C T layout hne u w t H hHsigned i s j r h
  have hH : TileTouching (H (layout.P i s)) (H (layout.P j r)) :=
    (TileTouchingCovariance _ _ t).1.mp
      ((TileTouchingCovariance _ _ 0).2.1.mp
        ((TileTouchingCovariance _ _ 0).2.1.mp h))
  have oa := ProtoTileObservableExtensionality _ _ (hHsigned i s)
    (fun he => False.elim ((hne i (!s)).ne_empty ((hHsigned i s).symm.trans he)))
  have ob := ProtoTileObservableExtensionality _ _ (hHsigned j r)
    (fun he => False.elim ((hne j (!r)).ne_empty ((hHsigned j r).symm.trans he)))
  rcases hH with hH | ⟨he, _⟩ | ⟨he, _⟩
  · left
    simpa only [hHsigned, oa.2.1, ob.2.1, oa.2.2.1, ob.2.2.1] using hH
  · exact False.elim ((hne i (!s)).ne_empty ((hHsigned i s).symm.trans he))
  · exact False.elim ((hne j (!r)).ne_empty ((hHsigned j r).symm.trans he))

private theorem touch_sym :
    (by
      classical
      exact
        ∀ U, ∀ V, TileTouching U V → TileTouching V U ) := by
  classical
  intro U V h
  rcases h with ⟨hu, hv, hd, hp⟩ | h | h
  · left
    exact ⟨hv, hu, hd.symm, by simpa only [Set.inter_comm] using hp⟩
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl h)

private theorem hlabels :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (layout : BandOrderedGeneralLayoutCertificate q cfg
            C T), ∀ (side : GaussianInt → ℤ), ∀ (k : Fin (3 : ℕ) → Bool → ℤ), (∀ (i : Fin (3 :
            ℕ)), ∀ (s : Bool), ∀ c ∈ (layout.P i s).cells, side c = k i s) → (
        let V : Fin 6 → Fin 3 × Bool :=
          ![(0, true), (2, false), (1, true), (0, false), (2, true), (1, false)]
        let P : Fin 6 → ProtoTile := fun j => layout.P (V j).1 (V j).2
        let l : Fin 6 → Int := fun j => k (V j).1 (V j).2
        ∀ j, ∀ c, c ∈ (P j).cells → side c = l j) ) := by
  classical
  intro q cfg C T layout side k hk V P l j c hc
  exact hk _ _ c hc

private theorem hcontacts :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (layout : BandOrderedGeneralLayoutCertificate q cfg
            C T), (∀ i, ∀ s, ∀ j, ∀ r, TileTouching (layout.P i s) (layout.P j r) → TileTouching
            (layout.P i (!s)) (layout.P j (!r))) → ((∀ U, ∀ V, TileTouching U V → TileTouching V
            U) → (
        let V : Fin 6 → Fin 3 × Bool :=
          ![(0, true), (2, false), (1, true), (0, false), (2, true), (1, false)]
        let P : Fin 6 → ProtoTile := fun j => layout.P (V j).1 (V j).2
        ∀ j : Fin 6, TileTouching (P j) (P (j + 1)))) ) := by
  classical
  intro q cfg C T layout touch_flip touch_sym V P j
  have hFA := layout.outer_touching.2.1.2.2.1
  have hDA := layout.outer_touching.2.2.2.1.2.2.1
  have hFC := layout.outer_touching.2.2.2.2.2.2.2.2.2.1
  fin_cases j
  · exact touch_sym _ _ hFA
  · exact hFC
  · exact touch_flip 1 false 0 true hDA
  · exact touch_flip 0 true 2 false (touch_sym _ _ hFA)
  · exact touch_flip 2 false 1 true hFC
  · exact hDA

private theorem incident :
    (by
      classical
      exact
        ∀ (x : LatticeCell), ∀ (y : LatticeCell), ∀ (a : GaussianInt), ∀ (b : GaussianInt), (a ≠
            b) → (({x, y} ∈ FootprintEdges (⟨{a}, a⟩ : ProtoTile)) → (({x, y} ∈ FootprintEdges
            (⟨{b}, b⟩ : ProtoTile)) → (∀ (z : GaussianInt), ∀ (z' : GaussianInt), ((x = z + (1 :
            GaussianInt) ∧ y = z + (1 : GaussianInt) + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ∨ y = z
            + (1 : GaussianInt) ∧ x = z + (1 : GaussianInt) + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt))
            ∧ z' = z + (1 : GaussianInt) ∨ (x = z + (1 : GaussianInt) + (⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt) ∧ y = z + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ∨ y = z + (1 : GaussianInt)
            + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ∧ x = z + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) ∧
            z' = z + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) → (∀ c, ({x, y} : Finset GaussianInt) ∈
            FootprintEdges (⟨{c}, c⟩ : ProtoTile) → c = a ∨ c = b)))) ) := by
  classical
  intro x y a b hab hea heb z z' hform c hc
  have hia := (P4397T1UnitEdgeCells.2 x y z z' hform ⟨{a}, a⟩).1.mp hea
  have hib := (P4397T1UnitEdgeCells.2 x y z z' hform ⟨{b}, b⟩).1.mp heb
  have hic := (P4397T1UnitEdgeCells.2 x y z z' hform ⟨{c}, c⟩).1.mp hc
  simp only [Finset.mem_singleton] at hia hib hic
  rcases hia with hia | hia <;> rcases hib with hib | hib <;>
    rcases hic with hic | hic
  all_goals first
    | exact Or.inl (hic.symm.trans hia)
    | exact Or.inr (hic.symm.trans hib)
    | exact False.elim (hab (hia.symm.trans hib))

private theorem chord_vertex :
    (by
      classical
      exact
        ∀ (x : LatticeCell), ∀ (y : LatticeCell), ∀ (z : GaussianInt), ∀ (z' : GaussianInt), ((x
            = z + (1 : GaussianInt) ∧ y = z + (1 : GaussianInt) + (⟨(0 : ℤ), (1 : ℤ)⟩ :
            GaussianInt) ∨ y = z + (1 : GaussianInt) ∧ x = z + (1 : GaussianInt) + (⟨(0 : ℤ), (1
            : ℤ)⟩ : GaussianInt)) ∧ z' = z + (1 : GaussianInt) ∨ (x = z + (1 : GaussianInt) +
            (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ∧ y = z + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ∨ y =
            z + (1 : GaussianInt) + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ∧ x = z + (⟨(0 : ℤ), (1 :
            ℤ)⟩ : GaussianInt)) ∧ z' = z + (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt)) → (∀ U, ({x, y} :
            Finset GaussianInt) ∈ FootprintEdges U → x ∈ FootprintVertices U) ) := by
  classical
  intro x y z z' hform U heU
  have hU := P4397T1UnitEdgeCells.2 x y z z' hform U
  exact (hU.2.2.1 (hU.1.mp heU)).1

private theorem trans0 :
    (by
      classical
      exact
        ∀ U : ProtoTile, TileTranslation U 0 = U ) := by
  classical
  intro U
  have hz : GaussianTranslation (0 : GaussianInt) = id := by
    funext z
    exact add_zero z
  cases U
  simp [TileTranslation, hz]

private theorem hOparents :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (layout : BandOrderedGeneralLayoutCertificate q cfg
            C T), ∀ c ∈ layout.O.cells, c ∈ (layout.P 0 true).cells ∧ c ∈ (layout.P 0
            false).cells ) := by
  classical
  intro q cfg C T layout c hc
  constructor
  · apply (layout.plus_union c).mpr
    exact ⟨0, false, by simpa only [← layout.precursor_eq] using hc⟩
  · apply (layout.minus_union c).mpr
    exact ⟨0, true, by simpa only [← layout.precursor_cells] using hc⟩

private theorem precursor_side :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (layout : BandOrderedGeneralLayoutCertificate q cfg
            C T), ∀ (x : LatticeCell), ∀ (y : LatticeCell), ∀ (side : GaussianInt → ℤ), ∀ (k :
            Fin (3 : ℕ) → Bool → ℤ), (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), ∀ c ∈ (layout.P i
            s).cells, side c = k i s) → ((∀ U, ({x, y} : Finset GaussianInt) ∈ FootprintEdges U →
            x ∈ FootprintVertices U) → ((∀ U : ProtoTile, TileTranslation U 0 = U) → ((∀ c ∈
            layout.O.cells, c ∈ (layout.P 0 true).cells ∧ c ∈ (layout.P 0 false).cells) → (∀ c, ∀
            d, c ∈ layout.O.cells → ({x, y} : Finset GaussianInt) ∈ FootprintEdges (⟨{c}, c⟩ :
            ProtoTile) → ({x, y} : Finset GaussianInt) ∈ FootprintEdges (⟨{d}, d⟩ : ProtoTile) →
            side c = side d)))) ) := by
  classical
  intro q cfg C T layout x y side k hk chord_vertex trans0 hOparents c d hc hec hed
  have hxO : x ∈ FootprintVertices layout.O := by
    apply chord_vertex
    obtain ⟨c', hc', hf⟩ := hec
    have hcc : c' = c := Finset.mem_singleton.mp hc'
    subst c'
    exact ⟨c, hc, hf⟩
  have hxO' : x ∈ FootprintVertices
      (TileTranslation layout.O ((0 : GaussianInt) * layout.u +
        (0 : GaussianInt) * layout.v)) := by
    simpa only [zero_mul, zero_add, trans0] using hxO
  have hd := layout.precursor_isolated 0 0 x hxO' d (chord_vertex _ hed)
  have hd' : d ∈ (layout.P 0 true).cells ∨ d ∈ (layout.P 0 false).cells := by
    simpa only [SubtileOccurrenceInterpretation, Int.cast_zero, zero_mul,
      zero_add, trans0] using hd
  rcases hd' with hd | hd
  · exact (hk 0 true c (hOparents c hc).1).trans (hk 0 true d hd).symm
  · exact (hk 0 false c (hOparents c hc).2).trans (hk 0 false d hd).symm

private theorem hmodzero :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (layout : BandOrderedGeneralLayoutCertificate q cfg
            C T),
        let V : Fin 6 → Fin 3 × Bool :=
          ![(0, true), (2, false), (1, true), (0, false), (2, true), (1, false)]
        let P : Fin 6 → ProtoTile := fun j => layout.P (V j).1 (V j).2
        (∀ U : ProtoTile, TileTranslation U 0 = U) → (
        let label : Fin 6 → SixSubtileLabel := ![.A, .F, .C, .B, .E, .D]
        ∀ j, ∀ c, c ∉ layout.O.cells → (c ∈ (P j).cells ↔ c ∈
            (ModifiedSubtileOccurrenceInterpretation layout.P layout.O layout.u layout.v ⟨label
            j, 0, 0⟩).cells)) ) := by
  classical
  intro q cfg C T layout V P trans0 label j c hc
  fin_cases j <;>
    simp [P, V, label, ModifiedSubtileOccurrenceInterpretation,
      TileCellComplement, hc, trans0]

private theorem unique_owner :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (layout : BandOrderedGeneralLayoutCertificate q cfg
            C T),
        let V : Fin 6 → Fin 3 × Bool :=
          ![(0, true), (2, false), (1, true), (0, false), (2, true), (1, false)]
        let P : Fin 6 → ProtoTile := fun j => layout.P (V j).1 (V j).2
        let label : Fin 6 → SixSubtileLabel := ![.A, .F, .C, .B, .E, .D]
        (∀ j, ∀ c, c ∉ layout.O.cells → (c ∈ (P j).cells ↔ c ∈
            (ModifiedSubtileOccurrenceInterpretation layout.P layout.O layout.u layout.v ⟨label
            j, 0, 0⟩).cells)) → ((Function.Injective label) → (∀ c, c ∉ layout.O.cells → ∀ i j :
            Fin 6, c ∈ (P i).cells → c ∈ (P j).cells → i = j)) ) := by
  classical
  intro q cfg C T layout V P label hmodzero hlabel_inj c hc i j hi hj
  have heq := (layout.partition c).unique
    ((hmodzero i c hc).mp hi) ((hmodzero j c hc).mp hj)
  exact hlabel_inj (congrArg PeriodicSubtileIndex.label heq)

private theorem cover :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (layout : BandOrderedGeneralLayoutCertificate q cfg
            C T),
        let V : Fin 6 → Fin 3 × Bool :=
          ![(0, true), (2, false), (1, true), (0, false), (2, true), (1, false)]
        let P : Fin 6 → ProtoTile := fun j => layout.P (V j).1 (V j).2
        ∀ c ∈ T.cells, ∃ j : Fin 6, c ∈ (P j).cells ) := by
  classical
  intro q cfg C T layout V P c hc
  obtain ⟨i, s, hc⟩ := (layout.outer_union c).mp hc
  fin_cases i <;> cases s
  · exact ⟨3, hc⟩
  · exact ⟨0, hc⟩
  · exact ⟨5, hc⟩
  · exact ⟨2, hc⟩
  · exact ⟨1, hc⟩
  · exact ⟨4, hc⟩

private theorem common_edge :
    (by
      classical
      exact
        ∀ U W : ProtoTile, U.cells.Nonempty → W.cells.Nonempty → TileTouching U W →
            (FootprintEdges U ∩ FootprintEdges W).Nonempty ) := by
  classical
  intro U W hU hW htouch
  rcases htouch with ⟨_, _, _, p, hnodup, hlength, hverts, hsteps, hedges⟩ |
      ⟨he, _⟩ | ⟨he, _⟩
  · cases p with
    | nil => simp at hlength
    | cons r p =>
      cases p with
      | nil => simp at hlength
      | cons s tail =>
        have hrs : FourNeighborAdjacent r s := hsteps r s [] tail rfl
        have hbound : ({r, s} : Finset GaussianInt) ∈
            BoundaryFootprintEdges U ∩ BoundaryFootprintEdges W :=
          (hedges _).mpr ⟨r, s, [], tail, rfl, rfl⟩
        obtain ⟨v, v', hgeom⟩ := P4397T1UnitEdgeCells.1 r s hrs
        have toFoot (J : ProtoTile) (hJ : ({r, s} : Finset GaussianInt) ∈
            BoundaryFootprintEdges J) : ({r, s} : Finset GaussianInt) ∈
              FootprintEdges J := by
          have hunit := P4397T1UnitEdgeCells.2 r s v v' hgeom J
          apply hunit.1.mpr
          rcases hunit.2.1.mp hJ with ⟨hv, _⟩ | ⟨_, hv'⟩
          · exact Or.inl hv
          · exact Or.inr hv'
        exact ⟨{r, s}, toFoot U hbound.1, toFoot W hbound.2⟩
  · exact False.elim (hU.ne_empty he)
  · exact False.elim (hW.ne_empty he)

private theorem changes :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C :
            BandCircle), ∀ (T : ProtoTile), ∀ (layout : BandOrderedGeneralLayoutCertificate q cfg
            C T), ∀ (x : LatticeCell), ∀ (y : LatticeCell), ∀ (side : GaussianInt → ℤ), ∀ (a :
            GaussianInt), ∀ (b : GaussianInt), (∀ c ∈ T.cells, ∀ d ∈ T.cells, c ≠ d → ∀ f ∈
            FootprintEdges (⟨{c}, c⟩ : ProtoTile) ∩ FootprintEdges (⟨{d}, d⟩ : ProtoTile), side c
            ≠ side d → f = {x, y}) → ((∀ i, ∀ s, (layout.P i s).cells ⊆ T.cells) → (∀ (k : Fin (3
            : ℕ) → Bool → ℤ), (∀ i, ∀ s, (layout.P i s).cells.Nonempty) → (
        let V : Fin 6 → Fin 3 × Bool :=
          ![(0, true), (2, false), (1, true), (0, false), (2, true), (1, false)]
        let P : Fin 6 → ProtoTile := fun j => layout.P (V j).1 (V j).2
        let l : Fin 6 → Int := fun j => k (V j).1 (V j).2
        (∀ j, ∀ c, c ∈ (P j).cells → side c = l j) → ((∀ j : Fin 6, TileTouching (P j) (P (j +
            1))) → ((∀ c, ({x, y} : Finset GaussianInt) ∈ FootprintEdges (⟨{c}, c⟩ : ProtoTile) →
            c = a ∨ c = b) → ((a ∉ layout.O.cells) → ((b ∉ layout.O.cells) → ((∀ c, c ∉
            layout.O.cells → ∀ i j : Fin 6, c ∈ (P i).cells → c ∈ (P j).cells → i = j) → (∀ (ia :
            Fin (6 : ℕ)), (a ∈ (P ia).cells) → (∀ (ib : Fin (6 : ℕ)), (b ∈ (P ib).cells) → ((∀ U
            W : ProtoTile, U.cells.Nonempty → W.cells.Nonempty → TileTouching U W →
            (FootprintEdges U ∩ FootprintEdges W).Nonempty) → (∀ j : Fin 6, l j ≠ l (j + 1) → (j
            = ia ∧ j + 1 = ib) ∨ (j = ib ∧ j + 1 = ia))))))))))))) ) := by
  classical
  intro q cfg C T layout x y side a b hstep hsub k hne V P l hlabels hcontacts incident haO hbO
      unique_owner ia hia ib hib common_edge j hj
  obtain ⟨f, hfU, hfW⟩ := common_edge (P j) (P (j + 1))
    (hne _ _) (hne _ _) (hcontacts j)
  obtain ⟨c, hc, hfc⟩ := hfU
  obtain ⟨d, hd, hfd⟩ := hfW
  have hfc' : f ∈ FootprintEdges (⟨{c}, c⟩ : ProtoTile) :=
    ⟨c, Finset.mem_singleton_self c, hfc⟩
  have hfd' : f ∈ FootprintEdges (⟨{d}, d⟩ : ProtoTile) :=
    ⟨d, Finset.mem_singleton_self d, hfd⟩
  have hdiff : side c ≠ side d := by
    rw [hlabels j c hc, hlabels (j + 1) d hd]
    exact hj
  have hcd : c ≠ d := fun heq => hdiff (congrArg side heq)
  have hfe : f = {x, y} := hstep c (hsub _ _ hc) d (hsub _ _ hd)
    hcd f ⟨hfc', hfd'⟩ hdiff
  rw [hfe] at hfc' hfd'
  rcases incident c hfc' with hca | hcb <;>
    rcases incident d hfd' with hda | hdb
  · exact False.elim (hcd (hca.trans hda.symm))
  · exact Or.inl ⟨unique_owner a haO j ia (hca ▸ hc) hia,
      unique_owner b hbO (j + 1) ib (hdb ▸ hd) hib⟩
  · exact Or.inr ⟨unique_owner b hbO j ib (hcb ▸ hc) hib,
      unique_owner a haO (j + 1) ia (hda ▸ hd) hia⟩
  · exact False.elim (hcd (hcb.trans hdb.symm))

private theorem hallAt444 :
    (by
      classical
      exact
        (∀ (f : Fin 6 → Int), ∀ (i : Fin 6), ∀ (i' : Fin 6), (∀ j : Fin 6, f j = f (j + 1) ∨ (j =
            i ∧ j + 1 = i') ∨ (j = i' ∧ j + 1 = i)) → ∀ j, f j = f 0) → (∀ (k : Fin (3 : ℕ) →
            Bool → ℤ),
        let V : Fin 6 → Fin 3 × Bool :=
          ![(0, true), (2, false), (1, true), (0, false), (2, true), (1, false)]
        let l : Fin 6 → Int := fun j => k (V j).1 (V j).2
        ∀ (ia : Fin (6 : ℕ)), ∀ (ib : Fin (6 : ℕ)), (∀ j : Fin 6, l j ≠ l (j + 1) → (j = ia ∧ j +
            1 = ib) ∨ (j = ib ∧ j + 1 = ia)) → (∀ j, l j = l 0)) ) := by
  classical
  intro cycle_constant k V l ia ib changes
  apply cycle_constant l ia ib
  intro j
  by_cases hj : l j = l (j + 1)
  · exact Or.inl hj
  · exact Or.inr (changes j hj)

end OrderedNoChordGeometry

theorem P4456T2OrderedNoChord
    (q : Fin 4 → CircleCoordinates) (cfg : BandOrderedGeneralConfiguration q)
    (C : BandCircle) (T : ProtoTile) (hT : LatticeTile T)
    (layout : BandOrderedGeneralLayoutCertificate q cfg C T)
    (hparents : ∀ i s, ∀ x y, FourNeighborAdjacent x y →
      x ∈ BoundaryFootprintVertices (layout.P i s) →
      y ∈ BoundaryFootprintVertices (layout.P i s) →
      ¬ OpenLatticeEdge x y ⊆ interior (TileRealization (layout.P i s))) :
    ∀ x y, FourNeighborAdjacent x y →
      x ∈ BoundaryFootprintVertices T → y ∈ BoundaryFootprintVertices T →
      ¬ OpenLatticeEdge x y ⊆ interior (TileRealization T) := by
-- BODY
  exact (by
    classical
    -- The six-cycle remains connected after deleting any one unordered edge.
    have cycle_constant := OrderedNoChordGeometry.cycle_constant
    intro x y hxy hx hy he
    obtain ⟨side, a, b, ha, hb, hab, hdifferent, hea, heb, hstep⟩ :=
      P4456T2CrosscutIndex T hT x y hxy hx hy he
    have hsub := OrderedNoChordGeometry.hsub q cfg C T layout
    choose k hk using fun i s =>
      P4456T2ParentSide T (layout.P i s) hT (layout.parent_lattice i s)
        (hsub i s) x y hxy hx hy side hstep (hparents i s)
    suffices hcycle : ∀ (k : Fin 3 → Bool → Int),
        (∀ i s, ∀ c ∈ (layout.P i s).cells, side c = k i s) →
          side a = side b by
      exact hdifferent (hcycle k hk)
    intro k hk
    have hne : ∀ i s, (layout.P i s).cells.Nonempty :=
      fun i s => (LatticeTileFourNeighborConnected _ (layout.parent_lattice i s)).1
    -- Construct one integral half-turn centered at the outer centroid.
    obtain ⟨u, hu, _⟩ := QuarterTurnSymmetricCenteredTransport
      (layout.P 0 false) (layout.parent_quarter_turn 0 false)
    let w := BandVectors.1 (q 3) (q 2)
    let t : GaussianInt :=
      ⟨u.re - u.im + w.re + w.im, u.re + u.im + w.im - w.re⟩
    have ht := OrderedNoChordGeometry.ht q cfg C T layout u hu
    let H : ProtoTile → ProtoTile := fun U =>
      TileTranslation (TileQuarterTurn (TileQuarterTurn U)) t
    let tau : GaussianInt → GaussianInt := fun z => t - z - 1 - ⟨0, 1⟩
    have htau := OrderedNoChordGeometry.htau q u
    have hHcells := OrderedNoChordGeometry.hHcells q u
    have hHreal := OrderedNoChordGeometry.hHreal q T u ht
    have hcenter := OrderedNoChordGeometry.hcenter
    have hHsigned := OrderedNoChordGeometry.hHsigned q cfg C T layout u htau hHcells hHreal hcenter
    have touch_flip := OrderedNoChordGeometry.touch_flip q cfg C T layout hne u hHsigned
    have touch_sym := OrderedNoChordGeometry.touch_sym
    let V : Fin 6 → Fin 3 × Bool :=
      ![(0, true), (2, false), (1, true), (0, false), (2, true), (1, false)]
    let P : Fin 6 → ProtoTile := fun j => layout.P (V j).1 (V j).2
    let l : Fin 6 → Int := fun j => k (V j).1 (V j).2
    have hlabels := OrderedNoChordGeometry.hlabels q cfg C T layout side k hk
    have hcontacts := OrderedNoChordGeometry.hcontacts q cfg C T layout touch_flip touch_sym
    obtain ⟨z, z', hform⟩ := P4397T1UnitEdgeCells.1 x y hxy
    have incident := OrderedNoChordGeometry.incident x y a b hab hea heb z z' hform
    have chord_vertex := OrderedNoChordGeometry.chord_vertex x y z z' hform
    have trans0 := OrderedNoChordGeometry.trans0
    have hOparents := OrderedNoChordGeometry.hOparents q cfg C T layout
    -- Isolation is used at a corner supported by an occupied precursor cell.
    have precursor_side := OrderedNoChordGeometry.precursor_side q cfg C T layout x y side k hk
        chord_vertex trans0 hOparents
    have haO : a ∉ layout.O.cells := fun h =>
      hdifferent (precursor_side a b h hea heb)
    have hbO : b ∉ layout.O.cells := fun h =>
      hdifferent (precursor_side b a h heb hea).symm
    -- Outside the precursor, the modified partition gives original owners.
    let label : Fin 6 → SixSubtileLabel := ![.A, .F, .C, .B, .E, .D]
    have hmodzero := OrderedNoChordGeometry.hmodzero q cfg C T layout trans0
    have hlabel_inj : Function.Injective label := by decide
    have unique_owner := OrderedNoChordGeometry.unique_owner q cfg C T layout hmodzero hlabel_inj
    have cover := OrderedNoChordGeometry.cover q cfg C T layout
    obtain ⟨ia, hia⟩ := cover a ha
    obtain ⟨ib, hib⟩ := cover b hb
    have common_edge := OrderedNoChordGeometry.common_edge
    -- Every change uses the chord itself and its same two incident cells.
    have changes := OrderedNoChordGeometry.changes q cfg C T layout x y side a b hstep hsub k hne
        hlabels hcontacts incident haO hbO unique_owner ia hia ib hib common_edge
    have hall := OrderedNoChordGeometry.hallAt444 cycle_constant k ia ib changes
    exact (hlabels ia a hia).trans ((hall ia).trans
      ((hall ib).symm.trans (hlabels ib b hib).symm)))

end ApollonianSuperharmonic

end
