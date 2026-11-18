/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.LatticeTileNonempty

public import LeanPool.ApollonianSuperharmonic.BandPrototileTranslationNormalForm
public import LeanPool.ApollonianSuperharmonic.BandSubtileOccurrenceTranslation
public import LeanPool.ApollonianSuperharmonic.TileCellComplementCovariance
public import LeanPool.ApollonianSuperharmonic.TouchingTripleCovariance
public import LeanPool.ApollonianSuperharmonic.TileCellComplement
public import LeanPool.ApollonianSuperharmonic.QuarterTurnSymmetric
public import LeanPool.ApollonianSuperharmonic.FordBaseT1
public import LeanPool.ApollonianSuperharmonic.FordBaseT2
public import LeanPool.ApollonianSuperharmonic.FordBaseTouching
public import LeanPool.ApollonianSuperharmonic.TileArea

-- [TABLET NODE: P4564T2FordGeometry]

/-!
# P4564T2FordGeometry

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace FordInterfaceGeometry

private theorem hFcells :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ((1 : ℕ) < P.q) → (
        let F := FordTile P.q
        (LatticeTile (FordTile P.q) ∧ TileArea (FordTile P.q) = P.q * P.q) → (F.cells.Nonempty))
            ) := by
  classical
  intro P hP F hFgeom
  by_contra hn
  have he : F.cells = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
  have harea := hFgeom.2
  simp [F, TileArea, he] at harea
  omega

private theorem hTstarCells :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (T : ProtoTile),
        let F := FordTile P.q
        ∀ (w : GaussianInt), (T.cells = (TileTranslation F w).cells) → (
        let Tstar := TileTranslation T (-w)
        Tstar.cells = F.cells) ) := by
  classical
  intro P T F w hcellsT Tstar
  have ht := (TileTranslationFormulas T (-w)).1
  rw [ht, hcellsT]
  ext x
  simp [TileTranslation, GaussianTranslation, Finset.mem_image]

private theorem hTstarTile :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (T : ProtoTile),
        let F := FordTile P.q
        ∀ (S₀ : Fin (3 : ℕ) → Bool → ProtoTile), ∀ (w : GaussianInt),
        let Tstar := TileTranslation T (-w)
        (FootprintVertices Tstar = FootprintVertices F ∧ BoundaryFootprintVertices Tstar =
            BoundaryFootprintVertices F ∧ BoundaryFootprintEdges Tstar = BoundaryFootprintEdges F
            ∧ TileRealization Tstar = TileRealization F ∧ TileCentroid Tstar = TileCentroid F) →
            ((LatticeTile (FordTile P.q) ∧ TileArea (FordTile P.q) = (FordRecursiveQuadruple P (0
            : Fin (4 : ℕ))).1.toNat ∧ ∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), LatticeTile
            (TileCellComplement (FordTile P.q) (S₀ i s)) ∧ TileTouching (TileCellComplement
            (FordTile P.q) (S₀ i s)) (S₀ i s)) → (LatticeTile Tstar)) ) := by
  classical
  intro P T F S₀ w Tstar hTstarObs hcanT1
  change TopologicalDisk (TileRealization Tstar)
  rw [hTstarObs.2.2.2.1]
  exact hcanT1.1

private theorem hareaT :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (T : ProtoTile),
        let F := FordTile P.q
        ∀ (w : GaussianInt),
        let Tstar := TileTranslation T (-w)
        (TileArea Tstar = TileArea F) → (TileArea T = TileArea F) ) := by
  classical
  intro P T F w Tstar hareaStar
  calc
    TileArea T = TileArea Tstar := (TileDiskAreaCovariance T (-w)).2.2.2.1.symm
    _ = TileArea F := hareaStar

private theorem hTstarquarter :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (T : ProtoTile),
        let F := FordTile P.q
        ∀ (w : GaussianInt),
        let Tstar := TileTranslation T (-w)
        (FootprintVertices Tstar = FootprintVertices F ∧ BoundaryFootprintVertices Tstar =
            BoundaryFootprintVertices F ∧ BoundaryFootprintEdges Tstar = BoundaryFootprintEdges F
            ∧ TileRealization Tstar = TileRealization F ∧ TileCentroid Tstar = TileCentroid F) →
            ((QuarterTurnSymmetric F) → (QuarterTurnSymmetric Tstar)) ) := by
  classical
  intro P T F w Tstar hTstarObs hFquarter
  simpa [QuarterTurnSymmetric, hTstarObs.2.2.2.1,
    hTstarObs.2.2.2.2] using hFquarter

private theorem hTstarCent :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (w : GaussianInt),
        let Tstar := TileTranslation T (-w)
        TileCentroid Tstar = ((TileCentroid T).1 - (w.re : Real), (TileCentroid T).2 - (w.im :
            Real)) ) := by
  classical
  intro T w Tstar
  simpa [Tstar, sub_eq_add_neg] using
    (TileTranslationFormulas T (-w)).2.2.2.2.1

private theorem translated_center_diff :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (T : ProtoTile),
        let F := FordTile P.q
        ∀ (w : GaussianInt),
        let Tstar := TileTranslation T (-w)
        (FootprintVertices Tstar = FootprintVertices F ∧ BoundaryFootprintVertices Tstar =
            BoundaryFootprintVertices F ∧ BoundaryFootprintEdges Tstar = BoundaryFootprintEdges F
            ∧ TileRealization Tstar = TileRealization F ∧ TileCentroid Tstar = TileCentroid F) →
            ((TileCentroid Tstar = ((TileCentroid T).1 - (w.re : Real), (TileCentroid T).2 -
            (w.im : Real))) → (∀ (U : ProtoTile), TileCentroid (TileTranslation U (-w)) -
            TileCentroid F = TileCentroid U - TileCentroid T)) ) := by
  classical
  intro P T F w Tstar hTstarObs hTstarCent U
  rw [(TileTranslationFormulas U (-w)).2.2.2.2.1,
    ← hTstarObs.2.2.2.2, hTstarCent]
  apply Prod.ext <;> dsimp <;> simp only [Int.cast_neg] <;> ring

private theorem translated_cells_comm :
    (by
      classical
      exact
        ∀ (A : ProtoTile), ∀ (a : GaussianInt), ∀ (b : GaussianInt), (TileTranslation
            (TileTranslation A a) b).cells = (TileTranslation (TileTranslation A b) a).cells ) := by
  classical
  intro A a b
  rw [(TileTranslationFormulas (TileTranslation A a) b).1,
    (TileTranslationFormulas (TileTranslation A b) a).1,
    (TileTranslationFormulas A a).1, (TileTranslationFormulas A b).1]
  ext x
  simp [GaussianTranslation, Finset.mem_image, add_comm,
    add_left_comm]

private theorem translate_cancel :
    (by
      classical
      exact
        ∀ (w : GaussianInt), ∀ (A : ProtoTile), TileTranslation (TileTranslation A (-w)) w = A )
            := by
  classical
  intro w A
  have hfun : GaussianTranslation w ∘ GaussianTranslation (-w) = id := by
    funext z
    simp [GaussianTranslation, add_comm,
      ]
  cases A with
  | mk cells anchor =>
    simp only [TileTranslation, ProtoTile.mk.injEq]
    constructor
    · rw [Finset.image_image, hfun]
      simp
    · simp [GaussianTranslation, add_comm]

private theorem triple_same_cells :
    (by
      classical
      exact
        ∀ (A : ProtoTile), ∀ (A' : ProtoTile), ∀ (B : ProtoTile), ∀ (B' : ProtoTile), ∀ (C :
            ProtoTile), (A.cells = A'.cells) → ((B.cells = B'.cells) → ((A.cells.Nonempty) →
            ((B.cells.Nonempty) → ((TouchingTriple A B C ↔ TouchingTriple A' B' C))))) ) := by
  classical
  intro A A' B B' C hAcells hBcells hAne hBne
  have hAobs := ProtoTileObservableExtensionality A A' hAcells (by
    intro he
    exact (hAne.ne_empty he).elim)
  have hBobs := ProtoTileObservableExtensionality B B' hBcells (by
    intro he
    exact (hBne.ne_empty he).elim)
  have hA'ne : A'.cells.Nonempty := by rw [← hAcells]; exact hAne
  have hB'ne : B'.cells.Nonempty := by rw [← hBcells]; exact hBne
  have hA'not : A'.cells ≠ ∅ := hA'ne.ne_empty
  have hB'not : B'.cells ≠ ∅ := hB'ne.ne_empty
  simp [TouchingTriple, TileTouching, hAcells, hBcells,
    hA'ne, hB'ne, hA'not, hB'not, hAobs.2.1, hAobs.2.2.1,
    hBobs.2.1, hBobs.2.2.1]

private theorem triple_same_root :
    (by
      classical
      exact
        ∀ (A : ProtoTile), ∀ (A' : ProtoTile), ∀ (B : ProtoTile), ∀ (C : ProtoTile), (A.cells =
            A'.cells) → ((A.cells.Nonempty) → ((TouchingTriple A B C ↔ TouchingTriple A' B C))) )
            := by
  classical
  intro A A' B C hAcells hAne
  have hAobs := ProtoTileObservableExtensionality A A' hAcells (by
    intro he
    exact (hAne.ne_empty he).elim)
  have hA'ne : A'.cells.Nonempty := by rw [← hAcells]; exact hAne
  have hA'not : A'.cells ≠ ∅ := hA'ne.ne_empty
  simp [TouchingTriple, TileTouching, hAcells, hA'ne, hA'not,
    hAobs.2.1, hAobs.2.2.1]

private theorem triple_same_cells_all :
    (by
      classical
      exact
        ∀ (A : ProtoTile), ∀ (A' : ProtoTile), ∀ (B : ProtoTile), ∀ (B' : ProtoTile), ∀ (C :
            ProtoTile), ∀ (C' : ProtoTile), (A.cells = A'.cells) → ((B.cells = B'.cells) →
            ((C.cells = C'.cells) → ((A.cells.Nonempty) → ((B.cells.Nonempty) →
            ((C.cells.Nonempty) → ((TouchingTriple A B C ↔ TouchingTriple A' B' C'))))))) ) := by
  classical
  intro A A' B B' C C' hAcells hBcells hCcells hAne hBne hCne
  have hAobs := ProtoTileObservableExtensionality A A' hAcells (by
    intro he
    exact (hAne.ne_empty he).elim)
  have hBobs := ProtoTileObservableExtensionality B B' hBcells (by
    intro he
    exact (hBne.ne_empty he).elim)
  have hCobs := ProtoTileObservableExtensionality C C' hCcells (by
    intro he
    exact (hCne.ne_empty he).elim)
  have hA'ne : A'.cells.Nonempty := by rw [← hAcells]; exact hAne
  have hB'ne : B'.cells.Nonempty := by rw [← hBcells]; exact hBne
  have hC'ne : C'.cells.Nonempty := by rw [← hCcells]; exact hCne
  have hA'not : A'.cells ≠ ∅ := hA'ne.ne_empty
  have hB'not : B'.cells ≠ ∅ := hB'ne.ne_empty
  have hC'not : C'.cells ≠ ∅ := hC'ne.ne_empty
  simp [TouchingTriple, TileTouching, hAcells, hBcells, hCcells,
    hA'ne, hB'ne, hC'ne, hA'not, hB'not, hC'not,
    hAobs.2.1, hAobs.2.2.1, hBobs.2.1, hBobs.2.2.1,
    hCobs.2.1, hCobs.2.2.1]

private theorem translated_root_cells :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (T : ProtoTile),
        let F := FordTile P.q
        ∀ (w : GaussianInt), (T.cells = (TileTranslation F w).cells) → ((∀ (A : ProtoTile), ∀ (a
            : GaussianInt), ∀ (b : GaussianInt), (TileTranslation (TileTranslation A a) b).cells
            = (TileTranslation (TileTranslation A b) a).cells) → (∀ (v : GaussianInt),
            (TileTranslation (TileTranslation F v) w).cells = (TileTranslation T v).cells)) ) := by
  classical
  intro P T F w hcellsT translated_cells_comm v
  rw [translated_cells_comm F v w,
    (TileTranslationFormulas (TileTranslation F w) v).1,
    (TileTranslationFormulas T v).1, hcellsT]

private abbrev lattice_cells_nonempty := ApollonianSuperharmonic.LatticeTileNonempty.cells

private theorem hoccStar :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (T : ProtoTile),
        let q := FordRecursiveQuadruple P
        ∀ (w : GaussianInt),
        let Tstar := TileTranslation T (-w)
        ∀ (S : Fin (3 : ℕ) → Bool → ProtoTile), (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool),
            BandSubtileOccurrence (FordRecursiveQuadruple P) T i s (S i s)) → (
        let Sstar : Fin 3 → Bool → ProtoTile := fun i s =>
          TileTranslation (S i s) (-w)
        ∀ (i : Fin 3), ∀ (s : Bool), BandSubtileOccurrence q Tstar i s (Sstar i s)) ) := by
  classical
  intro P T q w Tstar S hS Sstar i s
  simpa [Tstar, Sstar, q] using
    (BandSubtileOccurrenceTranslation q T (S i s) i s (-w)).mp (hS i s)

private theorem hoccF :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (T : ProtoTile),
        let q := FordRecursiveQuadruple P
        let F := FordTile P.q
        ∀ (w : GaussianInt),
        let Tstar := TileTranslation T (-w)
        (FootprintVertices Tstar = FootprintVertices F ∧ BoundaryFootprintVertices Tstar =
            BoundaryFootprintVertices F ∧ BoundaryFootprintEdges Tstar = BoundaryFootprintEdges F
            ∧ TileRealization Tstar = TileRealization F ∧ TileCentroid Tstar = TileCentroid F) →
            (∀ (S : Fin (3 : ℕ) → Bool → ProtoTile),
        let Sstar : Fin 3 → Bool → ProtoTile := fun i s =>
          TileTranslation (S i s) (-w)
        (∀ (i : Fin 3), ∀ (s : Bool), BandSubtileOccurrence q Tstar i s (Sstar i s)) → (∀ (i :
            Fin 3), ∀ (s : Bool), BandSubtileOccurrence q F i s (Sstar i s))) ) := by
  classical
  intro P T q F w Tstar hTstarObs S Sstar hoccStar i s
  rcases hoccStar i s with ⟨hband, hfoot, hcentroid⟩
  refine ⟨hband, ?_, ?_⟩
  · rw [hTstarObs.1] at hfoot
    exact hfoot
  · rw [hTstarObs.2.2.2.2] at hcentroid
    exact hcentroid

private theorem hunionF :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (T : ProtoTile),
        let F := FordTile P.q
        ∀ (w : GaussianInt),
        let Tstar := TileTranslation T (-w)
        (Tstar.cells = F.cells) → (∀ (S : Fin (3 : ℕ) → Bool → ProtoTile), (∀ (x : LatticeCell),
            x ∈ T.cells ↔ ∃ (i : Fin (3 : ℕ)) (s : Bool), x ∈ (S i s).cells) → (
        let Sstar : Fin 3 → Bool → ProtoTile := fun i s =>
          TileTranslation (S i s) (-w)
        ∀ (x : GaussianInt), x ∈ F.cells ↔ ∃ i s, x ∈ (Sstar i s).cells)) ) := by
  classical
  intro P T F w Tstar hTstarCells S hunion Sstar x
  constructor
  · intro hx
    have hx' : x ∈ Tstar.cells := by simpa [hTstarCells] using hx
    rw [(TileTranslationFormulas T (-w)).1] at hx'
    rcases Finset.mem_image.mp hx' with ⟨y, hy, hxy⟩
    rcases (hunion y).mp hy with ⟨i, s, hys⟩
    refine ⟨i, s, ?_⟩
    rw [(TileTranslationFormulas (S i s) (-w)).1]
    exact Finset.mem_image.mpr ⟨y, hys, hxy⟩
  · rintro ⟨i, s, hx⟩
    rw [(TileTranslationFormulas (S i s) (-w)).1] at hx
    rcases Finset.mem_image.mp hx with ⟨y, hy, hxy⟩
    have hyT : y ∈ T.cells := (hunion y).mpr ⟨i, s, hy⟩
    have hxStar : x ∈ Tstar.cells := by
      rw [(TileTranslationFormulas T (-w)).1]
      exact Finset.mem_image.mpr ⟨y, hyT, hxy⟩
    simpa [hTstarCells] using hxStar

private theorem hCobsAt360 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (T : ProtoTile),
        let F := FordTile P.q
        ∀ (w : GaussianInt),
        let Tstar := TileTranslation T (-w)
        ∀ (S : Fin (3 : ℕ) → Bool → ProtoTile),
        let Sstar : Fin 3 → Bool → ProtoTile := fun i s =>
          TileTranslation (S i s) (-w)
        ∀ (i : Fin (3 : ℕ)), ∀ (s : Bool),
        let Cstar := TileCellComplement Tstar (Sstar i s)
        let CF := TileCellComplement F (Sstar i s)
        (Cstar.cells = CF.cells) → ((Finset.Nonempty CF.cells) → (FootprintVertices Cstar =
            FootprintVertices CF ∧ BoundaryFootprintVertices Cstar = BoundaryFootprintVertices CF
            ∧ BoundaryFootprintEdges Cstar = BoundaryFootprintEdges CF ∧ TileRealization Cstar =
            TileRealization CF ∧ TileCentroid Cstar = TileCentroid CF)) ) := by
  classical
  intro P T F w Tstar S Sstar i s Cstar CF hCcells hCFne
  exact ProtoTileObservableExtensionality Cstar CF hCcells (by
    intro he
    have he' : CF.cells = ∅ := by rw [← hCcells]; exact he
    exact (hCFne.ne_empty he').elim)

private theorem hCtile :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (T : ProtoTile),
        let F := FordTile P.q
        ∀ (w : GaussianInt),
        let Tstar := TileTranslation T (-w)
        ∀ (S : Fin (3 : ℕ) → Bool → ProtoTile),
        let Sstar : Fin 3 → Bool → ProtoTile := fun i s =>
          TileTranslation (S i s) (-w)
        ∀ (i : Fin (3 : ℕ)), ∀ (s : Bool),
        let Cstar := TileCellComplement Tstar (Sstar i s)
        let CF := TileCellComplement F (Sstar i s)
        (LatticeTile (TileCellComplement (FordTile P.q) (Sstar i s))) → ((FootprintVertices Cstar
            = FootprintVertices CF ∧ BoundaryFootprintVertices Cstar = BoundaryFootprintVertices
            CF ∧ BoundaryFootprintEdges Cstar = BoundaryFootprintEdges CF ∧ TileRealization Cstar
            = TileRealization CF ∧ TileCentroid Cstar = TileCentroid CF) → (LatticeTile Cstar)) )
            := by
  classical
  intro P T F w Tstar S Sstar i s Cstar CF hCFtile hCobs
  change TopologicalDisk (TileRealization Cstar)
  rw [hCobs.2.2.2.1]
  exact hCFtile

private theorem hCtouch :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ∀ (T : ProtoTile),
        let F := FordTile P.q
        ∀ (w : GaussianInt),
        let Tstar := TileTranslation T (-w)
        (Tstar.cells = F.cells) → (∀ (S : Fin (3 : ℕ) → Bool → ProtoTile),
        let Sstar : Fin 3 → Bool → ProtoTile := fun i s =>
          TileTranslation (S i s) (-w)
        (LatticeTile (FordTile P.q) ∧ TileArea (FordTile P.q) = (FordRecursiveQuadruple P (0 :
            Fin (4 : ℕ))).1.toNat ∧ ∀ (i : Fin (3 : ℕ)), ∀ (s : Bool), LatticeTile
            (TileCellComplement (FordTile P.q) (Sstar i s)) ∧ TileTouching (TileCellComplement
            (FordTile P.q) (Sstar i s)) (Sstar i s)) → (∀ (i : Fin (3 : ℕ)), ∀ (s : Bool),
        let Cstar := TileCellComplement Tstar (Sstar i s)
        let CF := TileCellComplement F (Sstar i s)
        (Cstar.cells = CF.cells) → ((Finset.Nonempty CF.cells) → ((FootprintVertices Cstar =
            FootprintVertices CF ∧ BoundaryFootprintVertices Cstar = BoundaryFootprintVertices CF
            ∧ BoundaryFootprintEdges Cstar = BoundaryFootprintEdges CF ∧ TileRealization Cstar =
            TileRealization CF ∧ TileCentroid Cstar = TileCentroid CF) → (TileTouching Cstar
            (Sstar i s)))))) ) := by
  classical
  intro P T F w Tstar hTstarCells S Sstar hbase i s Cstar CF hCcells hCFne hCobs
  rcases (hbase.2.2 i s).2 with hregular | hemptyComp | hemptySubtile
  · rcases hregular with ⟨hcfne, hsne, hdisj, hpath⟩
    left
    refine ⟨?_, hsne, ?_, ?_⟩
    · rw [hCcells]
      exact hcfne
    · simpa [Cstar, CF, TileCellComplement, hTstarCells] using hdisj
    · simpa [hCobs.2.1, hCobs.2.2.1] using hpath
  · rcases hemptyComp with ⟨hce, ha⟩
    have : False := hCFne.ne_empty (by
      have he' : CF.cells = ∅ := by simpa [CF, TileCellComplement] using hce
      exact he')
    exact this.elim
  · rcases hemptySubtile with ⟨hse, ha⟩
    right
    right
    refine ⟨hse, ?_⟩
    rw [hCobs.2.1]
    exact ha

private theorem hTcomp :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (w : GaussianInt),
        let Tstar := TileTranslation T (-w)
        ∀ (S : Fin (3 : ℕ) → Bool → ProtoTile),
        let Sstar : Fin 3 → Bool → ProtoTile := fun i s =>
          TileTranslation (S i s) (-w)
        ∀ (i : Fin (3 : ℕ)), ∀ (s : Bool),
        let Cstar := TileCellComplement Tstar (Sstar i s)
        (LatticeTile Cstar) → ((TileTranslation (TileCellComplement T (S i s)) (-w) = Cstar) →
            (LatticeTile (TileCellComplement T (S i s)))) ) := by
  classical
  intro T w Tstar S Sstar i s Cstar hCtile hcovEq
  exact (TileDiskAreaCovariance (TileCellComplement T (S i s)) (-w)).1.mpr
    (hcovEq ▸ hCtile)

private theorem hTtouch :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (w : GaussianInt),
        let Tstar := TileTranslation T (-w)
        ∀ (S : Fin (3 : ℕ) → Bool → ProtoTile),
        let Sstar : Fin 3 → Bool → ProtoTile := fun i s =>
          TileTranslation (S i s) (-w)
        ∀ (i : Fin (3 : ℕ)), ∀ (s : Bool),
        let Cstar := TileCellComplement Tstar (Sstar i s)
        (TileTouching Cstar (Sstar i s)) → ((TileTranslation (TileCellComplement T (S i s)) (-w)
            = Cstar) → (TileTouching (TileCellComplement T (S i s)) (S i s))) ) := by
  classical
  intro T w Tstar S Sstar i s Cstar hCtouch hcovEq
  apply (TileTouchingCovariance (TileCellComplement T (S i s)) (S i s) (-w)).1.mpr
  simpa [Sstar, hcovEq] using hCtouch

private theorem hreal :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (w : GaussianInt),
        let Tstar := TileTranslation T (-w)
        TileRealization Tstar = (fun p : Real × Real => (p.1 - (w.re : Real), p.2 - (w.im :
            Real))) '' TileRealization T ) := by
  classical
  intro T w Tstar
  simpa [Tstar, sub_eq_add_neg] using
    (TileTranslationFormulas T (-w)).2.2.2.1

private theorem hf_inj :
    (by
      classical
      exact
        ∀ (w : GaussianInt),
        let f : Real × Real → Real × Real := fun p =>
          (p.1 - (w.re : Real), p.2 - (w.im : Real))
        Function.Injective f ) := by
  classical
  intro w f a b hab
  have h1 := congrArg Prod.fst hab
  have h2 := congrArg Prod.snd hab
  dsimp [f] at h1 h2
  exact Prod.ext (by linarith) (by linarith)

private theorem hrotate :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (w : GaussianInt),
        let Tstar := TileTranslation T (-w)
        (TileCentroid Tstar = ((TileCentroid T).1 - (w.re : Real), (TileCentroid T).2 - (w.im :
            Real))) → (
        let f : Real × Real → Real × Real := fun p =>
          (p.1 - (w.re : Real), p.2 - (w.im : Real))
        ∀ (p : Real × Real), ( (TileCentroid Tstar).1 - ((f p).2 - (TileCentroid Tstar).2),
            (TileCentroid Tstar).2 + ((f p).1 - (TileCentroid Tstar).1)) = f ((TileCentroid T).1
            - (p.2 - (TileCentroid T).2), (TileCentroid T).2 + (p.1 - (TileCentroid T).1))) ) := by
  classical
  intro T w Tstar hcent f p
  rw [hcent]
  dsimp [f]
  congr 1 <;> ring

private theorem hpsAt428 :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (w : GaussianInt),
        let Tstar := TileTranslation T (-w)
        (TileRealization Tstar = (fun p : Real × Real => (p.1 - (w.re : Real), p.2 - (w.im :
            Real))) '' TileRealization T) → (
        let f : Real × Real → Real × Real := fun p =>
          (p.1 - (w.re : Real), p.2 - (w.im : Real))
        ∀ (p : ℝ × ℝ), (p ∈ TileRealization T) → (f p ∈ TileRealization Tstar)) ) := by
  classical
  intro T w Tstar hreal f p hp
  rw [hreal]
  exact ⟨p, hp, rfl⟩

private theorem hr'At434 :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (w : GaussianInt),
        let Tstar := TileTranslation T (-w)
        let f : Real × Real → Real × Real := fun p =>
          (p.1 - (w.re : Real), p.2 - (w.im : Real))
        (Function.Injective f) → ((∀ (p : Real × Real), ( (TileCentroid Tstar).1 - ((f p).2 -
            (TileCentroid Tstar).2), (TileCentroid Tstar).2 + ((f p).1 - (TileCentroid Tstar).1))
            = f ((TileCentroid T).1 - (p.2 - (TileCentroid T).2), (TileCentroid T).2 + (p.1 -
            (TileCentroid T).1))) → (∀ (p : ℝ × ℝ), ∀ (r : ℝ × ℝ), ((fun (p : ℝ × ℝ) => (p.1 -
            (↑w.re : ℝ), p.2 - (↑w.im : ℝ))) r = ((TileCentroid Tstar).1 - ((f p).2 -
            (TileCentroid Tstar).2), (TileCentroid Tstar).2 + ((f p).1 - (TileCentroid
            Tstar).1))) → (r = ((TileCentroid T).1 - (p.2 - (TileCentroid T).2), (TileCentroid
            T).2 + (p.1 - (TileCentroid T).1))))) ) := by
  classical
  intro T w Tstar f hf_inj hrotate p r hrf
  apply hf_inj
  change f r = _ at hrf
  rw [hrotate] at hrf
  exact hrf

private theorem hpsAt443 :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (w : GaussianInt),
        let Tstar := TileTranslation T (-w)
        (TileRealization Tstar = (fun p : Real × Real => (p.1 - (w.re : Real), p.2 - (w.im :
            Real))) '' TileRealization T) → (
        let f : Real × Real → Real × Real := fun p =>
          (p.1 - (w.re : Real), p.2 - (w.im : Real))
        ∀ (p : ℝ × ℝ), (
        let c := TileCentroid T; (c.1 - (p.2 - c.2), c.2 + (p.1 - c.1)) ∈ TileRealization T) → (f
            ((TileCentroid T).1 - (p.2 - (TileCentroid T).2), (TileCentroid T).2 + (p.1 -
            (TileCentroid T).1)) ∈ TileRealization Tstar)) ) := by
  classical
  intro T w Tstar hreal f p hp
  rw [hreal]
  exact ⟨_, hp, rfl⟩

private theorem hrotmem :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (w : GaussianInt),
        let Tstar := TileTranslation T (-w)
        let f : Real × Real → Real × Real := fun p =>
          (p.1 - (w.re : Real), p.2 - (w.im : Real))
        (∀ (p : Real × Real), ( (TileCentroid Tstar).1 - ((f p).2 - (TileCentroid Tstar).2),
            (TileCentroid Tstar).2 + ((f p).1 - (TileCentroid Tstar).1)) = f ((TileCentroid T).1
            - (p.2 - (TileCentroid T).2), (TileCentroid T).2 + (p.1 - (TileCentroid T).1))) → (∀
            (p : ℝ × ℝ), (f ((TileCentroid T).1 - (p.2 - (TileCentroid T).2), (TileCentroid T).2
            + (p.1 - (TileCentroid T).1)) ∈ TileRealization Tstar) → (((TileCentroid Tstar).1 -
            ((f p).2 - (TileCentroid Tstar).2), (TileCentroid Tstar).2 + ((f p).1 - (TileCentroid
            Tstar).1)) ∈ TileRealization Tstar)) ) := by
  classical
  intro T w Tstar f hrotate p hps
  rw [hrotate]
  exact hps

private theorem hAneAt467 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
        let F := FordTile P.q
        ∀ (w : GaussianInt), (F.cells.Nonempty) → ((TileTranslation F w).cells.Nonempty) ) := by
  classical
  intro P F w hFcells
  rw [(TileTranslationFormulas F w).1]
  exact hFcells.image _

private theorem hBneAt470 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
        let q := FordRecursiveQuadruple P
        let F := FordTile P.q
        ∀ (w : GaussianInt), (F.cells.Nonempty) → (∀ (i : Fin (3 : ℕ)),
        let a := BandVectors.1 (q i.succ) (q 0)
        (TileTranslation (TileTranslation F a) w).cells.Nonempty) ) := by
  classical
  intro P q F w hFcells i a
  rw [(TileTranslationFormulas (TileTranslation F a) w).1,
    (TileTranslationFormulas F a).1]
  exact (hFcells.image _).image _

private theorem hCne :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter),
        let q := FordRecursiveQuadruple P
        let F := FordTile P.q
        ∀ (w : GaussianInt), (F.cells.Nonempty) → (∀ (i : Fin (3 : ℕ)),
        let b := -BandVectors.1 (q ((i + 1).succ)) (q 0)
        (TileTranslation (TileTranslation F b) w).cells.Nonempty) ) := by
  classical
  intro P q F w hFcells i b
  rw [(TileTranslationFormulas (TileTranslation F b) w).1,
    (TileTranslationFormulas F b).1]
  exact (hFcells.image _).image _

private theorem hbaseAt490 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ((1 : ℕ) < P.q) → (∀ (T : ProtoTile),
        let q := FordRecursiveQuadruple P
        let F := FordTile P.q
        ∀ (w : GaussianInt), (∀ (U : ProtoTile), TileCentroid (TileTranslation U (-w)) -
            TileCentroid F = TileCentroid U - TileCentroid T) → (∀ (i : Fin (3 : ℕ)), ∀ (U :
            ProtoTile), (TileCentroid U - TileCentroid T = (1 / 2 : ℝ) • (GaussianRealPoint
            (BandVectors.1 (FordRecursiveQuadruple P i.succ) (FordRecursiveQuadruple P (0 : Fin
            (4 : ℕ)))) + GaussianRealPoint (BandVectors.1 (FordRecursiveQuadruple P (0 : Fin (4 :
            ℕ))) (FordRecursiveQuadruple P i.succ)))) → (
        let a := BandVectors.1 (q i.succ) (q 0)
        let Ustar := TileTranslation U (-w)
        (BandPrototile (q i.succ) Ustar) → (TouchingTriple F (TileTranslation F a) Ustar)))) ) := by
  classical
  intro P hP T q F w translated_center_diff i U hcent a Ustar hUstar
  apply (FordBaseTouching P hP).2.1 i Ustar hUstar
  rw [translated_center_diff U]
  exact hcent

private theorem hbaseAt517 :
    (by
      classical
      exact
        ∀ (P : FordFareyParameter), ((1 : ℕ) < P.q) → (∀ (T : ProtoTile),
        let q := FordRecursiveQuadruple P
        let F := FordTile P.q
        ∀ (w : GaussianInt), (∀ (U : ProtoTile), TileCentroid (TileTranslation U (-w)) -
            TileCentroid F = TileCentroid U - TileCentroid T) → (∀ (i : Fin (3 : ℕ)), ∀ (U :
            ProtoTile), ∀ (V : ProtoTile), (TileCentroid U - TileCentroid T = (1 / 2 : ℝ) •
            (GaussianRealPoint (BandVectors.1 (FordRecursiveQuadruple P i.succ)
            (FordRecursiveQuadruple P (0 : Fin (4 : ℕ)))) + GaussianRealPoint (BandVectors.1
            (FordRecursiveQuadruple P (0 : Fin (4 : ℕ))) (FordRecursiveQuadruple P i.succ)))) →
            ((TileCentroid V - TileCentroid T = (1 / 2 : ℝ) • (GaussianRealPoint (BandVectors.1
            (FordRecursiveQuadruple P (i + (1 : Fin (3 : ℕ))).succ) (FordRecursiveQuadruple P (0
            : Fin (4 : ℕ)))) - GaussianRealPoint (BandVectors.1 (FordRecursiveQuadruple P (0 :
            Fin (4 : ℕ))) (FordRecursiveQuadruple P (i + (1 : Fin (3 : ℕ))).succ)))) → (
        let Ustar := TileTranslation U (-w)
        let Vstar := TileTranslation V (-w)
        (BandPrototile (q i.succ) Ustar) → ((BandPrototile (q ((i + 1).succ)) Vstar) →
            (TouchingTriple F Ustar Vstar)))))) ) := by
  classical
  intro P hP T q F w translated_center_diff i U V hUcent hVcent Ustar Vstar hUstar hVstar
  apply (FordBaseTouching P hP).2.2 i Ustar Vstar hUstar hVstar
  · rw [translated_center_diff U]
    exact hUcent
  · rw [translated_center_diff V]
    exact hVcent

end FordInterfaceGeometry

theorem P4564T2FordGeometry (P : FordFareyParameter) (hP : 1 < P.q)
    (T : ProtoTile) (hT : BandPrototile ((FordRecursiveQuadruple P) 0) T) :
    let q := FordRecursiveQuadruple P
    LatticeTile T ∧ TileArea T = Int.toNat (q 0).1 ∧
    (∀ (S : Fin 3 → Bool → ProtoTile),
      (∀ i s, BandSubtileOccurrence q T i s (S i s)) →
      (∀ x, x ∈ T.cells ↔ ∃ i s, x ∈ (S i s).cells) →
      ∀ i s, LatticeTile (TileCellComplement T (S i s)) ∧
        TileTouching (TileCellComplement T (S i s)) (S i s)) ∧
    QuarterTurnSymmetric T ∧
    (1 < (q 0).1 → ∀ i : Fin 3,
      TouchingTriple T
        (TileTranslation T (BandVectors.1 (q i.succ) (q 0)))
        (TileTranslation T
          (-BandVectors.1 (q ((i + 1).succ)) (q 0)))) ∧
    (1 < (q 0).1 → ∀ (i : Fin 3) (U : ProtoTile),
      BandPrototile (q i.succ) U →
      TileCentroid U - TileCentroid T = (1 / 2 : Real) •
        (GaussianRealPoint (BandVectors.1 (q i.succ) (q 0)) +
          GaussianRealPoint (BandVectors.1 (q 0) (q i.succ))) →
      TouchingTriple T
        (TileTranslation T (BandVectors.1 (q i.succ) (q 0))) U) ∧
    (∀ (i : Fin 3) (U V : ProtoTile),
      BandPrototile (q i.succ) U →
      BandPrototile (q ((i + 1).succ)) V →
      TileCentroid U - TileCentroid T = (1 / 2 : Real) •
        (GaussianRealPoint (BandVectors.1 (q i.succ) (q 0)) +
          GaussianRealPoint (BandVectors.1 (q 0) (q i.succ))) →
      TileCentroid V - TileCentroid T = (1 / 2 : Real) •
        (GaussianRealPoint (BandVectors.1 (q ((i + 1).succ)) (q 0)) -
          GaussianRealPoint (BandVectors.1 (q 0) (q ((i + 1).succ)))) →
      TouchingTriple T U V) := by
-- BODY
  classical
  dsimp only
  let q := FordRecursiveQuadruple P
  let F := FordTile P.q
  have hrec := FordTileRecursiveIdentification P
  have hF : BandPrototile (q 0) F := by
    simpa [q, F, FordRecursiveQuadruple] using hrec.1
  have hT' : BandPrototile (q 0) T := by
    simpa [q, FordRecursiveQuadruple] using hT
  have hcanon := hrec.2.2 hP
  rcases hcanon with ⟨hqproper, S₀, hS₀, hunion₀, _, _, _, _, _, _, _⟩
  have hnorm := BandPrototileTranslationNormalForm (q 0) T F hT' hF
  rcases hnorm with ⟨w, hcellsT, hemptyAnchor⟩
  have hFgeom := FordTileGeometry P.q P.q_pos
  have hFcells := FordInterfaceGeometry.hFcells P hP hFgeom
  let Tstar := TileTranslation T (-w)
  have hTstarCells : Tstar.cells = F.cells := FordInterfaceGeometry.hTstarCells P T w hcellsT
  have hTstarObs := ProtoTileObservableExtensionality Tstar F hTstarCells (by
    intro he
    exact (hFcells.ne_empty (hTstarCells.symm.trans he)).elim)
  have hcanT1 := FordBaseT1 P hP S₀ hS₀ hunion₀
  have hTstarTile := FordInterfaceGeometry.hTstarTile P T S₀ w hTstarObs hcanT1
  have hTtile : LatticeTile T := by
    exact (TileDiskAreaCovariance T (-w)).1.mpr hTstarTile
  have hareaStar : TileArea Tstar = TileArea F := by
    simp [TileArea, hTstarCells]
  have hareaT := FordInterfaceGeometry.hareaT P T w hareaStar
  have hFquarter : QuarterTurnSymmetric F := by
    simpa [F] using FordBaseT2 P.q P.q_pos
  have hTstarquarter := FordInterfaceGeometry.hTstarquarter P T w hTstarObs hFquarter
  have hTstarCent := FordInterfaceGeometry.hTstarCent T w
  have translated_center_diff (U : ProtoTile) := FordInterfaceGeometry.translated_center_diff P T
      w hTstarObs hTstarCent U
  have translated_cells_comm (A : ProtoTile) (a b : GaussianInt) :=
      FordInterfaceGeometry.translated_cells_comm A a b
  have translate_cancel (A : ProtoTile) :
      TileTranslation (TileTranslation A (-w)) w = A := FordInterfaceGeometry.translate_cancel w A
  have triple_same_cells (A A' B B' C : ProtoTile)
      (hAcells : A.cells = A'.cells) (hBcells : B.cells = B'.cells)
      (hAne : A.cells.Nonempty) (hBne : B.cells.Nonempty) :=
          FordInterfaceGeometry.triple_same_cells A A' B B' C hAcells hBcells hAne hBne
  have triple_same_root (A A' B C : ProtoTile)
      (hAcells : A.cells = A'.cells) (hAne : A.cells.Nonempty) :=
          FordInterfaceGeometry.triple_same_root A A' B C hAcells hAne
  have triple_same_cells_all (A A' B B' C C' : ProtoTile)
      (hAcells : A.cells = A'.cells) (hBcells : B.cells = B'.cells)
      (hCcells : C.cells = C'.cells)
      (hAne : A.cells.Nonempty) (hBne : B.cells.Nonempty)
      (hCne : C.cells.Nonempty) := FordInterfaceGeometry.triple_same_cells_all A A' B B' C C'
          hAcells hBcells hCcells hAne hBne hCne
  have translated_root_cells (v : GaussianInt) := FordInterfaceGeometry.translated_root_cells P T
      w hcellsT translated_cells_comm v
  have lattice_cells_nonempty (A : ProtoTile) (hA : LatticeTile A) :=
      FordInterfaceGeometry.lattice_cells_nonempty A hA
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hTtile
  · calc
      TileArea T = TileArea F := hareaT
      _ = Int.toNat ((q 0).1) := by
        simpa [F, q, FordRecursiveQuadruple] using hcanT1.2.1
  · intro S hS hunion
    let Sstar : Fin 3 → Bool → ProtoTile := fun i s =>
      TileTranslation (S i s) (-w)
    have hoccStar (i : Fin 3) (s : Bool) := FordInterfaceGeometry.hoccStar P T w S hS i s
    have hoccF (i : Fin 3) (s : Bool) := FordInterfaceGeometry.hoccF P T w hTstarObs S hoccStar i s
    have hunionF (x : GaussianInt) := FordInterfaceGeometry.hunionF P T w hTstarCells S hunion x
    have hbase := FordBaseT1 P hP Sstar hoccF hunionF
    intro i s
    let Cstar := TileCellComplement Tstar (Sstar i s)
    let CF := TileCellComplement F (Sstar i s)
    have hCcells : Cstar.cells = CF.cells := by
      simp [Cstar, CF, TileCellComplement, hTstarCells]
    have hCFtile := (hbase.2.2 i s).1
    have hCFne := lattice_cells_nonempty CF hCFtile
    have hCobs := FordInterfaceGeometry.hCobsAt360 P T w S i s hCcells hCFne
    have hCtile := FordInterfaceGeometry.hCtile P T w S i s hCFtile hCobs
    have hCtouch := FordInterfaceGeometry.hCtouch P T w hTstarCells S hbase i s hCcells hCFne hCobs
    have hcov := TileCellComplementCovariance T (S i s) (-w)
    have hcovEq : TileTranslation (TileCellComplement T (S i s)) (-w) = Cstar := by
      simpa [Tstar, Sstar, Cstar] using hcov.1
    have hTcomp := FordInterfaceGeometry.hTcomp T w S i s hCtile hcovEq
    have hTtouch := FordInterfaceGeometry.hTtouch T w S i s hCtouch hcovEq
    exact ⟨hTcomp, hTtouch⟩
  · have hreal : TileRealization Tstar =
        (fun p : Real × Real =>
          (p.1 - (w.re : Real), p.2 - (w.im : Real))) '' TileRealization T :=
              FordInterfaceGeometry.hreal T w
    have hcent := FordInterfaceGeometry.hTstarCent T w
    let f : Real × Real → Real × Real := fun p =>
      (p.1 - (w.re : Real), p.2 - (w.im : Real))
    have hf_inj := FordInterfaceGeometry.hf_inj w
    have hrotate (p : Real × Real) := FordInterfaceGeometry.hrotate T w hcent p
    unfold QuarterTurnSymmetric
    intro p
    constructor
    · intro hp
      have hps := FordInterfaceGeometry.hpsAt428 T w hreal p hp
      have hr := (hTstarquarter (f p)).mp hps
      rw [hreal] at hr
      rcases hr with ⟨r, hrT, hrf⟩
      have hr' : r =
          ((TileCentroid T).1 - (p.2 - (TileCentroid T).2),
            (TileCentroid T).2 + (p.1 - (TileCentroid T).1)) := FordInterfaceGeometry.hr'At434 T
                w hf_inj hrotate p r hrf
      simpa [hr'] using hrT
    · intro hp
      have hps := FordInterfaceGeometry.hpsAt443 T w hreal p hp
      have hrotmem := FordInterfaceGeometry.hrotmem T w hrotate p hps
      have hr := (hTstarquarter (f p)).mpr hrotmem
      rw [hreal] at hr
      rcases hr with ⟨r, hrT, hrf⟩
      change f r = f p at hrf
      have hr' : r = p := hf_inj hrf
      simpa [hr'] using hrT
  · intro hguard i
    let a := BandVectors.1 (q i.succ) (q 0)
    let b := -BandVectors.1 (q ((i + 1).succ)) (q 0)
    change TouchingTriple T (TileTranslation T a) (TileTranslation T b)
    have hbase : TouchingTriple F (TileTranslation F a) (TileTranslation F b) :=
      (FordBaseTouching P hP).1 i
    have hmove := (TouchingTripleCovariance F (TileTranslation F a)
      (TileTranslation F b) w).1.mp hbase
    have hAne := FordInterfaceGeometry.hAneAt467 P w hFcells
    have hBne := FordInterfaceGeometry.hBneAt470 P w hFcells i
    have hCne := FordInterfaceGeometry.hCne P w hFcells i
    exact (triple_same_cells_all
      (TileTranslation F w) T
      (TileTranslation (TileTranslation F a) w) (TileTranslation T a)
      (TileTranslation (TileTranslation F b) w) (TileTranslation T b)
      hcellsT.symm (translated_root_cells a) (translated_root_cells b)
      hAne hBne hCne).mp hmove
  · intro hguard i U hU hcent
    let a := BandVectors.1 (q i.succ) (q 0)
    let Ustar := TileTranslation U (-w)
    change TouchingTriple T (TileTranslation T a) U
    have hUstar : BandPrototile (q i.succ) Ustar :=
      BandPrototileTranslation (q i.succ) U (-w) hU
    have hbase := FordInterfaceGeometry.hbaseAt490 P hP T w translated_center_diff i U hcent hUstar
    have hmove := (TouchingTripleCovariance F (TileTranslation F a)
      Ustar w).1.mp hbase
    change TouchingTriple (TileTranslation F w)
      (TileTranslation (TileTranslation F a) w)
      (TileTranslation (TileTranslation U (-w)) w) at hmove
    rw [translate_cancel U] at hmove
    have hAne := FordInterfaceGeometry.hAneAt467 P w hFcells
    have hBne := FordInterfaceGeometry.hBneAt470 P w hFcells i
    exact (triple_same_cells (TileTranslation F w) T
      (TileTranslation (TileTranslation F a) w) (TileTranslation T a) U
      hcellsT.symm (translated_root_cells a) hAne hBne).mp hmove
  · intro i U V hU hV hUcent hVcent
    let Ustar := TileTranslation U (-w)
    let Vstar := TileTranslation V (-w)
    have hUstar : BandPrototile (q i.succ) Ustar :=
      BandPrototileTranslation (q i.succ) U (-w) hU
    have hVstar : BandPrototile (q ((i + 1).succ)) Vstar :=
      BandPrototileTranslation (q ((i + 1).succ)) V (-w) hV
    have hbase := FordInterfaceGeometry.hbaseAt517 P hP T w translated_center_diff i U V hUcent
        hVcent hUstar hVstar
    have hmove := (TouchingTripleCovariance F Ustar Vstar w).1.mp hbase
    change TouchingTriple (TileTranslation F w)
      (TileTranslation (TileTranslation U (-w)) w)
      (TileTranslation (TileTranslation V (-w)) w) at hmove
    rw [translate_cancel U, translate_cancel V] at hmove
    have hAne := FordInterfaceGeometry.hAneAt467 P w hFcells
    exact (triple_same_root (TileTranslation F w) T U V
      hcellsT.symm hAne).mp hmove

end ApollonianSuperharmonic

end
