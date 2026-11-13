/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.TileTranslationProperties
public import LeanPool.ApollonianSuperharmonic.LatticeTileNonempty

public import LeanPool.ApollonianSuperharmonic.BandPrototileTranslationNormalForm
public import LeanPool.ApollonianSuperharmonic.BandSubtileOccurrenceTranslation
public import LeanPool.ApollonianSuperharmonic.TileCellComplementCovariance
public import LeanPool.ApollonianSuperharmonic.TouchingTripleCovariance
public import LeanPool.ApollonianSuperharmonic.DiamondBaseT1
public import LeanPool.ApollonianSuperharmonic.DiamondBaseT2
public import LeanPool.ApollonianSuperharmonic.DiamondBaseTouching

-- [TABLET NODE: P4564T2DiamondGeometry]

/-!
# P4564T2DiamondGeometry

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace DiamondInterfaceGeometry

private theorem hT'cells :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (T : ProtoTile),
        let D := DiamondTile K.1
        ∀ (w : GaussianInt), (T.cells = (TileTranslation D w).cells) → (
        let T' := TileTranslation T (-w)
        T'.cells = D.cells) ) := by
  classical
  intro K T D w hwcells T'
  dsimp [T', TileTranslation]
  rw [hwcells]
  change ((D.cells.image (GaussianTranslation w)).image
    (GaussianTranslation (-w))) = D.cells
  rw [Finset.image_image]
  ext x
  simp [GaussianTranslation, add_assoc,
    add_comm]

private theorem hT'anchor :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (T : ProtoTile),
        let D := DiamondTile K.1
        ∀ (w : GaussianInt), (T.cells = ∅ → T.anchor = (TileTranslation D w).anchor) → (
        let T' := TileTranslation T (-w)
        T'.cells = ∅ → T'.anchor = D.anchor) ) := by
  classical
  intro K T D w hwanchor T' he
  have heT : T.cells = ∅ := by
    simpa [T', TileTranslation, Finset.image_eq_empty] using he
  have ha := hwanchor heT
  dsimp [T', TileTranslation]
  rw [ha]
  change (D.anchor + w) + -w = D.anchor
  abel

private theorem harea :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (T : ProtoTile),
        let q := DiamondRecursiveQuadruple K
        let D := DiamondTile K.1
        (TileArea D = Int.toNat (q 0).1) → (∀ (w : GaussianInt),
        let T' := TileTranslation T (-w)
        (T'.cells = D.cells) → (TileArea T = Int.toNat (q 0).1)) ) := by
  classical
  intro K T q D hDarea w T' hT'cells
  have htarea := (TileDiskAreaCovariance T (-w)).2.2.2.1
  calc
    TileArea T = TileArea T' := by simpa [T'] using htarea.symm
    _ = TileArea D := by
      change T'.cells.card = D.cells.card
      rw [hT'cells]
    _ = Int.toNat (q 0).1 := hDarea


private theorem touching_same_cells :
    (by
      classical
      exact
        ∀ (A : ProtoTile), ∀ (A' : ProtoTile), ∀ (B : ProtoTile), (A.cells = A'.cells) →
            ((A.cells.Nonempty) → ((BoundaryFootprintVertices A = BoundaryFootprintVertices A') →
            ((BoundaryFootprintEdges A = BoundaryFootprintEdges A') → (TileTouching A B ↔
            TileTouching A' B)))) ) := by
  classical
  intro A A' B hc hne hbv hbe
  have hne' : A'.cells.Nonempty := by rw [← hc]; exact hne
  unfold TileTouching
  have hneA : A'.cells ≠ ∅ := by
    intro he
    rw [he] at hne'
    simp at hne'
  simp [hc, hbv, hbe, hneA]

private theorem cancel_translationAt227 :
    (by
      classical
      exact
        ∀ (w : GaussianInt), ∀ (X : ProtoTile), TileTranslation (TileTranslation X (-w)) w = X )
            := by
  classical
  intro w X
  cases X with
  | mk cells anchor =>
    change ProtoTile.mk ((cells.image (GaussianTranslation (-w))).image
      (GaussianTranslation w))
      (GaussianTranslation w (GaussianTranslation (-w) anchor)) =
      ProtoTile.mk cells anchor
    congr
    · ext x
      simp [GaussianTranslation, add_comm]
    · simp [GaussianTranslation, add_comm]

private abbrev translate_comp := ApollonianSuperharmonic.TileTranslationProperties.add

private theorem touching_pair_congr :
    (by
      classical
      exact
        ∀ (A : ProtoTile), ∀ (A' : ProtoTile), ∀ (B : ProtoTile), ∀ (B' : ProtoTile), (A.cells =
            A'.cells) → ((B.cells = B'.cells) → ((A.cells.Nonempty) → ((B.cells.Nonempty) →
            ((BoundaryFootprintVertices A = BoundaryFootprintVertices A') →
            ((BoundaryFootprintVertices B = BoundaryFootprintVertices B') →
            ((BoundaryFootprintEdges A = BoundaryFootprintEdges A') → ((BoundaryFootprintEdges B
            = BoundaryFootprintEdges B') → (TileTouching A B ↔ TileTouching A' B')))))))) ) := by
  classical
  intro A A' B B' ha hb hane hbne hav hbv hae hbe
  have hane' : A'.cells.Nonempty := by rw [← ha]; exact hane
  have hbne' : B'.cells.Nonempty := by rw [← hb]; exact hbne
  have hane0 : A'.cells ≠ ∅ := by
    intro he
    rw [he] at hane'
    simp at hane'
  have hbne0 : B'.cells ≠ ∅ := by
    intro he
    rw [he] at hbne'
    simp at hbne'
  unfold TileTouching
  simp [ha, hb, hav, hbv, hae, hbe, hane0, hbne0]

private theorem translation_symmetry :
    (by
      classical
      exact
        ∀ (X : ProtoTile), ∀ (u : GaussianInt), (QuarterTurnSymmetric X) → (QuarterTurnSymmetric
            (TileTranslation X u)) ) := by
  classical
  intro X u hX p
  let a : Real := (GaussianInt.toComplex u).re
  let b : Real := (GaussianInt.toComplex u).im
  let unshift : Real × Real → Real × Real := fun z => (z.1 - a, z.2 - b)
  let rotate (c z : Real × Real) : Real × Real :=
    (c.1 - (z.2 - c.2), c.2 + (z.1 - c.1))
  have hre : (GaussianInt.toComplex u).re = (u.re : Real) :=
    (GaussianInt.intCast_re u).symm
  have him : (GaussianInt.toComplex u).im = (u.im : Real) :=
    (GaussianInt.intCast_im u).symm
  have hmem (z : Real × Real) :
      z ∈ TileRealization (TileTranslation X u) ↔
        unshift z ∈ TileRealization X := by
    rw [(TileTranslationFormulas X u).2.2.2.1]
    simp only [Set.mem_image]
    constructor
    · rintro ⟨y, hy, heq⟩
      have : y = unshift z := by
        apply Prod.ext
        · have h := congrArg Prod.fst heq
          dsimp [unshift, a] at ⊢ h
          linarith
        · have h := congrArg Prod.snd heq
          dsimp [unshift, b] at ⊢ h
          linarith
      simpa [this] using hy
    · intro hz
      refine ⟨unshift z, hz, ?_⟩
      apply Prod.ext
      · dsimp [unshift, a]
        rw [hre]
        ring
      · dsimp [unshift, b]
        rw [him]
        ring
  have hrot (z : Real × Real) :
      unshift (rotate (TileCentroid (TileTranslation X u)) z) =
        rotate (TileCentroid X) (unshift z) := by
    rw [(TileTranslationFormulas X u).2.2.2.2.1]
    apply Prod.ext <;> dsimp [unshift, rotate, a, b] <;>
      simp only [hre, him] <;> ring
  change p ∈ TileRealization (TileTranslation X u) ↔
    rotate (TileCentroid (TileTranslation X u)) p ∈
      TileRealization (TileTranslation X u)
  rw [hmem, hmem, hrot]
  exact hX (unshift p)

private theorem touching_symm :
    (by
      classical
      exact
        ∀ (A : ProtoTile), ∀ (B : ProtoTile), TileTouching A B ↔ TileTouching B A ) := by
  classical
  intro A B
  unfold TileTouching
  constructor
  · intro h
    rcases h with h | h | h
    · rcases h with ⟨ha, hb, hab, hp⟩
      exact Or.inl ⟨hb, ha, hab.symm, by simpa [Set.inter_comm] using hp⟩
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
  · intro h
    rcases h with h | h | h
    · rcases h with ⟨hb, ha, hba, hp⟩
      exact Or.inl ⟨ha, hb, hba.symm, by simpa [Set.inter_comm] using hp⟩
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)

private theorem triple_root_congr :
    (by
      classical
      exact
        (∀ (A : ProtoTile), ∀ (A' : ProtoTile), ∀ (B : ProtoTile), (A.cells = A'.cells) →
            ((A.cells.Nonempty) → ((BoundaryFootprintVertices A = BoundaryFootprintVertices A') →
            ((BoundaryFootprintEdges A = BoundaryFootprintEdges A') → (TileTouching A B ↔
            TileTouching A' B))))) → ((∀ (A : ProtoTile), ∀ (A' : ProtoTile), ∀ (B : ProtoTile),
            ∀ (B' : ProtoTile), (A.cells = A'.cells) → ((B.cells = B'.cells) →
            ((A.cells.Nonempty) → ((B.cells.Nonempty) → ((BoundaryFootprintVertices A =
            BoundaryFootprintVertices A') → ((BoundaryFootprintVertices B =
            BoundaryFootprintVertices B') → ((BoundaryFootprintEdges A = BoundaryFootprintEdges
            A') → ((BoundaryFootprintEdges B = BoundaryFootprintEdges B') → (TileTouching A B ↔
            TileTouching A' B'))))))))) → ((∀ (A : ProtoTile), ∀ (B : ProtoTile), TileTouching A
            B ↔ TileTouching B A) → (∀ (A : ProtoTile), ∀ (A' : ProtoTile), ∀ (B : ProtoTile), ∀
            (B' : ProtoTile), ∀ (C : ProtoTile), (A.cells = A'.cells) → ((B.cells = B'.cells) →
            ((A.cells.Nonempty) → ((B.cells.Nonempty) → ((BoundaryFootprintVertices A =
            BoundaryFootprintVertices A') → ((BoundaryFootprintVertices B =
            BoundaryFootprintVertices B') → ((BoundaryFootprintEdges A = BoundaryFootprintEdges
            A') → ((BoundaryFootprintEdges B = BoundaryFootprintEdges B') → (TouchingTriple A B C
            ↔ TouchingTriple A' B' C))))))))))) ) := by
  classical
  intro touching_same_cells touching_pair_congr touching_symm A A' B B' C ha hb hane hbne hav hbv
      hae hbe
  unfold TouchingTriple
  rw [touching_pair_congr A A' B B' ha hb hane hbne hav hbv hae hbe,
    touching_same_cells B B' C hb hbne hbv hbe]
  have hlast : TileTouching C A ↔ TileTouching C A' :=
    (touching_symm C A).trans
      ((touching_same_cells A A' C ha hane hav hae).trans
        (touching_symm A' C))
  rw [hlast, hav, hbv]

private theorem triple_root_one :
    (by
      classical
      exact
        (∀ (A : ProtoTile), ∀ (A' : ProtoTile), ∀ (B : ProtoTile), (A.cells = A'.cells) →
            ((A.cells.Nonempty) → ((BoundaryFootprintVertices A = BoundaryFootprintVertices A') →
            ((BoundaryFootprintEdges A = BoundaryFootprintEdges A') → (TileTouching A B ↔
            TileTouching A' B))))) → ((∀ (A : ProtoTile), ∀ (B : ProtoTile), TileTouching A B ↔
            TileTouching B A) → (∀ (A : ProtoTile), ∀ (A' : ProtoTile), ∀ (B : ProtoTile), ∀ (C :
            ProtoTile), (A.cells = A'.cells) → ((A.cells.Nonempty) → ((BoundaryFootprintVertices
            A = BoundaryFootprintVertices A') → ((BoundaryFootprintEdges A =
            BoundaryFootprintEdges A') → (TouchingTriple A B C ↔ TouchingTriple A' B C)))))) ) := by
  classical
  intro touching_same_cells touching_symm A A' B C ha hane hav hae
  unfold TouchingTriple
  rw [touching_same_cells A A' B ha hane hav hae]
  have hlast : TileTouching C A ↔ TileTouching C A' :=
    (touching_symm C A).trans
      ((touching_same_cells A A' C ha hane hav hae).trans
        (touching_symm A' C))
  rw [hlast, hav]

private theorem triple_all_congr :
    (by
      classical
      exact
        (∀ (A : ProtoTile), ∀ (A' : ProtoTile), ∀ (B : ProtoTile), ∀ (B' : ProtoTile), (A.cells =
            A'.cells) → ((B.cells = B'.cells) → ((A.cells.Nonempty) → ((B.cells.Nonempty) →
            ((BoundaryFootprintVertices A = BoundaryFootprintVertices A') →
            ((BoundaryFootprintVertices B = BoundaryFootprintVertices B') →
            ((BoundaryFootprintEdges A = BoundaryFootprintEdges A') → ((BoundaryFootprintEdges B
            = BoundaryFootprintEdges B') → (TileTouching A B ↔ TileTouching A' B'))))))))) → (∀
            (A : ProtoTile), ∀ (A' : ProtoTile), ∀ (B : ProtoTile), ∀ (B' : ProtoTile), ∀ (C :
            ProtoTile), ∀ (C' : ProtoTile), (A.cells = A'.cells) → ((B.cells = B'.cells) →
            ((C.cells = C'.cells) → ((A.cells.Nonempty) → ((B.cells.Nonempty) →
            ((C.cells.Nonempty) → ((BoundaryFootprintVertices A = BoundaryFootprintVertices A') →
            ((BoundaryFootprintVertices B = BoundaryFootprintVertices B') →
            ((BoundaryFootprintVertices C = BoundaryFootprintVertices C') →
            ((BoundaryFootprintEdges A = BoundaryFootprintEdges A') → ((BoundaryFootprintEdges B
            = BoundaryFootprintEdges B') → ((BoundaryFootprintEdges C = BoundaryFootprintEdges
            C') → (TouchingTriple A B C ↔ TouchingTriple A' B' C'))))))))))))) ) := by
  classical
  intro touching_pair_congr A A' B B' C C' ha hb hc hane hbne hcne hav hbv hcv hae hbe hce
  unfold TouchingTriple
  rw [touching_pair_congr A A' B B' ha hb hane hbne hav hbv hae hbe,
    touching_pair_congr B B' C C' hb hc hbne hcne hbv hcv hbe hce,
    touching_pair_congr C C' A A' hc ha hcne hane hcv hav hce hae,
    hav, hbv, hcv]

private theorem translation_observables :
    (by
      classical
      exact
        ∀ (A : ProtoTile), ∀ (A' : ProtoTile), ∀ (u : GaussianInt), (A.cells = A'.cells) →
            ((BoundaryFootprintVertices A = BoundaryFootprintVertices A') →
            ((BoundaryFootprintEdges A = BoundaryFootprintEdges A') → ((TileTranslation A
            u).cells = (TileTranslation A' u).cells ∧ BoundaryFootprintVertices (TileTranslation
            A u) = BoundaryFootprintVertices (TileTranslation A' u) ∧ BoundaryFootprintEdges
            (TileTranslation A u) = BoundaryFootprintEdges (TileTranslation A' u)))) ) := by
  classical
  intro A A' u hc hbv hbe
  refine ⟨?_, ?_, ?_⟩
  · rw [(TileTranslationFormulas A u).1, (TileTranslationFormulas A' u).1, hc]
  · rw [(TileTranslationFormulas A u).2.2.2.2.2.2.2.1,
      (TileTranslationFormulas A' u).2.2.2.2.2.2.2.1, hbv]
  · rw [(TileTranslationFormulas A u).2.2.2.2.2.2.2.2,
      (TileTranslationFormulas A' u).2.2.2.2.2.2.2.2, hbe]

private theorem translation_nonempty :
    (by
      classical
      exact
        ∀ (A : ProtoTile), ∀ (u : GaussianInt), (A.cells.Nonempty) → ((TileTranslation A
            u).cells.Nonempty) ) := by
  classical
  intro A u hne
  rw [(TileTranslationFormulas A u).1]
  exact hne.image _

private theorem translate_swap :
    (by
      classical
      exact
        (∀ (X : ProtoTile), ∀ (a : GaussianInt), ∀ (b : GaussianInt), TileTranslation
            (TileTranslation X a) b = TileTranslation X (a + b)) → (∀ (X : ProtoTile), ∀ (a :
            GaussianInt), ∀ (b : GaussianInt), TileTranslation (TileTranslation X a) b =
            TileTranslation (TileTranslation X b) a) ) := by
  classical
  intro translate_comp X a b
  rw [translate_comp X a b, translate_comp X b a]
  congr 1
  abel

private theorem translate_centroid_diff :
    (by
      classical
      exact
        ∀ (w : GaussianInt), ∀ (A : ProtoTile), ∀ (B : ProtoTile), TileCentroid (TileTranslation
            A (-w)) - TileCentroid (TileTranslation B (-w)) = TileCentroid A - TileCentroid B )
            := by
  classical
  intro w A B
  rw [(TileTranslationFormulas A (-w)).2.2.2.2.1,
    (TileTranslationFormulas B (-w)).2.2.2.2.1]
  apply Prod.ext <;> simp

private theorem arbitrary_family :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (T : ProtoTile),
        let q := DiamondRecursiveQuadruple K
        let D := DiamondTile K.1
        ∀ (w : GaussianInt),
        let T' := TileTranslation T (-w)
        (T'.cells = D.cells) → ((TileCentroid T' = TileCentroid D) → ((FootprintVertices T' =
            FootprintVertices D) → ((∀ (X : ProtoTile), (LatticeTile X) → (X.cells.Nonempty)) →
            ((∀ (A : ProtoTile), ∀ (A' : ProtoTile), ∀ (B : ProtoTile), (A.cells = A'.cells) →
            ((A.cells.Nonempty) → ((BoundaryFootprintVertices A = BoundaryFootprintVertices A') →
            ((BoundaryFootprintEdges A = BoundaryFootprintEdges A') → (TileTouching A B ↔
            TileTouching A' B))))) → (∀ (R : Fin 3 → Bool → ProtoTile), (∀ i, ∀ s,
            BandSubtileOccurrence q T i s (R i s)) → (∀ x, x ∈ T.cells ↔ ∃ i s, x ∈ (R i
            s).cells) → ∀ i, ∀ s, LatticeTile (TileCellComplement T (R i s)) ∧ TileTouching
            (TileCellComplement T (R i s)) (R i s)))))) ) := by
  classical
  intro K T q D w T' hT'cells hcent hfoot disk_cells_nonempty touching_same_cells R hR hRunion i s
  let R' : Fin 3 → Bool → ProtoTile := fun j b =>
    TileTranslation (R j b) (-w)
  have hRocc : ∀ j b, BandSubtileOccurrence q T' j b (R' j b) := by
    intro j b
    exact (BandSubtileOccurrenceTranslation q T (R j b) j b (-w)).mp
      (hR j b)
  have hRunion' : ∀ x, x ∈ T'.cells ↔ ∃ j b, x ∈ (R' j b).cells := by
    intro x
    change x ∈ T.cells.image (GaussianTranslation (-w)) ↔
      ∃ j b, x ∈ (R j b).cells.image (GaussianTranslation (-w))
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨y, hy, hxy⟩
      rcases (hRunion y).mp hy with ⟨j, b, hb⟩
      exact ⟨j, b, ⟨y, hb, hxy⟩⟩
    · rintro ⟨j, b, y, hy, hxy⟩
      exact ⟨y, (hRunion y).mpr ⟨j, b, hy⟩, hxy⟩
  have hRoccD : ∀ j b, BandSubtileOccurrence q D j b (R' j b) := by
    intro j b
    rcases hRocc j b with ⟨hband, hfp, hcentroid⟩
    refine ⟨hband, ?_, ?_⟩
    · rw [hfoot] at hfp
      exact hfp
    · rw [hcent] at hcentroid
      exact hcentroid
  have hRunionD : ∀ x, x ∈ D.cells ↔ ∃ j b, x ∈ (R' j b).cells := by
    intro x
    rw [← hT'cells]
    exact hRunion' x
  have hRbase := DiamondBaseT1 K R' hRoccD hRunionD
  have hDcompCells :
      (TileCellComplement D (R' i s)).cells =
        (TileCellComplement T' (R' i s)).cells := by
    simp only [TileCellComplement]
    rw [hT'cells]
  have hDcompDisk : LatticeTile (TileCellComplement D (R' i s)) :=
    (hRbase.2.2 i s).1
  have hDcompNe := disk_cells_nonempty _ hDcompDisk
  have hcompObs := ProtoTileObservableExtensionality
    (TileCellComplement D (R' i s)) (TileCellComplement T' (R' i s))
    hDcompCells (by
      intro he
      have hnot : ¬ (TileCellComplement D (R' i s)).cells.Nonempty := by
        rw [he]
        simp
      exact False.elim (hnot hDcompNe))
  have hTcompDisk : LatticeTile (TileCellComplement T' (R' i s)) := by
    change TopologicalDisk
      (TileRealization (TileCellComplement T' (R' i s)))
    change TopologicalDisk
      (TileRealization (TileCellComplement D (R' i s))) at hDcompDisk
    rw [hcompObs.2.2.2.1] at hDcompDisk
    exact hDcompDisk
  have hTcompNe : (TileCellComplement T' (R' i s)).cells.Nonempty := by
    rw [← hDcompCells]
    exact hDcompNe
  have hTcompTouch :
      TileTouching (TileCellComplement T' (R' i s)) (R' i s) := by
    exact (touching_same_cells _ _ _ hDcompCells hDcompNe
      hcompObs.2.1 hcompObs.2.2.1).mp (hRbase.2.2 i s).2
  have cancel_translation (X : ProtoTile) :
      TileTranslation (TileTranslation X (-w)) w = X := by
    cases X with
    | mk cells anchor =>
      change ProtoTile.mk ((cells.image (GaussianTranslation (-w))).image
        (GaussianTranslation w))
        (GaussianTranslation w (GaussianTranslation (-w) anchor)) =
        ProtoTile.mk cells anchor
      congr
      · ext x
        simp [GaussianTranslation, add_comm]
      · simp [GaussianTranslation, add_comm]
  have hbackDisk : LatticeTile (TileCellComplement T (R i s)) := by
    have hcov := (TileCellComplementCovariance T' (R' i s) w).1
    have htranslated :=
      (TileDiskAreaCovariance (TileCellComplement T' (R' i s)) w).1.mp
        hTcompDisk
    rw [hcov, cancel_translation T, cancel_translation (R i s)] at htranslated
    exact htranslated
  have hbackTouch :
      TileTouching (TileCellComplement T (R i s)) (R i s) := by
    have hcov := (TileCellComplementCovariance T' (R' i s) w).1
    have htranslated :=
      (TileTouchingCovariance (TileCellComplement T' (R' i s))
        (R' i s) w).1.mp hTcompTouch
    rw [hcov, cancel_translation T, cancel_translation (R i s)] at htranslated
    exact htranslated
  exact ⟨hbackDisk, hbackTouch⟩

private theorem hdisk' :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (T : ProtoTile),
        let D := DiamondTile K.1
        (LatticeTile D) → (∀ (w : GaussianInt),
        let T' := TileTranslation T (-w)
        (TileRealization T' = TileRealization D) → (LatticeTile T')) ) := by
  classical
  intro K T D hDdisk w T' hreal
  change TopologicalDisk (TileRealization T')
  change TopologicalDisk (TileRealization D) at hDdisk
  rw [← hreal] at hDdisk
  exact hDdisk

private theorem hsym' :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (T : ProtoTile),
        let D := DiamondTile K.1
        ∀ (w : GaussianInt),
        let T' := TileTranslation T (-w)
        (TileRealization T' = TileRealization D) → ((TileCentroid T' = TileCentroid D) →
            ((QuarterTurnSymmetric D) → (QuarterTurnSymmetric T'))) ) := by
  classical
  intro K T D w T' hreal hcent hsymD p
  simpa [QuarterTurnSymmetric, hreal, hcent] using hsymD p

private theorem htriple'At530 :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (T : ProtoTile),
        let q := DiamondRecursiveQuadruple K
        let D := DiamondTile K.1
        ∀ (w : GaussianInt),
        let T' := TileTranslation T (-w)
        (T'.cells = D.cells) → ((BoundaryFootprintVertices T' = BoundaryFootprintVertices D) →
            ((BoundaryFootprintEdges T' = BoundaryFootprintEdges D) → ((∀ (A : ProtoTile), ∀ (A'
            : ProtoTile), ∀ (B : ProtoTile), ∀ (B' : ProtoTile), ∀ (C : ProtoTile), ∀ (C' :
            ProtoTile), (A.cells = A'.cells) → ((B.cells = B'.cells) → ((C.cells = C'.cells) →
            ((A.cells.Nonempty) → ((B.cells.Nonempty) → ((C.cells.Nonempty) →
            ((BoundaryFootprintVertices A = BoundaryFootprintVertices A') →
            ((BoundaryFootprintVertices B = BoundaryFootprintVertices B') →
            ((BoundaryFootprintVertices C = BoundaryFootprintVertices C') →
            ((BoundaryFootprintEdges A = BoundaryFootprintEdges A') → ((BoundaryFootprintEdges B
            = BoundaryFootprintEdges B') → ((BoundaryFootprintEdges C = BoundaryFootprintEdges
            C') → (TouchingTriple A B C ↔ TouchingTriple A' B' C'))))))))))))) → ((∀ (A :
            ProtoTile), ∀ (u : GaussianInt), (A.cells.Nonempty) → ((TileTranslation A
            u).cells.Nonempty)) → (∀ (i : Fin (3 : ℕ)), (
        let q := DiamondRecursiveQuadruple K;
        let T := DiamondTile K.1; (∀ (i : Fin (3 : ℕ)), TouchingTriple T (TileTranslation T
            (BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ))))) (TileTranslation T (-BandVectors.1
            (q (i + (1 : Fin (3 : ℕ))).succ) (q (0 : Fin (4 : ℕ)))))) ∧ (∀ (i : Fin (3 : ℕ)), ∀
            (U : ProtoTile), BandPrototile (q i.succ) U → TileCentroid U - TileCentroid T = (1 /
            2 : ℝ) • (GaussianRealPoint (BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ)))) +
            GaussianRealPoint (BandVectors.1 (q (0 : Fin (4 : ℕ))) (q i.succ))) → TouchingTriple
            T (TileTranslation T (BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ))))) U) ∧ ∀ (i :
            Fin (3 : ℕ)), ∀ (U : ProtoTile), ∀ (V : ProtoTile), BandPrototile (q i.succ) U →
            BandPrototile (q (i + (1 : Fin (3 : ℕ))).succ) V → TileCentroid U - TileCentroid T =
            (1 / 2 : ℝ) • (GaussianRealPoint (BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ)))) +
            GaussianRealPoint (BandVectors.1 (q (0 : Fin (4 : ℕ))) (q i.succ))) → TileCentroid V
            - TileCentroid T = (1 / 2 : ℝ) • (GaussianRealPoint (BandVectors.1 (q (i + (1 : Fin
            (3 : ℕ))).succ) (q (0 : Fin (4 : ℕ)))) - GaussianRealPoint (BandVectors.1 (q (0 : Fin
            (4 : ℕ))) (q (i + (1 : Fin (3 : ℕ))).succ))) → TouchingTriple T U V) →
            ((Finset.Nonempty D.cells) → (
        let v := BandVectors.1 (q i.succ) (q 0)
        let z := -BandVectors.1 (q ((i + 1).succ)) (q 0)
        ((TileTranslation D v).cells = (TileTranslation T' v).cells ∧ BoundaryFootprintVertices
            (TileTranslation D v) = BoundaryFootprintVertices (TileTranslation T' v) ∧
            BoundaryFootprintEdges (TileTranslation D v) = BoundaryFootprintEdges
            (TileTranslation T' v)) → (((TileTranslation D z).cells = (TileTranslation T'
            z).cells ∧ BoundaryFootprintVertices (TileTranslation D z) =
            BoundaryFootprintVertices (TileTranslation T' z) ∧ BoundaryFootprintEdges
            (TileTranslation D z) = BoundaryFootprintEdges (TileTranslation T' z)) →
            (TouchingTriple T' (TileTranslation T' v) (TileTranslation T' z)))))))))) ) := by
  classical
  intro K T q D w T' hT'cells hbdv hbde triple_all_congr translation_nonempty i hbaseTouch hDne v
      z hobsV hobsZ
  apply (triple_all_congr D T' (TileTranslation D v)
    (TileTranslation T' v) (TileTranslation D z)
    (TileTranslation T' z) hT'cells.symm hobsV.1 hobsZ.1 hDne
    (translation_nonempty D v hDne) (translation_nonempty D z hDne)
    hbdv.symm hobsV.2.1 hobsZ.2.1 hbde.symm hobsV.2.2 hobsZ.2.2).mp
  exact hbaseTouch.1 i

private theorem hperiodVAt540 :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (T : ProtoTile),
        let q := DiamondRecursiveQuadruple K
        ∀ (w : GaussianInt),
        let T' := TileTranslation T (-w)
        (∀ (X : ProtoTile), ∀ (a : GaussianInt), ∀ (b : GaussianInt), TileTranslation
            (TileTranslation X a) b = TileTranslation (TileTranslation X b) a) →
            ((TileTranslation T' w = T) → (∀ (i : Fin (3 : ℕ)),
        let v := BandVectors.1 (q i.succ) (q 0)
        TileTranslation (TileTranslation T' v) w = TileTranslation T v)) ) := by
  classical
  intro K T q w T' translate_swap hTrestore i v
  rw [← hTrestore]
  exact translate_swap T' v w

private theorem hperiodZ :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (T : ProtoTile),
        let q := DiamondRecursiveQuadruple K
        ∀ (w : GaussianInt),
        let T' := TileTranslation T (-w)
        (∀ (X : ProtoTile), ∀ (a : GaussianInt), ∀ (b : GaussianInt), TileTranslation
            (TileTranslation X a) b = TileTranslation (TileTranslation X b) a) →
            ((TileTranslation T' w = T) → (∀ (i : Fin (3 : ℕ)),
        let z := -BandVectors.1 (q ((i + 1).succ)) (q 0)
        TileTranslation (TileTranslation T' z) w = TileTranslation T z)) ) := by
  classical
  intro K T q w T' translate_swap hTrestore i z
  rw [← hTrestore]
  exact translate_swap T' z w

private theorem hcenter' :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (T : ProtoTile),
        let q := DiamondRecursiveQuadruple K
        let D := DiamondTile K.1
        ∀ (w : GaussianInt),
        let T' := TileTranslation T (-w)
        (TileCentroid T' = TileCentroid D) → ((∀ (A : ProtoTile), ∀ (B : ProtoTile), TileCentroid
            (TileTranslation A (-w)) - TileCentroid (TileTranslation B (-w)) = TileCentroid A -
            TileCentroid B) → (∀ (i : Fin (3 : ℕ)), ∀ (U : ProtoTile), (TileCentroid U -
            TileCentroid T = (1 / 2 : ℝ) • (GaussianRealPoint (BandVectors.1
            (DiamondRecursiveQuadruple K i.succ) (DiamondRecursiveQuadruple K (0 : Fin (4 : ℕ))))
            + GaussianRealPoint (BandVectors.1 (DiamondRecursiveQuadruple K (0 : Fin (4 : ℕ)))
            (DiamondRecursiveQuadruple K i.succ)))) → (
        let U' := TileTranslation U (-w)
        TileCentroid U' - TileCentroid D = (1 / 2 : Real) • (GaussianRealPoint (BandVectors.1 (q
            i.succ) (q 0)) + GaussianRealPoint (BandVectors.1 (q 0) (q i.succ)))))) ) := by
  classical
  intro K T q D w T' hcent translate_centroid_diff i U hcenter U'
  calc
    TileCentroid U' - TileCentroid D =
        TileCentroid U' - TileCentroid T' := by rw [hcent]
    _ = TileCentroid U - TileCentroid T := translate_centroid_diff U T
    _ = _ := hcenter

private theorem htriple'At567 :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (T : ProtoTile),
        let q := DiamondRecursiveQuadruple K
        let D := DiamondTile K.1
        ∀ (w : GaussianInt),
        let T' := TileTranslation T (-w)
        (T'.cells = D.cells) → ((BoundaryFootprintVertices T' = BoundaryFootprintVertices D) →
            ((BoundaryFootprintEdges T' = BoundaryFootprintEdges D) → ((∀ (A : ProtoTile), ∀ (A'
            : ProtoTile), ∀ (B : ProtoTile), ∀ (B' : ProtoTile), ∀ (C : ProtoTile), (A.cells =
            A'.cells) → ((B.cells = B'.cells) → ((A.cells.Nonempty) → ((B.cells.Nonempty) →
            ((BoundaryFootprintVertices A = BoundaryFootprintVertices A') →
            ((BoundaryFootprintVertices B = BoundaryFootprintVertices B') →
            ((BoundaryFootprintEdges A = BoundaryFootprintEdges A') → ((BoundaryFootprintEdges B
            = BoundaryFootprintEdges B') → (TouchingTriple A B C ↔ TouchingTriple A' B'
            C))))))))) → ((∀ (A : ProtoTile), ∀ (u : GaussianInt), (A.cells.Nonempty) →
            ((TileTranslation A u).cells.Nonempty)) → (∀ (i : Fin (3 : ℕ)), ∀ (U : ProtoTile), (
        let q := DiamondRecursiveQuadruple K;
        let T := DiamondTile K.1; (∀ (i : Fin (3 : ℕ)), TouchingTriple T (TileTranslation T
            (BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ))))) (TileTranslation T (-BandVectors.1
            (q (i + (1 : Fin (3 : ℕ))).succ) (q (0 : Fin (4 : ℕ)))))) ∧ (∀ (i : Fin (3 : ℕ)), ∀
            (U : ProtoTile), BandPrototile (q i.succ) U → TileCentroid U - TileCentroid T = (1 /
            2 : ℝ) • (GaussianRealPoint (BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ)))) +
            GaussianRealPoint (BandVectors.1 (q (0 : Fin (4 : ℕ))) (q i.succ))) → TouchingTriple
            T (TileTranslation T (BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ))))) U) ∧ ∀ (i :
            Fin (3 : ℕ)), ∀ (U : ProtoTile), ∀ (V : ProtoTile), BandPrototile (q i.succ) U →
            BandPrototile (q (i + (1 : Fin (3 : ℕ))).succ) V → TileCentroid U - TileCentroid T =
            (1 / 2 : ℝ) • (GaussianRealPoint (BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ)))) +
            GaussianRealPoint (BandVectors.1 (q (0 : Fin (4 : ℕ))) (q i.succ))) → TileCentroid V
            - TileCentroid T = (1 / 2 : ℝ) • (GaussianRealPoint (BandVectors.1 (q (i + (1 : Fin
            (3 : ℕ))).succ) (q (0 : Fin (4 : ℕ)))) - GaussianRealPoint (BandVectors.1 (q (0 : Fin
            (4 : ℕ))) (q (i + (1 : Fin (3 : ℕ))).succ))) → TouchingTriple T U V) → (
        let v := BandVectors.1 (q i.succ) (q 0)
        let U' := TileTranslation U (-w)
        (BandPrototile (q i.succ) U') → ((TileCentroid U' - TileCentroid D = (1 / 2 : Real) •
            (GaussianRealPoint (BandVectors.1 (q i.succ) (q 0)) + GaussianRealPoint
            (BandVectors.1 (q 0) (q i.succ)))) → (((TileTranslation D v).cells = (TileTranslation
            T' v).cells ∧ BoundaryFootprintVertices (TileTranslation D v) =
            BoundaryFootprintVertices (TileTranslation T' v) ∧ BoundaryFootprintEdges
            (TileTranslation D v) = BoundaryFootprintEdges (TileTranslation T' v)) →
            ((Finset.Nonempty D.cells) → (TouchingTriple T' (TileTranslation T' v) U')))))))))) )
            := by
  classical
  intro K T q D w T' hT'cells hbdv hbde triple_root_congr translation_nonempty i U hbaseTouch v
      U' hU'band hcenter' hobsV hDne
  apply (triple_root_congr D T' (TileTranslation D v)
    (TileTranslation T' v) U' hT'cells.symm hobsV.1 hDne
    (translation_nonempty D v hDne) hbdv.symm hobsV.2.1 hbde.symm
    hobsV.2.2).mp
  exact hbaseTouch.2.1 i U' hU'band hcenter'

private abbrev hcenterU' :=
  ApollonianSuperharmonic.DiamondInterfaceGeometry.hcenter'

private theorem hcenterV' :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (T : ProtoTile),
        let q := DiamondRecursiveQuadruple K
        let D := DiamondTile K.1
        ∀ (w : GaussianInt),
        let T' := TileTranslation T (-w)
        (TileCentroid T' = TileCentroid D) → ((∀ (A : ProtoTile), ∀ (B : ProtoTile), TileCentroid
            (TileTranslation A (-w)) - TileCentroid (TileTranslation B (-w)) = TileCentroid A -
            TileCentroid B) → (∀ (i : Fin (3 : ℕ)), ∀ (V : ProtoTile), (TileCentroid V -
            TileCentroid T = (1 / 2 : ℝ) • (GaussianRealPoint (BandVectors.1
            (DiamondRecursiveQuadruple K (i + (1 : Fin (3 : ℕ))).succ) (DiamondRecursiveQuadruple
            K (0 : Fin (4 : ℕ)))) - GaussianRealPoint (BandVectors.1 (DiamondRecursiveQuadruple K
            (0 : Fin (4 : ℕ))) (DiamondRecursiveQuadruple K (i + (1 : Fin (3 : ℕ))).succ)))) → (
        let V' := TileTranslation V (-w)
        TileCentroid V' - TileCentroid D = (1 / 2 : Real) • (GaussianRealPoint (BandVectors.1 (q
            ((i + 1).succ)) (q 0)) - GaussianRealPoint (BandVectors.1 (q 0) (q ((i +
            1).succ))))))) ) := by
  classical
  intro K T q D w T' hcent translate_centroid_diff i V hcenterV V'
  calc
    TileCentroid V' - TileCentroid D =
        TileCentroid V' - TileCentroid T' := by rw [hcent]
    _ = TileCentroid V - TileCentroid T := translate_centroid_diff V T
    _ = _ := hcenterV

private theorem htriple'At612 :
    (by
      classical
      exact
        ∀ (K : DiamondParameter), ∀ (T : ProtoTile),
        let q := DiamondRecursiveQuadruple K
        let D := DiamondTile K.1
        ∀ (w : GaussianInt),
        let T' := TileTranslation T (-w)
        (T'.cells = D.cells) → ((BoundaryFootprintVertices T' = BoundaryFootprintVertices D) →
            ((BoundaryFootprintEdges T' = BoundaryFootprintEdges D) → ((∀ (A : ProtoTile), ∀ (A'
            : ProtoTile), ∀ (B : ProtoTile), ∀ (C : ProtoTile), (A.cells = A'.cells) →
            ((A.cells.Nonempty) → ((BoundaryFootprintVertices A = BoundaryFootprintVertices A') →
            ((BoundaryFootprintEdges A = BoundaryFootprintEdges A') → (TouchingTriple A B C ↔
            TouchingTriple A' B C))))) → (∀ (i : Fin (3 : ℕ)), ∀ (U : ProtoTile), ∀ (V :
            ProtoTile), (
        let q := DiamondRecursiveQuadruple K;
        let T := DiamondTile K.1; (∀ (i : Fin (3 : ℕ)), TouchingTriple T (TileTranslation T
            (BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ))))) (TileTranslation T (-BandVectors.1
            (q (i + (1 : Fin (3 : ℕ))).succ) (q (0 : Fin (4 : ℕ)))))) ∧ (∀ (i : Fin (3 : ℕ)), ∀
            (U : ProtoTile), BandPrototile (q i.succ) U → TileCentroid U - TileCentroid T = (1 /
            2 : ℝ) • (GaussianRealPoint (BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ)))) +
            GaussianRealPoint (BandVectors.1 (q (0 : Fin (4 : ℕ))) (q i.succ))) → TouchingTriple
            T (TileTranslation T (BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ))))) U) ∧ ∀ (i :
            Fin (3 : ℕ)), ∀ (U : ProtoTile), ∀ (V : ProtoTile), BandPrototile (q i.succ) U →
            BandPrototile (q (i + (1 : Fin (3 : ℕ))).succ) V → TileCentroid U - TileCentroid T =
            (1 / 2 : ℝ) • (GaussianRealPoint (BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ)))) +
            GaussianRealPoint (BandVectors.1 (q (0 : Fin (4 : ℕ))) (q i.succ))) → TileCentroid V
            - TileCentroid T = (1 / 2 : ℝ) • (GaussianRealPoint (BandVectors.1 (q (i + (1 : Fin
            (3 : ℕ))).succ) (q (0 : Fin (4 : ℕ)))) - GaussianRealPoint (BandVectors.1 (q (0 : Fin
            (4 : ℕ))) (q (i + (1 : Fin (3 : ℕ))).succ))) → TouchingTriple T U V) → (
        let U' := TileTranslation U (-w)
        let V' := TileTranslation V (-w)
        (BandPrototile (q i.succ) U') → ((BandPrototile (q ((i + 1).succ)) V') → ((TileCentroid
            U' - TileCentroid D = (1 / 2 : Real) • (GaussianRealPoint (BandVectors.1 (q i.succ)
            (q 0)) + GaussianRealPoint (BandVectors.1 (q 0) (q i.succ)))) → ((TileCentroid V' -
            TileCentroid D = (1 / 2 : Real) • (GaussianRealPoint (BandVectors.1 (q ((i +
            1).succ)) (q 0)) - GaussianRealPoint (BandVectors.1 (q 0) (q ((i + 1).succ))))) →
            ((Finset.Nonempty D.cells) → (TouchingTriple T' U' V')))))))))) ) := by
  classical
  intro K T q D w T' hT'cells hbdv hbde triple_root_one i U V hbaseTouch U' V' hU'band hV'band
      hcenterU' hcenterV' hDne
  apply (triple_root_one D T' U' V' hT'cells.symm hDne
    hbdv.symm hbde.symm).mp
  exact hbaseTouch.2.2 i U' V' hU'band hV'band hcenterU' hcenterV'

end DiamondInterfaceGeometry

theorem P4564T2DiamondGeometry :
    ∀ (K : DiamondParameter), (1 < K.1) → (∀ (T : ProtoTile), (BandPrototile
        ((DiamondRecursiveQuadruple K) 0) T) → (
    let q := DiamondRecursiveQuadruple K
    LatticeTile T ∧ TileArea T = Int.toNat (q 0).1 ∧
    (∀ (S : Fin 3 → Bool → ProtoTile), (∀ i, ∀ s, BandSubtileOccurrence q T i s (S i s)) →
      (∀ x, x ∈ T.cells ↔ ∃ i s, x ∈ (S i s).cells) →
      ∀ i, ∀ s, LatticeTile (TileCellComplement T (S i s)) ∧
        TileTouching (TileCellComplement T (S i s)) (S i s)) ∧
    QuarterTurnSymmetric T ∧
    (1 < (q 0).1 → ∀ i : Fin 3,
      TouchingTriple T
        (TileTranslation T (BandVectors.1 (q i.succ) (q 0)))
        (TileTranslation T
          (-BandVectors.1 (q ((i + 1).succ)) (q 0)))) ∧
    (1 < (q 0).1 → ∀ (i : Fin 3), ∀ (U : ProtoTile), BandPrototile (q i.succ) U →
      TileCentroid U - TileCentroid T = (1 / 2 : Real) •
        (GaussianRealPoint (BandVectors.1 (q i.succ) (q 0)) +
          GaussianRealPoint (BandVectors.1 (q 0) (q i.succ))) →
      TouchingTriple T
        (TileTranslation T (BandVectors.1 (q i.succ) (q 0))) U) ∧
    (∀ (i : Fin 3), ∀ (U : ProtoTile), ∀ (V : ProtoTile), BandPrototile (q i.succ) U →
      BandPrototile (q ((i + 1).succ)) V →
      TileCentroid U - TileCentroid T = (1 / 2 : Real) •
        (GaussianRealPoint (BandVectors.1 (q i.succ) (q 0)) +
          GaussianRealPoint (BandVectors.1 (q 0) (q i.succ))) →
      TileCentroid V - TileCentroid T = (1 / 2 : Real) •
        (GaussianRealPoint (BandVectors.1 (q ((i + 1).succ)) (q 0)) -
          GaussianRealPoint (BandVectors.1 (q 0) (q ((i + 1).succ)))) →
      TouchingTriple T U V))) := by
  intro K hK T hT
-- BODY
  classical
  dsimp
  let q := DiamondRecursiveQuadruple K
  let D := DiamondTile K.1
  have hrec := DiamondTileRecursiveIdentification K
  rcases hrec with ⟨hD, S₀, hS₀, hUnion₀, _, _, _, _, _, _⟩
  have hbase₀ := DiamondBaseT1 K S₀ hS₀ hUnion₀
  have hDarea : TileArea D = Int.toNat (q 0).1 := hbase₀.2.1
  have hDdisk : LatticeTile D := hbase₀.1
  have hnorm := BandPrototileTranslationNormalForm (q 0) T D hT hD
  rcases hnorm with ⟨w, hwcells, hwanchor⟩
  let T' := TileTranslation T (-w)
  have hT'cells := DiamondInterfaceGeometry.hT'cells K T w hwcells
  have hT'anchor := DiamondInterfaceGeometry.hT'anchor K T w hwanchor
  have hobs := ProtoTileObservableExtensionality T' D hT'cells hT'anchor
  have hreal : TileRealization T' = TileRealization D := hobs.2.2.2.1
  have hcent : TileCentroid T' = TileCentroid D := hobs.2.2.2.2
  have hfoot : FootprintVertices T' = FootprintVertices D := hobs.1
  have hbdv : BoundaryFootprintVertices T' = BoundaryFootprintVertices D :=
    hobs.2.1
  have hbde : BoundaryFootprintEdges T' = BoundaryFootprintEdges D :=
    hobs.2.2.1
  have harea := DiamondInterfaceGeometry.harea K T hDarea w hT'cells
  have disk_cells_nonempty (X : ProtoTile) (hX : LatticeTile X) :=
      LatticeTileNonempty.cells X hX
  have touching_same_cells (A A' B : ProtoTile)
      (hc : A.cells = A'.cells) (hne : A.cells.Nonempty)
      (hbv : BoundaryFootprintVertices A = BoundaryFootprintVertices A')
      (hbe : BoundaryFootprintEdges A = BoundaryFootprintEdges A') :=
          DiamondInterfaceGeometry.touching_same_cells A A' B hc hne hbv hbe
  have cancel_translation (X : ProtoTile) :
      TileTranslation (TileTranslation X (-w)) w = X :=
          DiamondInterfaceGeometry.cancel_translationAt227 w X
  have translate_comp (X : ProtoTile) (a b : GaussianInt) :=
      DiamondInterfaceGeometry.translate_comp X a b
  have touching_pair_congr (A A' B B' : ProtoTile)
      (ha : A.cells = A'.cells) (hb : B.cells = B'.cells)
      (hane : A.cells.Nonempty) (hbne : B.cells.Nonempty)
      (hav : BoundaryFootprintVertices A = BoundaryFootprintVertices A')
      (hbv : BoundaryFootprintVertices B = BoundaryFootprintVertices B')
      (hae : BoundaryFootprintEdges A = BoundaryFootprintEdges A')
      (hbe : BoundaryFootprintEdges B = BoundaryFootprintEdges B') :=
          DiamondInterfaceGeometry.touching_pair_congr A A' B B' ha hb hane hbne hav hbv hae hbe
  have translation_symmetry (X : ProtoTile) (u : GaussianInt)
      (hX : QuarterTurnSymmetric X) := DiamondInterfaceGeometry.translation_symmetry X u hX
  have touching_symm (A B : ProtoTile) := DiamondInterfaceGeometry.touching_symm A B
  have triple_root_congr (A A' B B' C : ProtoTile)
      (ha : A.cells = A'.cells) (hb : B.cells = B'.cells)
      (hane : A.cells.Nonempty) (hbne : B.cells.Nonempty)
      (hav : BoundaryFootprintVertices A = BoundaryFootprintVertices A')
      (hbv : BoundaryFootprintVertices B = BoundaryFootprintVertices B')
      (hae : BoundaryFootprintEdges A = BoundaryFootprintEdges A')
      (hbe : BoundaryFootprintEdges B = BoundaryFootprintEdges B') :=
          DiamondInterfaceGeometry.triple_root_congr touching_same_cells touching_pair_congr
          touching_symm A A' B B' C ha hb hane hbne hav hbv hae hbe
  have triple_root_one (A A' B C : ProtoTile)
      (ha : A.cells = A'.cells) (hane : A.cells.Nonempty)
      (hav : BoundaryFootprintVertices A = BoundaryFootprintVertices A')
      (hae : BoundaryFootprintEdges A = BoundaryFootprintEdges A') :=
          DiamondInterfaceGeometry.triple_root_one touching_same_cells touching_symm A A' B C ha
          hane hav hae
  have triple_all_congr (A A' B B' C C' : ProtoTile)
      (ha : A.cells = A'.cells) (hb : B.cells = B'.cells)
      (hc : C.cells = C'.cells)
      (hane : A.cells.Nonempty) (hbne : B.cells.Nonempty)
      (hcne : C.cells.Nonempty)
      (hav : BoundaryFootprintVertices A = BoundaryFootprintVertices A')
      (hbv : BoundaryFootprintVertices B = BoundaryFootprintVertices B')
      (hcv : BoundaryFootprintVertices C = BoundaryFootprintVertices C')
      (hae : BoundaryFootprintEdges A = BoundaryFootprintEdges A')
      (hbe : BoundaryFootprintEdges B = BoundaryFootprintEdges B')
      (hce : BoundaryFootprintEdges C = BoundaryFootprintEdges C') :=
          DiamondInterfaceGeometry.triple_all_congr touching_pair_congr A A' B B' C C' ha hb hc
          hane hbne hcne hav hbv hcv hae hbe hce
  have translation_observables (A A' : ProtoTile) (u : GaussianInt)
      (hc : A.cells = A'.cells)
      (hbv : BoundaryFootprintVertices A = BoundaryFootprintVertices A')
      (hbe : BoundaryFootprintEdges A = BoundaryFootprintEdges A') :=
          DiamondInterfaceGeometry.translation_observables A A' u hc hbv hbe
  have translation_nonempty (A : ProtoTile) (u : GaussianInt)
      (hne : A.cells.Nonempty) := DiamondInterfaceGeometry.translation_nonempty A u hne
  have translate_swap (X : ProtoTile) (a b : GaussianInt) :=
      DiamondInterfaceGeometry.translate_swap translate_comp X a b
  have translate_centroid_diff (A B : ProtoTile) :=
      DiamondInterfaceGeometry.translate_centroid_diff w A B
  have hTrestore : TileTranslation T' w = T := by
    simpa [T'] using cancel_translation T
  have arbitrary_family := DiamondInterfaceGeometry.arbitrary_family K T w hT'cells hcent hfoot
      disk_cells_nonempty touching_same_cells
  refine ⟨?_, harea, ?_, ?_, ?_, ?_, ?_⟩
  · have hdisk' := DiamondInterfaceGeometry.hdisk' K T hDdisk w hreal
    exact (TileDiskAreaCovariance T (-w)).1.mpr hdisk'
  · intro R hR hRunion i s
    exact (arbitrary_family R hR hRunion i s)
  · have hsymD : QuarterTurnSymmetric D := DiamondBaseT2 K
    have hsym' := DiamondInterfaceGeometry.hsym' K T w hreal hcent hsymD
    have hsymT := translation_symmetry T' w hsym'
    rw [hTrestore] at hsymT
    exact hsymT
  · intro hc i
    have hbaseTouch := DiamondBaseTouching K
    have hDne := disk_cells_nonempty D hDdisk
    let v := BandVectors.1 (q i.succ) (q 0)
    let z := -BandVectors.1 (q ((i + 1).succ)) (q 0)
    have hobsV := translation_observables D T' v hT'cells.symm hbdv.symm hbde.symm
    have hobsZ := translation_observables D T' z hT'cells.symm hbdv.symm hbde.symm
    have htriple' := DiamondInterfaceGeometry.htriple'At530 K T w hT'cells hbdv hbde
        triple_all_congr translation_nonempty i hbaseTouch hDne hobsV hobsZ
    have htripleW := (TouchingTripleCovariance T'
      (TileTranslation T' v) (TileTranslation T' z) w).1.mp htriple'
    have hperiodV : TileTranslation (TileTranslation T' v) w =
        TileTranslation T v := DiamondInterfaceGeometry.hperiodVAt540 K T w translate_swap
            hTrestore i
    have hperiodZ : TileTranslation (TileTranslation T' z) w =
        TileTranslation T z := DiamondInterfaceGeometry.hperiodZ K T w translate_swap hTrestore i
    rw [hTrestore, hperiodV, hperiodZ] at htripleW
    exact htripleW
  · intro hc i U hU hcenter
    have hbaseTouch := DiamondBaseTouching K
    let v := BandVectors.1 (q i.succ) (q 0)
    let U' := TileTranslation U (-w)
    have hU'band : BandPrototile (q i.succ) U' :=
      BandPrototileTranslation (q i.succ) U (-w) hU
    have hcenter' := DiamondInterfaceGeometry.hcenter' K T w hcent translate_centroid_diff i U
        hcenter
    have hobsV := translation_observables D T' v hT'cells.symm hbdv.symm hbde.symm
    have hDne := disk_cells_nonempty D hDdisk
    have htriple' := DiamondInterfaceGeometry.htriple'At567 K T w hT'cells hbdv hbde
        triple_root_congr translation_nonempty i U hbaseTouch hU'band hcenter' hobsV hDne
    have htripleW := (TouchingTripleCovariance T'
      (TileTranslation T' v) U' w).1.mp htriple'
    have hperiodV : TileTranslation (TileTranslation T' v) w =
        TileTranslation T v := DiamondInterfaceGeometry.hperiodVAt540 K T w translate_swap
            hTrestore i
    have hUrestore : TileTranslation U' w = U := by
      simpa [U'] using cancel_translation U
    rw [hTrestore, hperiodV, hUrestore] at htripleW
    exact htripleW
  · intro i U V hU hV hcenterU hcenterV
    have hbaseTouch := DiamondBaseTouching K
    let v := BandVectors.1 (q i.succ) (q 0)
    let z := BandVectors.1 (q ((i + 1).succ)) (q 0)
    let U' := TileTranslation U (-w)
    let V' := TileTranslation V (-w)
    have hU'band : BandPrototile (q i.succ) U' :=
      BandPrototileTranslation (q i.succ) U (-w) hU
    have hV'band : BandPrototile (q ((i + 1).succ)) V' :=
      BandPrototileTranslation (q ((i + 1).succ)) V (-w) hV
    have hcenterU' := DiamondInterfaceGeometry.hcenterU' K T w hcent translate_centroid_diff i U
        hcenterU
    have hcenterV' := DiamondInterfaceGeometry.hcenterV' K T w hcent translate_centroid_diff i V
        hcenterV
    have hDne := disk_cells_nonempty D hDdisk
    have htriple' := DiamondInterfaceGeometry.htriple'At612 K T w hT'cells hbdv hbde
        triple_root_one i U V hbaseTouch hU'band hV'band hcenterU' hcenterV' hDne
    have htripleW := (TouchingTripleCovariance T' U' V' w).1.mp htriple'
    have hUrestore : TileTranslation U' w = U := by
      simpa [U'] using cancel_translation U
    have hVrestore : TileTranslation V' w = V := by
      simpa [V'] using cancel_translation V
    rw [hTrestore, hUrestore, hVrestore] at htripleW
    exact htripleW

end ApollonianSuperharmonic

end
