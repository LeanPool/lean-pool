/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.OrderedParentVectorSum

public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralAggregatePatches
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralMixedAggregatePatches
public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralPeriodicBlockCells
public import LeanPool.ApollonianSuperharmonic.QuarterTurnSymmetricExactInterfaceTransport

-- [TABLET NODE: BandOrderedGeneralChildInterfaces]

/-!
# BandOrderedGeneralChildInterfaces

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

private noncomputable def retargetNonemptyTriple (A A' B B' C C' : ProtoTile)
    (hAc : A.cells = A'.cells) (hAn : A.cells.Nonempty)
    (hBc : B.cells = B'.cells) (hBn : B.cells.Nonempty)
    (hCc : C.cells = C'.cells) (hCn : C.cells.Nonempty)
    (E : ExactTileInterfaceTriple A B C) : ExactTileInterfaceTriple A' B' C' := by
  classical
  have ha : A.cells = ∅ → A.anchor = A'.anchor := by
    intro he
    exact False.elim ((Finset.not_nonempty_iff_eq_empty.mpr he) hAn)
  have hb : B.cells = ∅ → B.anchor = B'.anchor := by
    intro he
    exact False.elim ((Finset.not_nonempty_iff_eq_empty.mpr he) hBn)
  have hc : C.cells = ∅ → C.anchor = C'.anchor := by
    intro he
    exact False.elim ((Finset.not_nonempty_iff_eq_empty.mpr he) hCn)
  have oa := ProtoTileObservableExtensionality A A' hAc ha
  have ob := ProtoTileObservableExtensionality B B' hBc hb
  have oc := ProtoTileObservableExtensionality C C' hCc hc
  have ea : FootprintEdges A = FootprintEdges A' := by simp [FootprintEdges, hAc]
  have eb : FootprintEdges B = FootprintEdges B' := by simp [FootprintEdges, hBc]
  have ec : FootprintEdges C = FootprintEdges C' := by simp [FootprintEdges, hCc]
  exact {
    point := E.point
    otherAB := E.otherAB
    otherBC := E.otherBC
    otherCA := E.otherCA
    pathAB := by simpa [oa.1, ob.1, ea, eb] using E.pathAB
    pathBC := by simpa [ob.1, oc.1, eb, ec] using E.pathBC
    pathCA := by simpa [oc.1, oa.1, ec, ea] using E.pathCA
    unique_common := by intro x; simpa [oa.1, ob.1, oc.1] using E.unique_common x }

namespace ChildInterfaceGeometry

private theorem first_parent :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (T : ProtoTile), (
        let junctionData := fun (A B C : ProtoTile) => ∃ (AB : ProtoTile) (BC : ProtoTile) (CA :
            ProtoTile) (ABC : ProtoTile), LatticeTile A ∧ LatticeTile B ∧ LatticeTile C ∧
            LatticeTile AB ∧ LatticeTile BC ∧ LatticeTile CA ∧ LatticeTile ABC ∧ Disjoint A.cells
            B.cells ∧ Disjoint B.cells C.cells ∧ Disjoint C.cells A.cells ∧ (∀ (z : LatticeCell),
            z ∈ AB.cells ↔ z ∈ A.cells ∨ z ∈ B.cells) ∧ (∀ (z : LatticeCell), z ∈ BC.cells ↔ z ∈
            B.cells ∨ z ∈ C.cells) ∧ (∀ (z : LatticeCell), z ∈ CA.cells ↔ z ∈ C.cells ∨ z ∈
            A.cells) ∧ (∀ (z : LatticeCell), z ∈ ABC.cells ↔ z ∈ A.cells ∨ z ∈ B.cells ∨ z ∈
            C.cells) ∧ (FootprintEdges A ∩ FootprintEdges B).Nonempty ∧ (FootprintEdges B ∩
            FootprintEdges C).Nonempty ∧ (FootprintEdges C ∩ FootprintEdges A).Nonempty;
        let pairedEndpointData := fun (i : Fin (3 : ℕ)) (s : Fin (4 : ℕ)) (U V : ProtoTile) =>
            have uR := (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ^ (↑s : ℕ) * if Even (↑s : ℕ) then
            BandVectors.1 (q (0 : Fin (4 : ℕ))) (q i.succ) else BandVectors.1 (q i.succ) (q (0 :
            Fin (4 : ℕ)));
        let uL := (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ^ (↑s : ℕ) * if Even (↑s : ℕ) then
            BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ))) else BandVectors.1 (q (0 : Fin (4 :
            ℕ))) (q i.succ); ∃ (rightData : ExactTileInterfaceTriple T (TileTranslation T uR) U)
            (incomingData : ExactTileInterfaceTriple T (TileTranslation T uL) U) (t5Data :
            ExactTileInterfaceTriple T U V), rightData.point = t5Data.point ∧ incomingData.point
            ≠ t5Data.point ∧ incomingData.otherCA = t5Data.point ∧ rightData.otherCA =
            incomingData.point ∧ t5Data.otherAB = incomingData.point; (∀ (i : Fin (3 : ℕ)), ∀ (U
            : ProtoTile), BandPrototile (q i.succ) U → TileCentroid U - TileCentroid T = (1 / 2 :
            ℝ) • (GaussianRealPoint (BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ)))) +
            GaussianRealPoint (BandVectors.1 (q (0 : Fin (4 : ℕ))) (q i.succ))) → junctionData T
            (TileTranslation T (BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ))))) U) ∧ (∀ (i : Fin
            (3 : ℕ)), ∀ (U : ProtoTile), ∀ (V : ProtoTile), BandPrototile (q i.succ) U →
            BandPrototile (q (i + (1 : Fin (3 : ℕ))).succ) V → TileCentroid U - TileCentroid T =
            (1 / 2 : ℝ) • (GaussianRealPoint (BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ)))) +
            GaussianRealPoint (BandVectors.1 (q (0 : Fin (4 : ℕ))) (q i.succ))) → TileCentroid V
            - TileCentroid T = (1 / 2 : ℝ) • (GaussianRealPoint (BandVectors.1 (q (i + (1 : Fin
            (3 : ℕ))).succ) (q (0 : Fin (4 : ℕ)))) - GaussianRealPoint (BandVectors.1 (q (0 : Fin
            (4 : ℕ))) (q (i + (1 : Fin (3 : ℕ))).succ))) → junctionData T U V) ∧ ∀ (i : Fin (3 :
            ℕ)), ∀ (s : Fin (4 : ℕ)), ∀ (U : ProtoTile), ∀ (V : ProtoTile), BandPrototile (q
            i.succ) U → BandPrototile (q (if Even (↑s : ℕ) then i + (1 : Fin (3 : ℕ)) else i - (1
            : Fin (3 : ℕ))).succ) V → TileCentroid U - TileCentroid T = (1 / 2 : ℝ) •
            GaussianRealPoint ((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ^ (↑s : ℕ) * (BandVectors.1 (q
            i.succ) (q (0 : Fin (4 : ℕ))) + BandVectors.1 (q (0 : Fin (4 : ℕ))) (q i.succ))) →
            TileCentroid V - TileCentroid T = (1 / 2 : ℝ) • GaussianRealPoint ((⟨(0 : ℤ), (1 :
            ℤ)⟩ : GaussianInt) ^ (↑s : ℕ) * if Even (↑s : ℕ) then BandVectors.1 (q (i + (1 : Fin
            (3 : ℕ))).succ) (q (0 : Fin (4 : ℕ))) - BandVectors.1 (q (0 : Fin (4 : ℕ))) (q (i +
            (1 : Fin (3 : ℕ))).succ) else BandVectors.1 (q (0 : Fin (4 : ℕ))) (q (i - (1 : Fin (3
            : ℕ))).succ) - BandVectors.1 (q (i - (1 : Fin (3 : ℕ))).succ) (q (0 : Fin (4 : ℕ))))
            → pairedEndpointData i s U V) → (∀ (i : Fin 3), ∀ (U : ProtoTile), (BandPrototile (q
            i.succ) U) → ((TileCentroid U - TileCentroid T = (1 / 2 : Real) •
            (GaussianRealPoint (BandVectors.1 (q i.succ) (q 0)) +
              GaussianRealPoint (BandVectors.1 (q 0) (q i.succ)))) → (Nonempty
                  (ExactTileInterfaceTriple T (TileTranslation T (BandVectors.1 (q i.succ) (q
                  0))) U)))) ) := by
  classical
  intro q T mixed i U hU hc
  obtain ⟨AB, BC, CA, ABC, hA, hB, hC, hAB, hBC, hCA, hABC,
    hdAB, hdBC, hdCA, huAB, huBC, huCA, huABC, heAB, heBC, heCA⟩ :=
    mixed.1 i U hU hc
  exact LatticeTileThreeDiskJunction T
    (TileTranslation T (BandVectors.1 (q i.succ) (q 0))) U AB BC CA ABC
    hA hB hC hAB hBC hCA hABC hdAB hdBC hdCA
    huAB huBC huCA huABC heAB heBC heCA

private theorem parent_pair :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (T : ProtoTile), (
        let junctionData := fun (A B C : ProtoTile) => ∃ (AB : ProtoTile) (BC : ProtoTile) (CA :
            ProtoTile) (ABC : ProtoTile), LatticeTile A ∧ LatticeTile B ∧ LatticeTile C ∧
            LatticeTile AB ∧ LatticeTile BC ∧ LatticeTile CA ∧ LatticeTile ABC ∧ Disjoint A.cells
            B.cells ∧ Disjoint B.cells C.cells ∧ Disjoint C.cells A.cells ∧ (∀ (z : LatticeCell),
            z ∈ AB.cells ↔ z ∈ A.cells ∨ z ∈ B.cells) ∧ (∀ (z : LatticeCell), z ∈ BC.cells ↔ z ∈
            B.cells ∨ z ∈ C.cells) ∧ (∀ (z : LatticeCell), z ∈ CA.cells ↔ z ∈ C.cells ∨ z ∈
            A.cells) ∧ (∀ (z : LatticeCell), z ∈ ABC.cells ↔ z ∈ A.cells ∨ z ∈ B.cells ∨ z ∈
            C.cells) ∧ (FootprintEdges A ∩ FootprintEdges B).Nonempty ∧ (FootprintEdges B ∩
            FootprintEdges C).Nonempty ∧ (FootprintEdges C ∩ FootprintEdges A).Nonempty;
        let pairedEndpointData := fun (i : Fin (3 : ℕ)) (s : Fin (4 : ℕ)) (U V : ProtoTile) =>
            have uR := (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ^ (↑s : ℕ) * if Even (↑s : ℕ) then
            BandVectors.1 (q (0 : Fin (4 : ℕ))) (q i.succ) else BandVectors.1 (q i.succ) (q (0 :
            Fin (4 : ℕ)));
        let uL := (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ^ (↑s : ℕ) * if Even (↑s : ℕ) then
            BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ))) else BandVectors.1 (q (0 : Fin (4 :
            ℕ))) (q i.succ); ∃ (rightData : ExactTileInterfaceTriple T (TileTranslation T uR) U)
            (incomingData : ExactTileInterfaceTriple T (TileTranslation T uL) U) (t5Data :
            ExactTileInterfaceTriple T U V), rightData.point = t5Data.point ∧ incomingData.point
            ≠ t5Data.point ∧ incomingData.otherCA = t5Data.point ∧ rightData.otherCA =
            incomingData.point ∧ t5Data.otherAB = incomingData.point; (∀ (i : Fin (3 : ℕ)), ∀ (U
            : ProtoTile), BandPrototile (q i.succ) U → TileCentroid U - TileCentroid T = (1 / 2 :
            ℝ) • (GaussianRealPoint (BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ)))) +
            GaussianRealPoint (BandVectors.1 (q (0 : Fin (4 : ℕ))) (q i.succ))) → junctionData T
            (TileTranslation T (BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ))))) U) ∧ (∀ (i : Fin
            (3 : ℕ)), ∀ (U : ProtoTile), ∀ (V : ProtoTile), BandPrototile (q i.succ) U →
            BandPrototile (q (i + (1 : Fin (3 : ℕ))).succ) V → TileCentroid U - TileCentroid T =
            (1 / 2 : ℝ) • (GaussianRealPoint (BandVectors.1 (q i.succ) (q (0 : Fin (4 : ℕ)))) +
            GaussianRealPoint (BandVectors.1 (q (0 : Fin (4 : ℕ))) (q i.succ))) → TileCentroid V
            - TileCentroid T = (1 / 2 : ℝ) • (GaussianRealPoint (BandVectors.1 (q (i + (1 : Fin
            (3 : ℕ))).succ) (q (0 : Fin (4 : ℕ)))) - GaussianRealPoint (BandVectors.1 (q (0 : Fin
            (4 : ℕ))) (q (i + (1 : Fin (3 : ℕ))).succ))) → junctionData T U V) ∧ ∀ (i : Fin (3 :
            ℕ)), ∀ (s : Fin (4 : ℕ)), ∀ (U : ProtoTile), ∀ (V : ProtoTile), BandPrototile (q
            i.succ) U → BandPrototile (q (if Even (↑s : ℕ) then i + (1 : Fin (3 : ℕ)) else i - (1
            : Fin (3 : ℕ))).succ) V → TileCentroid U - TileCentroid T = (1 / 2 : ℝ) •
            GaussianRealPoint ((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ^ (↑s : ℕ) * (BandVectors.1 (q
            i.succ) (q (0 : Fin (4 : ℕ))) + BandVectors.1 (q (0 : Fin (4 : ℕ))) (q i.succ))) →
            TileCentroid V - TileCentroid T = (1 / 2 : ℝ) • GaussianRealPoint ((⟨(0 : ℤ), (1 :
            ℤ)⟩ : GaussianInt) ^ (↑s : ℕ) * if Even (↑s : ℕ) then BandVectors.1 (q (i + (1 : Fin
            (3 : ℕ))).succ) (q (0 : Fin (4 : ℕ))) - BandVectors.1 (q (0 : Fin (4 : ℕ))) (q (i +
            (1 : Fin (3 : ℕ))).succ) else BandVectors.1 (q (0 : Fin (4 : ℕ))) (q (i - (1 : Fin (3
            : ℕ))).succ) - BandVectors.1 (q (i - (1 : Fin (3 : ℕ))).succ) (q (0 : Fin (4 : ℕ))))
            → pairedEndpointData i s U V) → (∀ (i : Fin 3), ∀ (U : ProtoTile), ∀ (V : ProtoTile),
            (BandPrototile (q i.succ) U) → ((BandPrototile (q ((i + 1).succ)) V) → ((TileCentroid
            U - TileCentroid T = (1 / 2 : Real) •
            (GaussianRealPoint (BandVectors.1 (q i.succ) (q 0)) +
              GaussianRealPoint (BandVectors.1 (q 0) (q i.succ)))) → ((TileCentroid V -
                  TileCentroid T = (1 / 2 : Real) •
            (GaussianRealPoint (BandVectors.1 (q ((i + 1).succ)) (q 0)) -
              GaussianRealPoint (BandVectors.1 (q 0) (q ((i + 1).succ))))) → (Nonempty
                  (ExactTileInterfaceTriple T U V)))))) ) := by
  classical
  intro q T mixed i U V hU hV hcU hcV
  obtain ⟨AB, BC, CA, ABC, hA, hB, hC, hAB, hBC, hCA, hABC,
    hdAB, hdBC, hdCA, huAB, huBC, huCA, huABC, heAB, heBC, heCA⟩ :=
    mixed.2.1 i U V hU hV hcU hcV
  exact LatticeTileThreeDiskJunction T U V AB BC CA ABC
    hA hB hC hAB hBC hCA hABC hdAB hdBC hdCA
    huAB huBC huCA huABC heAB heBC heCA

private theorem τmem :
    (by
      classical
      exact
        let τ : Finset (Int × Int) := {(0, 0), (0, 1), (1, 1)}
        τ ∈ ({ {(0, 0), (1, 0), (0, -1)}, {(0, 0), (0, 1), (1, 1)}, {(0, 0), (-1, -1), (-1, 0)}}
            : Finset (Finset (Int × Int))) ) := by
  classical
  intro τ
  simp [τ]

private theorem patchFor :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let K : Int → Int → Finset PeriodicSubtileIndex := fun m n ↦
          {⟨.A, m, n⟩, ⟨.B, m, n⟩, ⟨.C, m, n⟩,
            ⟨.D, m, n⟩, ⟨.E, m, n⟩, ⟨.F, m, n⟩}
        let τ : Finset (Int × Int) := {(0, 0), (0, 1), (1, 1)}
        (∀ (τ : Finset (Int × Int)), τ ∈ ({{((0 : ℤ), (0 : ℤ)), ((1 : ℤ), (0 : ℤ)), ((0 : ℤ),
            (-1 : ℤ))}, {((0 : ℤ),
            (0 : ℤ)), ((0 : ℤ), (1 : ℤ)), ((1 : ℤ), (1 : ℤ))}, {((0 : ℤ), (0 : ℤ)), ((-1 : ℤ),
            (-1 : ℤ)), ((-1 : ℤ), (0 : ℤ))}} : Finset (Finset (Int × Int))) → ∀ (σ : Finset (Int
                × Int)), σ ∈ τ.powerset → σ.Nonempty → ∃ (patch :
            FiniteInducedTilePatch cert.modified.plane cert.modified.tile), (patch.indices =
            σ.biUnion fun (mn : ℤ × ℤ) => (K mn.1 mn.2)) ∧ ∀ (x : LatticeCell), x ∈
                patch.unionTile.cells ↔ ∃ mn ∈ σ,
            ∃ a ∈ (K mn.1 mn.2), x ∈ (cert.modified.tile a).cells) → ((τ ∈ ({ {(0, 0),
            (1, 0), (0, -1)}, {(0, 0), (0, 1), (1, 1)}, {(0, 0), (-1, -1), (-1, 0)}} : Finset
            (Finset (Int × Int)))) → (∀ (σ : Finset (Int × Int)), (σ ⊆ τ) → ((σ.Nonempty) → (∃ p
            : FiniteInducedTilePatch cert.modified.plane cert.modified.tile, p.indices =
            σ.biUnion (fun mn => K mn.1 mn.2) ∧ ∀ x, x ∈ p.unionTile.cells ↔ ∃ mn ∈ σ, ∃ a ∈ K
            mn.1 mn.2, x ∈ (cert.modified.tile a).cells)))) ) := by
  classical
  intro q cfg C₀ T cert K τ aggregate' τmem σ hσ hne
  exact aggregate' τ τmem σ (Finset.mem_powerset.mpr hσ) hne

private theorem patchForAt :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let K : Int → Int → Finset PeriodicSubtileIndex := fun m n ↦
          {⟨.A, m, n⟩, ⟨.B, m, n⟩, ⟨.C, m, n⟩,
            ⟨.D, m, n⟩, ⟨.E, m, n⟩, ⟨.F, m, n⟩}
        (∀ (τ : Finset (Int × Int)), τ ∈ ({{((0 : ℤ), (0 : ℤ)), ((1 : ℤ), (0 : ℤ)), ((0 : ℤ),
            (-1 : ℤ))}, {((0 : ℤ),
            (0 : ℤ)), ((0 : ℤ), (1 : ℤ)), ((1 : ℤ), (1 : ℤ))}, {((0 : ℤ), (0 : ℤ)), ((-1 : ℤ),
            (-1 : ℤ)), ((-1 : ℤ), (0 : ℤ))}} : Finset (Finset (Int × Int))) → ∀ (σ : Finset (Int
                × Int)), σ ∈ τ.powerset → σ.Nonempty → ∃ (patch :
            FiniteInducedTilePatch cert.modified.plane cert.modified.tile), (patch.indices =
            σ.biUnion fun (mn : ℤ × ℤ) => (K mn.1 mn.2)) ∧ ∀ (x : LatticeCell), x ∈
                patch.unionTile.cells ↔ ∃ mn ∈ σ,
            ∃ a ∈ (K mn.1 mn.2), x ∈ (cert.modified.tile a).cells) → (∀ (ρ : Finset
            (Int × Int)), ∀ (σ : Finset (Int × Int)), (ρ ∈ ({
          {(0, 0), (1, 0), (0, -1)},
          {(0, 0), (0, 1), (1, 1)},
          {(0, 0), (-1, -1), (-1, 0)}} : Finset (Finset (Int × Int)))) → ((σ ⊆ ρ) → ((σ.Nonempty)
              → (∃ p : FiniteInducedTilePatch cert.modified.plane cert.modified.tile, p.indices =
              σ.biUnion (fun mn => K mn.1 mn.2) ∧ ∀ x, x ∈ p.unionTile.cells ↔ ∃ mn ∈ σ, ∃ a ∈ K
              mn.1 mn.2, x ∈ (cert.modified.tile a).cells)))) ) := by
  classical
  intro q cfg C₀ T cert K aggregate' ρ σ hρ hσ hne
  exact aggregate' ρ hρ σ (Finset.mem_powerset.mpr hσ) hne

private theorem blockEq :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let K : Int → Int → Finset PeriodicSubtileIndex := fun m n ↦
          {⟨.A, m, n⟩, ⟨.B, m, n⟩, ⟨.C, m, n⟩,
            ⟨.D, m, n⟩, ⟨.E, m, n⟩, ⟨.F, m, n⟩}
        let blockTile (m n : Int) : ProtoTile :=
          ⟨(K m n).biUnion (fun a => (cert.modified.tile a).cells), 0⟩
        ∀ (m : Int), ∀ (n : Int), (blockTile m n).cells = (TileTranslation T ((m : GaussianInt) *
            cert.u + (n : GaussianInt) * cert.v)).cells ) := by
  classical
  intro q cfg C₀ T cert K blockTile m n
  ext x
  change x ∈ (K m n).biUnion (fun a => (cert.modified.tile a).cells) ↔ _
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨a, ha, hx⟩
    have hcoords : a.first = m ∧ a.second = n := by
      cases a with
      | mk l r s => cases l <;> simp only [Finset.mem_insert, PeriodicSubtileIndex.mk.injEq,
          reduceCtorEq, false_and, Finset.mem_singleton, true_and, false_or, K, or_false,
          or_self] at ha <;> exact ha
    have haeq : a = ⟨a.label, m, n⟩ := by
      cases a with
      | mk l r s =>
        simp only [PeriodicSubtileIndex.mk.injEq]
        exact ⟨trivial, by simpa using hcoords.1, by simpa using hcoords.2⟩
    rw [haeq] at hx
    apply (BandOrderedGeneralPeriodicBlockCells q cfg C₀ T cert).1 m n x |>.mpr
    exact ⟨a.label, by simpa [cert.modified_tile] using hx⟩
  · intro hx
    obtain ⟨label, hx⟩ := (BandOrderedGeneralPeriodicBlockCells q cfg C₀ T cert).1 m n x |>.mp hx
    refine ⟨⟨label,m,n⟩, ?_, ?_⟩
    · cases label <;> simp [K]
    · simpa [cert.modified_tile] using hx

private theorem blockDisjoint :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let K : Int → Int → Finset PeriodicSubtileIndex := fun m n ↦
          {⟨.A, m, n⟩, ⟨.B, m, n⟩, ⟨.C, m, n⟩,
            ⟨.D, m, n⟩, ⟨.E, m, n⟩, ⟨.F, m, n⟩}
        let blockTile (m n : Int) : ProtoTile :=
          ⟨(K m n).biUnion (fun a => (cert.modified.tile a).cells), 0⟩
        (∀ (m : Int), ∀ (n : Int), (blockTile m n).cells = (TileTranslation T ((m : GaussianInt)
            * cert.u + (n : GaussianInt) * cert.v)).cells) → (∀ (m : Int), ∀ (n : Int), ∀ (r :
            Int), ∀ (s : Int), ((m,n) ≠ (r,s)) → (Disjoint (blockTile m n).cells (blockTile r
            s).cells)) ) := by
  classical
  intro q cfg C₀ T cert K blockTile blockEq m n r s hne
  rw [blockEq m n, blockEq r s]
  exact (BandOrderedGeneralPeriodicBlockCells q cfg C₀ T cert).2 m n r s hne

private theorem hUA :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let K : Int → Int → Finset PeriodicSubtileIndex := fun m n ↦
          {⟨.A, m, n⟩, ⟨.B, m, n⟩, ⟨.C, m, n⟩,
            ⟨.D, m, n⟩, ⟨.E, m, n⟩, ⟨.F, m, n⟩}
        let blockTile (m n : Int) : ProtoTile :=
          ⟨(K m n).biUnion (fun a => (cert.modified.tile a).cells), 0⟩
        (∀ (p : FiniteInducedTilePatch cert.modified.plane cert.modified.tile), ∀ (σ : Finset
            (Int × Int)), (p.indices = σ.biUnion (fun mn => K mn.1 mn.2)) → ((∀ x, x ∈
            p.unionTile.cells ↔ ∃ mn ∈ σ, ∃ a ∈ K mn.1 mn.2, x ∈ (cert.modified.tile a).cells) →
            (∀ x, x ∈ p.unionTile.cells ↔ ∃ mn ∈ σ, x ∈ (blockTile mn.1 mn.2).cells))) → (
        let σA : Finset (Int × Int) := {(0,0)}
        ∀ (pA : FiniteInducedTilePatch cert.modified.plane cert.modified.tile), (pA.indices =
            σA.biUnion fun (mn : ℤ × ℤ) => K mn.1 mn.2) → ((∀ (x : LatticeCell), x ∈
            pA.unionTile.cells ↔ ∃ mn ∈ σA, ∃ a ∈ K mn.1 mn.2, x ∈ (cert.modified.tile a).cells)
            → (∀ x, x ∈ pA.unionTile.cells ↔ x ∈ (blockTile 0 0).cells))) ) := by
  classical
  intro q cfg C₀ T cert K blockTile patchUnion σA pA hpA hexA x
  simpa [σA] using patchUnion pA σA hpA hexA x

private theorem hUB :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let K : Int → Int → Finset PeriodicSubtileIndex := fun m n ↦
          {⟨.A, m, n⟩, ⟨.B, m, n⟩, ⟨.C, m, n⟩,
            ⟨.D, m, n⟩, ⟨.E, m, n⟩, ⟨.F, m, n⟩}
        let blockTile (m n : Int) : ProtoTile :=
          ⟨(K m n).biUnion (fun a => (cert.modified.tile a).cells), 0⟩
        (∀ (p : FiniteInducedTilePatch cert.modified.plane cert.modified.tile), ∀ (σ : Finset
            (Int × Int)), (p.indices = σ.biUnion (fun mn => K mn.1 mn.2)) → ((∀ x, x ∈
            p.unionTile.cells ↔ ∃ mn ∈ σ, ∃ a ∈ K mn.1 mn.2, x ∈ (cert.modified.tile a).cells) →
            (∀ x, x ∈ p.unionTile.cells ↔ ∃ mn ∈ σ, x ∈ (blockTile mn.1 mn.2).cells))) → (
        let σB : Finset (Int × Int) := {(0,1)}
        ∀ (pB : FiniteInducedTilePatch cert.modified.plane cert.modified.tile), (pB.indices =
            σB.biUnion fun (mn : ℤ × ℤ) => K mn.1 mn.2) → ((∀ (x : LatticeCell), x ∈
            pB.unionTile.cells ↔ ∃ mn ∈ σB, ∃ a ∈ K mn.1 mn.2, x ∈ (cert.modified.tile a).cells)
            → (∀ x, x ∈ pB.unionTile.cells ↔ x ∈ (blockTile 0 1).cells))) ) := by
  classical
  intro q cfg C₀ T cert K blockTile patchUnion σB pB hpB hexB x
  simpa [σB] using patchUnion pB σB hpB hexB x

private theorem hUC :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let K : Int → Int → Finset PeriodicSubtileIndex := fun m n ↦
          {⟨.A, m, n⟩, ⟨.B, m, n⟩, ⟨.C, m, n⟩,
            ⟨.D, m, n⟩, ⟨.E, m, n⟩, ⟨.F, m, n⟩}
        let blockTile (m n : Int) : ProtoTile :=
          ⟨(K m n).biUnion (fun a => (cert.modified.tile a).cells), 0⟩
        (∀ (p : FiniteInducedTilePatch cert.modified.plane cert.modified.tile), ∀ (σ : Finset
            (Int × Int)), (p.indices = σ.biUnion (fun mn => K mn.1 mn.2)) → ((∀ x, x ∈
            p.unionTile.cells ↔ ∃ mn ∈ σ, ∃ a ∈ K mn.1 mn.2, x ∈ (cert.modified.tile a).cells) →
            (∀ x, x ∈ p.unionTile.cells ↔ ∃ mn ∈ σ, x ∈ (blockTile mn.1 mn.2).cells))) → (
        let σC : Finset (Int × Int) := {(1,1)}
        ∀ (pC : FiniteInducedTilePatch cert.modified.plane cert.modified.tile), (pC.indices =
            σC.biUnion fun (mn : ℤ × ℤ) => K mn.1 mn.2) → ((∀ (x : LatticeCell), x ∈
            pC.unionTile.cells ↔ ∃ mn ∈ σC, ∃ a ∈ K mn.1 mn.2, x ∈ (cert.modified.tile a).cells)
            → (∀ x, x ∈ pC.unionTile.cells ↔ x ∈ (blockTile 1 1).cells))) ) := by
  classical
  intro q cfg C₀ T cert K blockTile patchUnion σC pC hpC hexC x
  simpa [σC] using patchUnion pC σC hpC hexC x

private theorem hUAB :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let K : Int → Int → Finset PeriodicSubtileIndex := fun m n ↦
          {⟨.A, m, n⟩, ⟨.B, m, n⟩, ⟨.C, m, n⟩,
            ⟨.D, m, n⟩, ⟨.E, m, n⟩, ⟨.F, m, n⟩}
        let blockTile (m n : Int) : ProtoTile :=
          ⟨(K m n).biUnion (fun a => (cert.modified.tile a).cells), 0⟩
        (∀ (p : FiniteInducedTilePatch cert.modified.plane cert.modified.tile), ∀ (σ : Finset
            (Int × Int)), (p.indices = σ.biUnion (fun mn => K mn.1 mn.2)) → ((∀ x, x ∈
            p.unionTile.cells ↔ ∃ mn ∈ σ, ∃ a ∈ K mn.1 mn.2, x ∈ (cert.modified.tile a).cells) →
            (∀ x, x ∈ p.unionTile.cells ↔ ∃ mn ∈ σ, x ∈ (blockTile mn.1 mn.2).cells))) → (
        let σAB : Finset (Int × Int) := {(0,0),(0,1)}
        ∀ (pAB : FiniteInducedTilePatch cert.modified.plane cert.modified.tile), (pAB.indices =
            σAB.biUnion fun (mn : ℤ × ℤ) => K mn.1 mn.2) → ((∀ (x : LatticeCell), x ∈
            pAB.unionTile.cells ↔ ∃ mn ∈ σAB, ∃ a ∈ K mn.1 mn.2, x ∈ (cert.modified.tile
            a).cells) → (∀ x, x ∈ pAB.unionTile.cells ↔ x ∈ (blockTile 0 0).cells ∨ x ∈
            (blockTile 0 1).cells))) ) := by
  classical
  intro q cfg C₀ T cert K blockTile patchUnion σAB pAB hpAB hexAB x
  simpa [σAB] using patchUnion pAB σAB hpAB hexAB x

private theorem hUBC :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let K : Int → Int → Finset PeriodicSubtileIndex := fun m n ↦
          {⟨.A, m, n⟩, ⟨.B, m, n⟩, ⟨.C, m, n⟩,
            ⟨.D, m, n⟩, ⟨.E, m, n⟩, ⟨.F, m, n⟩}
        let blockTile (m n : Int) : ProtoTile :=
          ⟨(K m n).biUnion (fun a => (cert.modified.tile a).cells), 0⟩
        (∀ (p : FiniteInducedTilePatch cert.modified.plane cert.modified.tile), ∀ (σ : Finset
            (Int × Int)), (p.indices = σ.biUnion (fun mn => K mn.1 mn.2)) → ((∀ x, x ∈
            p.unionTile.cells ↔ ∃ mn ∈ σ, ∃ a ∈ K mn.1 mn.2, x ∈ (cert.modified.tile a).cells) →
            (∀ x, x ∈ p.unionTile.cells ↔ ∃ mn ∈ σ, x ∈ (blockTile mn.1 mn.2).cells))) → (
        let σBC : Finset (Int × Int) := {(0,1),(1,1)}
        ∀ (pBC : FiniteInducedTilePatch cert.modified.plane cert.modified.tile), (pBC.indices =
            σBC.biUnion fun (mn : ℤ × ℤ) => K mn.1 mn.2) → ((∀ (x : LatticeCell), x ∈
            pBC.unionTile.cells ↔ ∃ mn ∈ σBC, ∃ a ∈ K mn.1 mn.2, x ∈ (cert.modified.tile
            a).cells) → (∀ x, x ∈ pBC.unionTile.cells ↔ x ∈ (blockTile 0 1).cells ∨ x ∈
            (blockTile 1 1).cells))) ) := by
  classical
  intro q cfg C₀ T cert K blockTile patchUnion σBC pBC hpBC hexBC x
  simpa [σBC] using patchUnion pBC σBC hpBC hexBC x

private theorem hUCA :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let K : Int → Int → Finset PeriodicSubtileIndex := fun m n ↦
          {⟨.A, m, n⟩, ⟨.B, m, n⟩, ⟨.C, m, n⟩,
            ⟨.D, m, n⟩, ⟨.E, m, n⟩, ⟨.F, m, n⟩}
        let blockTile (m n : Int) : ProtoTile :=
          ⟨(K m n).biUnion (fun a => (cert.modified.tile a).cells), 0⟩
        (∀ (p : FiniteInducedTilePatch cert.modified.plane cert.modified.tile), ∀ (σ : Finset
            (Int × Int)), (p.indices = σ.biUnion (fun mn => K mn.1 mn.2)) → ((∀ x, x ∈
            p.unionTile.cells ↔ ∃ mn ∈ σ, ∃ a ∈ K mn.1 mn.2, x ∈ (cert.modified.tile a).cells) →
            (∀ x, x ∈ p.unionTile.cells ↔ ∃ mn ∈ σ, x ∈ (blockTile mn.1 mn.2).cells))) → (
        let σCA : Finset (Int × Int) := {(1,1),(0,0)}
        ∀ (pCA : FiniteInducedTilePatch cert.modified.plane cert.modified.tile), (pCA.indices =
            σCA.biUnion fun (mn : ℤ × ℤ) => K mn.1 mn.2) → ((∀ (x : LatticeCell), x ∈
            pCA.unionTile.cells ↔ ∃ mn ∈ σCA, ∃ a ∈ K mn.1 mn.2, x ∈ (cert.modified.tile
            a).cells) → (∀ x, x ∈ pCA.unionTile.cells ↔ x ∈ (blockTile 1 1).cells ∨ x ∈
            (blockTile 0 0).cells))) ) := by
  classical
  intro q cfg C₀ T cert K blockTile patchUnion σCA pCA hpCA hexCA x
  simpa [σCA] using patchUnion pCA σCA hpCA hexCA x

private theorem hUABC :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let K : Int → Int → Finset PeriodicSubtileIndex := fun m n ↦
          {⟨.A, m, n⟩, ⟨.B, m, n⟩, ⟨.C, m, n⟩,
            ⟨.D, m, n⟩, ⟨.E, m, n⟩, ⟨.F, m, n⟩}
        let τ : Finset (Int × Int) := {(0, 0), (0, 1), (1, 1)}
        let blockTile (m n : Int) : ProtoTile :=
          ⟨(K m n).biUnion (fun a => (cert.modified.tile a).cells), 0⟩
        (∀ (p : FiniteInducedTilePatch cert.modified.plane cert.modified.tile), ∀ (σ : Finset
            (Int × Int)), (p.indices = σ.biUnion (fun mn => K mn.1 mn.2)) → ((∀ x, x ∈
            p.unionTile.cells ↔ ∃ mn ∈ σ, ∃ a ∈ K mn.1 mn.2, x ∈ (cert.modified.tile a).cells) →
            (∀ x, x ∈ p.unionTile.cells ↔ ∃ mn ∈ σ, x ∈ (blockTile mn.1 mn.2).cells))) → (∀ (pABC
            : FiniteInducedTilePatch cert.modified.plane cert.modified.tile), (pABC.indices =
            τ.biUnion fun (mn : ℤ × ℤ) => K mn.1 mn.2) → ((∀ (x : LatticeCell), x ∈
            pABC.unionTile.cells ↔ ∃ mn ∈ τ, ∃ a ∈ K mn.1 mn.2, x ∈ (cert.modified.tile a).cells)
            → (∀ x, x ∈ pABC.unionTile.cells ↔ x ∈ (blockTile 0 0).cells ∨ x ∈ (blockTile 0
            1).cells ∨ x ∈ (blockTile 1 1).cells))) ) := by
  classical
  intro q cfg C₀ T cert K τ blockTile patchUnion pABC hpABC hexABC x
  constructor
  · intro hx
    obtain ⟨mn, hmn, hcell⟩ := (patchUnion pABC τ hpABC hexABC x).mp hx
    simp only [τ, Finset.mem_insert, Finset.mem_singleton] at hmn
    rcases hmn with hmn | hmn | hmn
    · rcases hmn with rfl
      exact Or.inl hcell
    · rcases hmn with rfl
      exact Or.inr (Or.inl hcell)
    · rcases hmn with rfl
      exact Or.inr (Or.inr hcell)
  · intro hx
    rcases hx with hx | hx | hx
    · exact (patchUnion pABC τ hpABC hexABC x).mpr ⟨(0,0), by simp [τ], hx⟩
    · exact (patchUnion pABC τ hpABC hexABC x).mpr ⟨(0,1), by simp [τ], hx⟩
    · exact (patchUnion pABC τ hpABC hexABC x).mpr ⟨(1,1), by simp [τ], hx⟩

private theorem hcommonAB :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let K : Int → Int → Finset PeriodicSubtileIndex := fun m n ↦
          {⟨.A, m, n⟩, ⟨.B, m, n⟩, ⟨.C, m, n⟩,
            ⟨.D, m, n⟩, ⟨.E, m, n⟩, ⟨.F, m, n⟩}
        let blockTile (m n : Int) : ProtoTile :=
          ⟨(K m n).biUnion (fun a => (cert.modified.tile a).cells), 0⟩
        (FootprintEdges (blockTile 0 0) ∩ FootprintEdges (blockTile 0 1)).Nonempty ) := by
  classical
  intro q cfg C₀ T cert K blockTile
  have hadj := (cert.modified_adjacency ⟨.A,0,0⟩ ⟨.E,0,1⟩).2
    (AllowedSubtileIncidence.AE01 0 0)
  have he := cert.modified.adjacent_has_common_edge _ _ hadj
  rcases he with ⟨e, heA, heB⟩
  rcases heA with ⟨x, hx, hedge⟩
  rcases heB with ⟨y, hy, hedgeB⟩
  refine ⟨e, ?_, ?_⟩
  · exact ⟨x, Finset.mem_biUnion.mpr ⟨⟨.A,0,0⟩, by simp [K], hx⟩, hedge⟩
  · exact ⟨y, Finset.mem_biUnion.mpr ⟨⟨.E,0,1⟩, by simp [K], hy⟩, hedgeB⟩

private theorem hcommonBC :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let K : Int → Int → Finset PeriodicSubtileIndex := fun m n ↦
          {⟨.A, m, n⟩, ⟨.B, m, n⟩, ⟨.C, m, n⟩,
            ⟨.D, m, n⟩, ⟨.E, m, n⟩, ⟨.F, m, n⟩}
        let blockTile (m n : Int) : ProtoTile :=
          ⟨(K m n).biUnion (fun a => (cert.modified.tile a).cells), 0⟩
        (FootprintEdges (blockTile 0 1) ∩ FootprintEdges (blockTile 1 1)).Nonempty ) := by
  classical
  intro q cfg C₀ T cert K blockTile
  have hadj := (cert.modified_adjacency ⟨.C,1,1⟩ ⟨.E,0,1⟩).2
    (AllowedSubtileIncidence.CEm10 1 1)
  have he := cert.modified.adjacent_has_common_edge _ _ hadj
  rcases he with ⟨e, heC, heB⟩
  rcases heB with ⟨x, hx, hedge⟩
  rcases heC with ⟨y, hy, hedgeC⟩
  refine ⟨e, ?_, ?_⟩
  · exact ⟨x, Finset.mem_biUnion.mpr ⟨⟨.E,0,1⟩, by simp [K], hx⟩, hedge⟩
  · exact ⟨y, Finset.mem_biUnion.mpr ⟨⟨.C,1,1⟩, by simp [K], hy⟩, hedgeC⟩

private theorem hcommonCA :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let K : Int → Int → Finset PeriodicSubtileIndex := fun m n ↦
          {⟨.A, m, n⟩, ⟨.B, m, n⟩, ⟨.C, m, n⟩,
            ⟨.D, m, n⟩, ⟨.E, m, n⟩, ⟨.F, m, n⟩}
        let blockTile (m n : Int) : ProtoTile :=
          ⟨(K m n).biUnion (fun a => (cert.modified.tile a).cells), 0⟩
        (FootprintEdges (blockTile 1 1) ∩ FootprintEdges (blockTile 0 0)).Nonempty ) := by
  classical
  intro q cfg C₀ T cert K blockTile
  have hadj := (cert.modified_adjacency ⟨.A,0,0⟩ ⟨.C,1,1⟩).2
    (AllowedSubtileIncidence.AC11 0 0)
  have he := cert.modified.adjacent_has_common_edge _ _ hadj
  rcases he with ⟨e, heA, heC⟩
  rcases heC with ⟨x, hx, hedge⟩
  rcases heA with ⟨y, hy, hedgeA⟩
  refine ⟨e, ?_, ?_⟩
  · exact ⟨x, Finset.mem_biUnion.mpr ⟨⟨.C,1,1⟩, by simp [K], hx⟩, hedge⟩
  · exact ⟨y, Finset.mem_biUnion.mpr ⟨⟨.A,0,0⟩, by simp [K], hy⟩, hedgeA⟩

private theorem blockLattice :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let K : Int → Int → Finset PeriodicSubtileIndex := fun m n ↦
          {⟨.A, m, n⟩, ⟨.B, m, n⟩, ⟨.C, m, n⟩,
            ⟨.D, m, n⟩, ⟨.E, m, n⟩, ⟨.F, m, n⟩}
        let blockTile (m n : Int) : ProtoTile :=
          ⟨(K m n).biUnion (fun a => (cert.modified.tile a).cells), 0⟩
        ∀ (m : Int), ∀ (n : Int), ∀ (p : FiniteInducedTilePatch cert.modified.plane
            cert.modified.tile), (∀ x, x ∈ p.unionTile.cells ↔ x ∈ (blockTile m n).cells) →
            ((LatticeTile p.unionTile) → (LatticeTile (blockTile m n))) ) := by
  classical
  intro q cfg C₀ T cert K blockTile m n p hp hLp
  have hcells : p.unionTile.cells = (blockTile m n).cells := Finset.ext fun x => hp x
  have hne : p.unionTile.cells.Nonempty := (LatticeTileGridStructure _ hLp).1.1
  have hanchor : p.unionTile.cells = ∅ → p.unionTile.anchor = (blockTile m n).anchor := by
    intro h
    rw [h] at hne
    exact False.elim ((Finset.not_nonempty_iff_eq_empty.mpr rfl) hne)
  have hobs := ProtoTileObservableExtensionality p.unionTile (blockTile m n) hcells hanchor
  change TopologicalDisk (TileRealization p.unionTile) at hLp
  change TopologicalDisk (TileRealization (blockTile m n))
  rw [← hobs.2.2.2.1]
  exact hLp

private theorem blockJunction :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let K : Int → Int → Finset PeriodicSubtileIndex := fun m n ↦
          {⟨.A, m, n⟩, ⟨.B, m, n⟩, ⟨.C, m, n⟩,
            ⟨.D, m, n⟩, ⟨.E, m, n⟩, ⟨.F, m, n⟩}
        let blockTile (m n : Int) : ProtoTile :=
          ⟨(K m n).biUnion (fun a => (cert.modified.tile a).cells), 0⟩
        ∀ (pAB : FiniteInducedTilePatch cert.modified.plane cert.modified.tile), ∀ (pBC :
            FiniteInducedTilePatch cert.modified.plane cert.modified.tile), ∀ (pCA :
            FiniteInducedTilePatch cert.modified.plane cert.modified.tile), ∀ (pABC :
            FiniteInducedTilePatch cert.modified.plane cert.modified.tile), (LatticeTile
            pAB.unionTile) → ((LatticeTile pBC.unionTile) → ((LatticeTile pCA.unionTile) →
            ((LatticeTile pABC.unionTile) → ((∀ x, x ∈ pAB.unionTile.cells ↔ x ∈ (blockTile 0
            0).cells ∨ x ∈ (blockTile 0 1).cells) → ((∀ x, x ∈ pBC.unionTile.cells ↔ x ∈
            (blockTile 0 1).cells ∨ x ∈ (blockTile 1 1).cells) → ((∀ x, x ∈ pCA.unionTile.cells ↔
            x ∈ (blockTile 1 1).cells ∨ x ∈ (blockTile 0 0).cells) → ((∀ x, x ∈
            pABC.unionTile.cells ↔ x ∈ (blockTile 0 0).cells ∨ x ∈ (blockTile 0 1).cells ∨ x ∈
            (blockTile 1 1).cells) → ((Disjoint (blockTile 0 0).cells (blockTile 0 1).cells) →
            ((Disjoint (blockTile 0 1).cells (blockTile 1 1).cells) → ((Disjoint (blockTile 1
            1).cells (blockTile 0 0).cells) → (((FootprintEdges (blockTile 0 0) ∩ FootprintEdges
            (blockTile 0 1)).Nonempty) → (((FootprintEdges (blockTile 0 1) ∩ FootprintEdges
            (blockTile 1 1)).Nonempty) → (((FootprintEdges (blockTile 1 1) ∩ FootprintEdges
            (blockTile 0 0)).Nonempty) → ((LatticeTile (blockTile (0 : ℤ) (0 : ℤ))) →
            ((LatticeTile (blockTile (0 : ℤ) (1 : ℤ))) → ((LatticeTile (blockTile (1 : ℤ) (1 :
            ℤ))) → (Nonempty (ExactTileInterfaceTriple (blockTile 0 0) (blockTile 0 1) (blockTile
            1 1))))))))))))))))))) ) := by
  classical
  intro q cfg C₀ T cert K blockTile pAB pBC pCA pABC hLAB hLBC hLCA hLABC hUAB hUBC hUCA hUABC
      hdisjAB hdisjBC hdisjCA hcommonAB hcommonBC hcommonCA hLA' hLB' hLC'
  exact LatticeTileThreeDiskJunction (blockTile 0 0) (blockTile 0 1) (blockTile 1 1)
    pAB.unionTile pBC.unionTile pCA.unionTile pABC.unionTile
    hLA' hLB' hLC' hLAB hLBC hLCA hLABC
    hdisjAB hdisjBC hdisjCA hUAB hUBC hUCA hUABC hcommonAB hcommonBC hcommonCA

private theorem hzero :
    (by
      classical
      exact
        ∀ (T : ProtoTile), (TileTranslation T 0).cells = T.cells ) := by
  classical
  intro T
  rw [(TileTranslationFormulas T 0).1]
  have hz : GaussianTranslation (0 : GaussianInt) = id := by
    funext x
    simp [GaussianTranslation]
  rw [hz, Finset.image_id]

private theorem rootNe :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let K : Int → Int → Finset PeriodicSubtileIndex := fun m n ↦
          {⟨.A, m, n⟩, ⟨.B, m, n⟩, ⟨.C, m, n⟩,
            ⟨.D, m, n⟩, ⟨.E, m, n⟩, ⟨.F, m, n⟩}
        let blockTile (m n : Int) : ProtoTile :=
          ⟨(K m n).biUnion (fun a => (cert.modified.tile a).cells), 0⟩
        (∀ (m : Int), ∀ (n : Int), (blockTile m n).cells = (TileTranslation T ((m : GaussianInt)
            * cert.u + (n : GaussianInt) * cert.v)).cells) → ((LatticeTile (blockTile (0 : ℤ) (0
            : ℤ))) → (((TileTranslation T 0).cells = T.cells) → (T.cells.Nonempty))) ) := by
  classical
  intro q cfg C₀ T cert K blockTile blockEq hLA' hzero
  have hne : (blockTile 0 0).cells.Nonempty := (LatticeTileGridStructure _ hLA').1.1
  rw [blockEq 0 0] at hne
  simpa only [Int.cast_zero, zero_mul, zero_add, hzero] using hne

private theorem blockAne :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let K : Int → Int → Finset PeriodicSubtileIndex := fun m n ↦
          {⟨.A, m, n⟩, ⟨.B, m, n⟩, ⟨.C, m, n⟩,
            ⟨.D, m, n⟩, ⟨.E, m, n⟩, ⟨.F, m, n⟩}
        let blockTile (m n : Int) : ProtoTile :=
          ⟨(K m n).biUnion (fun a => (cert.modified.tile a).cells), 0⟩
        (∀ (m : Int), ∀ (n : Int), (blockTile m n).cells = (TileTranslation T ((m : GaussianInt)
            * cert.u + (n : GaussianInt) * cert.v)).cells) → (((TileTranslation T
            0).cells.Nonempty) → ((blockTile 0 0).cells.Nonempty)) ) := by
  classical
  intro q cfg C₀ T cert K blockTile blockEq transZeroNe
  rw [blockEq 0 0]
  simpa only [Int.cast_zero, zero_mul, zero_add] using transZeroNe

private theorem row2 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let K : Int → Int → Finset PeriodicSubtileIndex := fun m n ↦
          {⟨.A, m, n⟩, ⟨.B, m, n⟩, ⟨.C, m, n⟩,
            ⟨.D, m, n⟩, ⟨.E, m, n⟩, ⟨.F, m, n⟩}
        let blockTile (m n : Int) : ProtoTile :=
          ⟨(K m n).biUnion (fun a => (cert.modified.tile a).cells), 0⟩
        (∀ (m : Int), ∀ (n : Int), (blockTile m n).cells = (TileTranslation T ((m :
            GaussianInt) * cert.u + (n : GaussianInt) * cert.v)).cells) → (∀ [Nonempty
                (ExactTileInterfaceTriple (blockTile 0 0) (blockTile 0 1) (blockTile 1
                1))], ((TileTranslation T 0).cells = T.cells) → (((blockTile 0 0).cells.Nonempty) →
            (((blockTile 0 1).cells.Nonempty) → (((blockTile 1 1).cells.Nonempty) → (Nonempty
            (ExactTileInterfaceTriple T (TileTranslation T cert.v) (TileTranslation T (cert.u +
            cert.v))))))))) := by
  classical
  intro q cfg C₀ T cert K blockTile blockEq blockJunction hzero blockAne blockBne blockCne
  let retargetTriple := retargetNonemptyTriple
  obtain ⟨E⟩ := blockJunction
  refine ⟨retargetTriple (blockTile 0 0) T (blockTile 0 1)
    (TileTranslation T cert.v) (blockTile 1 1)
    (TileTranslation T (cert.u + cert.v)) ?_ blockAne ?_ blockBne ?_ blockCne E⟩
  · have hA0 : (blockTile 0 0).cells = (TileTranslation T 0).cells := by
      simpa only [Int.cast_zero, zero_mul, zero_add] using blockEq 0 0
    exact hA0.trans hzero
  · simpa only [Int.cast_zero, Int.cast_one, zero_mul, one_mul, zero_add] using blockEq 0 1
  · simpa only [Int.cast_one, one_mul] using blockEq 1 1

private theorem rowJunction :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let K : Int → Int → Finset PeriodicSubtileIndex := fun m n ↦
          {⟨.A, m, n⟩, ⟨.B, m, n⟩, ⟨.C, m, n⟩,
            ⟨.D, m, n⟩, ⟨.E, m, n⟩, ⟨.F, m, n⟩}
        (∀ (ρ : Finset (Int × Int)), ∀ (σ : Finset (Int × Int)), (ρ ∈ ({ {(0, 0), (1, 0), (0,
            -1)}, {(0, 0), (0, 1), (1, 1)}, {(0, 0), (-1, -1), (-1, 0)}} : Finset (Finset (Int ×
            Int)))) → ((σ ⊆ ρ) → ((σ.Nonempty) → (∃ p : FiniteInducedTilePatch
            cert.modified.plane cert.modified.tile, p.indices = σ.biUnion (fun mn => K mn.1 mn.2)
            ∧ ∀ x, x ∈ p.unionTile.cells ↔ ∃ mn ∈ σ, ∃ a ∈ K mn.1 mn.2, x ∈ (cert.modified.tile
            a).cells)))) → (
        let blockTile (m n : Int) : ProtoTile :=
          ⟨(K m n).biUnion (fun a => (cert.modified.tile a).cells), 0⟩
        (∀ (m : Int), ∀ (n : Int), ∀ (r : Int), ∀ (s : Int), ((m,n) ≠ (r,s)) → (Disjoint
            (blockTile m n).cells (blockTile r s).cells)) → ((∀ (p : FiniteInducedTilePatch
            cert.modified.plane cert.modified.tile), ∀ (σ : Finset (Int × Int)), (p.indices =
            σ.biUnion (fun mn => K mn.1 mn.2)) → ((∀ x, x ∈ p.unionTile.cells ↔ ∃ mn ∈ σ, ∃ a ∈ K
            mn.1 mn.2, x ∈ (cert.modified.tile a).cells) → (∀ x, x ∈ p.unionTile.cells ↔ ∃ mn ∈
            σ, x ∈ (blockTile mn.1 mn.2).cells))) → ((∀ (m : Int), ∀ (n : Int), ∀ (p :
            FiniteInducedTilePatch cert.modified.plane cert.modified.tile), (∀ x, x ∈
            p.unionTile.cells ↔ x ∈ (blockTile m n).cells) → ((LatticeTile p.unionTile) →
            (LatticeTile (blockTile m n)))) → (∀ (ρ : Finset (Int × Int)), (ρ ∈ ({
            {(0,0),(1,0),(0,-1)}, {(0,0),(0,1),(1,1)},
            {(0,0),(-1,-1),(-1,0)} } : Finset (Finset (Int × Int)))) → (∀ (a : Int × Int), ∀ (b :
                Int × Int), ∀ (c : Int × Int), (ρ = {a,b,c}) → (((a.1,a.2) ≠ (b.1,b.2)) →
                (((b.1,b.2) ≠ (c.1,c.2)) → (((c.1,c.2) ≠ (a.1,a.2)) → (((FootprintEdges
                (blockTile a.1 a.2) ∩ FootprintEdges (blockTile b.1 b.2)).Nonempty) →
                (((FootprintEdges (blockTile b.1 b.2) ∩ FootprintEdges (blockTile c.1
                c.2)).Nonempty) → (((FootprintEdges (blockTile c.1 c.2) ∩ FootprintEdges
                (blockTile a.1 a.2)).Nonempty) → (Nonempty (ExactTileInterfaceTriple (blockTile
                a.1 a.2) (blockTile b.1 b.2) (blockTile c.1 c.2)))))))))))))) ) := by
  classical
  intro q cfg C₀ T cert K patchForAt blockTile blockDisjoint patchUnion blockLattice ρ hρ a b c
      hρeq hneAB hneBC hneCA hab hbc hca
  let sa : Finset (Int × Int) := {a}
  let sb : Finset (Int × Int) := {b}
  let sc : Finset (Int × Int) := {c}
  let sab : Finset (Int × Int) := {a,b}
  let sbc : Finset (Int × Int) := {b,c}
  let sca : Finset (Int × Int) := {c,a}
  obtain ⟨pa, hpa, epa⟩ := patchForAt ρ sa hρ (by rw [hρeq]; simp [sa]) (by simp [sa])
  obtain ⟨pb, hpb, epb⟩ := patchForAt ρ sb hρ (by rw [hρeq]; simp [sb]) (by simp [sb])
  obtain ⟨pc, hpc, epc⟩ := patchForAt ρ sc hρ (by rw [hρeq]; simp [sc]) (by simp [sc])
  obtain ⟨pab, hpab, epab⟩ := patchForAt ρ sab hρ (by rw [hρeq]; simp [sab]) (by simp [sab])
  obtain ⟨pbc, hpbc, epbc⟩ := patchForAt ρ sbc hρ (by rw [hρeq]; simp [sbc]) (by simp [sbc])
  obtain ⟨pca, hpca, epca⟩ := patchForAt ρ sca hρ (by
    rw [hρeq]
    intro z hz
    simp only [sca, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> simp) (by simp [sca])
  obtain ⟨pabc, hpabc, epabc⟩ := patchForAt ρ ρ hρ (by simp) (by simp [hρeq])
  have la := FinitePatchTopology cert.modified.plane cert.modified.tile
    (PeriodicTileMultiplicityOne cert.modified) (PeriodicTileIndexedMultiplicityOne cert.modified)
    (fun x y _ hadj => cert.modified.adjacent_has_common_edge x y hadj) pa
  have lb := FinitePatchTopology cert.modified.plane cert.modified.tile
    (PeriodicTileMultiplicityOne cert.modified) (PeriodicTileIndexedMultiplicityOne cert.modified)
    (fun x y _ hadj => cert.modified.adjacent_has_common_edge x y hadj) pb
  have lc := FinitePatchTopology cert.modified.plane cert.modified.tile
    (PeriodicTileMultiplicityOne cert.modified) (PeriodicTileIndexedMultiplicityOne cert.modified)
    (fun x y _ hadj => cert.modified.adjacent_has_common_edge x y hadj) pc
  have lab := FinitePatchTopology cert.modified.plane cert.modified.tile
    (PeriodicTileMultiplicityOne cert.modified) (PeriodicTileIndexedMultiplicityOne cert.modified)
    (fun x y _ hadj => cert.modified.adjacent_has_common_edge x y hadj) pab
  have lbc := FinitePatchTopology cert.modified.plane cert.modified.tile
    (PeriodicTileMultiplicityOne cert.modified) (PeriodicTileIndexedMultiplicityOne cert.modified)
    (fun x y _ hadj => cert.modified.adjacent_has_common_edge x y hadj) pbc
  have lca := FinitePatchTopology cert.modified.plane cert.modified.tile
    (PeriodicTileMultiplicityOne cert.modified) (PeriodicTileIndexedMultiplicityOne cert.modified)
    (fun x y _ hadj => cert.modified.adjacent_has_common_edge x y hadj) pca
  have labc := FinitePatchTopology cert.modified.plane cert.modified.tile
    (PeriodicTileMultiplicityOne cert.modified) (PeriodicTileIndexedMultiplicityOne cert.modified)
    (fun x y _ hadj => cert.modified.adjacent_has_common_edge x y hadj) pabc
  have ua : ∀ x, x ∈ pa.unionTile.cells ↔ x ∈ (blockTile a.1 a.2).cells := by
    intro x; simpa [sa] using patchUnion pa sa hpa epa x
  have ub : ∀ x, x ∈ pb.unionTile.cells ↔ x ∈ (blockTile b.1 b.2).cells := by
    intro x; simpa [sb] using patchUnion pb sb hpb epb x
  have uc : ∀ x, x ∈ pc.unionTile.cells ↔ x ∈ (blockTile c.1 c.2).cells := by
    intro x; simpa [sc] using patchUnion pc sc hpc epc x
  have uab : ∀ x, x ∈ pab.unionTile.cells ↔
      x ∈ (blockTile a.1 a.2).cells ∨ x ∈ (blockTile b.1 b.2).cells := by
    intro x
    constructor
    · intro hx
      obtain ⟨z,hz,hcell⟩ := (patchUnion pab sab hpab epab x).mp hx
      simp only [sab, Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact Or.inl hcell
      · exact Or.inr hcell
    · rintro (hx | hx)
      · exact (patchUnion pab sab hpab epab x).mpr ⟨a, by simp [sab], hx⟩
      · exact (patchUnion pab sab hpab epab x).mpr ⟨b, by simp [sab], hx⟩
  have ubc : ∀ x, x ∈ pbc.unionTile.cells ↔
      x ∈ (blockTile b.1 b.2).cells ∨ x ∈ (blockTile c.1 c.2).cells := by
    intro x
    constructor
    · intro hx
      obtain ⟨z,hz,hcell⟩ := (patchUnion pbc sbc hpbc epbc x).mp hx
      simp only [sbc, Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact Or.inl hcell
      · exact Or.inr hcell
    · rintro (hx | hx)
      · exact (patchUnion pbc sbc hpbc epbc x).mpr ⟨b, by simp [sbc], hx⟩
      · exact (patchUnion pbc sbc hpbc epbc x).mpr ⟨c, by simp [sbc], hx⟩
  have uca : ∀ x, x ∈ pca.unionTile.cells ↔
      x ∈ (blockTile c.1 c.2).cells ∨ x ∈ (blockTile a.1 a.2).cells := by
    intro x
    constructor
    · intro hx
      obtain ⟨z,hz,hcell⟩ := (patchUnion pca sca hpca epca x).mp hx
      simp only [sca, Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact Or.inl hcell
      · exact Or.inr hcell
    · rintro (hx | hx)
      · exact (patchUnion pca sca hpca epca x).mpr ⟨c, by simp [sca], hx⟩
      · exact (patchUnion pca sca hpca epca x).mpr ⟨a, by simp [sca], hx⟩
  have uabc : ∀ x, x ∈ pabc.unionTile.cells ↔
      x ∈ (blockTile a.1 a.2).cells ∨ x ∈ (blockTile b.1 b.2).cells ∨
        x ∈ (blockTile c.1 c.2).cells := by
    intro x
    constructor
    · intro hx
      obtain ⟨z,hz,hcell⟩ := (patchUnion pabc ρ hpabc epabc x).mp hx
      rw [hρeq] at hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl
      · exact Or.inl hcell
      · exact Or.inr (Or.inl hcell)
      · exact Or.inr (Or.inr hcell)
    · rintro (hx | hx | hx)
      · exact (patchUnion pabc ρ hpabc epabc x).mpr ⟨a, by simp [hρeq], hx⟩
      · exact (patchUnion pabc ρ hpabc epabc x).mpr ⟨b, by simp [hρeq], hx⟩
      · exact (patchUnion pabc ρ hpabc epabc x).mpr ⟨c, by simp [hρeq], hx⟩
  have dab := blockDisjoint a.1 a.2 b.1 b.2 hneAB
  have dbc := blockDisjoint b.1 b.2 c.1 c.2 hneBC
  have dca := blockDisjoint c.1 c.2 a.1 a.2 hneCA
  exact LatticeTileThreeDiskJunction _ _ _ pab.unionTile pbc.unionTile pca.unionTile pabc.unionTile
    (blockLattice _ _ pa ua la) (blockLattice _ _ pb ub lb) (blockLattice _ _ pc uc lc)
    lab lbc lca labc dab dbc dca uab ubc uca uabc hab hbc hca

private theorem blockEdge :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let K : Int → Int → Finset PeriodicSubtileIndex := fun m n ↦
          {⟨.A, m, n⟩, ⟨.B, m, n⟩, ⟨.C, m, n⟩,
            ⟨.D, m, n⟩, ⟨.E, m, n⟩, ⟨.F, m, n⟩}
        let blockTile (m n : Int) : ProtoTile :=
          ⟨(K m n).biUnion (fun a => (cert.modified.tile a).cells), 0⟩
        ∀ (a : PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), ∀ (m : Int), ∀ (n : Int), ∀
            (r : Int), ∀ (s : Int), (a ∈ K m n) → ((b ∈ K r s) → ((cert.modified.plane.adjacent a
            b) → ((FootprintEdges (blockTile m n) ∩ FootprintEdges (blockTile r s)).Nonempty))) )
            := by
  classical
  intro q cfg C₀ T cert K blockTile a b m n r s ha hb hadj
  rcases cert.modified.adjacent_has_common_edge a b hadj with ⟨e, hea, heb⟩
  rcases hea with ⟨x, hx, hedgeA⟩
  rcases heb with ⟨y, hy, hedgeB⟩
  refine ⟨e, ?_, ?_⟩
  · exact ⟨x, Finset.mem_biUnion.mpr ⟨a, ha, hx⟩, hedgeA⟩
  · exact ⟨y, Finset.mem_biUnion.mpr ⟨b, hb, hy⟩, hedgeB⟩

private theorem row1 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let K : Int → Int → Finset PeriodicSubtileIndex := fun m n ↦
          {⟨.A, m, n⟩, ⟨.B, m, n⟩, ⟨.C, m, n⟩,
            ⟨.D, m, n⟩, ⟨.E, m, n⟩, ⟨.F, m, n⟩}
        let blockTile (m n : Int) : ProtoTile :=
          ⟨(K m n).biUnion (fun a => (cert.modified.tile a).cells), 0⟩
        (∀ (ρ : Finset (Int × Int)), (ρ ∈ ({ {(0,0),(1,0),(0,-1)}, {(0,0),(0,1),(1,1)},
            {(0,0),(-1,-1),(-1,0)} } : Finset (Finset (Int × Int)))) → (∀ (a : Int × Int), ∀ (b :
            Int × Int), ∀ (c : Int × Int), (ρ = {a,b,c}) → (((a.1,a.2) ≠ (b.1,b.2)) → (((b.1,b.2)
            ≠ (c.1,c.2)) → (((c.1,c.2) ≠ (a.1,a.2)) → (((FootprintEdges (blockTile a.1 a.2) ∩
            FootprintEdges (blockTile b.1 b.2)).Nonempty) → (((FootprintEdges (blockTile b.1 b.2)
            ∩ FootprintEdges (blockTile c.1 c.2)).Nonempty) → (((FootprintEdges (blockTile c.1
            c.2) ∩ FootprintEdges (blockTile a.1 a.2)).Nonempty) → (Nonempty
            (ExactTileInterfaceTriple (blockTile a.1 a.2) (blockTile b.1 b.2) (blockTile c.1
            c.2))))))))))) → ((∀ (a : PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), ∀ (m :
            Int), ∀ (n : Int), ∀ (r : Int), ∀ (s : Int), (a ∈ K m n) → ((b ∈ K r s) →
            ((cert.modified.plane.adjacent a b) → ((FootprintEdges (blockTile m n) ∩
            FootprintEdges (blockTile r s)).Nonempty)))) → (
        Nonempty (ExactTileInterfaceTriple (blockTile 0 0) (blockTile 1 0) (blockTile 0 (-1)))))
            ) := by
  classical
  intro q cfg C₀ T cert K blockTile rowJunction blockEdge
  let τ1 : Finset (Int × Int) := {(0,0),(1,0),(0,-1)}
  apply rowJunction τ1 (by simp [τ1]) (0,0) (1,0) (0,-1) (by ext; simp [τ1])
    (by decide) (by decide) (by decide) ?_ ?_ ?_
  · exact blockEdge ⟨.D,0,0⟩ ⟨.F,1,0⟩ 0 0 1 0 (by simp [K]) (by simp [K])
      ((cert.modified_adjacency _ _).2 (AllowedSubtileIncidence.DF10 0 0))
  · exact blockEdge ⟨.B,1,0⟩ ⟨.D,0,-1⟩ 1 0 0 (-1) (by simp [K]) (by simp [K])
      ((cert.modified_adjacency _ _).2 (AllowedSubtileIncidence.BDm1m1 1 0))
  · exact blockEdge ⟨.F,0,-1⟩ ⟨.B,0,0⟩ 0 (-1) 0 0 (by simp [K]) (by simp [K])
      ((cert.modified_adjacency _ _).2 (AllowedSubtileIncidence.BF0m1 0 0).symm)

private theorem row3 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let K : Int → Int → Finset PeriodicSubtileIndex := fun m n ↦
          {⟨.A, m, n⟩, ⟨.B, m, n⟩, ⟨.C, m, n⟩,
            ⟨.D, m, n⟩, ⟨.E, m, n⟩, ⟨.F, m, n⟩}
        let blockTile (m n : Int) : ProtoTile :=
          ⟨(K m n).biUnion (fun a => (cert.modified.tile a).cells), 0⟩
        (∀ (ρ : Finset (Int × Int)), (ρ ∈ ({ {(0,0),(1,0),(0,-1)}, {(0,0),(0,1),(1,1)},
            {(0,0),(-1,-1),(-1,0)} } : Finset (Finset (Int × Int)))) → (∀ (a : Int × Int), ∀ (b :
            Int × Int), ∀ (c : Int × Int), (ρ = {a,b,c}) → (((a.1,a.2) ≠ (b.1,b.2)) → (((b.1,b.2)
            ≠ (c.1,c.2)) → (((c.1,c.2) ≠ (a.1,a.2)) → (((FootprintEdges (blockTile a.1 a.2) ∩
            FootprintEdges (blockTile b.1 b.2)).Nonempty) → (((FootprintEdges (blockTile b.1 b.2)
            ∩ FootprintEdges (blockTile c.1 c.2)).Nonempty) → (((FootprintEdges (blockTile c.1
            c.2) ∩ FootprintEdges (blockTile a.1 a.2)).Nonempty) → (Nonempty
            (ExactTileInterfaceTriple (blockTile a.1 a.2) (blockTile b.1 b.2) (blockTile c.1
            c.2))))))))))) → ((∀ (a : PeriodicSubtileIndex), ∀ (b : PeriodicSubtileIndex), ∀ (m :
            Int), ∀ (n : Int), ∀ (r : Int), ∀ (s : Int), (a ∈ K m n) → ((b ∈ K r s) →
            ((cert.modified.plane.adjacent a b) → ((FootprintEdges (blockTile m n) ∩
            FootprintEdges (blockTile r s)).Nonempty)))) → (
        Nonempty (ExactTileInterfaceTriple (blockTile 0 0) (blockTile (-1) (-1)) (blockTile (-1)
            0)))) ) := by
  classical
  intro q cfg C₀ T cert K blockTile rowJunction blockEdge
  let τ3 : Finset (Int × Int) := {(0,0),(-1,-1),(-1,0)}
  apply rowJunction τ3 (by simp [τ3]) (0,0) (-1,-1) (-1,0) (by ext; simp [τ3])
    (by decide) (by decide) (by decide) ?_ ?_ ?_
  · exact blockEdge ⟨.B,0,0⟩ ⟨.D,-1,-1⟩ 0 0 (-1) (-1) (by simp [K]) (by simp [K])
      ((cert.modified_adjacency _ _).2 (AllowedSubtileIncidence.BDm1m1 0 0))
  · exact blockEdge ⟨.A,-1,-1⟩ ⟨.E,-1,0⟩ (-1) (-1) (-1) 0 (by simp [K]) (by simp [K])
      ((cert.modified_adjacency _ _).2 (AllowedSubtileIncidence.AE01 (-1) (-1)))
  · exact blockEdge ⟨.D,-1,0⟩ ⟨.F,0,0⟩ (-1) 0 0 0 (by simp [K]) (by simp [K])
      ((cert.modified_adjacency _ _).2 (AllowedSubtileIncidence.DF10 (-1) 0))

private theorem blockNonempty :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let K : Int → Int → Finset PeriodicSubtileIndex := fun m n ↦
          {⟨.A, m, n⟩, ⟨.B, m, n⟩, ⟨.C, m, n⟩,
            ⟨.D, m, n⟩, ⟨.E, m, n⟩, ⟨.F, m, n⟩}
        let blockTile (m n : Int) : ProtoTile :=
          ⟨(K m n).biUnion (fun a => (cert.modified.tile a).cells), 0⟩
        (∀ (m : Int), ∀ (n : Int), (blockTile m n).cells = (TileTranslation T ((m : GaussianInt)
            * cert.u + (n : GaussianInt) * cert.v)).cells) → ((T.cells.Nonempty) → (∀ (m : Int),
            ∀ (n : Int), (blockTile m n).cells.Nonempty)) ) := by
  classical
  intro q cfg C₀ T cert K blockTile blockEq rootNe m n
  rw [blockEq m n]
  apply Finset.nonempty_iff_ne_empty.mpr
  intro hempty
  exact (Finset.nonempty_iff_ne_empty.mp rootNe)
    ((TileTranslationFormulas T
      ((m : GaussianInt) * cert.u + (n : GaussianInt) * cert.v)).2.2.1.mp hempty)

private theorem block00T :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let K : Int → Int → Finset PeriodicSubtileIndex := fun m n ↦
          {⟨.A, m, n⟩, ⟨.B, m, n⟩, ⟨.C, m, n⟩,
            ⟨.D, m, n⟩, ⟨.E, m, n⟩, ⟨.F, m, n⟩}
        let blockTile (m n : Int) : ProtoTile :=
          ⟨(K m n).biUnion (fun a => (cert.modified.tile a).cells), 0⟩
        (∀ (m : Int), ∀ (n : Int), (blockTile m n).cells = (TileTranslation T ((m : GaussianInt)
            * cert.u + (n : GaussianInt) * cert.v)).cells) → (((TileTranslation T 0).cells =
            T.cells) → ((blockTile 0 0).cells = T.cells)) ) := by
  classical
  intro q cfg C₀ T cert K blockTile blockEq hzero
  have hA0 : (blockTile 0 0).cells = (TileTranslation T 0).cells := by
    simpa only [Int.cast_zero, zero_mul, zero_add] using blockEq 0 0
  exact hA0.trans hzero

private theorem htransNegV :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let K : Int → Int → Finset PeriodicSubtileIndex := fun m n ↦
          {⟨.A, m, n⟩, ⟨.B, m, n⟩, ⟨.C, m, n⟩,
            ⟨.D, m, n⟩, ⟨.E, m, n⟩, ⟨.F, m, n⟩}
        let blockTile (m n : Int) : ProtoTile :=
          ⟨(K m n).biUnion (fun a => (cert.modified.tile a).cells), 0⟩
        (∀ (m : Int), ∀ (n : Int), (blockTile m n).cells = (TileTranslation T ((m : GaussianInt)
            * cert.u + (n : GaussianInt) * cert.v)).cells) → ((blockTile 0 (-1)).cells =
            (TileTranslation T (-cert.v)).cells) ) := by
  classical
  intro q cfg C₀ T cert K blockTile blockEq
  simpa only [Int.cast_zero, Int.cast_neg, Int.cast_one, zero_mul, neg_one_mul,
    zero_add] using blockEq 0 (-1)

private theorem htransNegUV :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let K : Int → Int → Finset PeriodicSubtileIndex := fun m n ↦
          {⟨.A, m, n⟩, ⟨.B, m, n⟩, ⟨.C, m, n⟩,
            ⟨.D, m, n⟩, ⟨.E, m, n⟩, ⟨.F, m, n⟩}
        let blockTile (m n : Int) : ProtoTile :=
          ⟨(K m n).biUnion (fun a => (cert.modified.tile a).cells), 0⟩
        (∀ (m : Int), ∀ (n : Int), (blockTile m n).cells = (TileTranslation T ((m : GaussianInt)
            * cert.u + (n : GaussianInt) * cert.v)).cells) → ((blockTile (-1) (-1)).cells =
            (TileTranslation T (-cert.u - cert.v)).cells) ) := by
  classical
  intro q cfg C₀ T cert K blockTile blockEq
  simpa only [Int.cast_neg, Int.cast_one, neg_one_mul, sub_eq_add_neg] using
    blockEq (-1) (-1)

private theorem htransNegU :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let K : Int → Int → Finset PeriodicSubtileIndex := fun m n ↦
          {⟨.A, m, n⟩, ⟨.B, m, n⟩, ⟨.C, m, n⟩,
            ⟨.D, m, n⟩, ⟨.E, m, n⟩, ⟨.F, m, n⟩}
        let blockTile (m n : Int) : ProtoTile :=
          ⟨(K m n).biUnion (fun a => (cert.modified.tile a).cells), 0⟩
        (∀ (m : Int), ∀ (n : Int), (blockTile m n).cells = (TileTranslation T ((m : GaussianInt)
            * cert.u + (n : GaussianInt) * cert.v)).cells) → ((blockTile (-1) 0).cells =
            (TileTranslation T (-cert.u)).cells) ) := by
  classical
  intro q cfg C₀ T cert K blockTile blockEq
  simpa only [Int.cast_neg, Int.cast_one, neg_one_mul, Int.cast_zero, zero_mul,
    add_zero] using blockEq (-1) 0

private theorem row1T :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let K : Int → Int → Finset PeriodicSubtileIndex := fun m n ↦
          {⟨.A, m, n⟩, ⟨.B, m, n⟩, ⟨.C, m, n⟩,
            ⟨.D, m, n⟩, ⟨.E, m, n⟩, ⟨.F, m, n⟩}
        let blockTile (m n : Int) : ProtoTile :=
          ⟨(K m n).biUnion (fun a => (cert.modified.tile a).cells), 0⟩
        ∀ [Nonempty (ExactTileInterfaceTriple (blockTile 0 0) (blockTile 1 0) (blockTile 0
            (-1)))], (∀ (m : Int), ∀ (n : Int), (blockTile m n).cells.Nonempty) → (((blockTile 0
            0).cells = T.cells) → (((blockTile 1 0).cells = (TileTranslation T cert.u).cells) →
            (((blockTile 0 (-1)).cells = (TileTranslation T (-cert.v)).cells) → (Nonempty
            (ExactTileInterfaceTriple T (TileTranslation T cert.u) (TileTranslation T
            (-cert.v))))))) ) := by
  classical
  intro q cfg C₀ T cert K blockTile row1 blockNonempty block00T htransU htransNegV
  let retargetTriple := retargetNonemptyTriple
  obtain ⟨E⟩ := row1
  exact ⟨retargetTriple (blockTile 0 0) T (blockTile 1 0) (TileTranslation T cert.u)
    (blockTile 0 (-1)) (TileTranslation T (-cert.v))
    block00T (blockNonempty 0 0) htransU (blockNonempty 1 0)
    htransNegV (blockNonempty 0 (-1)) E⟩

private theorem row3T :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T),
        let K : Int → Int → Finset PeriodicSubtileIndex := fun m n ↦
          {⟨.A, m, n⟩, ⟨.B, m, n⟩, ⟨.C, m, n⟩,
            ⟨.D, m, n⟩, ⟨.E, m, n⟩, ⟨.F, m, n⟩}
        let blockTile (m n : Int) : ProtoTile :=
          ⟨(K m n).biUnion (fun a => (cert.modified.tile a).cells), 0⟩
        ∀ [Nonempty (ExactTileInterfaceTriple (blockTile 0 0) (blockTile (-1) (-1))
            (blockTile (-1) 0))], (∀ (m : Int), ∀ (n : Int), (blockTile m n).cells.Nonempty) →
            (((blockTile 0 0).cells = T.cells) → (((blockTile (-1) (-1)).cells = (TileTranslation
            T (-cert.u - cert.v)).cells) → (((blockTile (-1) 0).cells = (TileTranslation T
            (-cert.u)).cells) → (Nonempty (ExactTileInterfaceTriple T (TileTranslation T (-cert.u
            - cert.v)) (TileTranslation T (-cert.u))))))) ) := by
  classical
  intro q cfg C₀ T cert K blockTile row3 blockNonempty block00T htransNegUV htransNegU
  let retargetTriple := retargetNonemptyTriple
  obtain ⟨E⟩ := row3
  exact ⟨retargetTriple (blockTile 0 0) T (blockTile (-1) (-1))
    (TileTranslation T (-cert.u - cert.v)) (blockTile (-1) 0)
    (TileTranslation T (-cert.u)) block00T (blockNonempty 0 0)
    htransNegUV (blockNonempty (-1) (-1)) htransNegU (blockNonempty (-1) 0) E⟩

private theorem hturn1 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), (∀ (z : GaussianInt), GaussianQuarterTurn z = (⟨0,1⟩ : GaussianInt) * z) → ((∀
            (j : Fin (3 : ℕ)), BandVectors.1 (q (0 : Fin (4 : ℕ))) (q j.succ) = (⟨(0 : ℤ), (1 :
            ℤ)⟩ : GaussianInt) * BandVectors.1 (q j.succ) (q (0 : Fin (4 : ℕ))) ∧ BandVectors.2
            (q (0 : Fin (4 : ℕ))) (q j.succ) = -(⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) *
            BandVectors.2 (q j.succ) (q (0 : Fin (4 : ℕ)))) → (GaussianQuarterTurn (BandVectors.1
            (q 1) (q 0)) = cert.u)) ) := by
  classical
  intro q cfg C₀ T cert hmul hflip
  rw [hmul, cert.period_u]
  simpa using (hflip 0).1.symm

private theorem hturn2 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), (∀ (z : GaussianInt), GaussianQuarterTurn z = (⟨0,1⟩ : GaussianInt) * z) → ((∀
            (j : Fin (3 : ℕ)), BandVectors.1 (q (0 : Fin (4 : ℕ))) (q j.succ) = (⟨(0 : ℤ), (1 :
            ℤ)⟩ : GaussianInt) * BandVectors.1 (q j.succ) (q (0 : Fin (4 : ℕ))) ∧ BandVectors.2
            (q (0 : Fin (4 : ℕ))) (q j.succ) = -(⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) *
            BandVectors.2 (q j.succ) (q (0 : Fin (4 : ℕ)))) → (GaussianQuarterTurn (BandVectors.1
            (q 2) (q 0)) = cert.v)) ) := by
  classical
  intro q cfg C₀ T cert hmul hflip
  rw [hmul, cert.period_v]
  simpa using (hflip 1).1.symm


private theorem hthird :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), (BandVectors.1 (q 1) (q 0) + BandVectors.1 (q 2) (q 0)
            + BandVectors.1 (q 3) (q 0) = 0) → (BandVectors.1 (q 3) (q 0) = -BandVectors.1 (q 1)
            (q 0) - BandVectors.1 (q 2) (q 0)) ) := by
  classical
  intro q hsum
  linear_combination hsum

private theorem qneg3 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), (∀ (z : GaussianInt), GaussianQuarterTurn z = (⟨0,1⟩ : GaussianInt) * z) →
            ((GaussianQuarterTurn (BandVectors.1 (q 3) (q 0)) = -cert.u - cert.v) →
            (GaussianQuarterTurn (-BandVectors.1 (q 3) (q 0)) = cert.u + cert.v)) ) := by
  classical
  intro q cfg C₀ T cert hmul hturn3
  rw [hmul, mul_neg, ← hmul, hturn3]
  simp [add_comm]

private theorem qfour :
    (by
      classical
      exact
        ∀ (z : GaussianInt), GaussianQuarterTurn (GaussianQuarterTurn (GaussianQuarterTurn
            (GaussianQuarterTurn z))) = z ) := by
  classical
  intro z
  ext <;> simp [GaussianQuarterTurn]

private theorem turnThree :
    (by
      classical
      exact
        ∀ (T : ProtoTile), (QuarterTurnSymmetric T) → (∀ (a : GaussianInt), ∀ (b : GaussianInt),
            (ExactTileInterfaceTriple T (TileTranslation T a) (TileTranslation T b)) → (Nonempty
            (ExactTileInterfaceTriple T (TileTranslation T (GaussianQuarterTurn
            (GaussianQuarterTurn (GaussianQuarterTurn a)))) (TileTranslation T
            (GaussianQuarterTurn (GaussianQuarterTurn (GaussianQuarterTurn b))))))) ) := by
  classical
  intro T hsym a b E
  obtain ⟨g, hg, E1, hp1, ha1, hb1, hc1⟩ :=
    QuarterTurnSymmetricExactInterfaceTransport T a b E hsym
  obtain ⟨g, hg, E2, hp2, ha2, hb2, hc2⟩ :=
    QuarterTurnSymmetricExactInterfaceTransport T (GaussianQuarterTurn a)
      (GaussianQuarterTurn b) E1 hsym
  obtain ⟨g, hg, E3, hp3, ha3, hb3, hc3⟩ :=
    QuarterTurnSymmetricExactInterfaceTransport T
      (GaussianQuarterTurn (GaussianQuarterTurn a))
      (GaussianQuarterTurn (GaussianQuarterTurn b)) E2 hsym
  exact ⟨E3⟩

private theorem hback1 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), (GaussianQuarterTurn (BandVectors.1 (q 1) (q 0)) = cert.u) →
            (GaussianQuarterTurn (GaussianQuarterTurn (GaussianQuarterTurn cert.u)) =
            BandVectors.1 (q 1) (q 0)) ) := by
  classical
  intro q cfg C₀ T cert hturn1
  rw [← hturn1]
  simp [GaussianQuarterTurn]

private theorem hback2 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), (GaussianQuarterTurn (BandVectors.1 (q 2) (q 0)) = cert.v) →
            (GaussianQuarterTurn (GaussianQuarterTurn (GaussianQuarterTurn cert.v)) =
            BandVectors.1 (q 2) (q 0)) ) := by
  classical
  intro q cfg C₀ T cert hturn2
  rw [← hturn2]
  simp [GaussianQuarterTurn]

private theorem hback3 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), (GaussianQuarterTurn (BandVectors.1 (q 3) (q 0)) = -cert.u - cert.v) →
            (GaussianQuarterTurn (GaussianQuarterTurn (GaussianQuarterTurn (-cert.u-cert.v))) =
            BandVectors.1 (q 3) (q 0)) ) := by
  classical
  intro q cfg C₀ T cert hturn3
  rw [← hturn3]
  simp [GaussianQuarterTurn]

private theorem hbackNeg1 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), (GaussianQuarterTurn (-BandVectors.1 (q 1) (q 0)) = -cert.u) → ((∀ (z :
            GaussianInt), GaussianQuarterTurn (GaussianQuarterTurn (GaussianQuarterTurn
            (GaussianQuarterTurn z))) = z) → (GaussianQuarterTurn (GaussianQuarterTurn
            (GaussianQuarterTurn (-cert.u))) = -BandVectors.1 (q 1) (q 0))) ) := by
  classical
  intro q cfg C₀ T cert qneg1 qfour
  rw [← qneg1]
  exact qfour _

private theorem hbackNeg2 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), (GaussianQuarterTurn (-BandVectors.1 (q 2) (q 0)) = -cert.v) → ((∀ (z :
            GaussianInt), GaussianQuarterTurn (GaussianQuarterTurn (GaussianQuarterTurn
            (GaussianQuarterTurn z))) = z) → (GaussianQuarterTurn (GaussianQuarterTurn
            (GaussianQuarterTurn (-cert.v))) = -BandVectors.1 (q 2) (q 0))) ) := by
  classical
  intro q cfg C₀ T cert qneg2 qfour
  rw [← qneg2]
  exact qfour _

private theorem hbackNeg3 :
    (by
      classical
      exact
        ∀ (q : Fin 4 → CircleCoordinates), ∀ (cfg : BandOrderedGeneralConfiguration q), ∀ (C₀ :
            BandCircle), ∀ (T : ProtoTile), ∀ (cert : BandOrderedGeneralLayoutCertificate q cfg
            C₀ T), (GaussianQuarterTurn (-BandVectors.1 (q 3) (q 0)) = cert.u + cert.v) → ((∀ (z
            : GaussianInt), GaussianQuarterTurn (GaussianQuarterTurn (GaussianQuarterTurn
            (GaussianQuarterTurn z))) = z) → (GaussianQuarterTurn (GaussianQuarterTurn
            (GaussianQuarterTurn (cert.u+cert.v))) = -BandVectors.1 (q 3) (q 0))) ) := by
  classical
  intro q cfg C₀ T cert qneg3 qfour
  rw [← qneg3]
  exact qfour _

end ChildInterfaceGeometry

theorem BandOrderedGeneralChildInterfaces
    (q : Fin 4 → CircleCoordinates)
    (cfg : BandOrderedGeneralConfiguration q)
    (C₀ : BandCircle) (T : ProtoTile)
    (cert : BandOrderedGeneralLayoutCertificate q cfg C₀ T)
    (hsym : QuarterTurnSymmetric T) :
    (∀ i : Fin 3, Nonempty (ExactTileInterfaceTriple T
      (TileTranslation T (BandVectors.1 (q i.succ) (q 0)))
      (TileTranslation T (-BandVectors.1 (q ((i + 1).succ)) (q 0))))) ∧
    (∀ (i : Fin 3) (U : ProtoTile), BandPrototile (q i.succ) U →
      TileCentroid U - TileCentroid T = (1 / 2 : Real) •
        (GaussianRealPoint (BandVectors.1 (q i.succ) (q 0)) +
          GaussianRealPoint (BandVectors.1 (q 0) (q i.succ))) →
      Nonempty (ExactTileInterfaceTriple T
        (TileTranslation T (BandVectors.1 (q i.succ) (q 0))) U)) ∧
    (∀ (i : Fin 3) (U V : ProtoTile), BandPrototile (q i.succ) U →
      BandPrototile (q ((i + 1).succ)) V →
      TileCentroid U - TileCentroid T = (1 / 2 : Real) •
        (GaussianRealPoint (BandVectors.1 (q i.succ) (q 0)) +
          GaussianRealPoint (BandVectors.1 (q 0) (q i.succ))) →
      TileCentroid V - TileCentroid T = (1 / 2 : Real) •
        (GaussianRealPoint (BandVectors.1 (q ((i + 1).succ)) (q 0)) -
          GaussianRealPoint (BandVectors.1 (q 0) (q ((i + 1).succ)))) →
      Nonempty (ExactTileInterfaceTriple T U V)) ∧
    (∀ (i : Fin 3) (s : Fin 4) (U V : ProtoTile),
      BandPrototile (q i.succ) U →
      BandPrototile
        (q ((if Even s.val then i + 1 else i - 1).succ)) V →
      TileCentroid U - TileCentroid T = (1 / 2 : Real) •
        GaussianRealPoint
          ((⟨0, 1⟩ : GaussianInt) ^ s.val *
            (BandVectors.1 (q i.succ) (q 0) +
              BandVectors.1 (q 0) (q i.succ))) →
      TileCentroid V - TileCentroid T = (1 / 2 : Real) •
        GaussianRealPoint
          ((⟨0, 1⟩ : GaussianInt) ^ s.val *
            (if Even s.val then
              BandVectors.1 (q ((i + 1).succ)) (q 0) -
                BandVectors.1 (q 0) (q ((i + 1).succ))
            else
              BandVectors.1 (q 0) (q ((i - 1).succ)) -
                BandVectors.1 (q ((i - 1).succ)) (q 0))) →
      let uR := (⟨0, 1⟩ : GaussianInt) ^ s.val *
        (if Even s.val then BandVectors.1 (q 0) (q i.succ)
          else BandVectors.1 (q i.succ) (q 0))
      let uL := (⟨0, 1⟩ : GaussianInt) ^ s.val *
        (if Even s.val then BandVectors.1 (q i.succ) (q 0)
          else BandVectors.1 (q 0) (q i.succ))
      ∃ rightData : ExactTileInterfaceTriple T (TileTranslation T uR) U,
        ∃ incomingData : ExactTileInterfaceTriple T (TileTranslation T uL) U,
          ∃ t5Data : ExactTileInterfaceTriple T U V,
            rightData.point = t5Data.point ∧
            incomingData.point ≠ t5Data.point ∧
            incomingData.otherCA = t5Data.point ∧
            rightData.otherCA = incomingData.point ∧
            t5Data.otherAB = incomingData.point) := by
-- BODY
  classical
  have mixed := BandOrderedGeneralMixedAggregatePatches q cfg C₀ T cert hsym
  have first_parent := ChildInterfaceGeometry.first_parent q T mixed
  have parent_pair := ChildInterfaceGeometry.parent_pair q T mixed
  let K : Int → Int → Finset PeriodicSubtileIndex := fun m n ↦
    {⟨.A, m, n⟩, ⟨.B, m, n⟩, ⟨.C, m, n⟩,
      ⟨.D, m, n⟩, ⟨.E, m, n⟩, ⟨.F, m, n⟩}
  let τ : Finset (Int × Int) := {(0, 0), (0, 1), (1, 1)}
  let aggregate := BandOrderedGeneralAggregatePatches q cfg C₀ T cert
  have aggregate' := aggregate
  dsimp only at aggregate'
  have patchFor (σ : Finset (Int × Int)) (hσ : σ ⊆ τ)
      (hne : σ.Nonempty) :
      ∃ p : FiniteInducedTilePatch cert.modified.plane cert.modified.tile,
        p.indices = σ.biUnion (fun mn => K mn.1 mn.2) ∧
        ∀ x, x ∈ p.unionTile.cells ↔
          ∃ mn ∈ σ, ∃ a ∈ K mn.1 mn.2, x ∈ (cert.modified.tile a).cells :=
              ChildInterfaceGeometry.patchFor q cfg C₀ T cert aggregate'
                  (ChildInterfaceGeometry.τmem) σ hσ hne
  have patchForAt := ChildInterfaceGeometry.patchForAt q cfg C₀ T cert aggregate'
  let blockTile (m n : Int) : ProtoTile :=
    ⟨(K m n).biUnion (fun a => (cert.modified.tile a).cells), 0⟩
  have blockEq (m n : Int) : (blockTile m n).cells =
      (TileTranslation T ((m : GaussianInt) * cert.u +
        (n : GaussianInt) * cert.v)).cells := ChildInterfaceGeometry.blockEq q cfg C₀ T cert m n
  have blockDisjoint := ChildInterfaceGeometry.blockDisjoint q cfg C₀ T cert blockEq
  have patchUnion := (show
      ∀ (p : FiniteInducedTilePatch cert.modified.plane cert.modified.tile), ∀ (σ : Finset
      (Int × Int)), (p.indices = σ.biUnion (fun mn => K mn.1 mn.2)) → ((∀ x, x ∈
      p.unionTile.cells ↔ ∃ mn ∈ σ, ∃ a ∈ K mn.1 mn.2, x ∈ (cert.modified.tile a).cells) →
      (∀ x, x ∈ p.unionTile.cells ↔ ∃ mn ∈ σ, x ∈ (blockTile mn.1 mn.2).cells))
    from by
      classical
      intro p σ hp he x
      rw [he x]
      simp only [blockTile, Finset.mem_biUnion])
  let σA : Finset (Int × Int) := {(0,0)}
  let σB : Finset (Int × Int) := {(0,1)}
  let σC : Finset (Int × Int) := {(1,1)}
  let σAB : Finset (Int × Int) := {(0,0),(0,1)}
  let σBC : Finset (Int × Int) := {(0,1),(1,1)}
  let σCA : Finset (Int × Int) := {(1,1),(0,0)}
  obtain ⟨pA, hpA, hexA⟩ := patchFor σA (by decide) (by simp [σA])
  obtain ⟨pB, hpB, hexB⟩ := patchFor σB (by decide) (by simp [σB])
  obtain ⟨pC, hpC, hexC⟩ := patchFor σC (by decide) (by simp [σC])
  obtain ⟨pAB, hpAB, hexAB⟩ := patchFor σAB (by decide) (by simp [σAB])
  obtain ⟨pBC, hpBC, hexBC⟩ := patchFor σBC (by decide) (by simp [σBC])
  obtain ⟨pCA, hpCA, hexCA⟩ := patchFor σCA (by decide) (by simp [σCA])
  obtain ⟨pABC, hpABC, hexABC⟩ := patchFor τ (by decide) (by simp [τ])
  have hLA := FinitePatchTopology cert.modified.plane cert.modified.tile
    (PeriodicTileMultiplicityOne cert.modified)
    (PeriodicTileIndexedMultiplicityOne cert.modified)
    (fun a b hne hadj => cert.modified.adjacent_has_common_edge a b hadj) pA
  have hLB := FinitePatchTopology cert.modified.plane cert.modified.tile
    (PeriodicTileMultiplicityOne cert.modified)
    (PeriodicTileIndexedMultiplicityOne cert.modified)
    (fun a b hne hadj => cert.modified.adjacent_has_common_edge a b hadj) pB
  have hLC := FinitePatchTopology cert.modified.plane cert.modified.tile
    (PeriodicTileMultiplicityOne cert.modified)
    (PeriodicTileIndexedMultiplicityOne cert.modified)
    (fun a b hne hadj => cert.modified.adjacent_has_common_edge a b hadj) pC
  have hLAB := FinitePatchTopology cert.modified.plane cert.modified.tile
    (PeriodicTileMultiplicityOne cert.modified)
    (PeriodicTileIndexedMultiplicityOne cert.modified)
    (fun a b hne hadj => cert.modified.adjacent_has_common_edge a b hadj) pAB
  have hLBC := FinitePatchTopology cert.modified.plane cert.modified.tile
    (PeriodicTileMultiplicityOne cert.modified)
    (PeriodicTileIndexedMultiplicityOne cert.modified)
    (fun a b hne hadj => cert.modified.adjacent_has_common_edge a b hadj) pBC
  have hLCA := FinitePatchTopology cert.modified.plane cert.modified.tile
    (PeriodicTileMultiplicityOne cert.modified)
    (PeriodicTileIndexedMultiplicityOne cert.modified)
    (fun a b hne hadj => cert.modified.adjacent_has_common_edge a b hadj) pCA
  have hLABC := FinitePatchTopology cert.modified.plane cert.modified.tile
    (PeriodicTileMultiplicityOne cert.modified)
    (PeriodicTileIndexedMultiplicityOne cert.modified)
    (fun a b hne hadj => cert.modified.adjacent_has_common_edge a b hadj) pABC
  have hdisjAB : Disjoint (blockTile 0 0).cells (blockTile 0 1).cells :=
    blockDisjoint 0 0 0 1 (by decide)
  have hdisjBC : Disjoint (blockTile 0 1).cells (blockTile 1 1).cells :=
    blockDisjoint 0 1 1 1 (by decide)
  have hdisjCA : Disjoint (blockTile 1 1).cells (blockTile 0 0).cells :=
    blockDisjoint 1 1 0 0 (by decide)
  have blockLattice := ChildInterfaceGeometry.blockLattice q cfg C₀ T cert
  have hLA' := blockLattice 0 0 pA (ChildInterfaceGeometry.hUA q cfg C₀ T cert patchUnion pA hpA
      hexA) hLA
  have hLB' := blockLattice 0 1 pB (ChildInterfaceGeometry.hUB q cfg C₀ T cert patchUnion pB hpB
      hexB) hLB
  have hLC' := blockLattice 1 1 pC (ChildInterfaceGeometry.hUC q cfg C₀ T cert patchUnion pC hpC
      hexC) hLC
  have blockJunction := ChildInterfaceGeometry.blockJunction q
          cfg C₀ T cert pAB pBC pCA pABC hLAB hLBC hLCA hLABC (ChildInterfaceGeometry.hUAB q cfg
              C₀ T cert patchUnion pAB hpAB hexAB) (ChildInterfaceGeometry.hUBC q cfg C₀ T cert
              patchUnion pBC hpBC hexBC) (ChildInterfaceGeometry.hUCA q cfg C₀ T cert patchUnion
              pCA hpCA hexCA) (ChildInterfaceGeometry.hUABC q cfg C₀ T cert patchUnion pABC hpABC
              hexABC) hdisjAB
          hdisjBC hdisjCA (ChildInterfaceGeometry.hcommonAB q cfg C₀ T cert)
              (ChildInterfaceGeometry.hcommonBC q cfg C₀ T cert)
              (ChildInterfaceGeometry.hcommonCA q cfg C₀ T cert) hLA' hLB' hLC'
  have hzero : (TileTranslation T 0).cells = T.cells := ChildInterfaceGeometry.hzero T
  have rootNe : T.cells.Nonempty := ChildInterfaceGeometry.rootNe q cfg C₀ T cert blockEq hLA' hzero
  have transZeroNe : (TileTranslation T 0).cells.Nonempty := by
    simpa [hzero] using rootNe
  have blockBne : (blockTile 0 1).cells.Nonempty :=
    (LatticeTileGridStructure _ hLB').1.1
  have blockCne : (blockTile 1 1).cells.Nonempty :=
    (LatticeTileGridStructure _ hLC').1.1
  have row2 := @ChildInterfaceGeometry.row2 q cfg C₀ T cert blockEq blockJunction
          hzero (ChildInterfaceGeometry.blockAne q cfg C₀ T cert blockEq transZeroNe) blockBne
              blockCne
  have rowJunction := ChildInterfaceGeometry.rowJunction q cfg C₀ T cert patchForAt blockDisjoint
      patchUnion blockLattice
  have blockEdge := ChildInterfaceGeometry.blockEdge q cfg C₀ T cert
  have row1 := ChildInterfaceGeometry.row1 q cfg C₀ T cert
          rowJunction blockEdge
  have row3 := ChildInterfaceGeometry.row3 q cfg C₀ T cert
          rowJunction blockEdge
  have blockNonempty := ChildInterfaceGeometry.blockNonempty q cfg C₀ T cert blockEq rootNe
  have block00T := ChildInterfaceGeometry.block00T q cfg C₀ T
      cert blockEq hzero
  have htransU : (blockTile 1 0).cells = (TileTranslation T cert.u).cells := by
    simpa only [Int.cast_one, Int.cast_zero, one_mul, zero_mul, add_zero] using blockEq 1 0
  have row1T := @ChildInterfaceGeometry.row1T q
          cfg C₀ T cert row1 blockNonempty block00T htransU
              (ChildInterfaceGeometry.htransNegV q cfg C₀ T cert blockEq)
  have row3T := @ChildInterfaceGeometry.row3T q cfg C₀ T cert row3 blockNonempty block00T
          (ChildInterfaceGeometry.htransNegUV q cfg C₀ T cert blockEq)
              (ChildInterfaceGeometry.htransNegU q cfg C₀ T cert blockEq)
  have hmul (z : GaussianInt) : GaussianQuarterTurn z = (⟨0,1⟩ : GaussianInt) * z := by
    ext <;> simp [GaussianQuarterTurn]
  have hflip := (VectorRecursionLaws q cfg.proper.1).2.2.2.2 cfg.proper
  have hturn1 : GaussianQuarterTurn (BandVectors.1 (q 1) (q 0)) = cert.u :=
      ChildInterfaceGeometry.hturn1 q cfg C₀ T cert hmul hflip
  have hturn2 : GaussianQuarterTurn (BandVectors.1 (q 2) (q 0)) = cert.v :=
      ChildInterfaceGeometry.hturn2 q cfg C₀ T cert hmul hflip
  have hthird : BandVectors.1 (q 3) (q 0) =
      -BandVectors.1 (q 1) (q 0) - BandVectors.1 (q 2) (q 0) := ChildInterfaceGeometry.hthird q
          (OrderedParentVectorSum.incoming q cfg)
  have hturn3 : GaussianQuarterTurn (BandVectors.1 (q 3) (q 0)) = -cert.u - cert.v := by
    rw [hthird, hmul, mul_sub, mul_neg, ← hmul, ← hmul, hturn1, hturn2]
  have qneg1 : GaussianQuarterTurn (-BandVectors.1 (q 1) (q 0)) = -cert.u := by
    rw [hmul, mul_neg, ← hmul, hturn1]
  have qneg2 : GaussianQuarterTurn (-BandVectors.1 (q 2) (q 0)) = -cert.v := by
    rw [hmul, mul_neg, ← hmul, hturn2]
  have qfour := ChildInterfaceGeometry.qfour
  have turnThree := ChildInterfaceGeometry.turnThree T hsym
  have hback1 : GaussianQuarterTurn (GaussianQuarterTurn
      (GaussianQuarterTurn cert.u)) = BandVectors.1 (q 1) (q 0) := ChildInterfaceGeometry.hback1
          q cfg C₀ T cert hturn1
  have hback2 : GaussianQuarterTurn (GaussianQuarterTurn
      (GaussianQuarterTurn cert.v)) = BandVectors.1 (q 2) (q 0) := ChildInterfaceGeometry.hback2
          q cfg C₀ T cert hturn2
  have hback3 : GaussianQuarterTurn (GaussianQuarterTurn
      (GaussianQuarterTurn (-cert.u-cert.v))) = BandVectors.1 (q 3) (q 0) :=
          ChildInterfaceGeometry.hback3 q cfg C₀ T cert hturn3
  have hbackNeg1 : GaussianQuarterTurn (GaussianQuarterTurn
      (GaussianQuarterTurn (-cert.u))) = -BandVectors.1 (q 1) (q 0) :=
          ChildInterfaceGeometry.hbackNeg1 q cfg C₀ T cert qneg1 qfour
  have hbackNeg2 : GaussianQuarterTurn (GaussianQuarterTurn
      (GaussianQuarterTurn (-cert.v))) = -BandVectors.1 (q 2) (q 0) :=
          ChildInterfaceGeometry.hbackNeg2 q cfg C₀ T cert qneg2 qfour
  have hbackNeg3 : GaussianQuarterTurn (GaussianQuarterTurn
      (GaussianQuarterTurn (cert.u+cert.v))) = -BandVectors.1 (q 3) (q 0) :=
          ChildInterfaceGeometry.hbackNeg3 q cfg C₀ T cert (ChildInterfaceGeometry.qneg3 q cfg C₀
              T cert hmul hturn3) qfour
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · obtain ⟨E⟩ := row1T
      obtain ⟨E⟩ := turnThree cert.u (-cert.v) E
      exact ⟨by simpa [Fin.add_def] using (show ExactTileInterfaceTriple T
        (TileTranslation T (BandVectors.1 (q 1) (q 0)))
        (TileTranslation T (-BandVectors.1 (q 2) (q 0))) from by
          simpa only [hback1, hbackNeg2] using E)⟩
    · obtain ⟨E⟩ := row2
      obtain ⟨E⟩ := turnThree cert.v (cert.u + cert.v) E
      exact ⟨by simpa [Fin.add_def] using (show ExactTileInterfaceTriple T
        (TileTranslation T (BandVectors.1 (q 2) (q 0)))
        (TileTranslation T (-BandVectors.1 (q 3) (q 0))) from by
          simpa only [hback2, hbackNeg3] using E)⟩
    · obtain ⟨E⟩ := row3T
      obtain ⟨E⟩ := turnThree (-cert.u-cert.v) (-cert.u) E
      exact ⟨by simpa [Fin.add_def] using (show ExactTileInterfaceTriple T
        (TileTranslation T (BandVectors.1 (q 3) (q 0)))
        (TileTranslation T (-BandVectors.1 (q 1) (q 0))) from by
          simpa only [hback3, hbackNeg1] using E)⟩
  · intro i U hU hc
    exact first_parent i U hU hc
  · intro i U V hU hV hcU hcV
    exact parent_pair i U V hU hV hcU hcV
  · intro i s U V hU hV hcU hcV
    exact mixed.2.2 i s U V hU hV hcU hcV

end ApollonianSuperharmonic

end
