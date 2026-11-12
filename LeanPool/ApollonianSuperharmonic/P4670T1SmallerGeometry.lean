/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandSubtileOccurrence
public import LeanPool.ApollonianSuperharmonic.FordTileGeometry
public import LeanPool.ApollonianSuperharmonic.SemiProperForestClassification
public import LeanPool.ApollonianSuperharmonic.TileDiskAreaCovariance

-- [TABLET NODE: P4670T1SmallerGeometry]

/-!
# P4670T1SmallerGeometry

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4670T1SmallerGeometry (n : Nat)
    (hsmall : ∀ (p : Fin 4 → CircleCoordinates) (V : ProtoTile)
      (S : Fin 3 → Bool → ProtoTile), ProperBandQuadruple p →
      BandPrototile (p 0) V →
      (∀ i s, BandSubtileOccurrence p V i s (S i s)) →
      (∀ x, x ∈ V.cells ↔ ∃ i s, x ∈ (S i s).cells) →
      Int.toNat (p 0).1 < n →
      LatticeTile V ∧ TileArea V = Int.toNat (p 0).1)
    (c : CircleCoordinates) (U : ProtoTile) (hU : BandPrototile c U)
    (hlt : Int.toNat c.1 < n) :
    0 ≤ c.1 ∧ TileArea U = Int.toNat c.1 ∧
      (0 < c.1 → LatticeTile U) := by
-- BODY
  cases hU with
  | line w x hw =>
      simp [TileArea]
  | unit z x anchor =>
      refine ⟨by norm_num, by simp [TileArea], ?_⟩
      intro _
      have hd := ((TileDiskAreaCovariance (FordTile 1) x).1).mp
        (FordTileGeometry 1 (by decide)).1
      have hc : (TileTranslation (FordTile 1) x).cells = {x} := by
        simp [TileTranslation, FordTile, FordCellDomain, GaussianTranslation]
        rfl
      change TopologicalDisk (TileRealization (⟨{x}, anchor⟩ : ProtoTile))
      change TopologicalDisk (TileRealization (TileTranslation (FordTile 1) x)) at hd
      simpa only [TileRealization, hc] using hd
  | @decompose p hp S _ hS hcells hfoot hcent =>
      have hv : BandPrototile (p 0) U :=
        BandPrototile.decompose hp hS hcells hfoot hcent
      have hg := hsmall p U S hp hv (fun i s => ⟨hS i s, hfoot i s, hcent i s⟩)
        hcells hlt
      exact ⟨(SemiProperForestClassification p hp.1).1 0, hg.2, fun _ => hg.1⟩

end ApollonianSuperharmonic

end
