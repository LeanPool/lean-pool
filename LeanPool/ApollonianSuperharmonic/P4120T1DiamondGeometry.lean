/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.DiamondTileRecursiveIdentification
public import LeanPool.ApollonianSuperharmonic.DiamondVertexDomains
public import LeanPool.ApollonianSuperharmonic.BandSubtileOccurrenceTranslation
public import LeanPool.ApollonianSuperharmonic.BandPrototileCentroidUnique
public import LeanPool.ApollonianSuperharmonic.ProtoTileObservableExtensionality
public import LeanPool.ApollonianSuperharmonic.P4194T1DiamondBoundaryLedger

-- [TABLET NODE: P4120T1DiamondGeometry]

/-!
# P4120T1DiamondGeometry

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4120T1DiamondGeometry
    (K : DiamondParameter) (hK : 1 < K.1)
    (T : ProtoTile) (S : Fin 3 → Bool → ProtoTile) (u : GaussianInt)
    (hcells : T.cells = (TileTranslation (DiamondTile K.1) u).cells)
    (hanchor : T.cells = ∅ → T.anchor = (TileTranslation (DiamondTile K.1) u).anchor)
    (hS : ∀ i s, BandSubtileOccurrence (DiamondRecursiveQuadruple K) T i s (S i s))
    (x : GaussianInt) (hx : x ∈ FootprintVertices T)
    (hxb : x ∉ BoundaryFootprintVertices T) :
    let y := x - u
    let k := Nat.card {a : Fin 3 × Bool // x ∈ BoundaryFootprintVertices (S a.1 a.2)}
    (k = 2 → y ∈ DiamondVertexDomains K true ∧ Even (y.re + y.im) ∧
      (y.re = 0 ↔ GaussianRealPoint x = TileCentroid T) ∧
      (GaussianRealPoint x = TileCentroid T ↔ K.1 = 2)) ∧
    k ≠ 3 ∧
    (k = 4 → y ∈ DiamondVertexDomains K true ∧ ¬ Even (y.re + y.im) ∧
      y.re ≠ 0 ∧ GaussianRealPoint x ≠ TileCentroid T) ∧
    ((k = 2 ∨ k = 3 ∨ k = 4) ∨
      ∃ i : Fin 3, ∃ s : Bool,
        0 < ((DiamondRecursiveQuadruple K) i.succ).1 ∧
        x ∈ FootprintVertices (S i s) ∧ x ∉ BoundaryFootprintVertices (S i s)) := by
-- BODY
  classical
  let y := x - u
  let k := Nat.card {a : Fin 3 × Bool // x ∈ BoundaryFootprintVertices (S a.1 a.2)}
  have translated_mem (A : Set GaussianInt) :
      x ∈ GaussianTranslation u '' A ↔ y ∈ A := by
    constructor
    · rintro ⟨z, hz, heq⟩
      have hyz : y = z := by dsimp [y]; rw [← heq]; simp [GaussianTranslation]
      simpa [hyz] using hz
    · intro hy
      exact ⟨y, hy, sub_add_cancel x u⟩
  have rootObs := ProtoTileObservableExtensionality T
    (TileTranslation (DiamondTile K.1) u) hcells hanchor
  have hyFoot : y ∈ FootprintVertices (DiamondTile K.1) := by
    apply (translated_mem _).mp
    rw [← (TileTranslationFormulas (DiamondTile K.1) u).2.2.2.2.2.1,
      ← rootObs.1]
    exact hx
  have hyNo : y ∉ BoundaryFootprintVertices (DiamondTile K.1) := by
    intro hy
    apply hxb
    rw [rootObs.2.1, (TileTranslationFormulas (DiamondTile K.1) u).2.2.2.2.2.2.2.1]
    exact (translated_mem _).mpr hy
  have incidence := P4194T1DiamondVertexIncidence K.1 K.2 y
  have rootCells : ∀ j : Fin 4, LatticeVertexIncidentCell y j ∈ DiamondCellDomain K.1 := by
    intro j
    by_contra hj
    exact hyNo (incidence.2.mpr ⟨incidence.1.mp hyFoot, j, hj⟩)
  obtain ⟨_, C, hCocc, _, h00, h01, h10, h11, h2f, h2t⟩ :=
    DiamondTileRecursiveIdentification K
  have childObs : ∀ i s,
      FootprintVertices (S i s) = FootprintVertices (TileTranslation (C i s) u) ∧
      BoundaryFootprintVertices (S i s) =
        BoundaryFootprintVertices (TileTranslation (C i s) u) := by
    intro i s
    have hs := hS i s
    have hc := (BandSubtileOccurrenceTranslation
      (DiamondRecursiveQuadruple K) (DiamondTile K.1) (C i s) i s u).mp (hCocc i s)
    have hcent : TileCentroid (S i s) = TileCentroid (TileTranslation (C i s) u) := by
      have hoff := hs.2.2.trans hc.2.2.symm
      calc
        TileCentroid (S i s) =
            (TileCentroid (S i s) - TileCentroid T) + TileCentroid T := by abel
        _ = (TileCentroid (TileTranslation (C i s) u) -
              TileCentroid (TileTranslation (DiamondTile K.1) u)) +
              TileCentroid (TileTranslation (DiamondTile K.1) u) := by
          rw [hoff, rootObs.2.2.2.2]
        _ = TileCentroid (TileTranslation (C i s) u) := by abel
    obtain ⟨heq, ha⟩ := BandPrototileCentroidUnique
      ((DiamondRecursiveQuadruple K) i.succ) (S i s)
      (TileTranslation (C i s) u) hs.1 hc.1 hcent
    have obs := ProtoTileObservableExtensionality (S i s) (TileTranslation (C i s) u) heq ha
    exact ⟨obs.1, obs.2.1⟩
  have childFoot (i : Fin 3) (s : Bool) :
      x ∈ FootprintVertices (S i s) ↔ y ∈ FootprintVertices (C i s) := by
    rw [(childObs i s).1, (TileTranslationFormulas (C i s) u).2.2.2.2.2.1]
    exact translated_mem _
  have childBd (i : Fin 3) (s : Bool) :
      x ∈ BoundaryFootprintVertices (S i s) ↔ y ∈ BoundaryFootprintVertices (C i s) := by
    rw [(childObs i s).2, (TileTranslationFormulas (C i s) u).2.2.2.2.2.2.2.1]
    exact translated_mem _
  have hcount : k = Nat.card {a : Fin 3 × Bool //
      y ∈ BoundaryFootprintVertices (C a.1 a.2)} := by
    apply Nat.card_congr
    refine {
      toFun := fun a => ⟨a.1, (childBd a.1.1 a.1.2).mp a.2⟩
      invFun := fun a => ⟨a.1, (childBd a.1.1 a.1.2).mpr a.2⟩
      left_inv := ?_
      right_inv := ?_ }
    · intro a
      rfl
    · intro a
      rfl
  obtain ⟨htwo, hthree, hfour, _, _, hdes⟩ :=
    P4194T1DiamondBoundaryLedger K.1 hK C h00 h01 h10 h11 h2f h2t y rootCells
  rw [← hcount] at htwo hthree hfour hdes
  have hcent : TileCentroid T = ((u.re : Real), (K.1 : Real) + (u.im : Real)) := by
    rw [rootObs.2.2.2.2, (TileTranslationFormulas (DiamondTile K.1) u).2.2.2.2.1,
      P4194T1DiamondCentroid K.1 K.2]
    simp only [zero_add]
  have hxr : x.re = y.re + u.re := by dsimp [y]; simp
  have hxi : x.im = y.im + u.im := by dsimp [y]; simp
  have pointCent : GaussianRealPoint x = TileCentroid T ↔
      y.re = 0 ∧ y.im = (K.1 : Int) := by
    rw [hcent]
    simp only [GaussianRealPoint, Prod.mk.injEq]
    constructor
    · rintro ⟨hr, hi⟩
      have hr' : x.re = u.re := by exact_mod_cast hr
      have hi' : x.im = (K.1 : Int) + u.im := by exact_mod_cast hi
      constructor <;> omega
    · rintro ⟨hr, hi⟩
      have hr' : x.re = u.re := by omega
      have hi' : x.im = (K.1 : Int) + u.im := by omega
      constructor
      · exact_mod_cast hr'
      · exact_mod_cast hi'
  have inner (hb : y.im = (K.1 : Int))
      (ha : y.re = (K.1 : Int) - 2 ∨ y.re = -((K.1 : Int) - 2) ∨
        y.re = (K.1 : Int) - 1 ∨ y.re = -((K.1 : Int) - 1)) :
      y ∈ DiamondVertexDomains K true := by
    change Int.natAbs y.re + Int.natAbs (y.im - (K.1 : Int)) ≤ K.1 - 1
    rw [hb, sub_self, Int.natAbs_zero, Nat.add_zero]
    rcases ha with ha | ha | ha | ha <;> rw [ha] <;> omega
  refine ⟨?_, hthree, ?_, ?_⟩
  · intro hk
    obtain ⟨hb, ha⟩ := htwo.mp hk
    have heven : Even (y.re + y.im) := by
      rcases ha with ha | ha
      · exact ⟨(K.1 : Int) - 1, by rw [ha, hb]; omega⟩
      · exact ⟨1, by rw [ha, hb]; omega⟩
    have hz : y.re = 0 ↔ K.1 = 2 := by
      rcases ha with ha | ha <;> rw [ha] <;> omega
    have hc : GaussianRealPoint x = TileCentroid T ↔ y.re = 0 := by
      rw [pointCent]
      exact ⟨fun h => h.1, fun h => ⟨h, hb⟩⟩
    exact ⟨inner hb (ha.elim Or.inl (fun h => Or.inr (Or.inl h))), heven,
      hc.symm, hc.trans hz⟩
  · intro hk
    obtain ⟨hb, ha⟩ := hfour.mp hk
    have hodd : ¬ Even (y.re + y.im) := by
      rintro ⟨j, hj⟩
      rcases ha with ha | ha <;> rw [ha, hb] at hj <;> omega
    have hnonzero : y.re ≠ 0 := by
      rcases ha with ha | ha <;> rw [ha] <;> omega
    exact ⟨inner hb (Or.inr (Or.inr ha)), hodd, hnonzero,
      fun h => hnonzero (pointCent.mp h).1⟩
  · rcases hdes with (hk | hk) | ⟨s, hall⟩
    · exact Or.inl (Or.inl hk)
    · exact Or.inl (Or.inr (Or.inr hk))
    · have hne : (C 2 s).cells.Nonempty := ⟨_, hall 0⟩
      have hf : y ∈ FootprintVertices (C 2 s) := by
        rw [FootprintVertices, ite_eq_left hne]
        exact ⟨y, hall 0, Or.inl rfl⟩
      have hn : y ∉ BoundaryFootprintVertices (C 2 s) := by
        intro hb
        simp only [BoundaryFootprintVertices, ite_eq_left hne, Set.mem_ofPred_eq] at hb
        rcases hb with ⟨e, ⟨w, he⟩, hy⟩
        rcases he with ⟨rfl, hw⟩ | ⟨rfl, hw⟩
        · simp only [Finset.mem_insert, Finset.mem_singleton] at hy
          rcases hy with hy | hy
          · rcases hw with ⟨_, ho⟩ | ⟨ho, _⟩
            · exact ho (by simpa [LatticeVertexIncidentCell, hy] using hall 3)
            · exact ho (by simpa [LatticeVertexIncidentCell, hy] using hall 0)
          · rcases hw with ⟨_, ho⟩ | ⟨ho, _⟩
            · exact ho (by simpa [LatticeVertexIncidentCell, hy] using hall 2)
            · exact ho (by simpa [LatticeVertexIncidentCell, hy] using hall 1)
        · simp only [Finset.mem_insert, Finset.mem_singleton] at hy
          rcases hy with hy | hy
          · rcases hw with ⟨_, ho⟩ | ⟨ho, _⟩
            · exact ho (by simpa [LatticeVertexIncidentCell, hy] using hall 1)
            · exact ho (by simpa [LatticeVertexIncidentCell, hy] using hall 0)
          · rcases hw with ⟨_, ho⟩ | ⟨ho, _⟩
            · exact ho (by simpa [LatticeVertexIncidentCell, hy, sub_eq_add_neg,
                add_assoc, add_comm, add_left_comm] using hall 2)
            · exact ho (by simpa [LatticeVertexIncidentCell, hy] using hall 3)
      have hpos : 0 < ((DiamondRecursiveQuadruple K) (Fin.succ 2)).1 := by
        change (0 : Int) < ((2 * (K.1 - 1) * K.1 : Nat) : Int)
        have hKm : 0 < K.1 - 1 := by omega
        have hNat : 0 < 2 * (K.1 - 1) * K.1 :=
          Nat.mul_pos (Nat.mul_pos (by decide) hKm) K.2
        exact_mod_cast hNat
      exact Or.inr ⟨2, s, hpos, (childFoot 2 s).mpr hf,
        fun hb => hn ((childBd 2 s).mp hb)⟩

end ApollonianSuperharmonic

end
