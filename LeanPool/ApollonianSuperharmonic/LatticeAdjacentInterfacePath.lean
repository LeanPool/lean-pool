/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init
public import LeanPool.ApollonianSuperharmonic.TileQuarterTurnTranslation
public import LeanPool.ApollonianSuperharmonic.BandPrototileQuarterTurn
public import LeanPool.ApollonianSuperharmonic.TileOdometerBandPrototile
public import LeanPool.ApollonianSuperharmonic.BandPrototileNonempty

public import LeanPool.ApollonianSuperharmonic.BandTileSimultaneousInduction
public import LeanPool.ApollonianSuperharmonic.RightLatticeAdjacent
public import LeanPool.ApollonianSuperharmonic.SubtileLatticeAdjacent

-- [TABLET NODE: LatticeAdjacentInterfacePath]

/-!
# LatticeAdjacentInterfacePath

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace LatticeInterfacePathGeometry

private theorem incident_boundary :
    (by
      classical
      exact
        ∀ (U : ProtoTile), ∀ (V : ProtoTile), ∀ (x : GaussianInt), (Disjoint U.cells V.cells) →
            ((∃ j : Fin 4, LatticeVertexIncidentCell x j ∈ U.cells) → ((∃ j : Fin 4,
            LatticeVertexIncidentCell x j ∈ V.cells) → (x ∈ BoundaryFootprintVertices U ∧ x ∈
            BoundaryFootprintVertices V))) ) := by
  classical
  intro U V x hd hu hv
  have hd' := Finset.disjoint_left.mp hd
  constructor
  · apply P3161T2IncidentBoundary U x hu
    obtain ⟨j, hj⟩ := hv
    exact ⟨j, fun h => hd' h hj⟩
  · apply P3161T2IncidentBoundary V x hv
    obtain ⟨j, hj⟩ := hu
    exact ⟨j, fun h => hd' hj h⟩

private theorem boundary_subset_footprint :
    (by
      classical
      exact
        ∀ (T : ProtoTile), BoundaryFootprintVertices T ⊆ FootprintVertices T ) := by
  classical
  intro T x hx
  by_cases hne : T.cells.Nonempty
  · have hx' : ∃ e ∈ BoundaryFootprintEdges T, x ∈ e := by
      simpa [BoundaryFootprintVertices, hne] using hx
    obtain ⟨e, he, hxe⟩ := hx'
    rcases he with ⟨z, ⟨rfl, hcross⟩ | ⟨rfl, hcross⟩⟩
    · rcases hcross with ⟨hz, _⟩ | ⟨_, hz⟩
      · change x ∈ FootprintVertices T
        simp only [FootprintVertices, ite_eq_left hne, Set.mem_ofPred_eq]
        refine ⟨z, hz, ?_⟩
        rcases Finset.mem_insert.mp hxe with h | h
        · subst x; exact Or.inl rfl
        · have hxz : x = z + 1 := by simpa using h
          subst x; exact Or.inr (Or.inl rfl)
      · have hz' : z - ⟨0, 1⟩ ∈ T.cells := hz
        change x ∈ FootprintVertices T
        simp only [FootprintVertices, ite_eq_left hne, Set.mem_ofPred_eq]
        refine ⟨z - ⟨0, 1⟩, hz', ?_⟩
        rcases (Finset.mem_insert.mp hxe) with hxz | hxz
        · subst x
          exact Or.inr (Or.inr (Or.inl (by simp)))
        · have : x = z + 1 := by simpa using hxz
          subst x
          exact Or.inr (Or.inr (Or.inr (by simp [sub_eq_add_neg, add_comm, add_left_comm])))
    · rcases hcross with ⟨hz, _⟩ | ⟨_, hz⟩
      · change x ∈ FootprintVertices T
        simp only [FootprintVertices, ite_eq_left hne, Set.mem_ofPred_eq]
        refine ⟨z, hz, ?_⟩
        rcases (Finset.mem_insert.mp hxe) with hxz | hxz
        · subst x
          exact Or.inl rfl
        · have : x = z + ⟨0, 1⟩ := by simpa using hxz
          subst x
          exact Or.inr (Or.inr (Or.inl rfl))
      · have hz' : z - 1 ∈ T.cells := hz
        change x ∈ FootprintVertices T
        simp only [FootprintVertices, ite_eq_left hne, Set.mem_ofPred_eq]
        refine ⟨z - 1, hz', ?_⟩
        rcases (Finset.mem_insert.mp hxe) with hxz | hxz
        · subst x
          exact Or.inr (Or.inl (by simp))
        · have : x = z + ⟨0, 1⟩ := by simpa using hxz
          subst x
          exact Or.inr (Or.inr (Or.inr (by simp [sub_eq_add_neg, add_comm, add_left_comm])))
  · simp only [BoundaryFootprintVertices, hne, ↓reduceIte, Set.mem_singleton_iff,
      FootprintVertices] at hx ⊢
    exact hx

private theorem touching_path :
    (by
      classical
      exact
        (∀ (U : ProtoTile), ∀ (V : ProtoTile), ∀ (x : GaussianInt), (Disjoint U.cells V.cells) →
            ((∃ j : Fin 4, LatticeVertexIncidentCell x j ∈ U.cells) → ((∃ j : Fin 4,
            LatticeVertexIncidentCell x j ∈ V.cells) → (x ∈ BoundaryFootprintVertices U ∧ x ∈
            BoundaryFootprintVertices V)))) → ((∀ (T : ProtoTile), BoundaryFootprintVertices T ⊆
            FootprintVertices T) → (∀ (U : ProtoTile), ∀ (V : ProtoTile), (U.cells.Nonempty) →
            ((V.cells.Nonempty) → ((TileTouching U V) → (∃ x y, SimpleGridPathBetween
            (FootprintVertices U ∩ FootprintVertices V) (FootprintEdges U ∩ FootprintEdges V) x
            y))))) ) := by
  classical
  intro incident_boundary boundary_subset_footprint U V hU hV ht
  have ht' := ht
  unfold TileTouching at ht'
  have hdata : Disjoint U.cells V.cells ∧
      SimpleGridPath (BoundaryFootprintVertices U ∩ BoundaryFootprintVertices V)
        (BoundaryFootprintEdges U ∩ BoundaryFootprintEdges V) := by
    rcases ht' with hgood | hbad
    · rcases hgood with ⟨_, _, hd, hp⟩
      exact ⟨hd, hp⟩
    · rcases hbad with hleft | hright
      · exact (Finset.nonempty_iff_ne_empty.mp hU hleft.1).elim
      · exact (Finset.nonempty_iff_ne_empty.mp hV hright.1).elim
  rcases hdata with ⟨hd, hp⟩
  have hv_eq : FootprintVertices U ∩ FootprintVertices V =
      BoundaryFootprintVertices U ∩ BoundaryFootprintVertices V := by
    ext x
    constructor
    · intro hx
      have hu : x ∈ FootprintVertices U := hx.1
      have hv : x ∈ FootprintVertices V := hx.2
      simp only [FootprintVertices, ite_eq_left hU, Set.mem_ofPred_eq] at hu
      simp only [FootprintVertices, ite_eq_left hV, Set.mem_ofPred_eq] at hv
      have hincU : ∃ j : Fin 4, LatticeVertexIncidentCell x j ∈ U.cells := by
        obtain ⟨z, hz, hc⟩ := hu
        rcases hc with rfl | rfl | rfl | rfl
        · exact ⟨0, by simpa [LatticeVertexIncidentCell] using hz⟩
        · exact ⟨1, by simpa [LatticeVertexIncidentCell] using hz⟩
        · exact ⟨3, by simpa [LatticeVertexIncidentCell] using hz⟩
        · exact ⟨2, by simpa [LatticeVertexIncidentCell, sub_eq_add_neg,
            add_assoc, add_comm, add_left_comm] using hz⟩
      have hincV : ∃ j : Fin 4, LatticeVertexIncidentCell x j ∈ V.cells := by
        obtain ⟨z, hz, hc⟩ := hv
        rcases hc with rfl | rfl | rfl | rfl
        · exact ⟨0, by simpa [LatticeVertexIncidentCell] using hz⟩
        · exact ⟨1, by simpa [LatticeVertexIncidentCell] using hz⟩
        · exact ⟨3, by simpa [LatticeVertexIncidentCell] using hz⟩
        · exact ⟨2, by simpa [LatticeVertexIncidentCell, sub_eq_add_neg,
            add_assoc, add_comm, add_left_comm] using hz⟩
      obtain ⟨j, hj⟩ := hincU
      obtain ⟨k, hk⟩ := hincV
      exact incident_boundary U V x hd ⟨j, hj⟩ ⟨k, hk⟩
    · intro hx
      exact ⟨boundary_subset_footprint U hx.1, boundary_subset_footprint V hx.2⟩
  rw [hv_eq, CellDisjointCommonEdgesBoundary U V hd]
  have hendpoints : ∃ x y, SimpleGridPathBetween
      (BoundaryFootprintVertices U ∩ BoundaryFootprintVertices V)
      (BoundaryFootprintEdges U ∩ BoundaryFootprintEdges V) x y := by
    rcases hp with ⟨p, hn, hl, hv, ha, he⟩
    cases p with
    | nil => simp at hl
    | cons x p =>
      cases p with
      | nil => simp at hl
      | cons z p =>
        have hne : z :: p ≠ [] := by simp
        refine ⟨x, (z :: p).getLast hne, x :: z :: p, hn, hl, rfl, ?_, hv, ha, he⟩
        simpa using List.getLast?_eq_getLast_of_ne_nil hne
  exact hendpoints

private theorem touching_symm :
    (by
      classical
      exact
        ∀ (A : ProtoTile), ∀ (B : ProtoTile), TileTouching A B → TileTouching B A ) := by
  classical
  intro A B h
  unfold TileTouching at h ⊢
  rcases h with h | h | h
  · rcases h with ⟨ha, hb, hd, hp⟩
    exact Or.inl ⟨hb, ha, hd.symm, by simpa [Set.inter_comm] using hp⟩
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inl h)

private theorem touching_cells_congr :
    (by
      classical
      exact
        ∀ (A : ProtoTile), ∀ (B : ProtoTile), ∀ (A' : ProtoTile), ∀ (B' : ProtoTile),
            (A.cells.Nonempty) → ((B.cells.Nonempty) → ((A'.cells.Nonempty) →
            ((B'.cells.Nonempty) → ((A.cells = A'.cells) → ((B.cells = B'.cells) → (TileTouching
            A B ↔ TileTouching A' B')))))) ) := by
  classical
  intro A B A' B' hA hB hA' hB' ha hb
  have edges (X Y : ProtoTile) (hxy : X.cells = Y.cells) :
      BoundaryFootprintEdges X = BoundaryFootprintEdges Y := by
    ext e
    simp [BoundaryFootprintEdges, hxy]
  have verts (X Y : ProtoTile) (hx : X.cells.Nonempty) (hy : Y.cells.Nonempty)
      (hxy : X.cells = Y.cells) :
      BoundaryFootprintVertices X = BoundaryFootprintVertices Y := by
    simp [BoundaryFootprintVertices, hx, hy, edges X Y hxy]
  constructor
  · intro h
    unfold TileTouching at h ⊢
    rcases h with h | h | h
    · rcases h with ⟨_, _, hd, hp⟩
      apply Or.inl
      refine ⟨hA', hB', ?_, ?_⟩
      · simpa [ha, hb] using hd
      · simpa [verts A A' hA hA' ha, verts B B' hB hB' hb,
          edges A A' ha, edges B B' hb] using hp
    · have he : A'.cells = ∅ := by simpa [← ha] using h.1
      exact (Finset.not_nonempty_iff_eq_empty.mpr he hA').elim
    · have he : B'.cells = ∅ := by simpa [← hb] using h.1
      exact (Finset.not_nonempty_iff_eq_empty.mpr he hB').elim
  · intro h
    unfold TileTouching at h ⊢
    rcases h with h | h | h
    · rcases h with ⟨_, _, hd, hp⟩
      apply Or.inl
      refine ⟨hA, hB, ?_, ?_⟩
      · simpa [← ha, ← hb] using hd
      · simpa [← verts A A' hA hA' ha, ← verts B B' hB hB' hb,
          ← edges A A' ha, ← edges B B' hb] using hp
    · have : A.cells = ∅ := by simpa [ha] using h.1
      exact (Finset.not_nonempty_iff_eq_empty.mpr this hA).elim
    · have h' : B.cells = ∅ := by simpa [hb] using h.1
      exact (Finset.not_nonempty_iff_eq_empty.mpr h' hB).elim

private abbrev quarter_translate := ApollonianSuperharmonic.TileQuarterTurnTranslation.commute

private theorem translation_comm :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (x : GaussianInt), ∀ (y : GaussianInt), TileTranslation
            (TileTranslation T x) y = TileTranslation (TileTranslation T y) x ) := by
  classical
  intro T x y
  cases T with
  | mk cells anchor =>
    apply congrArg₂ (fun c : Finset GaussianInt => fun a : GaussianInt =>
      (⟨c, a⟩ : ProtoTile))
    · simp [TileTranslation, GaussianTranslation, Finset.image_image,
        Function.comp_def, add_comm, add_left_comm]
    · simp [TileTranslation, GaussianTranslation, add_comm, add_left_comm]

private theorem rotate_touch :
    (by
      classical
      exact
        (∀ (A : ProtoTile), ∀ (B : ProtoTile), ∀ (A' : ProtoTile), ∀ (B' : ProtoTile),
            (A.cells.Nonempty) → ((B.cells.Nonempty) → ((A'.cells.Nonempty) →
            ((B'.cells.Nonempty) → ((A.cells = A'.cells) → ((B.cells = B'.cells) → (TileTouching
            A B ↔ TileTouching A' B'))))))) → ((∀ (T : ProtoTile), ∀ (x : GaussianInt),
            TileQuarterTurn (TileTranslation T x) = TileTranslation (TileQuarterTurn T)
            (GaussianQuarterTurn x)) → ((∀ (T : ProtoTile), ∀ (x : GaussianInt), ∀ (y :
            GaussianInt), TileTranslation (TileTranslation T x) y = TileTranslation
            (TileTranslation T y) x) → (∀ (T : ProtoTile), ∀ (v : GaussianInt),
            (T.cells.Nonempty) → ((QuarterTurnSymmetric T) → ((TileTouching T (TileTranslation T
            v)) → (TileTouching T (TileTranslation T (GaussianQuarterTurn v)))))))) ) := by
  classical
  intro touching_cells_congr quarter_translate translation_comm T v hT hSym ht
  obtain ⟨u, hu, hcell, _, _, _⟩ :=
    QuarterTurnSymmetricCenteredTransport T hSym
  let V := TileTranslation T v
  have hrot := ((TileTouchingCovariance T V 0).2.1).mp (by simpa [V] using ht)
  have htrans := ((TileTouchingCovariance (TileQuarterTurn T)
    (TileQuarterTurn V) u).1).mp hrot
  have hright : (TileTranslation (TileQuarterTurn V) u).cells =
      (TileTranslation T (GaussianQuarterTurn v)).cells := by
    calc
      (TileTranslation (TileQuarterTurn V) u).cells =
          (TileTranslation (TileTranslation (TileQuarterTurn T)
            (GaussianQuarterTurn v)) u).cells := by
              rw [show TileQuarterTurn V =
                TileTranslation (TileQuarterTurn T) (GaussianQuarterTurn v) from
                quarter_translate T v]
      _ = (TileTranslation (TileTranslation (TileQuarterTurn T) u)
            (GaussianQuarterTurn v)).cells := by
              rw [translation_comm (TileQuarterTurn T) (GaussianQuarterTurn v) u]
      _ = (TileTranslation T (GaussianQuarterTurn v)).cells := by
        rw [(TileTranslationFormulas (TileTranslation (TileQuarterTurn T) u)
          (GaussianQuarterTurn v)).1,
          (TileTranslationFormulas T (GaussianQuarterTurn v)).1, hcell]
  have hcenterNonempty : (TileTranslation (TileQuarterTurn T) u).cells.Nonempty := by
    rw [hcell]
    exact hT
  have hrightNonempty : (TileTranslation (TileQuarterTurn V) u).cells.Nonempty := by
    rw [hright]
    rw [(TileTranslationFormulas T (GaussianQuarterTurn v)).1]
    exact Finset.image_nonempty.mpr hT
  exact (touching_cells_congr (TileTranslation (TileQuarterTurn T) u)
    (TileTranslation (TileQuarterTurn V) u) T
    (TileTranslation T (GaussianQuarterTurn v)) hcenterNonempty hrightNonempty hT
    (by
      rw [(TileTranslationFormulas T (GaussianQuarterTurn v)).1]
      exact Finset.image_nonempty.mpr hT)
    hcell hright).mp htrans

private theorem hgtAt439 :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), (ProperBandQuadruple q) → (((0 : ℤ) < (q (0 :
            Fin (4 : ℕ))).1 ∧ (∀ (i : Fin (3 : ℕ)), (0 : ℤ) ≤ (q i.succ).1) ∧ ∀ (i : Fin (3 :
            ℕ)), ∀ (j : Fin (3 : ℕ)), (q i.succ).1 = (0 : ℤ) → (q j.succ).1 = (0 : ℤ) → i = j) →
            (1 < (q 0).1)) ) := by
  classical
  intro q hq hs
  by_contra hn
  have hzero : ∀ j : Fin 3, (q j.succ).1 = 0 := by
    intro j
    have hlt := hq.2 j
    have hn' : (q j.succ).1 ≤ 0 := by omega
    exact le_antisymm hn' (hs.2.1 j)
  have h01 := hs.2.2 0 1 (hzero 0) (hzero 1)
  exact (by decide : (0 : Fin 3) ≠ 1) h01

private theorem hminus :
    (by
      classical
      exact
        (∀ (A : ProtoTile), ∀ (B : ProtoTile), TileTouching A B → TileTouching B A) → (∀ (T :
            ProtoTile), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (i : Fin (3 : ℕ)), (∀ (i : Fin
            (3 : ℕ)), TouchingTriple T (TileTranslation T (BandVectors.1 (q i.succ) (q (0 : Fin
            (4 : ℕ))))) (TileTranslation T (-BandVectors.1 (q (i + (1 : Fin (3 : ℕ))).succ) (q (0
            : Fin (4 : ℕ)))))) → (TileTouching T (TileTranslation T (-BandVectors.1 (q i.succ) (q
            0))))) ) := by
  classical
  intro touching_symm T q i hT3
  have hprev : ∀ j : Fin 3, TileTouching T
      (TileTranslation T (-BandVectors.1 (q j.succ) (q 0))) := by
    intro j
    fin_cases j
    · simpa using touching_symm _ T (hT3 2).2.2.1
    · simpa using touching_symm _ T (hT3 0).2.2.1
    · simpa using touching_symm _ T (hT3 1).2.2.1
  exact hprev i

private theorem hQ :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (i : Fin (3 : ℕ)), (∀ (j : Fin (3 : ℕ)),
            BandVectors.1 (q (0 : Fin (4 : ℕ))) (q j.succ) = (⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) *
            BandVectors.1 (q j.succ) (q (0 : Fin (4 : ℕ))) ∧ BandVectors.2 (q (0 : Fin (4 : ℕ)))
            (q j.succ) = -(⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) * BandVectors.2 (q j.succ) (q (0 :
            Fin (4 : ℕ)))) → (GaussianQuarterTurn (BandVectors.1 (q i.succ) (q 0)) =
            BandVectors.1 (q 0) (q i.succ)) ) := by
  classical
  intro q i hflip
  have hf := (hflip i).1
  calc
    GaussianQuarterTurn (BandVectors.1 (q i.succ) (q 0)) =
        (⟨0, 1⟩ : GaussianInt) * BandVectors.1 (q i.succ) (q 0) := by
          ext <;> simp [GaussianQuarterTurn]
    _ = BandVectors.1 (q 0) (q i.succ) := hf.symm

private theorem hQneg :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (i : Fin (3 : ℕ)), (GaussianQuarterTurn
            (BandVectors.1 (q i.succ) (q 0)) = BandVectors.1 (q 0) (q i.succ)) →
            (GaussianQuarterTurn (-BandVectors.1 (q i.succ) (q 0)) = -BandVectors.1 (q 0) (q
            i.succ)) ) := by
  classical
  intro q i hQ
  have hneg : GaussianQuarterTurn (-BandVectors.1 (q i.succ) (q 0)) =
      -GaussianQuarterTurn (BandVectors.1 (q i.succ) (q 0)) := by
    ext <;> simp [GaussianQuarterTurn]
  rw [hneg, hQ]

private theorem htouch :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (i : Fin (3 : ℕ)), ∀ (e :
            Bool), (TileTouching T (TileTranslation T (BandVectors.1 (q 0) (q i.succ)))) →
            ((TileTouching T (TileTranslation T (-BandVectors.1 (q 0) (q i.succ)))) → (
        let v := (if e = true then (BandVectors.1 (q 0) (q i.succ))
          else -BandVectors.1 (q 0) (q i.succ))
        TileTouching T (TileTranslation T v))) ) := by
  classical
  intro T q i e hrotplus hrotminus v
  by_cases he : e = true
  · simpa [v, he] using hrotplus
  · simpa [v, he] using hrotminus

private theorem hcentU :
    (by
      classical
      exact
        ∀ (T : ProtoTile),
          ∀ (T' : ProtoTile),
            ∀ (q : Fin (4 : ℕ) → CircleCoordinates),
              ∀ (i : Fin (3 : ℕ)),
                ∀ (e : Bool),
                  TileCentroid T' - TileCentroid T =
                      (if e = true then (1 : ℝ) else (-1 : ℝ)) •
                        GaussianRealPoint
                          (BandVectors.1 (q (0 : Fin (4 : ℕ))) (q i.succ)) →
                    let v :=
                      if e = true then BandVectors.1 (q 0) (q i.succ)
                      else -BandVectors.1 (q 0) (q i.succ)
                    TileTouching T (TileTranslation T v) →
                      let U := TileTranslation T v
                      BandPrototile (q 0) U → TileCentroid U = TileCentroid T'
    ) := by
  classical
  intro T T' q i e hcent v htouch U hU
  have hc1 := congrArg Prod.fst hcent
  have hc2 := congrArg Prod.snd hcent
  change (TileCentroid T').1 - (TileCentroid T).1 =
    (if e = true then 1 else -1) *
      ((BandVectors.1 (q 0) (q i.succ)).re : ℝ) at hc1
  change (TileCentroid T').2 - (TileCentroid T).2 =
    (if e = true then 1 else -1) *
      ((BandVectors.1 (q 0) (q i.succ)).im : ℝ) at hc2
  cases e
  · norm_num at hc1 hc2
    rw [← GaussianInt.intCast_re] at hc1
    rw [← GaussianInt.intCast_im] at hc2
    rw [(TileTranslationFormulas T v).2.2.2.2.1]
    have hre : (-BandVectors.1 (q 0) (q i.succ)).re =
        -(BandVectors.1 (q 0) (q i.succ)).re := by simp
    apply Prod.ext
    · change (TileCentroid T).1 +
        ((-BandVectors.1 (q 0) (q i.succ)).re : ℝ) = (TileCentroid T').1
      rw [hre]
      simp only [Int.cast_neg]
      linarith
    · change (TileCentroid T).2 +
        ((-BandVectors.1 (q 0) (q i.succ)).im : ℝ) = (TileCentroid T').2
      have him : (-BandVectors.1 (q 0) (q i.succ)).im =
          -(BandVectors.1 (q 0) (q i.succ)).im := by simp
      rw [him]
      simp only [Int.cast_neg]
      linarith
  · norm_num at hc1 hc2
    rw [← GaussianInt.intCast_re] at hc1
    rw [← GaussianInt.intCast_im] at hc2
    rw [(TileTranslationFormulas T v).2.2.2.2.1]
    apply Prod.ext
    · change (TileCentroid T).1 +
        (BandVectors.1 (q 0) (q i.succ)).re = (TileCentroid T').1
      linarith
    · change (TileCentroid T).2 +
        (BandVectors.1 (q 0) (q i.succ)).im = (TileCentroid T').2
      linarith

private theorem hUn :
    (by
      classical
      exact
        ∀ (T : ProtoTile), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (i : Fin (3 : ℕ)), ∀ (e :
            Bool), (Finset.Nonempty T.cells) → (
        let v := (if e = true then (BandVectors.1 (q 0) (q i.succ))
          else -BandVectors.1 (q 0) (q i.succ))
        let U := TileTranslation T v
        U.cells.Nonempty) ) := by
  classical
  intro T q i e hnonempty v U
  change (TileTranslation T v).cells.Nonempty
  rw [(TileTranslationFormulas T v).1]
  exact Finset.image_nonempty.mpr hnonempty

private abbrev hT2 := ApollonianSuperharmonic.BandPrototileQuarterTurn.symmetry

private theorem hT4 :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates),
          ProperBandQuadruple q →
            ((0 : ℤ) < (q (0 : Fin (4 : ℕ))).1 ∧
                (∀ (i : Fin (3 : ℕ)), (0 : ℤ) ≤ (q i.succ).1) ∧
                  ∀ (i : Fin (3 : ℕ)),
                    ∀ (j : Fin (3 : ℕ)),
                      (q i.succ).1 = (0 : ℤ) → (q j.succ).1 = (0 : ℤ) → i = j) →
              ∀ (A : ProtoTile),
                ∀ (B : ProtoTile),
                  ∀ (j : Fin 3),
                    BandPrototile (q 0) A →
                      BandPrototile (q j.succ) B →
                        TileCentroid B - TileCentroid A =
                            (1 / 2 : Real) •
                              (GaussianRealPoint (BandVectors.1 (q j.succ) (q 0)) +
                                GaussianRealPoint (BandVectors.1 (q 0) (q j.succ))) →
                          TouchingTriple A
                            (TileTranslation A (BandVectors.1 (q j.succ) (q 0))) B
    ) := by
  classical
  intro q hq hrootPos A B j hA hB hcentAB
  have hgt : 1 < (q 0).1 := by
    by_contra hn
    have hzero : ∀ k : Fin 3, (q k.succ).1 = 0 := by
      intro k
      have hlt := hq.2 k
      have hn' : (q k.succ).1 ≤ 0 := by omega
      exact le_antisymm hn' ((ProperBandCurvatureStructure q hq).2.1 k)
    have h01 := (ProperBandCurvatureStructure q hq).2.2 0 1 (hzero 0) (hzero 1)
    exact (by decide : (0 : Fin 3) ≠ 1) h01
  exact (BandTileSimultaneousInduction q hq A hA).2.2.2.2.2.1 hgt
    j B hB hcentAB

private theorem hT5 :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates),
          ProperBandQuadruple q →
            ∀ (A : ProtoTile),
              ∀ (B : ProtoTile),
                ∀ (D : ProtoTile),
                  ∀ (j : Fin 3),
                    BandPrototile (q 0) A →
                      BandPrototile (q j.succ) B →
                        BandPrototile (q (j + 1).succ) D →
                          TileCentroid B - TileCentroid A =
                              (1 / 2 : Real) •
                                (GaussianRealPoint (BandVectors.1 (q j.succ) (q 0)) +
                                GaussianRealPoint (BandVectors.1 (q 0) (q j.succ))) →
                            TileCentroid D - TileCentroid A =
                                (1 / 2 : Real) •
                                (GaussianRealPoint
                                (BandVectors.1 (q (j + 1).succ) (q 0)) -
                                GaussianRealPoint
                                (BandVectors.1 (q 0) (q (j + 1).succ))) →
                              TouchingTriple A B D
    ) := by
  classical
  intro q hq A B D j hA hB hD hcentB hcentD
  exact (BandTileSimultaneousInduction q hq A hA).2.2.2.2.2.2.1
    j B D hB hD hcentB hcentD

private theorem qturn_iter :
    (by
      classical
      exact
        let unitI : GaussianInt := ⟨0, 1⟩
        (∀ (z : GaussianInt), GaussianQuarterTurn z = unitI * z) → (∀ (n : ℕ), ∀ (z :
            GaussianInt), (GaussianQuarterTurn^[n]) z = unitI ^ n * z) ) := by
  classical
  intro unitI qturn_mul n z
  induction n with
  | zero => simp [unitI]
  | succ n ih =>
      calc
        (GaussianQuarterTurn^[n + 1]) z =
            GaussianQuarterTurn ((GaussianQuarterTurn^[n]) z) := by
              rw [Function.iterate_succ_apply']
        _ = unitI * (unitI ^ n * z) := by rw [qturn_mul, ih]
        _ = unitI ^ (n + 1) * z := by rw [pow_succ]; ring


private theorem rotcenter :
    (by
      classical
      exact
        ∀ (s : Fin (4 : ℕ)),
        let unitI : GaussianInt := ⟨0, 1⟩
        (∀ (n : ℕ), ∀ (z : GaussianInt), (GaussianQuarterTurn^[n]) z = unitI ^ n * z) → ((∀ (x :
            GaussianInt), ∀ (y : GaussianInt), GaussianRealPoint (x + y) = GaussianRealPoint x +
            GaussianRealPoint y) → (∀ (x : GaussianInt), ∀ (y : GaussianInt), GaussianRealPoint
            ((⟨0, 1⟩ : GaussianInt) ^ s.val * (x + y)) = GaussianRealPoint
            ((GaussianQuarterTurn^[s.val]) x) + GaussianRealPoint ((GaussianQuarterTurn^[s.val])
            y))) ) := by
  classical
  intro s unitI qturn_iter gaussianRealPoint_add x y
  rw [show (⟨0, 1⟩ : GaussianInt) = unitI by rfl,
    qturn_iter, qturn_iter]
  calc
    GaussianRealPoint (unitI ^ s.val * (x + y)) =
        GaussianRealPoint (unitI ^ s.val * x + unitI ^ s.val * y) := by
          rw [mul_add]
    _ = GaussianRealPoint (unitI ^ s.val * x) +
          GaussianRealPoint (unitI ^ s.val * y) := gaussianRealPoint_add _ _

private theorem hcentRot :
    (by
      classical
      exact
        ∀ (T0 : ProtoTile), ∀ (Ti : ProtoTile), ∀ (q : Fin (4 : ℕ) → CircleCoordinates), ∀ (i :
            Fin (3 : ℕ)), ∀ (s : Fin (4 : ℕ)), (TileCentroid Ti - TileCentroid T0 = (1 / 2 : ℝ) •
            GaussianRealPoint ((⟨(0 : ℤ), (1 : ℤ)⟩ : GaussianInt) ^ (↑s : ℕ) * (BandVectors.1 (q
            i.succ) (q (0 : Fin (4 : ℕ))) + BandVectors.1 (q (0 : Fin (4 : ℕ))) (q i.succ)))) →
            ((∀ (x : GaussianInt), ∀ (y : GaussianInt), GaussianRealPoint ((⟨0, 1⟩ : GaussianInt)
            ^ s.val * (x + y)) = GaussianRealPoint ((GaussianQuarterTurn^[s.val]) x) +
            GaussianRealPoint ((GaussianQuarterTurn^[s.val]) y)) → (TileCentroid Ti -
            TileCentroid T0 = (1 / 2 : Real) • (GaussianRealPoint ((GaussianQuarterTurn^[s.val])
            (BandVectors.1 (q i.succ) (q 0))) + GaussianRealPoint ((GaussianQuarterTurn^[s.val])
            (BandVectors.1 (q 0) (q i.succ)))))) ) := by
  classical
  intro T0 Ti q i s hcent rotcenter
  rw [← rotcenter]
  exact hcent

private theorem hT2' :
    (by
      classical
      exact
        ∀ (q : Fin (4 : ℕ) → CircleCoordinates), (∀ (D : CircleCoordinates), ∀ (X : ProtoTile),
            BandPrototile D X → QuarterTurnSymmetric X) → (∀ (a : Fin 4), ∀ (X : ProtoTile),
            BandPrototile (q a) X → QuarterTurnSymmetric X) ) := by
  classical
  intro q hT2 a X hx
  exact hT2 (q a) X hx

end LatticeInterfacePathGeometry

theorem LatticeAdjacentInterfacePath :
    (forall (C : BandCircle) (T T' : ProtoTile) (h h' : PartialOdometer),
      RightLatticeAdjacent C T T' h h' ->
      exists x y : GaussianInt,
        SimpleGridPathBetween
          (FootprintVertices T ∩ FootprintVertices T')
          (FootprintEdges T ∩ FootprintEdges T') x y) /\
    forall (C0 Ci : BandCircle) (T0 Ti : ProtoTile)
        (h0 hi : PartialOdometer),
      SubtileLatticeAdjacent C0 Ci T0 Ti h0 hi ->
      exists x y : GaussianInt,
        SimpleGridPathBetween
          (FootprintVertices T0 ∩ FootprintVertices Ti)
          (FootprintEdges T0 ∩ FootprintEdges Ti) x y := by
-- BODY
  classical
  have band_of_odometer (C : CircleCoordinates) (T : ProtoTile) (h : PartialOdometer)
      (ho : TileOdometer C T h) : BandPrototile C T :=
          TileOdometerBandPrototile C T h ho
  have positive_nonempty : ∀ (C : CircleCoordinates) (T : ProtoTile)
      (hT : BandPrototile C T), 0 < C.1 → T.cells.Nonempty :=
          (fun D V hV hD => BandPrototileNonempty.positive D V hD hV)
  have incident_boundary (U V : ProtoTile) (x : GaussianInt)
      (hd : Disjoint U.cells V.cells)
      (hu : ∃ j : Fin 4, LatticeVertexIncidentCell x j ∈ U.cells)
      (hv : ∃ j : Fin 4, LatticeVertexIncidentCell x j ∈ V.cells) :
      x ∈ BoundaryFootprintVertices U ∧ x ∈ BoundaryFootprintVertices V :=
          LatticeInterfacePathGeometry.incident_boundary U V x hd hu hv
  have boundary_subset_footprint (T : ProtoTile) :
      BoundaryFootprintVertices T ⊆ FootprintVertices T :=
          LatticeInterfacePathGeometry.boundary_subset_footprint T
  have touching_path (U V : ProtoTile) (hU : U.cells.Nonempty) (hV : V.cells.Nonempty)
      (ht : TileTouching U V) :
      ∃ x y, SimpleGridPathBetween
        (FootprintVertices U ∩ FootprintVertices V)
        (FootprintEdges U ∩ FootprintEdges V) x y := LatticeInterfacePathGeometry.touching_path
            incident_boundary boundary_subset_footprint U V hU hV ht
  have touching_symm (A B : ProtoTile) : TileTouching A B → TileTouching B A :=
      LatticeInterfacePathGeometry.touching_symm A B
  have touching_cells_congr (A B A' B' : ProtoTile)
      (hA : A.cells.Nonempty) (hB : B.cells.Nonempty)
      (hA' : A'.cells.Nonempty) (hB' : B'.cells.Nonempty)
      (ha : A.cells = A'.cells) (hb : B.cells = B'.cells) :
      TileTouching A B ↔ TileTouching A' B' := LatticeInterfacePathGeometry.touching_cells_congr
          A B A' B' hA hB hA' hB' ha hb
  have quarter_translate (T : ProtoTile) (x : GaussianInt) :
      TileQuarterTurn (TileTranslation T x) =
        TileTranslation (TileQuarterTurn T) (GaussianQuarterTurn x) :=
            LatticeInterfacePathGeometry.quarter_translate T x
  have translation_comm (T : ProtoTile) (x y : GaussianInt) :
      TileTranslation (TileTranslation T x) y =
        TileTranslation (TileTranslation T y) x := LatticeInterfacePathGeometry.translation_comm
            T x y
  have rotate_touch (T : ProtoTile) (v : GaussianInt)
      (hT : T.cells.Nonempty)
      (hSym : QuarterTurnSymmetric T)
      (ht : TileTouching T (TileTranslation T v)) :
      TileTouching T (TileTranslation T (GaussianQuarterTurn v)) :=
          LatticeInterfacePathGeometry.rotate_touch touching_cells_congr quarter_translate
          translation_comm T v hT hSym ht
  constructor
  · intro C T T' h h' hadj
    rcases hadj with ⟨ho, ho', ⟨p, p', hp, hp', q, i, e, hq, hq0,
      hcent, _, _⟩⟩
    have hT := band_of_odometer (C.1.1) T h ho
    have hT' := band_of_odometer (C.1.1) T' h' ho'
    have hTq : BandPrototile (q 0) T := by simpa [hq0] using hT
    have hT'q : BandPrototile (q 0) T' := by simpa [hq0] using hT'
    have hs := ProperBandCurvatureStructure q hq
    have hnonempty := positive_nonempty (q 0) T hTq hs.1
    have hgt : 1 < (q 0).1 := LatticeInterfacePathGeometry.hgtAt439 q hq hs
    have hsim := BandTileSimultaneousInduction q hq T hTq
    have hT3 := hsim.2.2.2.2.1 hgt
    have hplus : TileTouching T
        (TileTranslation T (BandVectors.1 (q i.succ) (q 0))) := (hT3 i).1
    have hminus : TileTouching T
        (TileTranslation T (-BandVectors.1 (q i.succ) (q 0))) :=
            LatticeInterfacePathGeometry.hminus touching_symm T q i hT3
    have hflip := (VectorRecursionLaws q hq.1).2.2.2.2 hq
    have hQ : GaussianQuarterTurn (BandVectors.1 (q i.succ) (q 0)) =
        BandVectors.1 (q 0) (q i.succ) := LatticeInterfacePathGeometry.hQ q i hflip
    have hQneg : GaussianQuarterTurn (-BandVectors.1 (q i.succ) (q 0)) =
        -BandVectors.1 (q 0) (q i.succ) := LatticeInterfacePathGeometry.hQneg q i hQ
    have hrotplus : TileTouching T
        (TileTranslation T (BandVectors.1 (q 0) (q i.succ))) := by
      have ht := rotate_touch T _ hnonempty hsim.2.2.2.1 hplus
      simpa [hQ] using ht
    have hrotminus : TileTouching T
        (TileTranslation T (-BandVectors.1 (q 0) (q i.succ))) := by
      have ht := rotate_touch T _ hnonempty hsim.2.2.2.1 hminus
      simpa [hQneg] using ht
    let v := (if e = true then (BandVectors.1 (q 0) (q i.succ))
      else -BandVectors.1 (q 0) (q i.succ))
    have htouch : TileTouching T (TileTranslation T v) := LatticeInterfacePathGeometry.htouch T q
        i e hrotplus hrotminus
    let U := TileTranslation T v
    have hU : BandPrototile (q 0) U := BandPrototileTranslation _ T v hTq
    have hcentU : TileCentroid U = TileCentroid T' := LatticeInterfacePathGeometry.hcentU T T' q
        i e hcent htouch hU
    have hcells := (BandPrototileCentroidUnique (q 0) U T' hU hT'q hcentU).1
    have hUn : U.cells.Nonempty := LatticeInterfacePathGeometry.hUn T q i e hnonempty
    have hT'nonempty : T'.cells.Nonempty := by rw [← hcells]; exact hUn
    have htouch' := (touching_cells_congr T U T T' hnonempty hUn hnonempty hT'nonempty
      rfl hcells).mp htouch
    exact touching_path T T' hnonempty hT'nonempty htouch'
  · intro C0 Ci T0 Ti h0 hi hadj
    rcases hadj with ⟨ho0, hoi, ⟨p0, pi, hp0, hpi, q, i, s, hq,
      hq0, hqi, hcent, _, _⟩⟩
    have hT0 := band_of_odometer (C0.1.1) T0 h0 ho0
    have hTi := band_of_odometer (Ci.1.1) Ti hi hoi
    have hT0q : BandPrototile (q 0) T0 := by simpa [hq0] using hT0
    have hTiq : BandPrototile (q i.succ) Ti := by simpa [hqi] using hTi
    have hrootPos := ProperBandCurvatureStructure q hq
    have hnonempty0 := positive_nonempty (q 0) T0 hT0q hrootPos.1
    have hchildPos : 0 < (q i.succ).1 := by rw [hqi]; exact Ci.2
    have hnonemptyi := positive_nonempty (q i.succ) Ti hTiq hchildPos
    have hT2 : ∀ (D : CircleCoordinates) (X : ProtoTile),
        BandPrototile D X → QuarterTurnSymmetric X := LatticeInterfacePathGeometry.hT2
    have hT4 : ∀ (A B : ProtoTile) (j : Fin 3),
        BandPrototile (q 0) A → BandPrototile (q j.succ) B →
        TileCentroid B - TileCentroid A =
          (1 / 2 : Real) •
            (GaussianRealPoint (BandVectors.1 (q j.succ) (q 0)) +
              GaussianRealPoint (BandVectors.1 (q 0) (q j.succ))) →
        TouchingTriple A (TileTranslation A (BandVectors.1 (q j.succ) (q 0))) B :=
            LatticeInterfacePathGeometry.hT4 q hq hrootPos
    have hT5 : ∀ (A B D : ProtoTile) (j : Fin 3),
        BandPrototile (q 0) A → BandPrototile (q j.succ) B →
        BandPrototile (q ((j + 1).succ)) D →
        TileCentroid B - TileCentroid A =
          (1 / 2 : Real) •
            (GaussianRealPoint (BandVectors.1 (q j.succ) (q 0)) +
              GaussianRealPoint (BandVectors.1 (q 0) (q j.succ))) →
        TileCentroid D - TileCentroid A =
          (1 / 2 : Real) •
            (GaussianRealPoint (BandVectors.1 (q ((j + 1).succ)) (q 0)) -
              GaussianRealPoint (BandVectors.1 (q 0) (q ((j + 1).succ)))) →
        TouchingTriple A B D := LatticeInterfacePathGeometry.hT5 q hq
    let unitI : GaussianInt := ⟨0, 1⟩
    have qturn_mul (z : GaussianInt) : GaussianQuarterTurn z = unitI * z := by
      ext <;> simp [GaussianQuarterTurn, unitI]
    have qturn_iter (n : ℕ) (z : GaussianInt) :
        (GaussianQuarterTurn^[n]) z = unitI ^ n * z := LatticeInterfacePathGeometry.qturn_iter
            qturn_mul n z
    have gaussianRealPoint_add (x y : GaussianInt) :
        GaussianRealPoint (x + y) = GaussianRealPoint x + GaussianRealPoint y :=
            GaussianRealPointProperties.add x y
    have rotcenter (x y : GaussianInt) :
        GaussianRealPoint ((⟨0, 1⟩ : GaussianInt) ^ s.val * (x + y)) =
          GaussianRealPoint ((GaussianQuarterTurn^[s.val]) x) +
            GaussianRealPoint ((GaussianQuarterTurn^[s.val]) y) :=
                LatticeInterfacePathGeometry.rotcenter s qturn_iter gaussianRealPoint_add x y
    have hcentRot : TileCentroid Ti - TileCentroid T0 =
        (1 / 2 : Real) •
          (GaussianRealPoint ((GaussianQuarterTurn^[s.val])
              (BandVectors.1 (q i.succ) (q 0))) +
            GaussianRealPoint ((GaussianQuarterTurn^[s.val])
              (BandVectors.1 (q 0) (q i.succ)))) := LatticeInterfacePathGeometry.hcentRot T0 Ti q
                  i s hcent rotcenter
    have hT2' : ∀ (a : Fin 4) (X : ProtoTile),
        BandPrototile (q a) X → QuarterTurnSymmetric X := LatticeInterfacePathGeometry.hT2' q hT2
    have hcov := OrientedTouchingCovariance q hq hT2' hT4 hT5
    have htriple := hcov.1 T0 Ti i s hT0q hTiq hcentRot
    exact touching_path T0 Ti hnonempty0 hnonemptyi
      (touching_symm Ti T0 htriple.2.2.1)

end ApollonianSuperharmonic

end
