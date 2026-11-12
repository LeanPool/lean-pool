/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P4677T2DrawingData
public import LeanPool.ApollonianSuperharmonic.SubtileOccurrenceInterpretation
public import LeanPool.ApollonianSuperharmonic.TouchingTriple
public import LeanPool.ApollonianSuperharmonic.TileTranslationFormulas

-- [TABLET NODE: P4677T2FacePoints]

/-!
# P4677T2FacePoints

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

namespace FacePointConstruction

private theorem boundary_to_footprint (T : ProtoTile) (x : GaussianInt)
      (hx : x ∈ BoundaryFootprintVertices T) : x ∈ FootprintVertices T := by
  classical
  have edge_to_footprint (e : Finset GaussianInt)
      (he : e ∈ BoundaryFootprintEdges T) : e ∈ FootprintEdges T := by
    change ∃ z : GaussianInt,
      (e = {z, z + 1} ∧
        ((z ∈ T.cells ∧ z - ⟨0, 1⟩ ∉ T.cells) ∨
          (z ∉ T.cells ∧ z - ⟨0, 1⟩ ∈ T.cells))) ∨
      (e = {z, z + ⟨0, 1⟩} ∧
        ((z ∈ T.cells ∧ z - 1 ∉ T.cells) ∨
          (z ∉ T.cells ∧ z - 1 ∈ T.cells))) at he
    change ∃ c ∈ T.cells,
      e = {c, c + 1} ∨ e = {c, c + ⟨0, 1⟩} ∨
        e = {c + 1, c + 1 + ⟨0, 1⟩} ∨
          e = {c + ⟨0, 1⟩, c + 1 + ⟨0, 1⟩}
    rcases he with ⟨z, ⟨rfl, h⟩ | ⟨rfl, h⟩⟩
    · rcases h with ⟨hz, -⟩ | ⟨-, hz⟩
      · exact ⟨z, hz, Or.inl rfl⟩
      · refine ⟨z - ⟨0, 1⟩, hz, Or.inr (Or.inr (Or.inr ?_))⟩
        congr 1 <;> simp [Zsqrtd.ext_iff]
    · rcases h with ⟨hz, -⟩ | ⟨-, hz⟩
      · exact ⟨z, hz, Or.inr (Or.inl rfl)⟩
      · refine ⟨z - 1, hz, Or.inr (Or.inr (Or.inl ?_))⟩
        congr 1 <;> simp []
  by_cases hne : T.cells.Nonempty
  · simp only [BoundaryFootprintVertices, ite_eq_left hne, Set.mem_ofPred_eq] at hx
    rcases hx with ⟨e, he, hxe⟩
    have he' := edge_to_footprint e he
    rcases he' with ⟨z, hz, he⟩
    rcases he with h | h | h | h
    all_goals
      rw [h] at hxe
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxe
      simp only [FootprintVertices, ite_eq_left hne]
    · rcases hxe with hxe | hxe
      · subst x; exact ⟨z, hz, Or.inl rfl⟩
      · subst x; exact ⟨z, hz, Or.inr (Or.inl rfl)⟩
    · rcases hxe with hxe | hxe
      · subst x; exact ⟨z, hz, Or.inl rfl⟩
      · subst x; exact ⟨z, hz, Or.inr (Or.inr (Or.inl rfl))⟩
    · rcases hxe with hxe | hxe
      · subst x; exact ⟨z, hz, Or.inr (Or.inl rfl)⟩
      · subst x; exact ⟨z, hz, Or.inr (Or.inr (Or.inr rfl))⟩
    · rcases hxe with hxe | hxe
      · subst x; exact ⟨z, hz, Or.inr (Or.inr (Or.inl rfl))⟩
      · subst x; exact ⟨z, hz, Or.inr (Or.inr (Or.inr rfl))⟩
  · simp only [BoundaryFootprintVertices, ite_eq_right hne, Set.mem_singleton_iff] at hx
    subst x
    simp [FootprintVertices, hne]

private theorem touching_point (A B C : ProtoTile) (h : TouchingTriple A B C) :
      ∃ x : GaussianInt, x ∈ BoundaryFootprintVertices A ∧
        x ∈ BoundaryFootprintVertices B ∧ x ∈ BoundaryFootprintVertices C := by
  classical
  change TileTouching A B ∧ TileTouching B C ∧ TileTouching C A ∧
    (∃! x : GaussianInt, x ∈ BoundaryFootprintVertices A ∧
      x ∈ BoundaryFootprintVertices B ∧ x ∈ BoundaryFootprintVertices C) at h
  exact h.2.2.2.exists

private theorem fp3 (boundary_to_footprint : ∀ (T : ProtoTile), ∀ x ∈ BoundaryFootprintVertices
    T, x ∈ FootprintVertices T) (A B C : ProtoTile) (x : GaussianInt)
      (h : x ∈ BoundaryFootprintVertices A ∧
        x ∈ BoundaryFootprintVertices B ∧ x ∈ BoundaryFootprintVertices C) :
      x ∈ FootprintVertices A ∧ x ∈ FootprintVertices B ∧
        x ∈ FootprintVertices C := by
  classical
  exact ⟨boundary_to_footprint A x h.1,
    boundary_to_footprint B x h.2.1,
    boundary_to_footprint C x h.2.2⟩

private theorem h1 (P : Fin 3 → Bool → ProtoTile) (Q : Fin 3 → Bool → ProtoTile) (S : Fin 3 →
    Bool → ProtoTile) (p1 : GaussianInt) (hp1 : p1 ∈ BoundaryFootprintVertices (Q 1 true) ∧
  p1 ∈ BoundaryFootprintVertices (S 2 false) ∧ p1 ∈ BoundaryFootprintVertices (P 1 true)) (fp3 :
      ∀ (A B C : ProtoTile) (x : GaussianInt),
  x ∈ BoundaryFootprintVertices A ∧ x ∈ BoundaryFootprintVertices B ∧ x ∈
      BoundaryFootprintVertices C →
    x ∈ FootprintVertices A ∧ x ∈ FootprintVertices B ∧ x ∈ FootprintVertices C) : p1 ∈
        FootprintVertices (Q 1 true) ∧ p1 ∈ FootprintVertices (S 2 false) ∧ p1 ∈
        FootprintVertices (P 1 true) := by
  classical
  exact fp3 (Q 1 true) (S 2 false) (P 1 true) p1 hp1

private theorem h2 (P : Fin 3 → Bool → ProtoTile) (Q : Fin 3 → Bool → ProtoTile) (S : Fin 3 →
    Bool → ProtoTile) (p2 : GaussianInt) (hp2 : p2 ∈ BoundaryFootprintVertices (Q 2 true) ∧
  p2 ∈ BoundaryFootprintVertices (S 1 false) ∧ p2 ∈ BoundaryFootprintVertices (P 1 false)) (fp3 :
      ∀ (A B C : ProtoTile) (x : GaussianInt),
  x ∈ BoundaryFootprintVertices A ∧ x ∈ BoundaryFootprintVertices B ∧ x ∈
      BoundaryFootprintVertices C →
    x ∈ FootprintVertices A ∧ x ∈ FootprintVertices B ∧ x ∈ FootprintVertices C) : p2 ∈
        FootprintVertices (Q 2 true) ∧ p2 ∈ FootprintVertices (S 1 false) ∧ p2 ∈
        FootprintVertices (P 1 false) := by
  classical
  exact fp3 (Q 2 true) (S 1 false) (P 1 false) p2 hp2

private theorem h3 (P : Fin 3 → Bool → ProtoTile) (Q : Fin 3 → Bool → ProtoTile) (p3 :
    GaussianInt) (hp3 : p3 ∈ BoundaryFootprintVertices (Q 1 true) ∧
  p3 ∈ BoundaryFootprintVertices (P 1 true) ∧ p3 ∈ BoundaryFootprintVertices (P 2 false)) (fp3 :
      ∀ (A B C : ProtoTile) (x : GaussianInt),
  x ∈ BoundaryFootprintVertices A ∧ x ∈ BoundaryFootprintVertices B ∧ x ∈
      BoundaryFootprintVertices C →
    x ∈ FootprintVertices A ∧ x ∈ FootprintVertices B ∧ x ∈ FootprintVertices C) : p3 ∈
        FootprintVertices (Q 1 true) ∧ p3 ∈ FootprintVertices (P 1 true) ∧ p3 ∈ FootprintVertices
        (P 2 false) := by
  classical
  exact fp3 (Q 1 true) (P 1 true) (P 2 false) p3 hp3

private theorem h4 (P : Fin 3 → Bool → ProtoTile) (S : Fin 3 → Bool → ProtoTile) (p4 :
    GaussianInt) (hp4 : p4 ∈ BoundaryFootprintVertices (S 1 false) ∧
  p4 ∈ BoundaryFootprintVertices (P 1 false) ∧ p4 ∈ BoundaryFootprintVertices (P 2 true)) (fp3 :
      ∀ (A B C : ProtoTile) (x : GaussianInt),
  x ∈ BoundaryFootprintVertices A ∧ x ∈ BoundaryFootprintVertices B ∧ x ∈
      BoundaryFootprintVertices C →
    x ∈ FootprintVertices A ∧ x ∈ FootprintVertices B ∧ x ∈ FootprintVertices C) : p4 ∈
        FootprintVertices (S 1 false) ∧ p4 ∈ FootprintVertices (P 1 false) ∧ p4 ∈
        FootprintVertices (P 2 true) := by
  classical
  exact fp3 (S 1 false) (P 1 false) (P 2 true) p4 hp4

private theorem h1' (P : Fin 3 → Bool → ProtoTile) (Q : Fin 3 → Bool → ProtoTile) (S : Fin 3 →
    Bool → ProtoTile) (hQfoot : ∀ (i : Fin 3) (s : Bool), FootprintVertices (Q i s) ⊆
    FootprintVertices (P 0 true)) (hSfoot : ∀ (i : Fin 3) (s : Bool), FootprintVertices (S i s) ⊆
    FootprintVertices (P 0 false)) (p1 : GaussianInt) (h1 : p1 ∈ FootprintVertices (Q 1 true) ∧
    p1 ∈ FootprintVertices (S 2 false) ∧ p1 ∈ FootprintVertices (P 1 true)) : p1 ∈
    FootprintVertices (P 0 true) ∧
      p1 ∈ FootprintVertices (P 0 false) ∧ p1 ∈ FootprintVertices (P 1 true) := by
  classical
  exact ⟨hQfoot 1 true h1.1, hSfoot 2 false h1.2.1, h1.2.2⟩

private theorem h2' (P : Fin 3 → Bool → ProtoTile) (Q : Fin 3 → Bool → ProtoTile) (S : Fin 3 →
    Bool → ProtoTile) (hQfoot : ∀ (i : Fin 3) (s : Bool), FootprintVertices (Q i s) ⊆
    FootprintVertices (P 0 true)) (hSfoot : ∀ (i : Fin 3) (s : Bool), FootprintVertices (S i s) ⊆
    FootprintVertices (P 0 false)) (p2 : GaussianInt) (h2 : p2 ∈ FootprintVertices (Q 2 true) ∧
    p2 ∈ FootprintVertices (S 1 false) ∧ p2 ∈ FootprintVertices (P 1 false)) : p2 ∈
    FootprintVertices (P 0 true) ∧
      p2 ∈ FootprintVertices (P 0 false) ∧ p2 ∈ FootprintVertices (P 1 false) := by
  classical
  exact ⟨hQfoot 2 true h2.1, hSfoot 1 false h2.2.1, h2.2.2⟩

private theorem h3' (P : Fin 3 → Bool → ProtoTile) (Q : Fin 3 → Bool → ProtoTile) (hQfoot : ∀ (i
    : Fin 3) (s : Bool), FootprintVertices (Q i s) ⊆ FootprintVertices (P 0 true)) (p3 :
    GaussianInt) (h3 : p3 ∈ FootprintVertices (Q 1 true) ∧ p3 ∈ FootprintVertices (P 1 true) ∧ p3
    ∈ FootprintVertices (P 2 false)) : p3 ∈ FootprintVertices (P 0 true) ∧
      p3 ∈ FootprintVertices (P 1 true) ∧ p3 ∈ FootprintVertices (P 2 false) := by
  classical
  exact ⟨hQfoot 1 true h3.1, h3.2.1, h3.2.2⟩

private theorem h4' (P : Fin 3 → Bool → ProtoTile) (S : Fin 3 → Bool → ProtoTile) (hSfoot : ∀ (i
    : Fin 3) (s : Bool), FootprintVertices (S i s) ⊆ FootprintVertices (P 0 false)) (p4 :
    GaussianInt) (h4 : p4 ∈ FootprintVertices (S 1 false) ∧ p4 ∈ FootprintVertices (P 1 false) ∧
    p4 ∈ FootprintVertices (P 2 true)) : p4 ∈ FootprintVertices (P 0 false) ∧
      p4 ∈ FootprintVertices (P 1 false) ∧ p4 ∈ FootprintVertices (P 2 true) := by
  classical
  exact ⟨hSfoot 1 false h4.1, h4.2.1, h4.2.2⟩

private theorem h5 (P : Fin 3 → Bool → ProtoTile) (v : GaussianInt) (p5 : GaussianInt) (hp5 : p5
    ∈ BoundaryFootprintVertices (P 0 true) ∧
  p5 ∈ BoundaryFootprintVertices (TileTranslation (P 0 false) v) ∧
    p5 ∈ BoundaryFootprintVertices (TileTranslation (P 2 true) v)) (fp3 : ∀ (A B C : ProtoTile)
        (x : GaussianInt),
  x ∈ BoundaryFootprintVertices A ∧ x ∈ BoundaryFootprintVertices B ∧ x ∈
      BoundaryFootprintVertices C →
    x ∈ FootprintVertices A ∧ x ∈ FootprintVertices B ∧ x ∈ FootprintVertices C) : p5 ∈
        FootprintVertices (P 0 true) ∧
  p5 ∈ FootprintVertices (TileTranslation (P 0 false) v) ∧ p5 ∈ FootprintVertices
      (TileTranslation (P 2 true) v) := by
  classical
  exact fp3 (P 0 true) (TileTranslation (P 0 false) v)
    (TileTranslation (P 2 true) v) p5 hp5

private theorem h6 (P : Fin 3 → Bool → ProtoTile) (v : GaussianInt) (p6 : GaussianInt) (hp6 : p6
    ∈ BoundaryFootprintVertices (P 0 true) ∧
  p6 ∈ BoundaryFootprintVertices (TileTranslation (P 0 false) v) ∧ p6 ∈ BoundaryFootprintVertices
      (P 2 false)) (fp3 : ∀ (A B C : ProtoTile) (x : GaussianInt),
  x ∈ BoundaryFootprintVertices A ∧ x ∈ BoundaryFootprintVertices B ∧ x ∈
      BoundaryFootprintVertices C →
    x ∈ FootprintVertices A ∧ x ∈ FootprintVertices B ∧ x ∈ FootprintVertices C) : p6 ∈
        FootprintVertices (P 0 true) ∧
  p6 ∈ FootprintVertices (TileTranslation (P 0 false) v) ∧ p6 ∈ FootprintVertices (P 2 false) := by
  classical
  exact fp3 (P 0 true) (TileTranslation (P 0 false) v)
    (P 2 false) p6 hp6

private theorem h7 (P : Fin 3 → Bool → ProtoTile) (u : GaussianInt) (v : GaussianInt) (p7 :
    GaussianInt) (hp7 : p7 ∈ BoundaryFootprintVertices (P 0 true) ∧
  p7 ∈ BoundaryFootprintVertices (TileTranslation (P 0 false) (u + v)) ∧
    p7 ∈ BoundaryFootprintVertices (TileTranslation (P 1 true) (u + v))) (fp3 : ∀ (A B C :
        ProtoTile) (x : GaussianInt),
  x ∈ BoundaryFootprintVertices A ∧ x ∈ BoundaryFootprintVertices B ∧ x ∈
      BoundaryFootprintVertices C →
    x ∈ FootprintVertices A ∧ x ∈ FootprintVertices B ∧ x ∈ FootprintVertices C) : p7 ∈
        FootprintVertices (P 0 true) ∧
  p7 ∈ FootprintVertices (TileTranslation (P 0 false) (u + v)) ∧
    p7 ∈ FootprintVertices (TileTranslation (P 1 true) (u + v)) := by
  classical
  exact fp3 (P 0 true) (TileTranslation (P 0 false) (u + v))
    (TileTranslation (P 1 true) (u + v)) p7 hp7

private theorem h8 (P : Fin 3 → Bool → ProtoTile) (u : GaussianInt) (v : GaussianInt) (p8 :
    GaussianInt) (hp8 : p8 ∈ BoundaryFootprintVertices (P 0 true) ∧
  p8 ∈ BoundaryFootprintVertices (TileTranslation (P 0 false) (u + v)) ∧ p8 ∈
      BoundaryFootprintVertices (P 1 false)) (fp3 : ∀ (A B C : ProtoTile) (x : GaussianInt),
  x ∈ BoundaryFootprintVertices A ∧ x ∈ BoundaryFootprintVertices B ∧ x ∈
      BoundaryFootprintVertices C →
    x ∈ FootprintVertices A ∧ x ∈ FootprintVertices B ∧ x ∈ FootprintVertices C) : p8 ∈
        FootprintVertices (P 0 true) ∧
  p8 ∈ FootprintVertices (TileTranslation (P 0 false) (u + v)) ∧ p8 ∈ FootprintVertices (P 1
      false) := by
  classical
  exact fp3 (P 0 true) (TileTranslation (P 0 false) (u + v))
    (P 1 false) p8 hp8

private theorem h9 (P : Fin 3 → Bool → ProtoTile) (u : GaussianInt) (v : GaussianInt) (p9 :
    GaussianInt) (hp9 : p9 ∈ BoundaryFootprintVertices (P 0 true) ∧
  p9 ∈ BoundaryFootprintVertices (TileTranslation (P 1 true) (u + v)) ∧
    p9 ∈ BoundaryFootprintVertices (TileTranslation (P 2 true) v)) (fp3 : ∀ (A B C : ProtoTile)
        (x : GaussianInt),
  x ∈ BoundaryFootprintVertices A ∧ x ∈ BoundaryFootprintVertices B ∧ x ∈
      BoundaryFootprintVertices C →
    x ∈ FootprintVertices A ∧ x ∈ FootprintVertices B ∧ x ∈ FootprintVertices C) : p9 ∈
        FootprintVertices (P 0 true) ∧
  p9 ∈ FootprintVertices (TileTranslation (P 1 true) (u + v)) ∧ p9 ∈ FootprintVertices
      (TileTranslation (P 2 true) v) := by
  classical
  exact fp3 (P 0 true) (TileTranslation (P 1 true) (u + v))
    (TileTranslation (P 2 true) v) p9 hp9

private theorem h10 (P : Fin 3 → Bool → ProtoTile) (u : GaussianInt) (v : GaussianInt) (p10 :
    GaussianInt) (hp10 : p10 ∈ BoundaryFootprintVertices (P 0 false) ∧
  p10 ∈ BoundaryFootprintVertices (TileTranslation (P 1 false) (-u - v)) ∧
    p10 ∈ BoundaryFootprintVertices (TileTranslation (P 2 false) (-v))) (fp3 : ∀ (A B C :
        ProtoTile) (x : GaussianInt),
  x ∈ BoundaryFootprintVertices A ∧ x ∈ BoundaryFootprintVertices B ∧ x ∈
      BoundaryFootprintVertices C →
    x ∈ FootprintVertices A ∧ x ∈ FootprintVertices B ∧ x ∈ FootprintVertices C) : p10 ∈
        FootprintVertices (P 0 false) ∧
  p10 ∈ FootprintVertices (TileTranslation (P 1 false) (-u - v)) ∧
    p10 ∈ FootprintVertices (TileTranslation (P 2 false) (-v)) := by
  classical
  exact fp3 (P 0 false) (TileTranslation (P 1 false) (-u-v))
    (TileTranslation (P 2 false) (-v)) p10 hp10

private theorem h11 (P : Fin 3 → Bool → ProtoTile) (u : GaussianInt) (p11 : GaussianInt) (hp11 :
    p11 ∈ BoundaryFootprintVertices (P 1 true) ∧
  p11 ∈ BoundaryFootprintVertices (TileTranslation (P 1 false) (-u)) ∧
    p11 ∈ BoundaryFootprintVertices (TileTranslation (P 2 true) (-u))) (fp3 : ∀ (A B C :
        ProtoTile) (x : GaussianInt),
  x ∈ BoundaryFootprintVertices A ∧ x ∈ BoundaryFootprintVertices B ∧ x ∈
      BoundaryFootprintVertices C →
    x ∈ FootprintVertices A ∧ x ∈ FootprintVertices B ∧ x ∈ FootprintVertices C) : p11 ∈
        FootprintVertices (P 1 true) ∧
  p11 ∈ FootprintVertices (TileTranslation (P 1 false) (-u)) ∧ p11 ∈ FootprintVertices
      (TileTranslation (P 2 true) (-u)) := by
  classical
  exact fp3 (P 1 true) (TileTranslation (P 1 false) (-u))
    (TileTranslation (P 2 true) (-u)) p11 hp11

private theorem h12 (P : Fin 3 → Bool → ProtoTile) (u : GaussianInt) (p12 : GaussianInt) (hp12 :
    p12 ∈ BoundaryFootprintVertices (P 1 true) ∧
  p12 ∈ BoundaryFootprintVertices (TileTranslation (P 1 false) (-u)) ∧ p12 ∈
      BoundaryFootprintVertices (P 2 false)) (fp3 : ∀ (A B C : ProtoTile) (x : GaussianInt),
  x ∈ BoundaryFootprintVertices A ∧ x ∈ BoundaryFootprintVertices B ∧ x ∈
      BoundaryFootprintVertices C →
    x ∈ FootprintVertices A ∧ x ∈ FootprintVertices B ∧ x ∈ FootprintVertices C) : p12 ∈
        FootprintVertices (P 1 true) ∧
  p12 ∈ FootprintVertices (TileTranslation (P 1 false) (-u)) ∧ p12 ∈ FootprintVertices (P 2
      false) := by
  classical
  exact fp3 (P 1 true) (TileTranslation (P 1 false) (-u))
    (P 2 false) p12 hp12

private noncomputable abbrev point (p1 : GaussianInt) (p2 : GaussianInt) (p3 : GaussianInt) (p4 :
    GaussianInt) (p5 : GaussianInt) (p6 : GaussianInt) (p7 : GaussianInt) (p8 : GaussianInt) (p9
    : GaussianInt) (p10 : GaussianInt) (p11 : GaussianInt) (p12 : GaussianInt) :
    SixSubtileFaceLabel → GaussianInt := by
  classical
  exact fun
    | .I1 => p1 | .I2 => p2 | .I3 => p3 | .I4 => p4
    | .J1 => p5 | .J2 => p6 | .J3 => p7 | .J4 => p8
    | .J5 => p9 | .J6 => p10 | .J7 => p11 | .J8 => p12

private theorem translate_zero (T : ProtoTile) : TileTranslation T 0 = T := by
  classical
  cases T with
  | mk cells anchor =>
    simp only [TileTranslation]
    rw [ProtoTile.mk.injEq]
    constructor
    · ext z
      simp [GaussianTranslation]
    · simp [GaussianTranslation]

private theorem zero_membership (P : Fin 3 → Bool → ProtoTile) (u : GaussianInt) (v :
    GaussianInt) (p1 : GaussianInt) (p2 : GaussianInt) (p3 : GaussianInt) (p4 : GaussianInt) (p5
    : GaussianInt) (p6 : GaussianInt) (p7 : GaussianInt) (p8 : GaussianInt) (p9 : GaussianInt)
    (p10 : GaussianInt) (p11 : GaussianInt) (p12 : GaussianInt) (h1' : p1 ∈ FootprintVertices (P
    0 true) ∧ p1 ∈ FootprintVertices (P 0 false) ∧ p1 ∈ FootprintVertices (P 1 true)) (h2' : p2 ∈
    FootprintVertices (P 0 true) ∧ p2 ∈ FootprintVertices (P 0 false) ∧ p2 ∈ FootprintVertices (P
    1 false)) (h3' : p3 ∈ FootprintVertices (P 0 true) ∧ p3 ∈ FootprintVertices (P 1 true) ∧ p3 ∈
    FootprintVertices (P 2 false)) (h4' : p4 ∈ FootprintVertices (P 0 false) ∧ p4 ∈
    FootprintVertices (P 1 false) ∧ p4 ∈ FootprintVertices (P 2 true)) (h5 : p5 ∈
    FootprintVertices (P 0 true) ∧
  p5 ∈ FootprintVertices (TileTranslation (P 0 false) v) ∧ p5 ∈ FootprintVertices
      (TileTranslation (P 2 true) v)) (h6 : p6 ∈ FootprintVertices (P 0 true) ∧
  p6 ∈ FootprintVertices (TileTranslation (P 0 false) v) ∧ p6 ∈ FootprintVertices (P 2 false))
      (h7 : p7 ∈ FootprintVertices (P 0 true) ∧
  p7 ∈ FootprintVertices (TileTranslation (P 0 false) (u + v)) ∧
    p7 ∈ FootprintVertices (TileTranslation (P 1 true) (u + v))) (h8 : p8 ∈ FootprintVertices (P
        0 true) ∧
  p8 ∈ FootprintVertices (TileTranslation (P 0 false) (u + v)) ∧ p8 ∈ FootprintVertices (P 1
      false)) (h9 : p9 ∈ FootprintVertices (P 0 true) ∧
  p9 ∈ FootprintVertices (TileTranslation (P 1 true) (u + v)) ∧ p9 ∈ FootprintVertices
      (TileTranslation (P 2 true) v)) (h10 : p10 ∈ FootprintVertices (P 0 false) ∧
  p10 ∈ FootprintVertices (TileTranslation (P 1 false) (-u - v)) ∧
    p10 ∈ FootprintVertices (TileTranslation (P 2 false) (-v))) (h11 : p11 ∈ FootprintVertices (P
        1 true) ∧
  p11 ∈ FootprintVertices (TileTranslation (P 1 false) (-u)) ∧ p11 ∈ FootprintVertices
      (TileTranslation (P 2 true) (-u))) (h12 : p12 ∈ FootprintVertices (P 1 true) ∧
  p12 ∈ FootprintVertices (TileTranslation (P 1 false) (-u)) ∧ p12 ∈ FootprintVertices (P 2
      false)) (translate_zero : ∀ (T : ProtoTile), TileTranslation T 0 = T) : ∀ l i,
      (point p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12) l ∈ FootprintVertices
        (SubtileOccurrenceInterpretation P u v
          (SixSubtileFaceVertices ⟨l, 0, 0⟩ i)) := by
  classical
  let point : SixSubtileFaceLabel → GaussianInt := fun
    | .I1 => p1 | .I2 => p2 | .I3 => p3 | .I4 => p4
    | .J1 => p5 | .J2 => p6 | .J3 => p7 | .J4 => p8
    | .J5 => p9 | .J6 => p10 | .J7 => p11 | .J8 => p12
  change (∀ l i,
      point l ∈ FootprintVertices
        (SubtileOccurrenceInterpretation P u v
          (SixSubtileFaceVertices ⟨l, 0, 0⟩ i)))
  intro l i
  cases l
  · fin_cases i
    · simpa [point, SixSubtileFaceVertices, SubtileOccurrenceInterpretation,
        translate_zero] using h1'.1
    · simpa [point, SixSubtileFaceVertices, SubtileOccurrenceInterpretation,
        translate_zero] using h1'.2.1
    · simpa [point, SixSubtileFaceVertices, SubtileOccurrenceInterpretation,
        translate_zero] using h1'.2.2
  · fin_cases i
    · simpa [point, SixSubtileFaceVertices, SubtileOccurrenceInterpretation,
        translate_zero] using h2'.1
    · simpa [point, SixSubtileFaceVertices, SubtileOccurrenceInterpretation,
        translate_zero] using h2'.2.1
    · simpa [point, SixSubtileFaceVertices, SubtileOccurrenceInterpretation,
        translate_zero] using h2'.2.2
  · fin_cases i
    · simpa [point, SixSubtileFaceVertices, SubtileOccurrenceInterpretation,
        translate_zero] using h3'.1
    · simpa [point, SixSubtileFaceVertices, SubtileOccurrenceInterpretation,
        translate_zero] using h3'.2.1
    · simpa [point, SixSubtileFaceVertices, SubtileOccurrenceInterpretation,
        translate_zero] using h3'.2.2
  · fin_cases i
    · simpa [point, SixSubtileFaceVertices, SubtileOccurrenceInterpretation,
        translate_zero] using h4'.1
    · simpa [point, SixSubtileFaceVertices, SubtileOccurrenceInterpretation,
        translate_zero] using h4'.2.1
    · simpa [point, SixSubtileFaceVertices, SubtileOccurrenceInterpretation,
        translate_zero] using h4'.2.2
  · fin_cases i
    · simpa [point, SixSubtileFaceVertices, SubtileOccurrenceInterpretation,
        translate_zero] using h5.1
    · simpa [point, SixSubtileFaceVertices, SubtileOccurrenceInterpretation,
        translate_zero] using h5.2.1
    · simpa [point, SixSubtileFaceVertices, SubtileOccurrenceInterpretation,
        translate_zero] using h5.2.2
  · fin_cases i
    · simpa [point, SixSubtileFaceVertices, SubtileOccurrenceInterpretation,
        translate_zero] using h6.1
    · simpa [point, SixSubtileFaceVertices, SubtileOccurrenceInterpretation,
        translate_zero] using h6.2.1
    · simpa [point, SixSubtileFaceVertices, SubtileOccurrenceInterpretation,
        translate_zero] using h6.2.2
  · fin_cases i
    · simpa [point, SixSubtileFaceVertices, SubtileOccurrenceInterpretation,
        translate_zero] using h7.1
    · simpa [point, SixSubtileFaceVertices, SubtileOccurrenceInterpretation,
        translate_zero] using h7.2.1
    · simpa [point, SixSubtileFaceVertices, SubtileOccurrenceInterpretation,
        translate_zero] using h7.2.2
  · fin_cases i
    · simpa [point, SixSubtileFaceVertices, SubtileOccurrenceInterpretation,
        translate_zero] using h8.1
    · simpa [point, SixSubtileFaceVertices, SubtileOccurrenceInterpretation,
        translate_zero] using h8.2.1
    · simpa [point, SixSubtileFaceVertices, SubtileOccurrenceInterpretation,
        translate_zero] using h8.2.2
  · fin_cases i
    · simpa [point, SixSubtileFaceVertices, SubtileOccurrenceInterpretation,
        translate_zero] using h9.1
    · simpa [point, SixSubtileFaceVertices, SubtileOccurrenceInterpretation,
        translate_zero] using h9.2.1
    · simpa [point, SixSubtileFaceVertices, SubtileOccurrenceInterpretation,
        translate_zero] using h9.2.2
  · fin_cases i
    · simpa [point, SixSubtileFaceVertices, SubtileOccurrenceInterpretation,
        translate_zero] using h10.1
    · simpa [point, SixSubtileFaceVertices, SubtileOccurrenceInterpretation,
        translate_zero, sub_eq_add_neg] using h10.2.1
    · simpa [point, SixSubtileFaceVertices, SubtileOccurrenceInterpretation,
        translate_zero] using h10.2.2
  · fin_cases i
    · simpa [point, SixSubtileFaceVertices, SubtileOccurrenceInterpretation,
        translate_zero] using h11.1
    · simpa [point, SixSubtileFaceVertices, SubtileOccurrenceInterpretation,
        translate_zero] using h11.2.1
    · simpa [point, SixSubtileFaceVertices, SubtileOccurrenceInterpretation,
        translate_zero] using h11.2.2
  · fin_cases i
    · simpa [point, SixSubtileFaceVertices, SubtileOccurrenceInterpretation,
        translate_zero] using h12.1
    · simpa [point, SixSubtileFaceVertices, SubtileOccurrenceInterpretation,
        translate_zero] using h12.2.1
    · simpa [point, SixSubtileFaceVertices, SubtileOccurrenceInterpretation,
        translate_zero] using h12.2.2

private theorem translate_comp (T : ProtoTile) (a b : GaussianInt) :
      TileTranslation (TileTranslation T a) b = TileTranslation T (a + b) := by
  classical
  cases T with
  | mk cells anchor =>
    simp only [TileTranslation]
    rw [ProtoTile.mk.injEq]
    constructor
    · rw [Finset.image_image]
      congr 1
      funext x
      simp [GaussianTranslation, add_assoc]
    · simp [GaussianTranslation, add_assoc]

private theorem occurrence_shift (P : Fin 3 → Bool → ProtoTile) (u : GaussianInt) (v :
    GaussianInt) (translate_comp : ∀ (T : ProtoTile) (a b : GaussianInt), TileTranslation
    (TileTranslation T a) b = TileTranslation T (a + b)) (f : PeriodicSubtileFaceIndex) (i : Fin
    3) :
      SubtileOccurrenceInterpretation P u v (SixSubtileFaceVertices f i) =
        TileTranslation
          (SubtileOccurrenceInterpretation P u v
            (SixSubtileFaceVertices ⟨f.label, 0, 0⟩ i))
          ((f.first : GaussianInt) * u + (f.second : GaussianInt) * v) := by
  classical
  cases f with
  | mk l m n =>
    cases l <;> fin_cases i <;>
      simp only [SubtileOccurrenceInterpretation, SixSubtileFaceVertices, Fin.mk_one,
          Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero, Int.cast_add, Int.cast_one,
          zero_add, Int.cast_zero, zero_mul, one_mul, Int.cast_sub, zero_sub, Int.reduceNeg,
          Int.cast_neg, neg_mul, add_zero, Fin.reduceFinMk, Matrix.cons_val, Fin.zero_eta] <;>
      rw [translate_comp] <;> congr 1 <;> ring_nf

private noncomputable abbrev rho (u : GaussianInt) (v : GaussianInt) (p1 : GaussianInt) (p2 :
    GaussianInt) (p3 : GaussianInt) (p4 : GaussianInt) (p5 : GaussianInt) (p6 : GaussianInt) (p7
    : GaussianInt) (p8 : GaussianInt) (p9 : GaussianInt) (p10 : GaussianInt) (p11 : GaussianInt)
    (p12 : GaussianInt) : PeriodicSubtileFaceIndex → GaussianInt := by
  classical
  let point : SixSubtileFaceLabel → GaussianInt := fun
    | .I1 => p1 | .I2 => p2 | .I3 => p3 | .I4 => p4
    | .J1 => p5 | .J2 => p6 | .J3 => p7 | .J4 => p8
    | .J5 => p9 | .J6 => p10 | .J7 => p11 | .J8 => p12
  exact fun f =>
    GaussianTranslation
      ((f.first : GaussianInt) * u + (f.second : GaussianInt) * v)
      (point f.label)

private theorem rho_mem (P : Fin 3 → Bool → ProtoTile) (u : GaussianInt) (v : GaussianInt) (p1 :
    GaussianInt) (p2 : GaussianInt) (p3 : GaussianInt) (p4 : GaussianInt) (p5 : GaussianInt) (p6
    : GaussianInt) (p7 : GaussianInt) (p8 : GaussianInt) (p9 : GaussianInt) (p10 : GaussianInt)
    (p11 : GaussianInt) (p12 : GaussianInt) (zero_membership : ∀ (l : SixSubtileFaceLabel) (i :
    Fin 3),
  (point p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12) l ∈
    FootprintVertices
      (SubtileOccurrenceInterpretation P u v (SixSubtileFaceVertices ⟨l, 0, 0⟩ i)))
          (occurrence_shift : ∀ (f : PeriodicSubtileFaceIndex) (i : Fin 3),
  SubtileOccurrenceInterpretation P u v (SixSubtileFaceVertices f i) =
    TileTranslation
      (SubtileOccurrenceInterpretation P u v (SixSubtileFaceVertices ⟨f.label, 0, 0⟩ i))
      (↑f.first * u + ↑f.second * v)) : ∀ f i,
      (rho u v p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12) f ∈ FootprintVertices
        (SubtileOccurrenceInterpretation P u v (SixSubtileFaceVertices f i)) := by
  classical
  let point : SixSubtileFaceLabel → GaussianInt := fun
    | .I1 => p1 | .I2 => p2 | .I3 => p3 | .I4 => p4
    | .J1 => p5 | .J2 => p6 | .J3 => p7 | .J4 => p8
    | .J5 => p9 | .J6 => p10 | .J7 => p11 | .J8 => p12
  let rho : PeriodicSubtileFaceIndex → GaussianInt := fun f =>
    GaussianTranslation
      ((f.first : GaussianInt) * u + (f.second : GaussianInt) * v)
      (point f.label)
  change (∀ (l : SixSubtileFaceLabel) (i : Fin 3),
  point l ∈
    FootprintVertices
      (SubtileOccurrenceInterpretation P u v (SixSubtileFaceVertices ⟨l, 0, 0⟩ i)))
          at zero_membership
  change (∀ f i,
      rho f ∈ FootprintVertices
        (SubtileOccurrenceInterpretation P u v (SixSubtileFaceVertices f i)))
  intro f i
  rw [occurrence_shift]
  dsimp [rho]
  rcases TileTranslationFormulas
      (SubtileOccurrenceInterpretation P u v
        (SixSubtileFaceVertices ⟨f.label, 0, 0⟩ i))
      ((f.first : GaussianInt) * u + (f.second : GaussianInt) * v) with
    ⟨_, _, _, _, _, hfoot, _, _, _⟩
  rw [hfoot]
  exact ⟨point f.label, zero_membership f.label i, rfl⟩

end FacePointConstruction

theorem P4677T2FacePoints
    (P Q S : Fin 3 → Bool → ProtoTile) (u v : GaussianInt)
    (L : AddSubgroup GaussianInt) (D : P4677T2DrawingData u v L)
    (hQfoot : forall i s,
      FootprintVertices (Q i s) ⊆ FootprintVertices (P 0 true))
    (hSfoot : forall i s,
      FootprintVertices (S i s) ⊆ FootprintVertices (P 0 false))
    (hinner :
      TouchingTriple (Q 1 true) (S 2 false) (P 1 true) ∧
      TouchingTriple (Q 2 true) (S 1 false) (P 1 false) ∧
      TouchingTriple (Q 1 true) (P 1 true) (P 2 false) ∧
      TouchingTriple (S 1 false) (P 1 false) (P 2 true))
    (houter :
      TouchingTriple (P 0 true) (TileTranslation (P 0 false) v)
          (TileTranslation (P 2 true) v) ∧
      TouchingTriple (P 0 true) (TileTranslation (P 0 false) v)
          (P 2 false) ∧
      TouchingTriple (P 0 true) (TileTranslation (P 0 false) (u + v))
          (TileTranslation (P 1 true) (u + v)) ∧
      TouchingTriple (P 0 true) (TileTranslation (P 0 false) (u + v))
          (P 1 false) ∧
      TouchingTriple (P 0 true) (TileTranslation (P 1 true) (u + v))
          (TileTranslation (P 2 true) v) ∧
      TouchingTriple (P 0 false) (TileTranslation (P 1 false) (-u - v))
          (TileTranslation (P 2 false) (-v)) ∧
      TouchingTriple (P 1 true) (TileTranslation (P 1 false) (-u))
          (TileTranslation (P 2 true) (-u)) ∧
      TouchingTriple (P 1 true) (TileTranslation (P 1 false) (-u))
          (P 2 false)) :
    ∃ rho : PeriodicSubtileFaceIndex → GaussianInt,
      (∀ f i, rho f ∈ FootprintVertices
        (SubtileOccurrenceInterpretation P u v (SixSubtileFaceVertices f i))) ∧
      (∀ w f, rho (D.faceShift w f) = rho f + (w : GaussianInt)) ∧
      rho ⟨.I1, 0, 0⟩ ∈ FootprintVertices (Q 1 true) ∩ FootprintVertices (S 2 false) ∧
      rho ⟨.I2, 0, 0⟩ ∈ FootprintVertices (Q 2 true) ∩ FootprintVertices (S 1 false) ∧
      rho ⟨.I3, 0, 0⟩ ∈ FootprintVertices (Q 1 true) ∩ FootprintVertices (P 1 true) ∧
      rho ⟨.I4, 0, 0⟩ ∈ FootprintVertices (S 1 false) ∩ FootprintVertices (P 1 false) := by
-- BODY
  classical
  have boundary_to_footprint (T : ProtoTile) (x : GaussianInt)
      (hx : x ∈ BoundaryFootprintVertices T) : x ∈ FootprintVertices T :=
          FacePointConstruction.boundary_to_footprint T x hx
  have touching_point (A B C : ProtoTile) (h : TouchingTriple A B C) :
      ∃ x : GaussianInt, x ∈ BoundaryFootprintVertices A ∧
        x ∈ BoundaryFootprintVertices B ∧ x ∈ BoundaryFootprintVertices C :=
            FacePointConstruction.touching_point A B C h
  rcases hinner with ⟨hI1, hI2, hI3, hI4⟩
  rcases houter with ⟨hJ1, hJ2, hJ3, hJ4, hJ5, hJ6, hJ7, hJ8⟩
  obtain ⟨p1, hp1⟩ := touching_point _ _ _ hI1
  obtain ⟨p2, hp2⟩ := touching_point _ _ _ hI2
  obtain ⟨p3, hp3⟩ := touching_point _ _ _ hI3
  obtain ⟨p4, hp4⟩ := touching_point _ _ _ hI4
  obtain ⟨p5, hp5⟩ := touching_point _ _ _ hJ1
  obtain ⟨p6, hp6⟩ := touching_point _ _ _ hJ2
  obtain ⟨p7, hp7⟩ := touching_point _ _ _ hJ3
  obtain ⟨p8, hp8⟩ := touching_point _ _ _ hJ4
  obtain ⟨p9, hp9⟩ := touching_point _ _ _ hJ5
  obtain ⟨p10, hp10⟩ := touching_point _ _ _ hJ6
  obtain ⟨p11, hp11⟩ := touching_point _ _ _ hJ7
  obtain ⟨p12, hp12⟩ := touching_point _ _ _ hJ8
  have fp3 (A B C : ProtoTile) (x : GaussianInt)
      (h : x ∈ BoundaryFootprintVertices A ∧
        x ∈ BoundaryFootprintVertices B ∧ x ∈ BoundaryFootprintVertices C) :
      x ∈ FootprintVertices A ∧ x ∈ FootprintVertices B ∧
        x ∈ FootprintVertices C := FacePointConstruction.fp3 boundary_to_footprint A B C x h
  have h1 := FacePointConstruction.h1 P Q S p1 hp1 fp3
  have h2 := FacePointConstruction.h2 P Q S p2 hp2 fp3
  have h3 := FacePointConstruction.h3 P Q p3 hp3 fp3
  have h4 := FacePointConstruction.h4 P S p4 hp4 fp3
  have h1' : p1 ∈ FootprintVertices (P 0 true) ∧
      p1 ∈ FootprintVertices (P 0 false) ∧ p1 ∈ FootprintVertices (P 1 true) :=
          FacePointConstruction.h1' P Q S hQfoot hSfoot p1 h1
  have h2' : p2 ∈ FootprintVertices (P 0 true) ∧
      p2 ∈ FootprintVertices (P 0 false) ∧ p2 ∈ FootprintVertices (P 1 false) :=
          FacePointConstruction.h2' P Q S hQfoot hSfoot p2 h2
  have h3' : p3 ∈ FootprintVertices (P 0 true) ∧
      p3 ∈ FootprintVertices (P 1 true) ∧ p3 ∈ FootprintVertices (P 2 false) :=
          FacePointConstruction.h3' P Q hQfoot p3 h3
  have h4' : p4 ∈ FootprintVertices (P 0 false) ∧
      p4 ∈ FootprintVertices (P 1 false) ∧ p4 ∈ FootprintVertices (P 2 true) :=
          FacePointConstruction.h4' P S hSfoot p4 h4
  have h5 := FacePointConstruction.h5 P v p5 hp5 fp3
  have h6 := FacePointConstruction.h6 P v p6 hp6 fp3
  have h7 := FacePointConstruction.h7 P u v p7 hp7 fp3
  have h8 := FacePointConstruction.h8 P u v p8 hp8 fp3
  have h9 := FacePointConstruction.h9 P u v p9 hp9 fp3
  have h10 := FacePointConstruction.h10 P u v p10 hp10 fp3
  have h11 := FacePointConstruction.h11 P u p11 hp11 fp3
  have h12 := FacePointConstruction.h12 P u p12 hp12 fp3
  let point : SixSubtileFaceLabel → GaussianInt
    | .I1 => p1 | .I2 => p2 | .I3 => p3 | .I4 => p4
    | .J1 => p5 | .J2 => p6 | .J3 => p7 | .J4 => p8
    | .J5 => p9 | .J6 => p10 | .J7 => p11 | .J8 => p12
  have translate_zero (T : ProtoTile) : TileTranslation T 0 = T :=
      FacePointConstruction.translate_zero T
  have zero_membership : ∀ l i,
      point l ∈ FootprintVertices
        (SubtileOccurrenceInterpretation P u v
          (SixSubtileFaceVertices ⟨l, 0, 0⟩ i)) := FacePointConstruction.zero_membership P u v p1
              p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 h1' h2' h3' h4' h5 h6 h7 h8 h9 h10 h11 h12
              translate_zero
  have translate_comp (T : ProtoTile) (a b : GaussianInt) :
      TileTranslation (TileTranslation T a) b = TileTranslation T (a + b) :=
          FacePointConstruction.translate_comp T a b
  have occurrence_shift (f : PeriodicSubtileFaceIndex) (i : Fin 3) :
      SubtileOccurrenceInterpretation P u v (SixSubtileFaceVertices f i) =
        TileTranslation
          (SubtileOccurrenceInterpretation P u v
            (SixSubtileFaceVertices ⟨f.label, 0, 0⟩ i))
          ((f.first : GaussianInt) * u + (f.second : GaussianInt) * v) :=
              FacePointConstruction.occurrence_shift P u v translate_comp f i
  let rho : PeriodicSubtileFaceIndex → GaussianInt := fun f =>
    GaussianTranslation
      ((f.first : GaussianInt) * u + (f.second : GaussianInt) * v)
      (point f.label)
  have rho_mem : ∀ f i,
      rho f ∈ FootprintVertices
        (SubtileOccurrenceInterpretation P u v (SixSubtileFaceVertices f i)) :=
            FacePointConstruction.rho_mem P u v p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12
            zero_membership occurrence_shift
  refine ⟨rho, rho_mem, ?_, ?_, ?_, ?_, ?_⟩
  · intro w f
    rw [D.faceShift_eq]
    change point f.label +
        (((((f.first + (D.coordinates w).1 : Int) : GaussianInt) * u) +
          (((f.second + (D.coordinates w).2 : Int) : GaussianInt) * v))) =
      (point f.label +
        ((f.first : GaussianInt) * u + (f.second : GaussianInt) * v)) +
        (w : GaussianInt)
    rw [Int.cast_add, Int.cast_add, ← D.coordinates_spec w]
    ring_nf
  · simpa [rho, point, GaussianTranslation] using
      (show p1 ∈ FootprintVertices (Q 1 true) ∧
        p1 ∈ FootprintVertices (S 2 false) from ⟨h1.1, h1.2.1⟩)
  · simpa [rho, point, GaussianTranslation] using
      (show p2 ∈ FootprintVertices (Q 2 true) ∧
        p2 ∈ FootprintVertices (S 1 false) from ⟨h2.1, h2.2.1⟩)
  · simpa [rho, point, GaussianTranslation] using
      (show p3 ∈ FootprintVertices (Q 1 true) ∧
        p3 ∈ FootprintVertices (P 1 true) from ⟨h3.1, h3.2.1⟩)
  · simpa [rho, point, GaussianTranslation] using
      (show p4 ∈ FootprintVertices (S 1 false) ∧
        p4 ∈ FootprintVertices (P 1 false) from ⟨h4.1, h4.2.1⟩)

end ApollonianSuperharmonic

end
