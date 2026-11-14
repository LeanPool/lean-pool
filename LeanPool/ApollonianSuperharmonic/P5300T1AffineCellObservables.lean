/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.ProtoTileObservableExtensionality
public import LeanPool.ApollonianSuperharmonic.TileTranslationFormulas
public import LeanPool.ApollonianSuperharmonic.TileQuarterTurnFormulas

-- [TABLET NODE: P5300T1AffineCellObservables]

/-!
# P5300T1AffineCellObservables

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5300T1AffineCellObservables (T V : ProtoTile)
    (a C : GaussianInt) (neg : Bool) (hne : T.cells.Nonempty)
    (hc : V.cells = T.cells.image (fun z =>
      a + (if neg then C - z - 1 - ⟨0, 1⟩ else z))) :
    let f := fun z : GaussianInt => a + (if neg then C - z else z)
    FootprintVertices V = f '' FootprintVertices T ∧
      FootprintEdges V =
        (fun e : Finset GaussianInt => e.image f) '' FootprintEdges T := by
-- BODY
  classical
  let R := if neg then TileQuarterTurn (TileQuarterTurn T) else T
  let d := if neg then a + C else a
  let B := TileTranslation R d
  have hb : B.cells = T.cells.image (fun z =>
      a + (if neg then C - z - 1 - ⟨0, 1⟩ else z)) := by
    cases neg <;>
      simp only [B, R, d, Bool.false_eq_true, ite_false, ite_true, TileTranslation,
        TileQuarterTurn, Finset.image_image, Function.comp_def]
    · congr 1
      funext z
      simp [GaussianTranslation, add_comm]
    · congr 1
      funext z
      ext <;> simp [GaussianTranslation, GaussianQuarterTurn] <;> ring
  have hVB : V.cells = B.cells := hc.trans hb.symm
  have hnV : V.cells.Nonempty := by rw [hc]; exact hne.image _
  have hv := (ProtoTileObservableExtensionality V B hVB
    (by intro he; exact (hnV.ne_empty he).elim)).1
  have he : FootprintEdges V = FootprintEdges B := by
    unfold FootprintEdges
    rw [hVB]
  dsimp only
  rw [hv, he]
  cases neg
  · change FootprintVertices (TileTranslation T a) =
        (fun z => a + z) '' FootprintVertices T ∧
      FootprintEdges (TileTranslation T a) =
        (fun e => e.image (fun z => a + z)) '' FootprintEdges T
    constructor
    · rw [(TileTranslationFormulas T a).2.2.2.2.2.1]
      congr 1
      funext z
      exact add_comm z a
    · rw [(TileTranslationFormulas T a).2.2.2.2.2.2.1]
      congr 1
      funext e
      congr 1
      funext z
      exact add_comm z a
  · change FootprintVertices
        (TileTranslation (TileQuarterTurn (TileQuarterTurn T)) (a + C)) = _ ∧
      FootprintEdges
        (TileTranslation (TileQuarterTurn (TileQuarterTurn T)) (a + C)) = _
    have qv (S : ProtoTile) := (TileQuarterTurnFormulas S).2.2.2.2.2.1
    have qe (S : ProtoTile) := (TileQuarterTurnFormulas S).2.2.2.2.2.2.1
    constructor
    · rw [(TileTranslationFormulas _ _).2.2.2.2.2.1, qv, qv,
        Set.image_image, Set.image_image]
      congr 1
      funext z
      ext <;> simp [GaussianTranslation, GaussianQuarterTurn] <;> ring
    · rw [(TileTranslationFormulas _ _).2.2.2.2.2.2.1, qe, qe,
        Set.image_image, Set.image_image]
      congr 1
      funext e
      simp only [Finset.image_image, Function.comp_def]
      congr 1
      funext z
      ext <;> simp [GaussianTranslation, GaussianQuarterTurn] <;> ring

end ApollonianSuperharmonic

end
