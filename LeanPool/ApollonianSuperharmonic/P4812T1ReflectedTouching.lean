/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.QuarterTurnSymmetricCenteredTransport
public import LeanPool.ApollonianSuperharmonic.ProtoTileObservableExtensionality
public import LeanPool.ApollonianSuperharmonic.TouchingTripleCovariance
public import LeanPool.ApollonianSuperharmonic.TileQuarterTurn
public import LeanPool.ApollonianSuperharmonic.TileTranslation
public import LeanPool.ApollonianSuperharmonic.TileTouching
public import LeanPool.ApollonianSuperharmonic.TouchingTriple
public import Mathlib.Tactic.Ring

-- [TABLET NODE: P4812T1ReflectedTouching]

/-!
# P4812T1ReflectedTouching

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4812T1ReflectedTouching (T : ProtoTile) (a b : GaussianInt)
    (hne : T.cells.Nonempty) (hsym : QuarterTurnSymmetric T)
    (ht : TouchingTriple T (TileTranslation T a) (TileTranslation T (-b))) :
    TouchingTriple T (TileTranslation T (-a)) (TileTranslation T b) := by
-- BODY
  classical
  obtain ⟨u, _, hfixed, _⟩ := QuarterTurnSymmetricCenteredTransport T hsym
  let F : ProtoTile → ProtoTile := fun U => TileTranslation (TileQuarterTurn U) u
  let f : GaussianInt → GaussianInt := fun z => GaussianQuarterTurn z - 1 + u
  have cellsF (U : ProtoTile) : (F U).cells = U.cells.image f := by
    simp [F, f, TileTranslation, TileQuarterTurn, Finset.image_image,
      Function.comp_def, GaussianTranslation]
  have fixed2 : (F (F T)).cells = T.cells := by
    calc
      (F (F T)).cells = (F T).cells.image f := cellsF _
      _ = T.cells.image f := congrArg (fun s => s.image f) hfixed
      _ = (F T).cells := (cellsF T).symm
      _ = T.cells := hfixed
  have translated (z : GaussianInt) :
      (F (F (TileTranslation T z))).cells = (TileTranslation T (-z)).cells := by
    have comm : (F (F (TileTranslation T z))).cells =
        (TileTranslation (F (F T)) (-z)).cells := by
      simp only [cellsF, TileTranslation, Finset.image_image]
      congr 1
      funext x
      apply Zsqrtd.ext <;> simp [f, Function.comp_def, GaussianQuarterTurn,
        GaussianTranslation] <;> ring
    rw [comm]
    change (F (F T)).cells.image _ = T.cells.image _
    rw [fixed2]
  have preserves (A B C : ProtoTile) (h : TouchingTriple A B C) :
      TouchingTriple (F A) (F B) (F C) :=
    (TouchingTripleCovariance (TileQuarterTurn A) (TileQuarterTurn B)
      (TileQuarterTurn C) u).1.mp ((TouchingTripleCovariance A B C u).2.1.mp h)
  have ht2 := preserves _ _ _ (preserves _ _ _ ht)
  have ha := translated a
  have hb : (F (F (TileTranslation T (-b)))).cells = (TileTranslation T b).cells := by
    simpa only [neg_neg] using translated (-b)
  have nonempty_tr (z : GaussianInt) : (TileTranslation T z).cells.Nonempty :=
    hne.image _
  have obs (A B : ProtoTile) (hc : A.cells = B.cells) (hn : B.cells.Nonempty) :=
    ProtoTileObservableExtensionality A B hc (by
      intro h
      exact (Finset.nonempty_iff_ne_empty.mp hn (hc.symm.trans h)).elim)
  have o0 := obs _ _ fixed2 hne
  have oa := obs _ _ ha (nonempty_tr (-a))
  have ob := obs _ _ hb (nonempty_tr b)
  have e0 := Finset.nonempty_iff_ne_empty.mp hne
  have ea := Finset.nonempty_iff_ne_empty.mp (nonempty_tr (-a))
  have eb := Finset.nonempty_iff_ne_empty.mp (nonempty_tr b)
  unfold TouchingTriple TileTouching at ht2 ⊢
  simpa only [fixed2, ha, hb, o0.2.1, o0.2.2.1,
    oa.2.1, oa.2.2.1, ob.2.1, ob.2.2.1, e0, ea, eb, false_and, or_false] using ht2

end ApollonianSuperharmonic

end
