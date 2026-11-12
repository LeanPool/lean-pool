/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.BandOrderedGeneralLayoutCertificate
public import LeanPool.ApollonianSuperharmonic.BandSignedOccurrenceHalfTurn
public import LeanPool.ApollonianSuperharmonic.P4630T1RingIndex
public import LeanPool.ApollonianSuperharmonic.QuarterTurnSymmetricCenteredTransport
public import LeanPool.ApollonianSuperharmonic.VectorRecursionLaws

-- [TABLET NODE: P4630T1ParentRotation]

/-!
# P4630T1ParentRotation

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4630T1ParentRotation
    (q : Fin 4 → CircleCoordinates) (cfg : BandOrderedGeneralConfiguration q)
    (C₀ : BandCircle) (T : ProtoTile)
    (cert : BandOrderedGeneralLayoutCertificate q cfg C₀ T) :
    ∃ t : GaussianInt,
      GaussianRealPoint t =
        ((TileCentroid T).1 + (TileCentroid T).2,
          (TileCentroid T).2 - (TileCentroid T).1) ∧
      ∀ i k,
        (SubtileOccurrenceInterpretation cert.P cert.u cert.v
          (P4630T1RingIndex i k)).cells.image
            (fun x => GaussianQuarterTurn x - 1 + t) =
          (SubtileOccurrenceInterpretation cert.P cert.u cert.v
            (P4630T1RingIndex i (k + 1))).cells := by
-- BODY
  classical
  let W := fun i : Fin 3 =>
    BandVectors.1 (q ((i + 2).succ)) (q ((i + 1).succ))
  let r : Fin 3 → GaussianInt := ![-cert.u - cert.v, cert.u, cert.v]
  let s : Fin 3 → GaussianInt := ![-cert.v, cert.u + cert.v, -cert.u]
  have quarter_add (x y : GaussianInt) :
      GaussianQuarterTurn (x + y) = GaussianQuarterTurn x + GaussianQuarterTurn y := by
    ext <;> simp [GaussianQuarterTurn]; ring
  have quarter_sub (x y : GaussianInt) :
      GaussianQuarterTurn (x - y) = GaussianQuarterTurn x - GaussianQuarterTurn y := by
    ext <;> simp [GaussianQuarterTurn]; ring
  have quarter_twice (x : GaussianInt) :
      GaussianQuarterTurn (GaussianQuarterTurn x) = -x := by
    ext <;> simp [GaussianQuarterTurn]
  have rotated : ProperBandQuadruple (![q 0, q 2, q 3, q 1]) := by
    refine ⟨SemiProperQuadruple.rotate cfg.proper.1, ?_⟩
    intro j
    fin_cases j
    · exact cfg.proper.2 1
    · exact cfg.proper.2 2
    · exact cfg.proper.2 0
  have laws := VectorRecursionLaws q cfg.proper.1
  have laws' := VectorRecursionLaws (![q 0, q 2, q 3, q 1]) rotated.1
  have U : cert.u = BandVectors.1 (q 2) (q 1) +
      GaussianQuarterTurn (BandVectors.1 (q 1) (q 3)) := by
    rw [cert.period_u]
    have flip : BandVectors.1 (q 0) (q 1) =
        (⟨0, 1⟩ : GaussianInt) * BandVectors.1 (q 1) (q 0) :=
      (laws.2.2.2.2 cfg.proper 0).1
    rw [flip, laws.2.2.1]
    ext <;> simp [GaussianQuarterTurn] <;> ring
  have V : cert.v = BandVectors.1 (q 3) (q 2) +
      GaussianQuarterTurn (BandVectors.1 (q 2) (q 1)) := by
    rw [cert.period_v]
    have flip : BandVectors.1 (q 0) (q 2) =
        (⟨0, 1⟩ : GaussianInt) * BandVectors.1 (q 2) (q 0) :=
      (laws.2.2.2.2 cfg.proper 1).1
    have recurrence : BandVectors.1 (q 2) (q 0) =
        BandVectors.1 (q 2) (q 1) -
          (⟨0, 1⟩ : GaussianInt) * BandVectors.1 (q 3) (q 2) := by
      simpa using laws'.2.2.1
    rw [flip, recurrence]
    ext <;> simp [GaussianQuarterTurn] <;> ring
  have offsets (i : Fin 3) : s i = GaussianQuarterTurn (W i) +
      GaussianQuarterTurn (r i) := by
    have hre := congrArg Zsqrtd.re laws.1
    have him := congrArg Zsqrtd.im laws.1
    fin_cases i
    all_goals
      simp? [W, r, s, U, V, GaussianQuarterTurn] at hre him ⊢
      apply Zsqrtd.ext_iff.mpr
      simp
      constructor <;> omega
  have offsets' (i : Fin 3) : GaussianQuarterTurn (s i) = -W i - r i := by
    rw [offsets i, quarter_add, quarter_twice, quarter_twice]
    abel
  have half := BandSignedOccurrenceHalfTurn q (TileCentroid T) cert.P
    (fun i b => (cert.outer_occurrence i b).1)
    (fun i b => (cert.outer_occurrence i b).2.2)
  choose τ hτ using fun i : Fin 3 =>
    QuarterTurnSymmetricCenteredTransport (cert.P i true) (cert.parent_quarter_turn i true)
  have root (i : Fin 3) : GaussianRealPoint (τ i + GaussianQuarterTurn (W i)) =
      ((TileCentroid T).1 + (TileCentroid T).2,
        (TileCentroid T).2 - (TileCentroid T).1) := by
    have hc := (cert.outer_occurrence i true).2.2
    have hx := congrArg Prod.fst hc
    have hy := congrArg Prod.snd hc
    have tx := congrArg Prod.fst (hτ i).1
    have ty := congrArg Prod.snd (hτ i).1
    have hx' : (TileCentroid (cert.P i true)).1 - (TileCentroid T).1 =
        (1 / 2 : Real) * ((W i).re + (W i).im) := by
      simpa [W, GaussianRealPoint, sub_eq_add_neg] using hx
    have hy' : (TileCentroid (cert.P i true)).2 - (TileCentroid T).2 =
        (1 / 2 : Real) * ((W i).im - (W i).re) := by
      simpa [W, GaussianRealPoint] using hy
    apply Prod.ext
    all_goals
      dsimp [GaussianRealPoint, GaussianQuarterTurn] at tx ty ⊢
      push_cast
      linarith
  let t := τ 0 + GaussianQuarterTurn (W 0)
  have center (i : Fin 3) : τ i + GaussianQuarterTurn (W i) = t := by
    have he := (root i).trans (root 0).symm
    have he₁ := congrArg Prod.fst he
    have he₂ := congrArg Prod.snd he
    dsimp [GaussianRealPoint] at he₁ he₂
    apply Zsqrtd.ext_iff.mpr
    constructor
    · exact_mod_cast he₁
    · exact_mod_cast he₂
  let F := fun x => GaussianQuarterTurn x - 1 + t
  have translate (S : ProtoTile) (z : GaussianInt) :
      (TileTranslation S z).cells.image F =
        (S.cells.image F).image (fun x => x + GaussianQuarterTurn z) := by
    simp only [TileTranslation, Finset.image_image, GaussianTranslation]
    apply congrArg (fun f : GaussianInt → GaussianInt => S.cells.image f)
    funext x
    dsimp [Function.comp_def, F, GaussianTranslation]
    rw [quarter_add]
    abel
  have plus (i : Fin 3) : (cert.P i true).cells.image F =
      (cert.P i true).cells.image (fun x => x + GaussianQuarterTurn (W i)) := by
    have hc : (cert.P i true).cells.image
        (fun x => GaussianQuarterTurn x - 1 + τ i) = (cert.P i true).cells := by
      simpa only [TileTranslation, TileQuarterTurn, Finset.image_image,
        GaussianTranslation, Function.comp_def] using (hτ i).2.1
    calc
      _ = ((cert.P i true).cells.image
          (fun x => GaussianQuarterTurn x - 1 + τ i)).image
            (fun x => x + GaussianQuarterTurn (W i)) := by
        rw [Finset.image_image]
        apply congrArg (fun f : GaussianInt → GaussianInt => (cert.P i true).cells.image f)
        funext x
        dsimp [F, Function.comp_def]
        rw [← center i]
        abel
      _ = _ := by rw [hc]
  have plus_shift (i : Fin 3) (z : GaussianInt) :
      (TileTranslation (cert.P i true) z).cells.image F =
        (cert.P i true).cells.image
          (fun x => x + GaussianQuarterTurn (W i) + GaussianQuarterTurn z) := by
    rw [translate, plus, Finset.image_image]
    rfl
  have negative (i : Fin 3) : (cert.P i false).cells.image F =
      (cert.P i true).cells.image (fun x => x - W i) := by
    have hc := (half i).1
    change (TileTranslation (cert.P i true)
      (GaussianQuarterTurn (W i) - W i)).cells = (cert.P i false).cells at hc
    rw [← hc, plus_shift]
    apply congrArg (fun f : GaussianInt → GaussianInt => (cert.P i true).cells.image f)
    funext x
    rw [quarter_sub, quarter_twice]
    abel
  have negative_shift (i : Fin 3) (z : GaussianInt) :
      (TileTranslation (cert.P i false) z).cells.image F =
        (cert.P i true).cells.image (fun x => x - W i + GaussianQuarterTurn z) := by
    rw [translate, negative, Finset.image_image]
    rfl
  have minus_cells (i : Fin 3) (z : GaussianInt) :
      (TileTranslation (cert.P i false) z).cells =
        (cert.P i true).cells.image (fun x => x + GaussianQuarterTurn (W i) - W i + z) := by
    have hc := (half i).1
    change (TileTranslation (cert.P i true)
      (GaussianQuarterTurn (W i) - W i)).cells = (cert.P i false).cells at hc
    change (cert.P i false).cells.image (GaussianTranslation z) = _
    rw [← hc]
    simp only [TileTranslation, Finset.image_image, GaussianTranslation]
    congr 1
    funext x
    dsimp [Function.comp_def, GaussianTranslation]
    abel
  have table (i : Fin 3) (k : Fin 4) :
      SubtileOccurrenceInterpretation cert.P cert.u cert.v (P4630T1RingIndex i k) =
        if k = 0 then TileTranslation (cert.P i true) (r i)
        else if k = 1 then TileTranslation (cert.P i true) (s i)
        else if k = 2 then TileTranslation (cert.P i false) (-r i)
        else TileTranslation (cert.P i false) (-s i) := by
    fin_cases i <;> fin_cases k <;>
      simp [P4630T1RingIndex, SubtileOccurrenceInterpretation, r, s,
        sub_eq_add_neg, add_comm]
  refine ⟨t, root 0, ?_⟩
  intro i k
  change Finset.image F _ = _
  rw [table, table]
  fin_cases k
  all_goals norm_num [Fin.ext_iff, Fin.add_def]
  · rw [plus_shift]
    change _ = (cert.P i true).cells.image (GaussianTranslation (s i))
    rw [offsets i]
    congr 1
    funext x
    simp [GaussianTranslation, add_assoc]
  · rw [plus_shift, minus_cells, offsets']
    congr 1
    funext x
    abel
  · rw [negative_shift, minus_cells]
    simp only [show ∀ x : GaussianInt, GaussianQuarterTurn (-x) =
      -GaussianQuarterTurn x by intro x; ext <;> simp [GaussianQuarterTurn]]
    rw [offsets i]
    congr 1
    funext x
    abel
  · rw [negative_shift]
    change _ = (cert.P i true).cells.image (GaussianTranslation (r i))
    simp only [show ∀ x : GaussianInt, GaussianQuarterTurn (-x) =
      -GaussianQuarterTurn x by intro x; ext <;> simp [GaussianQuarterTurn]]
    rw [offsets']
    congr 1
    funext x
    simp only [GaussianTranslation]
    abel

end ApollonianSuperharmonic

end
