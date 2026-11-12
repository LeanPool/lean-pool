/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.BoundaryFootprintVertices
public import LeanPool.ApollonianSuperharmonic.FootprintEdges
public import LeanPool.ApollonianSuperharmonic.FootprintVertices
public import LeanPool.ApollonianSuperharmonic.TileCentroid
public import LeanPool.ApollonianSuperharmonic.TileRealization
public import LeanPool.ApollonianSuperharmonic.TileTranslation

-- [TABLET NODE: TileTranslationFormulas]

/-!
# TileTranslationFormulas

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

private theorem translationRealization (T : ProtoTile) (u : GaussianInt) :
    TileRealization (TileTranslation T u) =
      (fun p : Real × Real =>
        (p.1 + (u.re : Int), p.2 + (u.im : Int))) '' TileRealization T := by
  dsimp [TileTranslation]
  ext p
  rcases p with ⟨p, q⟩
  simp only [TileRealization, ClosedSquareRealization, GaussianTranslation,
    Set.mem_iUnion, Set.mem_image, Finset.mem_image,
    ]
  have realPart (z w : GaussianInt) :
      ((GaussianTranslation w z).re : Real) = (z.re : Real) + (w.re : Real) := by
    cases z; cases w; simp [GaussianTranslation]
  have imagPart (z w : GaussianInt) :
      ((GaussianTranslation w z).im : Real) = (z.im : Real) + (w.im : Real) := by
    cases z; cases w; simp [GaussianTranslation]
  have realAdd (z w : GaussianInt) :
      (((z + w).re : Int) : Real) = (z.re : Real) + (w.re : Real) := by
    cases z; cases w; simp
  have imagAdd (z w : GaussianInt) :
      (((z + w).im : Int) : Real) = (z.im : Real) + (w.im : Real) := by
    cases z; cases w; simp
  have realCoord (w : GaussianInt) :
      (GaussianInt.toComplex w).re = (w.re : Real) := by
    exact (GaussianInt.intCast_re w).symm
  have imagCoord (w : GaussianInt) :
      (GaussianInt.toComplex w).im = (w.im : Real) := by
    exact (GaussianInt.intCast_im w).symm
  constructor
  · rintro ⟨i, hi, hp⟩
    rcases Finset.mem_image.mp hi with ⟨a, ha, hia⟩
    subst i
    refine ⟨((p - (u.re : Real)), (q - (u.im : Real))), ?_, ?_⟩
    · refine ⟨a, ha, ?_⟩
      simp only [realPart, imagPart] at hp ⊢
      simp only [Set.mem_Icc, Prod.le_def] at hp ⊢
      constructor <;> constructor <;>
        linarith [hp.1.1, hp.1.2, hp.2.1, hp.2.2]
    · apply Prod.ext
      all_goals dsimp
      all_goals ring
  · rintro ⟨x, ⟨i, hi, hx⟩, heq⟩
    rcases x with ⟨x, y⟩
    refine ⟨i + u, Finset.mem_image.mpr ⟨i, hi, rfl⟩, ?_⟩
    simp only [Set.mem_Icc, Prod.le_def] at hx ⊢
    simp only [realAdd, imagAdd]
    have hp := congrArg Prod.fst heq
    have hq := congrArg Prod.snd heq
    dsimp at hp hq
    constructor <;> constructor <;>
      linarith [hx.1.1, hx.1.2, hx.2.1, hx.2.2, hp, hq]

private theorem translationCentroid (T : ProtoTile) (u : GaussianInt) :
    TileCentroid (TileTranslation T u) =
      ((TileCentroid T).1 + (u.re : Int),
        (TileCentroid T).2 + (u.im : Int)) := by
  dsimp [TileTranslation]
  by_cases h : T.cells.Nonempty
  · have hinj : Function.Injective (GaussianTranslation u) := by
      intro a b hab
      exact add_right_cancel hab
    have translatedRe (x : GaussianInt) :
        (GaussianInt.toComplex (GaussianTranslation u x)).re =
          (GaussianInt.toComplex x).re + (GaussianInt.toComplex u).re := by
      cases x; cases u; simp [GaussianTranslation]
    have translatedIm (x : GaussianInt) :
        (GaussianInt.toComplex (GaussianTranslation u x)).im =
          (GaussianInt.toComplex x).im + (GaussianInt.toComplex u).im := by
      cases x; cases u; simp [GaussianTranslation]
    simp only [TileCentroid, Finset.image_nonempty, h, ↓reduceIte, Int.reduceNeg,
        Int.cast_sum, GaussianInt.intCast_re, one_div, GaussianInt.intCast_im, Prod.mk.injEq]
    rw [Finset.card_image_of_injective T.cells hinj]
    rw [Finset.sum_image hinj.injOn]
    rw [Finset.sum_image hinj.injOn]
    simp only [translatedRe, translatedIm]
    simp [Finset.sum_add_distrib]
    have cardReal : (Finset.card T.cells : Real) ≠ 0 := by
      exact_mod_cast h.card_pos.ne'
    constructor <;>
      field_simp [cardReal] <;> ring_nf
  · have translatedRe (x : GaussianInt) :
        (GaussianInt.toComplex (GaussianTranslation u x)).re =
          (GaussianInt.toComplex x).re + (GaussianInt.toComplex u).re := by
      cases x; cases u; simp [GaussianTranslation]
    have translatedIm (x : GaussianInt) :
        (GaussianInt.toComplex (GaussianTranslation u x)).im =
          (GaussianInt.toComplex x).im + (GaussianInt.toComplex u).im := by
      cases x; cases u; simp [GaussianTranslation]
    simp [TileCentroid, h, translatedRe, translatedIm]

private theorem translationVertices (T : ProtoTile) (u : GaussianInt) :
    FootprintVertices (TileTranslation T u) =
      GaussianTranslation u '' FootprintVertices T := by
  dsimp [TileTranslation]
  by_cases h : T.cells.Nonempty
  · ext v
    simp only [FootprintVertices, Finset.image_nonempty, h, ↓reduceIte, Finset.mem_image,
        GaussianTranslation, Int.reduceNeg, exists_exists_and_eq_and, Set.mem_ofPred_eq,
        Set.mem_image]
    constructor
    · rintro ⟨a, ha, hv⟩
      rcases hv with h0 | h1 | h2 | h3
      · refine ⟨a, ⟨a, ha, Or.inl rfl⟩, h0.symm⟩
      · refine ⟨a + 1, ⟨a, ha, Or.inr (Or.inl rfl)⟩, ?_⟩
        simpa [add_assoc, add_comm] using h1.symm
      · refine ⟨a + ⟨0, 1⟩, ⟨a, ha, Or.inr (Or.inr (Or.inl rfl))⟩, ?_⟩
        simpa [add_assoc, add_comm] using h2.symm
      · refine ⟨a + 1 + ⟨0, 1⟩, ⟨a, ha, Or.inr (Or.inr (Or.inr rfl))⟩, ?_⟩
        simpa [add_assoc, add_comm] using h3.symm
    · rintro ⟨x, ⟨a, ha, hx⟩, hv⟩
      refine ⟨a, ha, ?_⟩
      rw [← hv]
      rcases hx with rfl | rfl | rfl | rfl <;>
        simp [add_assoc, add_comm]
  · simp [FootprintVertices, h, GaussianTranslation]

private theorem translationEdges (T : ProtoTile) (u : GaussianInt) :
    FootprintEdges (TileTranslation T u) =
      (fun e : Finset GaussianInt => e.image (GaussianTranslation u)) ''
        FootprintEdges T := by
  dsimp [TileTranslation]
  ext e
  simp only [FootprintEdges, Finset.mem_image, GaussianTranslation, Int.reduceNeg,
      exists_exists_and_eq_and, Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · rintro ⟨a, ha, he⟩
    rcases he with h0 | h1 | h2 | h3
    · refine ⟨{a, a + 1}, ⟨a, ha, Or.inl rfl⟩, ?_⟩
      rw [h0]
      simp [GaussianTranslation, Finset.image_insert, add_assoc, add_comm]
    · refine ⟨{a, a + ⟨0, 1⟩}, ⟨a, ha, Or.inr (Or.inl rfl)⟩, ?_⟩
      rw [h1]
      simp [GaussianTranslation, Finset.image_insert, add_assoc, add_comm]
    · refine ⟨{a + 1, a + 1 + ⟨0, 1⟩},
        ⟨a, ha, Or.inr (Or.inr (Or.inl rfl))⟩, ?_⟩
      rw [h2]
      simp [GaussianTranslation, Finset.image_insert, add_assoc, add_comm]
    · refine ⟨{a + ⟨0, 1⟩, a + 1 + ⟨0, 1⟩},
        ⟨a, ha, Or.inr (Or.inr (Or.inr rfl))⟩, ?_⟩
      rw [h3]
      simp [GaussianTranslation, Finset.image_insert, add_assoc, add_comm]
  · rintro ⟨x, ⟨a, ha, hx⟩, he⟩
    refine ⟨a, ha, ?_⟩
    rcases hx with rfl | rfl | rfl | rfl <;>
      rw [← he] <;>
      simp [GaussianTranslation, Finset.image_insert, add_assoc, add_comm]

private theorem translationBoundaryVertices (T : ProtoTile) (u : GaussianInt) :
    BoundaryFootprintVertices (TileTranslation T u) =
      GaussianTranslation u '' BoundaryFootprintVertices T := by
  dsimp [TileTranslation]
  by_cases h : T.cells.Nonempty
  · ext v
    simp only [BoundaryFootprintVertices, ite_eq_left h]
    have cellMem (z : GaussianInt) :
        (∃ a ∈ T.cells, a + u = z) ↔ z - u ∈ T.cells := by
      constructor
      · rintro ⟨a, ha, rfl⟩
        simpa [add_comm] using ha
      · intro hz
        exact ⟨z - u, hz, by simp⟩
    have imageMem (z : GaussianInt) :
        (∃ a ∈ T.cells, a + u = z) ↔ z - u ∈ T.cells := cellMem z
    have absentMem (z : GaussianInt) :
        (∀ a ∈ T.cells, ¬a + u = z) ↔ z - u ∉ T.cells := by
      constructor
      · intro ha hz
        obtain ⟨a, hca, heq⟩ := (cellMem z).mpr hz
        exact ha a hca heq
      · intro hz a ha heq
        apply hz
        exact (cellMem z).mp ⟨a, ha, heq⟩
    have translatedCell (z : GaussianInt) :
        z ∈ (TileTranslation T u).cells ↔ z - u ∈ T.cells := by
      change z ∈ T.cells.image (GaussianTranslation u) ↔ z - u ∈ T.cells
      simpa [GaussianTranslation] using cellMem z
    have edgeFormula :
        BoundaryFootprintEdges (TileTranslation T u) =
          (fun e : Finset GaussianInt => e.image (GaussianTranslation u)) ''
            BoundaryFootprintEdges T := by
      ext e
      change (∃ z : GaussianInt,
          (e = {z, z + 1} ∧
            ((z ∈ (TileTranslation T u).cells ∧
                z - ⟨0, 1⟩ ∉ (TileTranslation T u).cells) ∨
              (z ∉ (TileTranslation T u).cells ∧
                z - ⟨0, 1⟩ ∈ (TileTranslation T u).cells))) ∨
          (e = {z, z + ⟨0, 1⟩} ∧
            ((z ∈ (TileTranslation T u).cells ∧
                z - 1 ∉ (TileTranslation T u).cells) ∨
              (z ∉ (TileTranslation T u).cells ∧
                z - 1 ∈ (TileTranslation T u).cells)))) ↔
        ∃ f, f ∈ BoundaryFootprintEdges T ∧
          f.image (GaussianTranslation u) = e
      constructor
      · rintro ⟨z, hz⟩
        rcases hz with ⟨rfl, hz⟩ | ⟨rfl, hz⟩
        · rcases hz with hz | hz
          · refine ⟨{z - u, (z - u) + 1}, ?_, ?_⟩
            · change ∃ w, ({z - u, (z - u) + 1} = {w, w + 1} ∧
                ((w ∈ T.cells ∧ w - ⟨0, 1⟩ ∉ T.cells) ∨
                  (w ∉ T.cells ∧ w - ⟨0, 1⟩ ∈ T.cells))) ∨
                ({z - u, (z - u) + 1} = {w, w + ⟨0, 1⟩} ∧
                ((w ∈ T.cells ∧ w - 1 ∉ T.cells) ∨
                  (w ∉ T.cells ∧ w - 1 ∈ T.cells)))
              refine ⟨z - u, Or.inl ⟨rfl, Or.inl ?_⟩⟩
              convert hz using 1 <;>
                simp [translatedCell, sub_eq_add_neg,
                  add_assoc, add_comm, add_left_comm]
            · simp [GaussianTranslation, Finset.image_insert, sub_eq_add_neg,
                add_assoc, add_comm]; try abel
          · refine ⟨{z - u, (z - u) + 1}, ?_, ?_⟩
            · change ∃ w, ({z - u, (z - u) + 1} = {w, w + 1} ∧
                ((w ∈ T.cells ∧ w - ⟨0, 1⟩ ∉ T.cells) ∨
                  (w ∉ T.cells ∧ w - ⟨0, 1⟩ ∈ T.cells))) ∨
                ({z - u, (z - u) + 1} = {w, w + ⟨0, 1⟩} ∧
                ((w ∈ T.cells ∧ w - 1 ∉ T.cells) ∨
                  (w ∉ T.cells ∧ w - 1 ∈ T.cells)))
              refine ⟨z - u, Or.inl ⟨rfl, Or.inr ?_⟩⟩
              convert hz using 1 <;>
                simp [translatedCell, sub_eq_add_neg,
                  add_assoc, add_comm, add_left_comm]
            · simp [GaussianTranslation, Finset.image_insert, sub_eq_add_neg,
                add_assoc, add_comm]; try abel
        · rcases hz with hz | hz
          · refine ⟨{z - u, (z - u) + ⟨0, 1⟩}, ?_, ?_⟩
            · change ∃ w, ({z - u, (z - u) + ⟨0, 1⟩} = {w, w + 1} ∧
                ((w ∈ T.cells ∧ w - ⟨0, 1⟩ ∉ T.cells) ∨
                  (w ∉ T.cells ∧ w - ⟨0, 1⟩ ∈ T.cells))) ∨
                ({z - u, (z - u) + ⟨0, 1⟩} = {w, w + ⟨0, 1⟩} ∧
                ((w ∈ T.cells ∧ w - 1 ∉ T.cells) ∨
                  (w ∉ T.cells ∧ w - 1 ∈ T.cells)))
              refine ⟨z - u, Or.inr ⟨rfl, Or.inl ?_⟩⟩
              convert hz using 1 <;>
                simp [translatedCell, sub_eq_add_neg,
                  add_assoc, add_comm, add_left_comm]
            · simp [GaussianTranslation, Finset.image_insert, sub_eq_add_neg,
                add_assoc, add_comm]; try abel
          · refine ⟨{z - u, (z - u) + ⟨0, 1⟩}, ?_, ?_⟩
            · change ∃ w, ({z - u, (z - u) + ⟨0, 1⟩} = {w, w + 1} ∧
                ((w ∈ T.cells ∧ w - ⟨0, 1⟩ ∉ T.cells) ∨
                  (w ∉ T.cells ∧ w - ⟨0, 1⟩ ∈ T.cells))) ∨
                ({z - u, (z - u) + ⟨0, 1⟩} = {w, w + ⟨0, 1⟩} ∧
                ((w ∈ T.cells ∧ w - 1 ∉ T.cells) ∨
                  (w ∉ T.cells ∧ w - 1 ∈ T.cells)))
              refine ⟨z - u, Or.inr ⟨rfl, Or.inr ?_⟩⟩
              convert hz using 1 <;>
                simp [translatedCell, sub_eq_add_neg,
                  add_assoc, add_comm, add_left_comm]
            · simp [GaussianTranslation, Finset.image_insert, sub_eq_add_neg,
                add_assoc, add_comm]; try abel
      · rintro ⟨f, hf, rfl⟩
        rcases hf with ⟨z, hz⟩
        rcases hz with ⟨hf, hz⟩ | ⟨hf, hz⟩
        · refine ⟨z + u, ?_⟩
          left
          refine ⟨?_, ?_⟩
          · simpa [GaussianTranslation, Finset.image_insert, add_assoc, add_comm]
            using congrArg (fun q => q.image (GaussianTranslation u)) hf
          · convert hz using 1 <;>
              simp [translatedCell, sub_eq_add_neg,
                add_assoc, add_comm, add_left_comm] <;> try abel; simp
        · refine ⟨z + u, ?_⟩
          right
          refine ⟨?_, ?_⟩
          · simpa [GaussianTranslation, Finset.image_insert, add_assoc, add_comm]
            using congrArg (fun q => q.image (GaussianTranslation u)) hf
          · convert hz using 1 <;>
              simp [translatedCell, sub_eq_add_neg,
                add_assoc, add_comm, add_left_comm] <;> try abel; simp
    have imageNonempty : (T.cells.image (GaussianTranslation u)).Nonempty :=
      h.image _
    simp only [ite_eq_left imageNonempty]
    change (v ∈ {v | ∃ e ∈ BoundaryFootprintEdges (TileTranslation T u), v ∈ e}) ↔ _
    rw [edgeFormula]
    constructor
    · rintro ⟨e, ⟨f, hf, rfl⟩, hv⟩
      rcases Finset.mem_image.mp hv with ⟨y, hy, rfl⟩
      exact ⟨y, ⟨f, hf, hy⟩, rfl⟩
    · rintro ⟨y, ⟨f, hf, hy⟩, rfl⟩
      exact ⟨f.image (GaussianTranslation u), ⟨f, hf, rfl⟩,
        Finset.mem_image.mpr ⟨y, hy, rfl⟩⟩
  · simp [BoundaryFootprintVertices, GaussianTranslation, h]

private theorem translationBoundaryEdges (T : ProtoTile) (u : GaussianInt) :
    BoundaryFootprintEdges (TileTranslation T u) =
      (fun e : Finset GaussianInt => e.image (GaussianTranslation u)) ''
        BoundaryFootprintEdges T := by
  dsimp [TileTranslation]
  ext e
  have translatedCell (z : GaussianInt) :
      z ∈ (TileTranslation T u).cells ↔ z - u ∈ T.cells := by
    change z ∈ T.cells.image (GaussianTranslation u) ↔ z - u ∈ T.cells
    constructor
    · intro hz
      rw [Finset.mem_image] at hz
      rcases hz with ⟨a, ha, rfl⟩
      simpa [GaussianTranslation, sub_eq_add_neg, add_assoc, add_comm,
        add_left_comm] using ha
    · intro hz
      apply Finset.mem_image.mpr
      refine ⟨z - u, hz, ?_⟩
      simp [GaussianTranslation, sub_eq_add_neg, add_comm,
        ]
  change (∃ z : GaussianInt,
      (e = {z, z + 1} ∧
        ((z ∈ (TileTranslation T u).cells ∧
            z - ⟨0, 1⟩ ∉ (TileTranslation T u).cells) ∨
          (z ∉ (TileTranslation T u).cells ∧
            z - ⟨0, 1⟩ ∈ (TileTranslation T u).cells))) ∨
      (e = {z, z + ⟨0, 1⟩} ∧
        ((z ∈ (TileTranslation T u).cells ∧
            z - 1 ∉ (TileTranslation T u).cells) ∨
          (z ∉ (TileTranslation T u).cells ∧
            z - 1 ∈ (TileTranslation T u).cells)))) ↔
    ∃ f, f ∈ BoundaryFootprintEdges T ∧
      f.image (GaussianTranslation u) = e
  constructor
  · rintro ⟨z, hz⟩
    rcases hz with ⟨he, hp⟩ | ⟨he, hp⟩
    · rcases hp with hp | hp
      · refine ⟨{z - u, (z - u) + 1}, ?_, ?_⟩
        · refine ⟨z - u, Or.inl ⟨rfl, Or.inl ?_⟩⟩
          simpa [translatedCell, sub_eq_add_neg, add_assoc, add_comm,
            add_left_comm] using hp
        · subst e
          simp [GaussianTranslation, Finset.image_insert, sub_eq_add_neg,
            add_assoc, add_comm]; abel
      · refine ⟨{z - u, (z - u) + 1}, ?_, ?_⟩
        · refine ⟨z - u, Or.inl ⟨rfl, Or.inr ?_⟩⟩
          simpa [translatedCell, sub_eq_add_neg, add_assoc, add_comm,
            add_left_comm] using hp
        · subst e
          simp [GaussianTranslation, Finset.image_insert, sub_eq_add_neg,
            add_assoc, add_comm]; abel
    · rcases hp with hp | hp
      · refine ⟨{z - u, (z - u) + ⟨0, 1⟩}, ?_, ?_⟩
        · refine ⟨z - u, Or.inr ⟨rfl, Or.inl ?_⟩⟩
          simpa [translatedCell, sub_eq_add_neg, add_assoc, add_comm,
            add_left_comm] using hp
        · subst e
          simp [GaussianTranslation, Finset.image_insert, sub_eq_add_neg,
            add_assoc, add_comm]; abel
      · refine ⟨{z - u, (z - u) + ⟨0, 1⟩}, ?_, ?_⟩
        · refine ⟨z - u, Or.inr ⟨rfl, Or.inr ?_⟩⟩
          simpa [translatedCell, sub_eq_add_neg, add_assoc, add_comm,
            add_left_comm] using hp
        · subst e
          simp [GaussianTranslation, Finset.image_insert, sub_eq_add_neg,
            add_assoc, add_comm]; abel
  · rintro ⟨f, hf, he⟩
    rcases hf with ⟨z, hz⟩
    rcases hz with ⟨hf, hp⟩ | ⟨hf, hp⟩
    · refine ⟨z + u, ?_⟩
      left
      refine ⟨?_, ?_⟩
      · rw [← he]
        simpa [GaussianTranslation, Finset.image_insert, add_assoc, add_comm]
          using congrArg (fun q => q.image (GaussianTranslation u)) hf
      · subst e
        rw [translatedCell, translatedCell]
        rcases hp with hp | hp
        · left
          constructor
          · simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hp.1
          · have shift : z + u - ⟨0, 1⟩ - u = z - ⟨0, 1⟩ := by abel
            rw [shift]
            exact hp.2
        · right
          constructor
          · simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hp.1
          · have shift : z + u - ⟨0, 1⟩ - u = z - ⟨0, 1⟩ := by abel
            rw [shift]
            exact hp.2
    · refine ⟨z + u, ?_⟩
      right
      refine ⟨?_, ?_⟩
      · rw [← he]
        simpa [GaussianTranslation, Finset.image_insert, add_assoc, add_comm]
          using congrArg (fun q => q.image (GaussianTranslation u)) hf
      · subst e
        rw [translatedCell, translatedCell]
        rcases hp with hp | hp
        · left
          constructor
          · simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hp.1
          · have shift : z + u - 1 - u = z - 1 := by abel
            rw [shift]
            exact hp.2
        · right
          constructor
          · simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hp.1
          · have shift : z + u - 1 - u = z - 1 := by abel
            rw [shift]
            exact hp.2

theorem TileTranslationFormulas (T : ProtoTile) (u : GaussianInt) :
    (TileTranslation T u).cells = T.cells.image (GaussianTranslation u) ∧
    (TileTranslation T u).anchor = GaussianTranslation u T.anchor ∧
    ((TileTranslation T u).cells = ∅ ↔ T.cells = ∅) ∧
    TileRealization (TileTranslation T u) =
      (fun p : Real × Real =>
        (p.1 + (u.re : Int), p.2 + (u.im : Int))) '' TileRealization T ∧
    TileCentroid (TileTranslation T u) =
      ((TileCentroid T).1 + (u.re : Int),
        (TileCentroid T).2 + (u.im : Int)) ∧
    FootprintVertices (TileTranslation T u) =
      GaussianTranslation u '' FootprintVertices T ∧
    FootprintEdges (TileTranslation T u) =
      (fun e : Finset GaussianInt => e.image (GaussianTranslation u)) ''
        FootprintEdges T ∧
    BoundaryFootprintVertices (TileTranslation T u) =
      GaussianTranslation u '' BoundaryFootprintVertices T ∧
    BoundaryFootprintEdges (TileTranslation T u) =
      (fun e : Finset GaussianInt => e.image (GaussianTranslation u)) ''
        BoundaryFootprintEdges T := by
  refine ⟨rfl, rfl, ?_, translationRealization T u, translationCentroid T u, translationVertices
      T u, translationEdges T u, translationBoundaryVertices T u, translationBoundaryEdges T u⟩
  simp [TileTranslation]

end ApollonianSuperharmonic

end
