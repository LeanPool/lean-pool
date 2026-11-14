/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.AllowedSubtileIncidence
public import LeanPool.ApollonianSuperharmonic.SubtileOccurrenceInterpretation
public import LeanPool.ApollonianSuperharmonic.TileTranslationFormulas
public import LeanPool.ApollonianSuperharmonic.TouchingTriple

-- [TABLET NODE: P4670T1OrdinaryEdges]

/-!
# P4670T1OrdinaryEdges

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P4670T1OrdinaryEdges
    (P : Fin 3 → Bool → ProtoTile) (u v : GaussianInt)
    (hP : ∀ i s, (P i s).cells.Nonempty)
    (X Y : ProtoTile) (hX : X.cells.Nonempty) (hY : Y.cells.Nonempty)
    (hXA : X.cells ⊆ (P 0 true).cells)
    (hYB : Y.cells ⊆ (P 0 false).cells)
    (hXC : TileTouching X (P 1 true))
    (hYD : TileTouching Y (P 1 false))
    (houter :
      TouchingTriple (P 0 true) (TileTranslation (P 0 false) v)
          (TileTranslation (P 2 true) v) ∧
      TouchingTriple (P 0 true) (TileTranslation (P 0 false) v) (P 2 false) ∧
      TouchingTriple (P 0 true) (TileTranslation (P 0 false) (u + v))
          (TileTranslation (P 1 true) (u + v)) ∧
      TouchingTriple (P 0 true) (TileTranslation (P 0 false) (u + v)) (P 1 false) ∧
      TouchingTriple (P 0 true) (TileTranslation (P 1 true) (u + v))
          (TileTranslation (P 2 true) v) ∧
      TouchingTriple (P 0 false) (TileTranslation (P 1 false) (-u - v))
          (TileTranslation (P 2 false) (-v)) ∧
      TouchingTriple (P 1 true) (TileTranslation (P 1 false) (-u))
          (TileTranslation (P 2 true) (-u)) ∧
      TouchingTriple (P 1 true) (TileTranslation (P 1 false) (-u)) (P 2 false)) :
    ∀ a b : PeriodicSubtileIndex, AllowedSubtileIncidence a b →
      ¬ ((a.label = .A ∧ b.label = .B ∨ a.label = .B ∧ b.label = .A) ∧
        a.first = b.first ∧ a.second = b.second) →
      (FootprintEdges (SubtileOccurrenceInterpretation P u v a) ∩
        FootprintEdges (SubtileOccurrenceInterpretation P u v b)).Nonempty := by
-- BODY
  classical
  let common (A B : ProtoTile) := (FootprintEdges A ∩ FootprintEdges B).Nonempty
  have boundary (U : ProtoTile) (e : Finset GaussianInt)
      (he : e ∈ BoundaryFootprintEdges U) : e ∈ FootprintEdges U := by
    rcases he with ⟨z, ⟨rfl, h⟩ | ⟨rfl, h⟩⟩
    · rcases h with ⟨hz, _⟩ | ⟨_, hz⟩
      · exact ⟨z, hz, Or.inl rfl⟩
      · refine ⟨z - ⟨0, 1⟩, hz, Or.inr (Or.inr (Or.inr ?_))⟩
        congr 1 <;> simp [Zsqrtd.ext_iff]
    · rcases h with ⟨hz, _⟩ | ⟨_, hz⟩
      · exact ⟨z, hz, Or.inr (Or.inl rfl)⟩
      · refine ⟨z - 1, hz, Or.inr (Or.inr (Or.inl ?_))⟩
        congr 1 <;> simp []
  have pair (A B : ProtoTile) (ha : A.cells.Nonempty) (hb : B.cells.Nonempty)
      (ht : TileTouching A B) : common A B := by
    rcases ht with h | h | h
    · obtain ⟨p, _, hp, _, _, he⟩ := h.2.2.2
      cases p with
      | nil => simp at hp
      | cons a p =>
        cases p with
        | nil => simp at hp
        | cons b p =>
          have h := (he {a, b}).mpr ⟨a, b, [], p, rfl, rfl⟩
          exact ⟨{a, b}, boundary _ _ h.1, boundary _ _ h.2⟩
    · exact (ha.ne_empty h.1).elim
    · exact (hb.ne_empty h.1).elim
  have sym (A B : ProtoTile) (h : common A B) : common B A := by
    simpa only [common, Set.inter_comm] using h
  have triple (A B C : ProtoTile) (ha : A.cells.Nonempty) (hb : B.cells.Nonempty)
      (hc : C.cells.Nonempty) (h : TouchingTriple A B C) :
      common A B ∧ common B C ∧ common C A :=
    ⟨pair A B ha hb h.1, pair B C hb hc h.2.1, pair C A hc ha h.2.2.1⟩
  have ne (i : Fin 3) (s : Bool) (w : GaussianInt) :
      (TileTranslation (P i s) w).cells.Nonempty := Finset.image_nonempty.mpr (hP i s)
  have H1 := triple _ _ _ (hP 0 true) (ne 0 false v) (ne 2 true v) houter.1
  have H2 := triple _ _ _ (hP 0 true) (ne 0 false v) (hP 2 false) houter.2.1
  have H3 := triple _ _ _ (hP 0 true) (ne 0 false (u + v))
    (ne 1 true (u + v)) houter.2.2.1
  have H4 := triple _ _ _ (hP 0 true) (ne 0 false (u + v)) (hP 1 false) houter.2.2.2.1
  have H6 := triple _ _ _ (hP 0 false) (ne 1 false (-u - v))
    (ne 2 false (-v)) houter.2.2.2.2.2.1
  have H7 := triple _ _ _ (hP 1 true) (ne 1 false (-u))
    (ne 2 true (-u)) houter.2.2.2.2.2.2.1
  have H8 := triple _ _ _ (hP 1 true) (ne 1 false (-u))
    (hP 2 false) houter.2.2.2.2.2.2.2
  have trans (A B : ProtoTile) (w : GaussianInt) (h : common A B) :
      common (TileTranslation A w) (TileTranslation B w) := by
    obtain ⟨e, hea, heb⟩ := h
    refine ⟨e.image (GaussianTranslation w), ?_, ?_⟩
    · rw [(TileTranslationFormulas A w).2.2.2.2.2.2.1]
      exact ⟨e, hea, rfl⟩
    · rw [(TileTranslationFormulas B w).2.2.2.2.2.2.1]
      exact ⟨e, heb, rfl⟩
  have tr0 (A : ProtoTile) : TileTranslation A 0 = A := by
    have hz : GaussianTranslation 0 = id := by funext z; exact add_zero z
    cases A
    simp only [TileTranslation, hz, Finset.image_id, id_eq]
  have trcomp (A : ProtoTile) (x y : GaussianInt) :
      TileTranslation (TileTranslation A x) y = TileTranslation A (x + y) := by
    cases A
    simp only [TileTranslation, Finset.image_image]
    congr 1
    · congr 1
      funext z
      exact add_assoc z x y
    · exact add_assoc _ x y
  have ac : common (P 0 true) (P 1 true) := by
    obtain ⟨e, ⟨z, hz, he⟩, hc⟩ := pair X _ hX (hP 1 true) hXC
    exact ⟨e, ⟨z, hXA hz, he⟩, hc⟩
  have bd : common (P 0 false) (P 1 false) := by
    obtain ⟨e, ⟨z, hz, he⟩, hc⟩ := pair Y _ hY (hP 1 false) hYD
    exact ⟨e, ⟨z, hYB hz, he⟩, hc⟩
  have bc : common (P 0 false) (P 1 true) := by
    simpa only [trcomp, add_neg_cancel, tr0] using trans _ _ (-(u + v)) H3.2.1
  have be : common (P 0 false) (P 2 true) := by
    simpa only [trcomp, add_neg_cancel, tr0] using trans _ _ (-v) H1.2.1
  have de : common (P 1 false) (P 2 true) := by
    simpa only [trcomp, neg_add_cancel, tr0] using trans _ _ u H7.2.1
  have df : common (P 1 false) (TileTranslation (P 2 false) u) := by
    simpa only [trcomp, neg_add_cancel, tr0] using trans _ _ u H8.2.1
  have shifted (o : PeriodicSubtileIndex) (m n : Int) :
      SubtileOccurrenceInterpretation P u v
          {o with first := o.first + m, second := o.second + n} =
        TileTranslation (SubtileOccurrenceInterpretation P u v o)
          ((m : GaussianInt) * u + (n : GaussianInt) * v) := by
    rcases o with ⟨l, a, b⟩
    cases l <;> simp only [SubtileOccurrenceInterpretation, trcomp] <;>
      congr 1 <;> simp only [Int.cast_add, add_mul] <;> abel
  have lift (a b : PeriodicSubtileIndex) (m n : Int)
      (h : common (SubtileOccurrenceInterpretation P u v a)
        (SubtileOccurrenceInterpretation P u v b)) :
      common (SubtileOccurrenceInterpretation P u v
          {a with first := a.first + m, second := a.second + n})
        (SubtileOccurrenceInterpretation P u v
          {b with first := b.first + m, second := b.second + n}) := by
    rw [shifted, shifted]
    exact trans _ _ _ h
  intro a b hab
  induction hab with
  | AB m n => intro h; exact (h (by simp)).elim
  | AB01 m n =>
    intro _
    have h := lift ⟨.A, 0, 0⟩ ⟨.B, 0, 1⟩ m n (by
      simpa [SubtileOccurrenceInterpretation, tr0] using H1.1)
    simpa only [zero_add, add_zero, add_comm] using h
  | AB11 m n =>
    intro _
    have h := lift ⟨.A, 0, 0⟩ ⟨.B, 1, 1⟩ m n (by
      simpa [SubtileOccurrenceInterpretation, tr0] using H3.1)
    simpa only [zero_add, add_zero, add_comm] using h
  | AC m n =>
    intro _
    simpa only [zero_add] using lift ⟨.A, 0, 0⟩ ⟨.C, 0, 0⟩ m n (by simpa
        [SubtileOccurrenceInterpretation, tr0] using ac)
  | AC11 m n =>
    intro _
    have h := lift ⟨.A, 0, 0⟩ ⟨.C, 1, 1⟩ m n (by
      simpa [SubtileOccurrenceInterpretation, tr0] using sym _ _ H3.2.2)
    simpa only [zero_add, add_zero, add_comm] using h
  | AD m n =>
    intro _
    simpa only [zero_add] using lift ⟨.A, 0, 0⟩ ⟨.D, 0, 0⟩ m n (by
      simpa [SubtileOccurrenceInterpretation, tr0] using sym _ _ H4.2.2)
  | AE01 m n =>
    intro _
    have h := lift ⟨.A, 0, 0⟩ ⟨.E, 0, 1⟩ m n (by
      simpa [SubtileOccurrenceInterpretation, tr0] using sym _ _ H1.2.2)
    simpa only [zero_add, add_zero, add_comm] using h
  | AF m n =>
    intro _
    simpa only [zero_add] using lift ⟨.A, 0, 0⟩ ⟨.F, 0, 0⟩ m n (by
      simpa [SubtileOccurrenceInterpretation, tr0] using sym _ _ H2.2.2)
  | BC m n =>
    intro _
    simpa only [zero_add] using lift ⟨.B, 0, 0⟩ ⟨.C, 0, 0⟩ m n (by simpa
        [SubtileOccurrenceInterpretation, tr0] using bc)
  | BDm1m1 m n =>
    intro _
    have h := lift ⟨.B, 0, 0⟩ ⟨.D, -1, -1⟩ m n (by
      simpa [SubtileOccurrenceInterpretation, tr0, sub_eq_add_neg] using H6.1)
    simpa only [zero_add, add_zero, add_comm, sub_eq_add_neg] using h
  | BD m n =>
    intro _
    simpa only [zero_add] using lift ⟨.B, 0, 0⟩ ⟨.D, 0, 0⟩ m n (by simpa
        [SubtileOccurrenceInterpretation, tr0] using bd)
  | BE m n =>
    intro _
    simpa only [zero_add] using lift ⟨.B, 0, 0⟩ ⟨.E, 0, 0⟩ m n (by simpa
        [SubtileOccurrenceInterpretation, tr0] using be)
  | BF0m1 m n =>
    intro _
    have h := lift ⟨.B, 0, 0⟩ ⟨.F, 0, -1⟩ m n (by
      simpa [SubtileOccurrenceInterpretation, tr0] using sym _ _ H6.2.2)
    simpa only [zero_add, add_zero, add_comm, sub_eq_add_neg] using h
  | CDm10 m n =>
    intro _
    have h := lift ⟨.C, 0, 0⟩ ⟨.D, -1, 0⟩ m n (by
      simpa [SubtileOccurrenceInterpretation, tr0] using H7.1)
    simpa only [zero_add, add_zero, add_comm, sub_eq_add_neg] using h
  | CEm10 m n =>
    intro _
    have h := lift ⟨.C, 0, 0⟩ ⟨.E, -1, 0⟩ m n (by
      simpa [SubtileOccurrenceInterpretation, tr0] using sym _ _ H7.2.2)
    simpa only [zero_add, add_zero, add_comm, sub_eq_add_neg] using h
  | CF m n =>
    intro _
    simpa only [zero_add] using lift ⟨.C, 0, 0⟩ ⟨.F, 0, 0⟩ m n (by
      simpa [SubtileOccurrenceInterpretation, tr0] using sym _ _ H8.2.2)
  | DE m n =>
    intro _
    simpa only [zero_add] using lift ⟨.D, 0, 0⟩ ⟨.E, 0, 0⟩ m n (by simpa
        [SubtileOccurrenceInterpretation, tr0] using de)
  | DF10 m n =>
    intro _
    have h := lift ⟨.D, 0, 0⟩ ⟨.F, 1, 0⟩ m n (by
      simpa [SubtileOccurrenceInterpretation, tr0] using df)
    simpa only [zero_add, add_zero, add_comm] using h
  | @symm a b hab ih =>
    intro h
    apply sym
    apply ih
    simpa only [and_comm, or_comm, eq_comm] using h

end ApollonianSuperharmonic

end
