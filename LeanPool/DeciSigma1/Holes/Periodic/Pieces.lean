/-
Copyright (c) 2026 Yaoyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaoyu Zhao
-/

module

public import LeanPool.DeciSigma1.Arithmetic.FinitePaths
public import LeanPool.DeciSigma1.Holes.Periodic.Deletion
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Ring.RingNF

/-! Ported to Lean Pool’s module system and pinned Lean and Mathlib.

 # Pieces and cuts after an admissible deletion

The effect of an admissible deletion on runs, pieces and cuts. Inside a piece, the states at
offsets of at least `stateTransientLength` repeat with period `statePeriodModulus`
(`Piece.runPrefix_mod`). So every deleted block starts and ends in the same state, and the
edited tuple has the same endpoints and visits only original states (`editedTuple_endState`,
`editedTuple_visitedStates`). Each piece of the class keeps `retainedLength` letters, at least
`fixedMargin` if it is shortened, and its image is a piece of the edited tuple (`imagePiece`).

Every cut of the edited tuple has a canonical original cut, its greatest preimage
`Words.greatestPreimage` (`CanonicalCut`, `exists_canonicalCut`,
`canonicalCut_eq_greatestPreimage`); a text read
from a canonical cut is original text as long as it crosses no deleted block
(`text_canonicalCut`). The last section compares the retained lengths of two pieces joined by a
follower edge.

## Main declarations

- `Piece.runPrefix_mod`: periodicity of states inside a piece.
- `retainedLength`, `imagePiece`: the retained length and the image of a piece.
- `editedTuple_endState`, `editedTuple_visitedStates`: endpoints and visited states of the
  edited tuple.
- `CanonicalCut`, `exists_canonicalCut`, `text_canonicalCut`: canonical original cuts.
-/

@[expose] public section


namespace DeciSigma1.Holes.Periodic

open DeciSigma1.Readers DeciSigma1.Words
open DeciSigma1.Readers.Table

variable {α S : Type} [DecidableEq α] {k : ℕ} {W : Fin k → List α} {ρ : List α}

omit [DecidableEq α] in
theorem Piece.start_add_len {d : ℕ} (P : Piece W d) : P.start + P.len = P.stop := by
  unfold Piece.len; have := P.long; omega

/-! ## States inside a piece are periodic -/

omit [DecidableEq α] in
theorem Piece.runPrefix_add_mul [Fintype S] (T : Table α S k) {d : ℕ} (P : Piece W d) {o m : ℕ}
    (ho : Fintype.card S * d ≤ o) (hm : o + m * (d * (Fintype.card S).factorial) ≤ P.len) :
    T.runPrefix W P.coordinate (P.start + o + m * (d * (Fintype.card S).factorial)) =
        T.runPrefix W P.coordinate (P.start + o) := by
  set u := ((W P.coordinate).drop P.start).take P.len
  have hlenu : u.length = P.len := by
    simp only [u, List.length_take, List.length_drop]; have :=
        P.stop_le_length; unfold Piece.len; omega
  have hper : Words.PeriodicOn u d 0 u.length := by
    intro p _ hp
    simp only [u, List.getElem?_take, List.getElem?_drop]
    rw [hlenu] at hp
    rw [ite_eq_left (by omega), ite_eq_left (by omega), ← Nat.add_assoc]
    exact P.periodic (P.start + p) (by omega) (by unfold Piece.len at hp; omega)
  have htake : ∀ t ≤ P.len, ((W P.coordinate).drop P.start).take t = u.take t := by
    intro t ht; simp only [u, List.take_take, min_eq_left ht]
  rw [Nat.add_assoc, runPrefix_add, runPrefix_add, htake _ hm, htake _ (by omega)]
  exact Arithmetic.runFrom_take_periodic T _ P.period_pos hper ho m (by omega)

omit [DecidableEq α] in
/-- The states of a piece at offsets of at least `stateTransientLength` that agree modulo
`statePeriodModulus` are equal. -/
theorem Piece.runPrefix_mod [Fintype S] (T : Table α S k) {d : ℕ} (P : Piece W d) {o₁ o₂ : ℕ}
    (h₁ : Periodic.stateTransientLength (Fintype.card S) d ≤ o₁)
        (h₂ : Periodic.stateTransientLength (Fintype.card S) d ≤ o₂)
    (h₁' : o₁ ≤ P.len) (h₂' : o₂ ≤ P.len)
        (hmod : o₁ % Periodic.statePeriodModulus (Fintype.card S) d =
      o₂ % Periodic.statePeriodModulus (Fintype.card S) d) :
    T.runPrefix W P.coordinate (P.start + o₁) = T.runPrefix W P.coordinate (P.start + o₂) := by
  unfold Periodic.stateTransientLength at h₁ h₂
  unfold Periodic.statePeriodModulus at hmod
  rcases le_total o₁ o₂ with h | h
  · obtain ⟨m, hm⟩ := (Nat.modEq_iff_dvd' h).mp hmod
    rw [show o₂ = o₁ + m * (d * (Fintype.card S).factorial) by rw [mul_comm m]; omega,
      ← Nat.add_assoc, P.runPrefix_add_mul T h₁ (by rw [mul_comm m]; omega)]
  · obtain ⟨m, hm⟩ := (Nat.modEq_iff_dvd' h).mp hmod.symm
    rw [show o₁ = o₂ + m * (d * (Fintype.card S).factorial) by rw [mul_comm m]; omega,
      ← Nat.add_assoc, P.runPrefix_add_mul T h₂ (by rw [mul_comm m]; omega)]

namespace AdmissibleDeletion

variable {N : ℕ} {x : Piece W ρ.length → ℕ} (hx : AdmissibleDeletion W ρ N x)
include hx

/-! ## Retained positions -/

theorem site_sub {P : Piece W ρ.length} {p : ℕ}
    (hp1 : P.start + Periodic.boundaryMargin N ρ.length ≤ p)
    (hp2 : p < P.start + Periodic.boundaryMargin N ρ.length + Periodic.statePeriodModulus N ρ.length
        * x P) :
    p ∈ deletedPositions W ρ N x P.coordinate := by
  have hxP : x P ≠ 0 := by intro h0; rw [h0] at hp2; omega
  exact mem_deletedPositions.mpr ⟨P, hx.supp P hxP, rfl, hp1, hp2⟩

/-- The letter before a piece is retained. -/
theorem before_not_mem (P : Piece W ρ.length) (hs : P.start ≠ 0) :
    P.start - 1 ∉ deletedPositions W ρ N x P.coordinate := by
  intro hp
  obtain ⟨R, _, hRl, h1, h2⟩ := mem_deletedPositions.mp hp
  have hxR : x R ≠ 0 := by intro h0; rw [h0] at h2; omega
  have hb := hx.site_bound hxR
  have hdA := Periodic.d_le_boundaryMargin N ρ.length
  have hd := P.period_pos
  have hne : R ≠ P := by intro h; subst h; omega
  rcases le_total R.start P.start with h | h
  · have := Piece.sep hne hRl h; omega
  · omega

/-- The letter after a piece (if any) is retained. -/
theorem end_not_mem (P : Piece W ρ.length) : P.stop ∉ deletedPositions W ρ N x P.coordinate := by
  intro hp
  obtain ⟨R, _, hRl, h1, h2⟩ := mem_deletedPositions.mp hp
  have hxR : x R ≠ 0 := by intro h0; rw [h0] at h2; omega
  have hb := hx.site_bound hxR
  have hdA := Periodic.d_le_boundaryMargin N ρ.length
  have hd := P.period_pos
  have hne : R ≠ P := by intro h; subst h; omega
  rcases le_total R.start P.start with h | h
  · have := Piece.sep hne hRl h; have := P.long; omega
  · have := Piece.sep (Ne.symm hne) hRl.symm h; omega

theorem in_piece_not_mem (P : Piece W ρ.length) {p : ℕ} (h1 : P.start ≤ p) (h2 : p < P.stop)
    (hns : p < P.start + Periodic.boundaryMargin N ρ.length ∨ P.start + Periodic.boundaryMargin N
        ρ.length + Periodic.statePeriodModulus N ρ.length * x P ≤ p) :
    p ∉ deletedPositions W ρ N x P.coordinate :=
  hx.not_mem_deletedPositions P rfl h1 h2 hns

/-- Positions of a piece outside its site are retained. -/
theorem not_mem_deletedPositions_of_piece_margin (P : Piece W ρ.length) {p : ℕ} (h1 : P.start ≤ p)
    (h2 : p < P.stop)
    (hns : p < P.start + Periodic.boundaryMargin N ρ.length ∨ x P = 0 ∨
      P.start + Periodic.boundaryMargin N ρ.length + Periodic.statePeriodModulus N ρ.length * x P ≤
          p) :
    p ∉ deletedPositions W ρ N x P.coordinate := by
  apply hx.in_piece_not_mem P h1 h2
  rcases hns with h | h | h
  · exact Or.inl h
  · by_cases hp : p < P.start + Periodic.boundaryMargin N ρ.length
    · exact Or.inl hp
    · exact Or.inr (by rw [h]; omega)
  · exact Or.inr h

/-- The retained-cut map inside a piece, before its site. -/
theorem retainedCount_head (P : Piece W ρ.length) {o : ℕ}
    (ho : o ≤ Periodic.boundaryMargin N ρ.length ∨ x P = 0)
    (hoL : o ≤ P.len) : keepCut W ρ N x P.coordinate (P.start + o) =
        keepCut W ρ N x P.coordinate P.start + o := by
  apply retainedCount_add_of_not_mem
  intro i hi
  apply hx.not_mem_deletedPositions_of_piece_margin P (by omega) (by unfold Piece.len at hoL; omega)
  exact ho.elim (fun h => Or.inl (by omega)) (fun h => Or.inr (Or.inl h))

/-- The retained-cut map inside a shortened piece, after its site. -/
theorem retainedCount_tail (P : Piece W ρ.length) {o : ℕ}
    (ho : Periodic.boundaryMargin N ρ.length ≤ o)
    (hoL : o + Periodic.statePeriodModulus N ρ.length * x P ≤ P.len) :
    keepCut W ρ N x P.coordinate (P.start + o + Periodic.statePeriodModulus N ρ.length * x P) =
        keepCut W ρ N x P.coordinate P.start + o := by
  have h1 :=
      hx.retainedCount_head P (o := Periodic.boundaryMargin N ρ.length) (Or.inl le_rfl) (by omega)
  have h2 : keepCut W ρ N x P.coordinate
      (P.start + Periodic.boundaryMargin N ρ.length + Periodic.statePeriodModulus N ρ.length * x
          P) =
      keepCut W ρ N x P.coordinate (P.start + Periodic.boundaryMargin N ρ.length) :=
    retainedCount_add_of_mem (fun i hi => hx.site_sub (by omega) (by omega))
  have h3 : keepCut W ρ N x P.coordinate
      (P.start + Periodic.boundaryMargin N ρ.length + Periodic.statePeriodModulus N ρ.length * x P +
      (o - Periodic.boundaryMargin N ρ.length)) =
          keepCut W ρ N x P.coordinate (P.start + Periodic.boundaryMargin N ρ.length +
      Periodic.statePeriodModulus N ρ.length * x P) + (o - Periodic.boundaryMargin N ρ.length) :=
    retainedCount_add_of_not_mem (fun i hi => hx.in_piece_not_mem P (by omega)
      (by unfold Piece.len at hoL; omega) (Or.inr (by omega)))
  rw [show P.start + o + Periodic.statePeriodModulus N ρ.length * x P = P.start +
      Periodic.boundaryMargin N ρ.length +
    Periodic.statePeriodModulus N ρ.length * x P +
        (o - Periodic.boundaryMargin N ρ.length) by omega, h3, h2, h1]
  omega

/-- The image of the end of a piece lies `retainedLength` letters after the image of its start. -/
theorem retainedCount_piece_end (P : Piece W ρ.length) :
    keepCut W ρ N x P.coordinate P.stop = keepCut W ρ N x P.coordinate P.start +
        (P.len - Periodic.statePeriodModulus N ρ.length * x P) := by
  by_cases hxP : x P = 0
  · have := hx.retainedCount_head P (o := P.len) (Or.inr hxP) le_rfl
    rw [hxP, Nat.mul_zero, Nat.sub_zero, ← this]; unfold Piece.len; congr 1; have := P.long; omega
  · have hb := hx.site_bound hxP
    have := hx.retainedCount_tail P (o := P.len - Periodic.statePeriodModulus N ρ.length * x P)
      (by unfold Piece.len; omega) (by unfold Piece.len; omega)
    rw [← this]; congr 1; unfold Piece.len; have := P.long; omega

/-! ## The image of a piece -/

/-- The length of a piece after the deletion, which removes `x P` blocks of
`statePeriodModulus` letters from it. -/
def retainedLength (P : Piece W ρ.length) :
    ℕ := P.len - Periodic.statePeriodModulus N ρ.length * x P

theorem retainedLength_ge (P : Piece W ρ.length) :
    2 * ρ.length ≤ retainedLength (N := N) (x := x) P := by
  unfold retainedLength
  by_cases hxP : x P = 0
  · rw [hxP]; simpa using P.len_ge
  · have := hx.long P (hx.supp P hxP) hxP
    have := Periodic.d_le_boundaryMargin N ρ.length
    unfold Periodic.fixedMargin at *; omega

theorem retainedLength_ge_fixedMargin (P : Piece W ρ.length) (hxP : x P ≠ 0) :
    Periodic.fixedMargin N ρ.length ≤ retainedLength (N := N) (x := x) P := by
  unfold retainedLength; have := hx.long P (hx.supp P hxP) hxP; omega

omit [DecidableEq α] hx in
theorem retainedLength_le (P : Piece W ρ.length) :
    retainedLength (N := N) (x := x) P ≤ P.len := by
  unfold retainedLength; omega

/-- The edited text of a piece at offset `o` is its original text at offset `o`. -/
theorem getElem?_new (P : Piece W ρ.length) {o : ℕ} (ho : o < retainedLength (N := N) (x := x) P) :
    (editedTuple W ρ N x P.coordinate)[keepCut W ρ N x P.coordinate P.start + o]? =
        (W P.coordinate)[P.start + o]? := by
  have hL := retainedLength_le (N := N) (x := x) P
  have hPl := P.start_add_len
  have hle := P.stop_le_length
  unfold retainedLength at ho hL
  by_cases hh : o < Periodic.boundaryMargin N ρ.length ∨ x P = 0
  · have hret : P.start + o ∉ deletedPositions W ρ N x P.coordinate :=
      hx.not_mem_deletedPositions_of_piece_margin P (by omega)
      (by omega) (hh.elim (fun h => Or.inl (by omega)) (fun h => Or.inr (Or.inl h)))
    rw [← hx.retainedCount_head P (o := o) (hh.elim (fun h => Or.inl h.le) Or.inr) (by omega)]
    exact getElem?_deletePositions _ hret (by omega)
  · push Not at hh
    have hret : P.start + o + Periodic.statePeriodModulus N ρ.length * x P ∉
        deletedPositions W ρ N x P.coordinate :=
      hx.in_piece_not_mem P (by omega) (by omega) (Or.inr (by omega))
    rw [← hx.retainedCount_tail P hh.1 (by omega)]
    unfold keepCut
    rw [editedTuple, getElem?_deletePositions _ hret (by omega), Nat.add_assoc]
    apply P.getElem?_eq_of_mod (by omega) (by omega)
    rw [Periodic.statePeriodModulus, Nat.mul_assoc, Nat.add_mul_mod_self_left]

omit hx in
theorem keepCut_stop_le_length (P : Piece W ρ.length) :
    keepCut W ρ N x P.coordinate P.stop ≤ (editedTuple W ρ N x P.coordinate).length := by
  rw [editedTuple, length_deletePositions]; exact retainedCount_mono P.stop_le_length

theorem imagePiece_period (P : Piece W ρ.length) : ∀ p, keepCut W ρ N x P.coordinate P.start ≤ p →
    p + ρ.length < keepCut W ρ N x P.coordinate P.stop →
    (editedTuple W ρ N x P.coordinate)[p]? = (editedTuple W ρ N x P.coordinate)[p + ρ.length]? := by
  intro p hp hpe
  have hend := hx.retainedCount_piece_end P
  have hL := retainedLength_le (N := N) (x := x) P
  have hPl := P.start_add_len
  unfold retainedLength at hL
  obtain ⟨o, rfl⟩ := Nat.exists_eq_add_of_le hp
  rw [hx.getElem?_new P (by unfold retainedLength; omega), Nat.add_assoc,
    hx.getElem?_new P (by unfold retainedLength; omega), ← Nat.add_assoc]
  exact P.periodic _ (by omega) (by omega)

theorem take_drop_editedTuple_eq_root (P : Piece W ρ.length) :
    ((editedTuple W ρ N x P.coordinate).drop (keepCut W ρ N x P.coordinate P.start)).take ρ.length =
        P.root := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < ρ.length
  · rw [List.getElem?_take_of_lt hi, List.getElem?_drop, hx.getElem?_new P
      (by have := hx.retainedLength_ge P; omega), Piece.root, List.getElem?_take_of_lt hi,
      List.getElem?_drop]
  · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none
      (by rw [P.root_length]; omega)]

theorem imagePiece_maxL (P : Piece W ρ.length) : keepCut W ρ N x P.coordinate P.start = 0 ∨
    (editedTuple W ρ N x P.coordinate)[keepCut W ρ N x P.coordinate P.start - 1]? ≠
      (editedTuple W ρ N x P.coordinate)[keepCut W ρ N x P.coordinate P.start - 1 + ρ.length]? := by
  by_cases hs0 : P.start = 0
  · left; rw [hs0]; rfl
  rcases P.left_maximal with h | h
  · exact absurd h hs0
  · right
    have hb := hx.before_not_mem P hs0
    have hk := retainedCount_succ_of_not_mem hb
    rw [show P.start - 1 + 1 = P.start by omega] at hk
    have hd := P.period_pos
    have hlt : P.start - 1 <
        (W P.coordinate).length := by have := P.start_lt_stop; have := P.stop_le_length; omega
    have hnew := hx.getElem?_new P (o := ρ.length - 1) (by have := hx.retainedLength_ge P; omega)
    unfold keepCut at hnew ⊢
    rw [hk, Nat.add_sub_cancel, editedTuple, getElem?_deletePositions _ hb hlt]
    rw [show retainedCount (deletedPositions W ρ N x P.coordinate) (P.start - 1) + ρ.length =
      retainedCount (deletedPositions W ρ N x P.coordinate) P.start + (ρ.length - 1) by omega]
    rw [editedTuple] at hnew
    rw [hnew, show P.start + (ρ.length - 1) = P.start - 1 + ρ.length by omega]
    exact h

theorem imagePiece_maxR (P : Piece W ρ.length) :
    keepCut W ρ N x P.coordinate P.stop = (editedTuple W ρ N x P.coordinate).length ∨
    (editedTuple W ρ N x P.coordinate)[keepCut W ρ N x P.coordinate P.stop]? ≠
      (editedTuple W ρ N x P.coordinate)[keepCut W ρ N x P.coordinate P.stop - ρ.length]? := by
  by_cases hE : P.stop = (W P.coordinate).length
  · left; unfold keepCut; rw [hE, editedTuple, length_deletePositions]
  rcases P.right_maximal with h | h
  · exact absurd h hE
  · right
    have he := hx.end_not_mem P
    have hlt : P.stop < (W P.coordinate).length := lt_of_le_of_ne P.stop_le_length hE
    have hend := hx.retainedCount_piece_end P
    have hd := P.period_pos
    have hnl := hx.retainedLength_ge P
    have hL := retainedLength_le (N := N) (x := x) P
    have hPl := P.start_add_len
    unfold retainedLength at hnl hL
    have hnew :=
        hx.getElem?_new P (o := P.len - Periodic.statePeriodModulus N ρ.length * x P - ρ.length)
      (by unfold retainedLength; omega)
    have hmod : (P.len - Periodic.statePeriodModulus N ρ.length * x P - ρ.length) % ρ.length =
        (P.len - ρ.length) % ρ.length := by
      have : P.len - ρ.length = (P.len - Periodic.statePeriodModulus N ρ.length * x P - ρ.length) +
          ρ.length * ((Nat.factorial N) * x P) := by
        have : Periodic.statePeriodModulus N ρ.length * x P = ρ.length *
            ((Nat.factorial N) * x P) := by
          unfold Periodic.statePeriodModulus; ring
        omega
      rw [this, Nat.add_mul_mod_self_left]
    have hper :=
        P.getElem?_eq_of_mod (o₁ := P.len - Periodic.statePeriodModulus N ρ.length * x P - ρ.length)
      (o₂ := P.len - ρ.length) (by omega) (by omega) hmod
    unfold keepCut at hnew hend ⊢
    rw [editedTuple, getElem?_deletePositions _ he hlt, hend]
    rw [editedTuple] at hnew
    rw [show retainedCount (deletedPositions W ρ N x P.coordinate) P.start +
        (P.len - Periodic.statePeriodModulus N ρ.length * x P) -
      ρ.length = retainedCount (deletedPositions W ρ N x P.coordinate) P.start +
          (P.len - Periodic.statePeriodModulus N ρ.length * x P -
      ρ.length) by omega, hnew, hper,
          show P.start + (P.len - ρ.length) = P.stop - ρ.length by omega]
    exact h

/-- The image of a piece is a piece of the edited tuple. -/
def imagePiece (P : Piece W ρ.length) : Piece (editedTuple W ρ N x) ρ.length where
  coordinate := P.coordinate
  start := keepCut W ρ N x P.coordinate P.start
  stop := keepCut W ρ N x P.coordinate P.stop
  long := by rw [hx.retainedCount_piece_end P]; have := hx.retainedLength_ge P;
             unfold retainedLength at this; omega
  stop_le_length := keepCut_stop_le_length (N := N) (x := x) P
  periodic := hx.imagePiece_period P
  primitive := by rw [hx.take_drop_editedTuple_eq_root P]; exact P.primitive
  left_maximal := hx.imagePiece_maxL P
  right_maximal := hx.imagePiece_maxR P

@[simp] theorem imagePiece_coordinate (P : Piece W ρ.length) :
    (hx.imagePiece P).coordinate = P.coordinate := rfl
@[simp] theorem imagePiece_start (P : Piece W ρ.length) :
    (hx.imagePiece P).start = keepCut W ρ N x P.coordinate P.start := rfl
@[simp] theorem imagePiece_stop (P : Piece W ρ.length) :
    (hx.imagePiece P).stop = keepCut W ρ N x P.coordinate P.stop := rfl

theorem imagePiece_len (P : Piece W ρ.length) :
    (hx.imagePiece P).len = retainedLength (N := N) (x := x) P := by
  unfold Piece.len; rw
      [imagePiece_stop, imagePiece_start,
          hx.retainedCount_piece_end P]; unfold retainedLength; omega

theorem imagePiece_stop_eq (P : Piece W ρ.length) :
    (hx.imagePiece P).stop = (hx.imagePiece P).start + retainedLength (N := N) (x := x) P := by
  rw [← hx.imagePiece_len]; unfold Piece.len; have := (hx.imagePiece P).long; omega

theorem getElem?_imagePiece (P : Piece W ρ.length) {o : ℕ}
    (ho : o < retainedLength (N := N) (x := x) P) :
    (editedTuple W ρ N x P.coordinate)[(hx.imagePiece P).start + o]? =
        (W P.coordinate)[P.start + o]? := hx.getElem?_new P ho

theorem imagePiece_root (P : Piece W ρ.length) : (hx.imagePiece P).root = P.root := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < ρ.length
  · simp only [Piece.root, imagePiece_coordinate, List.getElem?_take_of_lt hi, List.getElem?_drop]
    exact hx.getElem?_new P (by have := hx.retainedLength_ge P; omega)
  · rw [List.getElem?_eq_none (by rw [Piece.root_length]; omega),
      List.getElem?_eq_none (by rw [Piece.root_length]; omega)]

theorem imagePiece_mem_iff (P : Piece W ρ.length) :
    hx.imagePiece P ∈ piecesOf (editedTuple W ρ N x) ρ ↔ P ∈ piecesOf W ρ := by
  rw [mem_piecesOf, mem_piecesOf, imagePiece_root]

/-! ## States -/

section States

variable [Fintype S] (T : Table α S k) (hN : N = Fintype.card S)
include hN

/-- The two end cuts of a maximal interval of deleted positions carry equal states. -/
theorem block_states (l : Fin k) :
    ∀ j c, j < c → c ≤ (W l).length → (∀ p, j ≤ p → p < c → p ∈ deletedPositions W ρ N x l) →
      (j = 0 ∨ j - 1 ∉ deletedPositions W ρ N x l) → c ∉ deletedPositions W ρ N x l →
      runFrom T.step (T.start l) ((W l).take j) = runFrom T.step (T.start l) ((W l).take c) := by
  intro j c hjc hc hD hj hcD
  obtain ⟨P, hP, hPl, h1, h2⟩ := mem_deletedPositions.mp (hD (c - 1) (by omega) (by omega))
  subst hPl
  have hxP : x P ≠ 0 := by intro h0; rw [h0] at h2; omega
  have hb := hx.site_bound hxP
  have hdA := Periodic.d_le_boundaryMargin N ρ.length
  have hd := P.period_pos
  have hcE : c = P.start + Periodic.boundaryMargin N ρ.length +
      Periodic.statePeriodModulus N ρ.length * x P := by
    by_contra hne
    exact hcD (hx.site_sub (by omega) (by omega))
  have hjE : j = P.start + Periodic.boundaryMargin N ρ.length := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact hx.in_piece_not_mem P (p := P.start + Periodic.boundaryMargin N ρ.length - 1) (by omega)
        (by omega)
        (Or.inl (by omega)) (hD _ (by omega) (by omega))
    · rcases hj with h' | h'
      · omega
      · exact h' (hx.site_sub (by omega) (by omega))
  subst hcE hjE
  have := P.runPrefix_add_mul T (o := Periodic.boundaryMargin N ρ.length) (m := x P)
    (by rw [← hN]; unfold Periodic.boundaryMargin Periodic.stateTransientLength; omega)
    (by rw [← hN]; unfold Piece.len; unfold Periodic.statePeriodModulus at hb; rw [mul_comm (x P)];
        omega)
  unfold runPrefix at this
  rw [← this, hN, Periodic.statePeriodModulus, mul_comm (x P)]

/-- At a cut that is not strictly inside an interval of deleted positions, the edited tuple has
the original state at the image of the cut. -/
theorem runPrefix_editedTuple (l : Fin k) {c : ℕ} (hc : c ≤ (W l).length)
    (hint : c = 0 ∨ c ∉ deletedPositions W ρ N x l ∨ c - 1 ∉ deletedPositions W ρ N x l) :
    T.runPrefix (editedTuple W ρ N x) l (keepCut W ρ N x l c) = T.runPrefix W l c := by
  unfold runPrefix keepCut editedTuple
  rw [deletePositions_take _ hc]
  exact runFrom_deletePositions_take T _ _ (hx.block_states T hN l) c hc hint

/-- The state of the edited tuple at a cut is the original state at the greatest preimage of
the cut. -/
theorem runPrefix_editedTuple_greatestPreimage (l : Fin k) (a : ℕ) :
    T.runPrefix (editedTuple W ρ N x) l a =
      T.runPrefix W l (greatestPreimage (deletedPositions W ρ N x l) a) :=
  runFrom_take_deletePositions T _ _ (hx.block_states T hN l)
    (fun h => absurd (hx.deletedPositions_lt_length h) (lt_irrefl _)) a

/-- The states of the image of a piece are its original states at the same offsets. -/
theorem runPrefix_imagePiece (P : Piece W ρ.length) {o : ℕ}
    (ho : o ≤ retainedLength (N := N) (x := x) P) :
    T.runPrefix (editedTuple W ρ N x) P.coordinate ((hx.imagePiece P).start + o) =
        T.runPrefix W P.coordinate (P.start + o) := by
  have hL := retainedLength_le (N := N) (x := x) P
  have hPl := P.start_add_len
  have hle := P.stop_le_length
  have hdA := Periodic.d_le_boundaryMargin N ρ.length
  have hd := P.period_pos
  unfold retainedLength at ho hL
  by_cases hh : o ≤ Periodic.boundaryMargin N ρ.length ∨ x P = 0
  · rw [imagePiece_start, ← hx.retainedCount_head P hh (by omega)]
    apply hx.runPrefix_editedTuple T hN P.coordinate (by omega)
    rcases Nat.eq_zero_or_pos o with h0 | h0
    · right; left; subst h0
      exact hx.in_piece_not_mem P (by omega) P.start_lt_stop (Or.inl (by omega))
    · right; right
      exact hx.not_mem_deletedPositions_of_piece_margin P (by omega) (by omega)
        (hh.elim (fun h => Or.inl (by omega)) (fun h => Or.inr (Or.inl h)))
  · push Not at hh
    rw [imagePiece_start, ← hx.retainedCount_tail P (by omega) (by omega)]
    rw [hx.runPrefix_editedTuple T hN P.coordinate (by omega)
      (Or.inr (Or.inr (hx.in_piece_not_mem P (by omega) (by omega) (Or.inr (by omega)))))]
    have hM : Periodic.statePeriodModulus N ρ.length * x P = x P *
        (ρ.length * (Fintype.card S).factorial) := by
      rw [hN, Periodic.statePeriodModulus]; ring
    have :=
        P.runPrefix_add_mul T (o := o) (m := x P)
            (by rw [← hN]; unfold Periodic.boundaryMargin Periodic.stateTransientLength at hh;
                omega)
      (by omega)
    rw [← this, hM]

/-- The edited tuple has the same endpoints. -/
theorem editedTuple_endState (l : Fin k) : T.endState (editedTuple W ρ N x) l = T.endState W l := by
  unfold endState
  rw [show (editedTuple W ρ N x l).length = keepCut W ρ N x l (W l).length by
    rw [editedTuple, length_deletePositions]; rfl]
  exact hx.runPrefix_editedTuple T hN l le_rfl
      (Or.inr (Or.inl fun h => absurd (hx.deletedPositions_lt_length h)
    (lt_irrefl _)))

end States

/-! ## Canonical original cuts -/

omit hx in
/-- `c` is the canonical original cut of the cut `c'` of the edited word `l`: a retained
position, or the end of the word, whose image is `c'`. -/
def CanonicalCut (l : Fin k) (c c' : ℕ) : Prop :=
  c ≤ (W l).length ∧ keepCut W ρ N x l c = c' ∧ (c < (W l).length → c ∉ deletedPositions W ρ N x l)

omit hx in
theorem length_editedTuple (l : Fin k) :
    (editedTuple W ρ N x l).length = keepCut W ρ N x l (W l).length := by
  rw [editedTuple, length_deletePositions]; rfl

/-- Every cut of an edited word has a canonical original cut: its greatest preimage. -/
theorem exists_canonicalCut (l : Fin k) {c' : ℕ} (hc' : c' ≤ (editedTuple W ρ N x l).length) :
    ∃ c, CanonicalCut (W := W) (ρ := ρ) (N := N) (x := x) l c c' :=
  ⟨greatestPreimage (deletedPositions W ρ N x l) c',
    greatestPreimage_le_length _
        (fun h => absurd (hx.deletedPositions_lt_length h) (lt_irrefl _)) hc',
    retainedCount_greatestPreimage c', fun _ => greatestPreimage_not_mem c'⟩

theorem canonicalCut_eq_greatestPreimage {l : Fin k} {c c' : ℕ} (h :
    CanonicalCut (W := W) (ρ := ρ) (N := N) (x := x) l c c') :
    greatestPreimage (deletedPositions W ρ N x l) c' = c := by
  obtain ⟨-, hk, hr⟩ := h
  rw [← hk]
  exact greatestPreimage_retainedCount fun hm => hr (hx.deletedPositions_lt_length hm) hm

omit hx in
theorem canonicalCut_unique {l : Fin k} {c₁ c₂ c' : ℕ} (h₁ :
    CanonicalCut (W := W) (ρ := ρ) (N := N) (x := x) l c₁ c')
    (h₂ : CanonicalCut (W := W) (ρ := ρ) (N := N) (x := x) l c₂ c') :
    c₁ = c₂ := by
  obtain ⟨h1l, h1k, h1r⟩ := h₁
  obtain ⟨h2l, h2k, h2r⟩ := h₂
  unfold keepCut at h1k h2k
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have := retainedCount_lt_of_not_mem (h1r (by omega)) h; omega
  · have := retainedCount_lt_of_not_mem (h2r (by omega)) h; omega

theorem runPrefix_canonicalCut [Fintype S] (T : Table α S k) (hN : N = Fintype.card S) {l : Fin k}
    {c c' : ℕ} (h :
        CanonicalCut (W := W) (ρ := ρ) (N := N) (x := x) l c c') :
    T.runPrefix (editedTuple W ρ N x) l c' =
        T.runPrefix W l c := by
  rw [← h.2.1]
  apply hx.runPrefix_editedTuple T hN l h.1
  right; left
  intro hm
  exact (h.2.2 (hx.deletedPositions_lt_length hm)) hm

theorem canonicalCut_start (P : Piece W ρ.length) :
    CanonicalCut (W := W) (ρ := ρ) (N := N) (x := x) P.coordinate P.start (hx.imagePiece P).start :=
  ⟨by have := P.start_lt_stop; have := P.stop_le_length; omega, rfl,
      fun _ => hx.in_piece_not_mem P le_rfl
    P.start_lt_stop (Or.inl
        (by have := Periodic.d_le_boundaryMargin N ρ.length; have := P.period_pos; omega))⟩

/-- The cut `|ρ|` letters before the end of a piece is the canonical original cut of the cut
`|ρ|` letters before the end of its image. -/
theorem canonicalCut_end_sub (P : Piece W ρ.length) :
    CanonicalCut (W := W) (ρ := ρ) (N := N) (x := x) P.coordinate (P.stop - ρ.length)
        ((hx.imagePiece P).stop - ρ.length) := by
  have hPl := P.start_add_len
  have hd := P.period_pos
  have hnl := hx.retainedLength_ge P
  have hL := retainedLength_le (N := N) (x := x) P
  have hlg := P.len_ge
  have hdA := Periodic.d_le_boundaryMargin N ρ.length
  have hpos : ∀ i < ρ.length, P.stop - ρ.length + i ∉ deletedPositions W ρ N x P.coordinate := by
    intro i hi
    by_cases hxP : x P = 0
    · exact hx.not_mem_deletedPositions_of_piece_margin P (by omega) (by omega)
        (Or.inr (Or.inl hxP))
    · have hb := hx.site_bound hxP
      exact hx.in_piece_not_mem P (by omega) (by omega) (Or.inr (by omega))
  have hk := retainedCount_add_of_not_mem hpos
  rw [show P.stop - ρ.length + ρ.length = P.stop by have := P.long; omega] at hk
  refine ⟨by have := P.stop_le_length; omega, ?_, fun _ => by simpa using hpos 0 hd⟩
  rw [imagePiece_stop]; unfold keepCut; omega

theorem imagePiece_stop_eq_length_iff (P : Piece W ρ.length) :
    (hx.imagePiece P).stop = (editedTuple W ρ N x P.coordinate).length ↔ P.stop =
        (W P.coordinate).length := by
  rw [length_editedTuple, imagePiece_stop]
  constructor
  · intro h
    by_contra hne
    have := retainedCount_lt_of_not_mem (hx.end_not_mem P) (lt_of_le_of_ne P.stop_le_length hne)
    unfold keepCut at h; omega
  · intro h; rw [h]

/-! ## Copying text across retained stretches -/

/-- The junction of a shortened piece: the image of the start of its site. -/
theorem retainedCount_junction (P : Piece W ρ.length) (hxP : x P ≠ 0) :
    keepCut W ρ N x P.coordinate (P.start + Periodic.boundaryMargin N ρ.length) =
        (hx.imagePiece P).start + Periodic.boundaryMargin N ρ.length := by
  rw [hx.retainedCount_head P (Or.inl le_rfl)
      (by have := hx.site_bound hxP; unfold Piece.len; omega)]
  rfl

omit hx in
theorem zero_not_mem (l : Fin k) :
    0 ∉ deletedPositions W ρ N x l := by
  intro hp
  obtain ⟨R, _, _, h1, _⟩ := mem_deletedPositions.mp hp
  have := Periodic.d_le_boundaryMargin N ρ.length; have := R.period_pos; omega

/-- The image of a deleted position is the junction of a shortened piece. -/
theorem keepCut_of_mem {l : Fin k} {p : ℕ} (hp : p ∈ deletedPositions W ρ N x l) :
    ∃ R : Piece W ρ.length, R.coordinate = l ∧ x R ≠ 0 ∧
      retainedCount (deletedPositions W ρ N x l) p =
        (hx.imagePiece R).start + Periodic.boundaryMargin N ρ.length := by
  obtain ⟨R, _, hRl, h1, h2⟩ := mem_deletedPositions.mp hp
  have hxR : x R ≠ 0 := by intro h0; rw [h0] at h2; omega
  subst hRl
  refine ⟨R, rfl, hxR, ?_⟩
  rw [← hx.retainedCount_junction R hxR]
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h1
  exact retainedCount_add_of_mem fun i hi => hx.site_sub (by omega) (by omega)

/-- From a canonical cut, the positions up to the next junction are retained. -/
theorem not_mem_of_canonicalCut {l : Fin k} {c c' n : ℕ} (hc :
    CanonicalCut (W := W) (ρ := ρ) (N := N) (x := x) l c c')
    (hJ : ∀ R : Piece W ρ.length, R.coordinate = l → x R ≠ 0 →
      ¬ (c' < (hx.imagePiece R).start + Periodic.boundaryMargin N ρ.length ∧
          (hx.imagePiece R).start + Periodic.boundaryMargin N ρ.length < c' + n)) :
    ∀ i < n, c + i ∉ deletedPositions W ρ N x l := by
  rw [← hx.canonicalCut_eq_greatestPreimage hc]
  refine not_mem_of_no_junction fun p hp h => ?_
  obtain ⟨R, hRl, hxR, hR⟩ := hx.keepCut_of_mem hp
  exact hJ R hRl hxR (hR ▸ h)

/-- From a canonical cut, `n` letters of the edited word with no deleted block in
`(c', c' + n)` are `n` retained letters of the original word. -/
theorem text_canonicalCut {l : Fin k} {c c' n : ℕ} (hc :
    CanonicalCut (W := W) (ρ := ρ) (N := N) (x := x) l c c')
    (hn : c' + n ≤ (editedTuple W ρ N x l).length)
    (hJ : ∀ R : Piece W ρ.length, R.coordinate = l → x R ≠ 0 →
      ¬ (c' < (hx.imagePiece R).start + Periodic.boundaryMargin N ρ.length ∧
          (hx.imagePiece R).start + Periodic.boundaryMargin N ρ.length < c' + n)) :
    (∀ i < n, c + i ∉ deletedPositions W ρ N x l ∧ c + i < (W l).length) ∧
      keepCut W ρ N x l (c + n) = c' + n ∧
      ∀ i < n, (W l)[c + i]? = (editedTuple W ρ N x l)[c' + i]? := by
  have hret := hx.not_mem_of_canonicalCut hc hJ
  have hck : retainedCount (deletedPositions W ρ N x l) c = c' := hc.2.1
  have hk : ∀ i ≤ n, retainedCount (deletedPositions W ρ N x l) (c + i) = c' + i := fun i hi => by
    rw [retainedCount_add_of_not_mem fun j hj => hret j (by omega), hck]
  have hlt : ∀ i < n, c + i < (W l).length := fun i hi => by
    by_contra hge
    have := retainedCount_mono (D := deletedPositions W ρ N x l) (Nat.le_of_not_lt hge)
    have := hk i hi.le
    rw [editedTuple, length_deletePositions] at hn
    omega
  refine ⟨fun i hi => ⟨hret i hi, hlt i hi⟩, hk n le_rfl, fun i hi => ?_⟩
  rw [← hk i hi.le]
  exact (getElem?_deletePositions _ (hret i hi) (hlt i hi)).symm

/-- With no junction in `(c', c' + n]` either, the cut `n` letters later is again canonical, and
the `n` letters in between are original letters. -/
theorem canonicalCut_add {l : Fin k} {c c' n : ℕ} (hc :
    CanonicalCut (W := W) (ρ := ρ) (N := N) (x := x) l c c')
    (hn : c' + n ≤ (editedTuple W ρ N x l).length)
    (hJ : ∀ R : Piece W ρ.length, R.coordinate = l → x R ≠ 0 →
      ¬ (c' < (hx.imagePiece R).start + Periodic.boundaryMargin N ρ.length ∧
          (hx.imagePiece R).start + Periodic.boundaryMargin N ρ.length < c' + (n + 1))) :
    CanonicalCut (W := W) (ρ := ρ) (N := N) (x := x) l (c + n) (c' + n) ∧
      ∀ i < n, (W l)[c + i]? = (editedTuple W ρ N x l)[c' + i]? := by
  obtain ⟨hall, hkn, htext⟩ :=
    hx.text_canonicalCut hc hn fun R hRl hxR h => hJ R hRl hxR ⟨h.1, by omega⟩
  refine ⟨⟨?_, hkn, fun _ => hx.not_mem_of_canonicalCut hc hJ n (by omega)⟩, htext⟩
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0; simpa using hc.1
  · have := (hall (n - 1) (by omega)).2; omega

/-- Every piece of the edited tuple is the image of a piece. -/
theorem exists_imagePiece (P' : Piece (editedTuple W ρ N x) ρ.length) :
    ∃ P : Piece W ρ.length, hx.imagePiece P = P' := by
  have hd := P'.period_pos
  have hdA := Periodic.d_le_boundaryMargin N ρ.length
  by_cases hcase : ∃ R : Piece W ρ.length, R.coordinate = P'.coordinate ∧ x R ≠ 0 ∧
      P'.start ≤ (hx.imagePiece R).start + Periodic.boundaryMargin N ρ.length ∧
          (hx.imagePiece R).start + Periodic.boundaryMargin N ρ.length ≤ P'.stop
  · obtain ⟨R, hRl, hxR, h1, h2⟩ := hcase
    refine ⟨R, piece_eq_of_overlap hRl (by omega) ?_⟩
    have := hx.imagePiece_stop_eq R
    have := hx.retainedLength_ge_fixedMargin R hxR
    unfold Periodic.fixedMargin at this
    omega
  push Not at hcase
  have hPs : P'.start ≤
      (editedTuple W ρ N x
          P'.coordinate).length := by have := P'.start_lt_stop; have := P'.stop_le_length; omega
  obtain ⟨c, hc⟩ := hx.exists_canonicalCut P'.coordinate hPs
  have hPl := P'.start_add_len
  obtain ⟨hcn, htext⟩ := hx.canonicalCut_add (n := P'.len) hc
    (by have := P'.stop_le_length; omega)
    fun R hRl hxR h => absurd (hcase R hRl hxR (by omega)) (by omega)
  obtain ⟨hcl, hck, hcr⟩ := hc
  obtain ⟨hcnl, hcnk, hcnr⟩ := hcn
  have hlenU := length_editedTuple (W := W) (ρ := ρ) (N := N) (x := x) P'.coordinate
  unfold keepCut at hck hcnk hlenU
  have hcW : c < (W P'.coordinate).length := by
    by_contra hge
    have : c = (W P'.coordinate).length := by omega
    subst this
    have := P'.start_lt_stop; have := P'.stop_le_length; omega
  have hlg := P'.len_ge
  -- the letters of the original stretch
  have hper : ∀ p, c ≤ p → p + ρ.length < c + P'.len → (W P'.coordinate)[p]? =
      (W P'.coordinate)[p + ρ.length]? := by
    intro p hp hpe
    rw [show p = c + (p - c) by omega, htext _ (by omega), Nat.add_assoc,
      htext _ (by omega), ← Nat.add_assoc]
    exact P'.periodic _ (by omega) (by omega)
  have hroot : ((W P'.coordinate).drop c).take ρ.length = P'.root := by
    apply List.ext_getElem?
    intro i
    by_cases hi : i < ρ.length
    · rw [List.getElem?_take_of_lt hi, List.getElem?_drop, htext i (by omega), Piece.root,
        List.getElem?_take_of_lt hi, List.getElem?_drop]
    · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none
        (by rw [P'.root_length]; omega)]
  have hmaxL : c = 0 ∨ (W P'.coordinate)[c - 1]? ≠ (W P'.coordinate)[c - 1 + ρ.length]? := by
    by_cases hs0 : P'.start = 0
    · left
      by_contra hc0
      have := retainedCount_succ_of_not_mem
        (zero_not_mem (W := W) (ρ := ρ) (N := N) (x := x) (l := P'.coordinate))
      have := retainedCount_mono (D := deletedPositions W ρ N x P'.coordinate) (show 1 ≤ c by omega)
      simp at *; omega
    rcases P'.left_maximal with h | h
    · exact absurd h hs0
    right
    have hc0 : c ≠ 0 := by intro h0; subst h0; simp at hck; omega
    have hcm : c - 1 ∉ deletedPositions W ρ N x P'.coordinate := by
      intro hm
      have hcD := hcr hcW
      obtain ⟨R, _, hRl, h1, h2⟩ := mem_deletedPositions.mp hm
      have hxR : x R ≠ 0 := by intro h0; rw [h0] at h2; omega
      have hend : c = R.start + Periodic.boundaryMargin N ρ.length +
          Periodic.statePeriodModulus N ρ.length * x R := by
        by_contra hne
        exact hcD (by rw [← hRl]; exact hx.site_sub (by omega) (by omega))
      have hj := hx.retainedCount_junction R hxR
      have hkm : keepCut W ρ N x R.coordinate
          (R.start + Periodic.boundaryMargin N ρ.length + Periodic.statePeriodModulus N ρ.length * x
              R) =
          keepCut W ρ N x R.coordinate (R.start + Periodic.boundaryMargin N ρ.length) :=
        retainedCount_add_of_mem (fun i hi => hx.site_sub (by omega) (by omega))
      rw [← hend, hRl] at hkm
      rw [hRl] at hj
      unfold keepCut at hj hkm
      exact absurd (hcase R hRl hxR (by omega)) (by have := P'.start_lt_stop; omega)
    have hk1 := retainedCount_succ_of_not_mem hcm
    rw [show c - 1 + 1 = c by omega] at hk1
    rw [← (show (editedTuple W ρ N x P'.coordinate)[P'.start - 1]? = (W P'.coordinate)[c - 1]? by
      rw [show P'.start - 1 = retainedCount (deletedPositions W ρ N x P'.coordinate)
          (c - 1) by omega, editedTuple,
        getElem?_deletePositions _ hcm (by omega)]),
      show c - 1 + ρ.length = c + (ρ.length - 1) by omega, htext _ (by omega),
      show P'.start + (ρ.length - 1) = P'.start - 1 + ρ.length by omega]
    exact h
  have hmaxR : c + P'.len = (W P'.coordinate).length ∨
      (W P'.coordinate)[c + P'.len]? ≠ (W P'.coordinate)[c + P'.len - ρ.length]? := by
    by_cases hE : P'.stop = (editedTuple W ρ N x P'.coordinate).length
    · left
      by_contra hne
      have :=
          retainedCount_lt_of_not_mem (hcnr (by omega))
              (show c + P'.len < (W P'.coordinate).length by omega)
      omega
    rcases P'.right_maximal with h | h
    · exact absurd h hE
    right
    have hlt : c + P'.len < (W P'.coordinate).length := by
      by_contra hge
      have : c + P'.len = (W P'.coordinate).length := by omega
      rw [this] at hcnk; omega
    rw [← (show (editedTuple W ρ N x P'.coordinate)[P'.stop]? = (W P'.coordinate)[c + P'.len]? by
      rw [show P'.stop = retainedCount (deletedPositions W ρ N x P'.coordinate)
          (c + P'.len) by omega, editedTuple,
        getElem?_deletePositions _ (hcnr hlt) hlt]),
      show c + P'.len - ρ.length = c + (P'.len - ρ.length) by omega, htext _ (by omega),
      show P'.start + (P'.len - ρ.length) = P'.stop - ρ.length by omega]
    exact h
  refine
      ⟨⟨P'.coordinate, c, c + P'.len, by omega, hcnl, hper, by rw [hroot]; exact P'.primitive,
          hmaxL,
    hmaxR⟩, ?_⟩
  apply Piece.ext_coordinates
  · rfl
  · exact hck
  · change retainedCount (deletedPositions W ρ N x P'.coordinate) (c + P'.len) = P'.stop
    rw [hcnk]; omega

/-- The last letter of a word is never deleted. -/
theorem last_not_mem (l : Fin k) (h : 0 < (W l).length) :
    (W l).length - 1 ∉ deletedPositions W ρ N x l := by
  intro hm
  obtain ⟨R, _, hRl, h1, h2⟩ := mem_deletedPositions.mp hm
  have hxR : x R ≠ 0 := by intro h0; rw [h0] at h2; omega
  have hb := hx.site_bound hxR
  have := R.stop_le_length; have := R.period_pos; have := Periodic.d_le_boundaryMargin N ρ.length
  subst hRl; omega

theorem retainedCount_lt_length {l : Fin k} {c : ℕ} (hc : c < (W l).length) :
    keepCut W ρ N x l c < keepCut W ρ N x l (W l).length := by
  have :=
      retainedCount_lt_of_not_mem (D := deletedPositions W ρ N x l) (hx.last_not_mem l (by omega))
    (show (W l).length - 1 < (W l).length by omega)
  have := retainedCount_mono (D := deletedPositions W ρ N x l) (show c ≤ (W l).length - 1 by omega)
  unfold keepCut; omega

/-- The edited tuple visits only states that the original visits. -/
theorem editedTuple_visitedStates [Fintype S] [DecidableEq S] (T : Table α S k)
    (hN : N = Fintype.card S)
    (l : Fin k) : T.visitedStates (editedTuple W ρ N x) l ⊆ T.visitedStates W l := by
  intro q hq
  obtain ⟨c', hc', rfl⟩ := mem_visitedStates.mp hq
  obtain ⟨c, hc⟩ := hx.exists_canonicalCut l hc'
  exact mem_visitedStates.mpr ⟨c, hc.1, (hx.runPrefix_canonicalCut T hN hc).symm⟩

/-! ## Pieces joined by a follower edge -/

theorem len_eq_retainedLength_add (P : Piece W ρ.length) :
    P.len = retainedLength (N := N) (x := x) P + Periodic.statePeriodModulus N ρ.length * x P := by
  unfold retainedLength
  by_cases hxP : x P = 0
  · rw [hxP]; simp
  · have := hx.long P (hx.supp P hxP) hxP; omega

omit [DecidableEq α] hx in
theorem comparisonGap_pos (P : Piece W ρ.length) :
    0 < Periodic.comparisonGap N ρ.length := by
  have := Periodic.d_le_boundaryMargin N ρ.length; have :=
      P.period_pos; unfold Periodic.comparisonGap; omega

/-- Two pieces joined by a follower edge lose the same number of blocks, or one is shorter than
the other by at least `comparisonGap` both before and after the deletion. -/
theorem followerEdge_cases {P Q : Piece W ρ.length} (hP : P ∈ piecesOf W ρ) (hQ : Q ∈ piecesOf W ρ)
    (hG : FollowerEdge P Q) : x P = x Q ∨
      (P.len + Periodic.comparisonGap N ρ.length ≤ Q.len ∧
        retainedLength (N := N) (x := x) P + Periodic.comparisonGap N ρ.length ≤ retainedLength
            (N := N) (x := x) Q) ∨
      (Q.len + Periodic.comparisonGap N ρ.length ≤ P.len ∧
        retainedLength (N := N) (x := x) Q + Periodic.comparisonGap N ρ.length ≤ retainedLength
            (N := N) (x := x) P) := by
  by_cases h1 : P.len + Periodic.comparisonGap N ρ.length ≤ Q.len
  · right; left; exact ⟨h1, by have := hx.far P hP Q hQ hG h1; unfold retainedLength; omega⟩
  by_cases h2 : Q.len + Periodic.comparisonGap N ρ.length ≤ P.len
  · right; right; exact ⟨h2, by have := hx.far Q hQ P hP hG.symm h2; unfold retainedLength; omega⟩
  left; exact hx.near P hP Q hQ hG (by omega) (by omega)

theorem len_le_of_followerEdge {P Q : Piece W ρ.length} (hP : P ∈ piecesOf W ρ)
    (hQ : Q ∈ piecesOf W ρ)
    (hG : FollowerEdge P Q)
        (hle : retainedLength (N := N) (x := x) P ≤ retainedLength (N := N) (x := x) Q) :
    P.len ≤ Q.len := by
  have := comparisonGap_pos (N := N) P
  rcases hx.followerEdge_cases hP hQ hG with h | h | h
  · rw [hx.len_eq_retainedLength_add P, hx.len_eq_retainedLength_add Q, h]; omega
  · omega
  · omega

theorem eq_of_followerEdge {P Q : Piece W ρ.length} (hP : P ∈ piecesOf W ρ) (hQ : Q ∈ piecesOf W ρ)
    (hG : FollowerEdge P Q)
        (heq : retainedLength (N := N) (x := x) P = retainedLength (N := N) (x := x) Q) :
    x P = x Q ∧ P.len = Q.len := by
  have := comparisonGap_pos (N := N) P
  rcases hx.followerEdge_cases hP hQ hG with h | h | h
  · refine ⟨h, ?_⟩; rw [hx.len_eq_retainedLength_add P, hx.len_eq_retainedLength_add Q, h, heq]
  · omega
  · omega

end AdmissibleDeletion

end DeciSigma1.Holes.Periodic
