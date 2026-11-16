/-
Copyright (c) 2026 Yaoyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaoyu Zhao
-/

module

public import LeanPool.DeciSigma1.Holes.Periodic.Pieces
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Pow

/-! Ported to Lean Pool’s module system and pinned Lean and Mathlib.

 # Admissible deletions are dominations

A channel pair of the edited tuple compares two suffixes of edited words. Read from the
canonical original cuts, the compared texts are original texts unless the comparison crosses a
deleted block of a piece. Pieces met by a comparison are copied from host to target, and the
conditions of an admissible deletion on pieces joined by a follower edge make the deleted blocks
on both sides match. Hence every comparison of edited texts is a comparison of original texts at
the canonical cuts (`AdmissibleDeletion.canonicalCut_suffixComparison`), every channel of the
edited tuple is contained in the original channel, and the edited tuple dominates the original
one (`editedTuple_dominates`).

For a hole, the first rejected cut moves to its image (`editedTuple_firstRejection`). A piece
of another class whose period is at most `|ρ|` and that is long enough survives the deletion
unchanged (`exists_preserved_piece_of_nonconjugate_root`), which lets the compression of the
rejected-tail bound treat the classes one at a time.

## Main declarations

- `SuffixComparison`: comparison of suffixes in index form.
- `AdmissibleDeletion.canonicalCut_suffixComparison`: comparisons lift to canonical cuts.
- `editedTuple_channel_subset`, `editedTuple_dominates`: the edited tuple dominates the
  original one.
- `editedTuple_firstRejection`: the first rejected cut follows the cut map.
- `exists_preserved_piece_of_nonconjugate_root`: pieces of other classes are preserved.
-/

@[expose] public section


namespace DeciSigma1.Holes.Periodic

open DeciSigma1.Readers DeciSigma1.Words
open DeciSigma1.Readers.Table

variable {α : Type} {k : ℕ}

/-! ## Comparisons in index form -/

/-- `SuffixComparison y b z a`: the suffix of `y` from cut `b` is a prefix of the suffix of `z`
from cut `a`. -/
def SuffixComparison (y : List α) (b : ℕ) (z : List α) (a : ℕ) : Prop :=
  ∀ n, b + n < y.length → y[b + n]? = z[a + n]?

theorem drop_prefix_iff_suffixComparison {y z : List α} {b a : ℕ} :
    y.drop b <+: z.drop a ↔ SuffixComparison y b z a := by
  rw [List.prefix_iff_getElem?]
  constructor
  · intro h n hn
    have := h n (by simp; omega)
    rw [List.getElem?_drop] at this
    rw [this, List.getElem_drop, List.getElem?_eq_getElem hn]
  · intro h n hn
    simp only [List.length_drop] at hn
    rw [List.getElem?_drop, ← h n (by omega), List.getElem_drop, List.getElem?_eq_getElem]

namespace SuffixComparison

variable {y z : List α} {b a : ℕ}

theorem shift (h : SuffixComparison y b z a) (m : ℕ) : SuffixComparison y (b + m) z (a + m) := by
  intro n hn
  have := h (m + n) (by omega)
  rwa [← Nat.add_assoc, ← Nat.add_assoc] at this

theorem lt_length (h : SuffixComparison y b z a) {n : ℕ} (hn : b + n < y.length) :
    a + n < z.length := by
  have := h n hn
  rw [List.getElem?_eq_getElem hn] at this
  by_contra hge
  rw [List.getElem?_eq_none (by omega)] at this
  exact absurd this (by simp)

theorem append {r : ℕ} (h₁ : ∀ n < r, y[b + n]? = z[a + n]?)
    (h₂ : SuffixComparison y (b + r) z (a + r)) :
    SuffixComparison y b z a := by
  intro n hn
  rcases Nat.lt_or_ge n r with h | h
  · exact h₁ n h
  · have := h₂ (n - r) (by omega)
    rwa [Nat.add_assoc, Nat.add_sub_cancel' h, Nat.add_assoc, Nat.add_sub_cancel' h] at this

end SuffixComparison

/-! ## Copying pieces through a comparison -/

section Copy

variable [DecidableEq α] {V : Fin k → List α} {d : ℕ}

omit [DecidableEq α] in
/-- A piece whose start (with its left break) lies inside a stretch where two words agree is
copied: the other word has a piece starting at the corresponding cut with the same root, at
least as long as the copied part, and ending at the corresponding cut when its right break is
copied too. -/
theorem copy_piece {a b : Fin k} {u v m : ℕ}
    (hag : ∀ n < m, (V a)[u + n]? = (V b)[v + n]?) (R : Piece V d) (hRl : R.coordinate = a)
    (h1 : u < R.start) {ℓ : ℕ} (hℓ : 2 * d ≤ ℓ) (hℓR : R.start + ℓ ≤ R.stop)
        (hℓm : R.start + ℓ ≤ u + m) :
    ∃ P : Piece V d, P.coordinate = b ∧ P.start = v + (R.start - u) ∧ P.root = R.root ∧
      v + (R.start - u) + ℓ ≤ P.stop ∧
      (R.stop < u + m → R.stop < (V a).length → P.stop = v + (R.stop - u)) := by
  subst hRl
  have hd := R.period_pos
  have hle := R.stop_le_length
  -- letters of `R` up to `R.start + ℓ` exist on the other side
  have hcopy : ∀ p, u ≤ p → p < u + m → (V R.coordinate)[p]? = (V b)[v + (p - u)]? := by
    intro p hp hpm; have := hag (p - u) (by omega); rwa [Nat.add_sub_cancel' hp] at this
  have hlen : v + (R.start - u) + ℓ ≤ (V b).length := by
    have h := hcopy (R.start + ℓ - 1) (by omega) (by omega)
    rw [List.getElem?_eq_getElem (by omega)] at h
    by_contra hge
    rw [List.getElem?_eq_none (by omega)] at h
    exact absurd h (by simp)
  have hper : PeriodicOn (V b) d (v + (R.start - u)) (v + (R.start - u) + ℓ) := by
    intro p hp hpe
    have e1 := hcopy (p - v + u) (by omega) (by omega)
    have e2 := hcopy (p - v + u + d) (by omega) (by omega)
    rw [show v + (p - v + u - u) = p by omega] at e1
    rw [show v + (p - v + u + d - u) = p + d by omega] at e2
    rw [← e1, ← e2]
    exact R.periodic _ (by omega) (by omega)
  have hwin : ((V b).drop (v + (R.start - u))).take d = R.root := by
    apply List.ext_getElem?
    intro t
    by_cases ht : t < d
    · rw [List.getElem?_take_of_lt ht, List.getElem?_drop, Piece.root, List.getElem?_take_of_lt ht,
        List.getElem?_drop, hcopy (R.start + t) (by omega) (by omega)]
      congr 1; omega
    · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none
        (by rw [R.root_length]; omega)]
  have hbrkL : v + (R.start - u) = 0 ∨ (V b)[v + (R.start - u) - 1]? ≠
      (V b)[v + (R.start - u) - 1 + d]? := by
    right
    rcases R.left_maximal with h | h
    · omega
    · have e1 := hcopy (R.start - 1) (by omega) (by omega)
      have e2 := hcopy (R.start - 1 + d) (by omega) (by omega)
      rw [show v + (R.start - 1 - u) = v + (R.start - u) - 1 by omega] at e1
      rw [show v + (R.start - 1 + d - u) = v + (R.start - u) - 1 + d by omega] at e2
      rw [← e1, ← e2]; exact h
  obtain ⟨P, hPl, hPs, hPe, hcls, hL, hR⟩ := exists_piece_of_stretch V b (by omega) hlen hper
    (by rw [hwin]; exact R.primitive)
  have hPs' : P.start = v + (R.start - u) := hL hbrkL
  refine ⟨P, hPl, hPs', ?_, hPe, ?_⟩
  · change ((V P.coordinate).drop P.start).take d = R.root
    rw [hPl, hPs']; exact hwin
  · intro hRm hRlen
    -- the right break of `R` is copied
    have hEle : R.start + ℓ ≤ R.stop := hℓR
    rcases R.right_maximal with h | h
    · omega
    · have hstretch : PeriodicOn (V b) d (v + (R.start - u)) (v + (R.stop - u)) := by
        intro p hp hpe
        have e1 := hcopy (p - v + u) (by omega) (by omega)
        have e2 := hcopy (p - v + u + d) (by omega) (by omega)
        rw [show v + (p - v + u - u) = p by omega] at e1
        rw [show v + (p - v + u + d - u) = p + d by omega] at e2
        rw [← e1, ← e2]
        exact R.periodic _ (by omega) (by omega)
      have hlen' : v + (R.stop - u) ≤ (V b).length := by
        have h' := hcopy R.stop (by omega) hRm
        rw [List.getElem?_eq_getElem hRlen] at h'
        by_contra hge
        rw [List.getElem?_eq_none (by omega)] at h'
        exact absurd h' (by simp)
      obtain ⟨P₂, hP₂l, hP₂s, hP₂e, _, hL₂, hR₂⟩ := exists_piece_of_stretch V b (by omega) hlen'
        hstretch (by rw [hwin]; exact R.primitive)
      have hP₂s' := hL₂ hbrkL
      have hP₂e' : P₂.stop = v + (R.stop - u) := hR₂ (by
        right
        have e1 := hcopy R.stop (by omega) hRm
        have e2 := hcopy (R.stop - d) (by omega) (by omega)
        rw [show v + (R.stop - d - u) = v + (R.stop - u) - d by omega] at e2
        rw [← e1, ← e2]; exact h)
      have : P = P₂ := Piece.ext_coordinates (hPl.trans hP₂l.symm) (hPs'.trans hP₂s'.symm) (by
        by_contra hne
        exact absurd (piece_eq_of_overlap (P := P) (Q := P₂) (hPl.trans hP₂l.symm)
          (by omega) (by omega)) (by intro h'; rw [h'] at hne; exact hne rfl))
      rw [this, hP₂e']

omit [DecidableEq α] in
/-- A periodic stretch of length `> 2d` inside a piece, seen through an agreement, lies in a
piece of the other word of the same class; if the stretch ends with the piece's right break,
copied too, the other piece ends at the corresponding cut. -/
theorem copy_stretch {a b : Fin k} {u v m : ℕ}
    (hag : ∀ n < m, (V a)[u + n]? = (V b)[v + n]?) (R : Piece V d) (hRl : R.coordinate = a)
    (h1 : R.start ≤ u) {ℓ : ℕ} (hℓ : 2 * d < ℓ) (hℓR : u + ℓ ≤ R.stop) (hℓm : ℓ ≤ m) :
    ∃ P : Piece V d, P.coordinate = b ∧ P.start ≤ v ∧ v + ℓ ≤ P.stop ∧ IsConjugate P.root R.root ∧
      (u + ℓ = R.stop → ℓ < m → R.stop < (V a).length → P.stop = v + ℓ) := by
  subst hRl
  have hd := R.period_pos
  have hle := R.stop_le_length
  have hcopy : ∀ p, u ≤ p → p < u + m → (V R.coordinate)[p]? = (V b)[v + (p - u)]? := by
    intro p hp hpm; have := hag (p - u) (by omega); rwa [Nat.add_sub_cancel' hp] at this
  have hlen : v + ℓ ≤ (V b).length := by
    have h := hcopy (u + ℓ - 1) (by omega) (by omega)
    rw [List.getElem?_eq_getElem (by omega)] at h
    by_contra hge
    rw [List.getElem?_eq_none (by omega)] at h
    exact absurd h (by simp)
  have hper : PeriodicOn (V b) d v (v + ℓ) := by
    intro p hp hpe
    have e1 := hcopy (p - v + u) (by omega) (by omega)
    have e2 := hcopy (p - v + u + d) (by omega) (by omega)
    rw [show v + (p - v + u - u) = p by omega] at e1
    rw [show v + (p - v + u + d - u) = p + d by omega] at e2
    rw [← e1, ← e2]
    exact R.periodic _ (by omega) (by omega)
  have hwin : ((V b).drop v).take d = ((V R.coordinate).drop u).take d := by
    apply List.ext_getElem?
    intro t
    by_cases ht : t < d
    · rw [List.getElem?_take_of_lt ht, List.getElem?_drop, List.getElem?_take_of_lt ht,
        List.getElem?_drop, hcopy (u + t) (by omega) (by omega)]
      congr 1; omega
    · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
  have hRcls : IsConjugate R.root (((V R.coordinate).drop u).take d) :=
      R.window_isConjugate h1 (by omega)
  obtain ⟨P, hPl, hPs, hPe, hcls, _, hR⟩ := exists_piece_of_stretch V b (by omega) hlen hper
    (by rw [hwin]; exact hRcls.isPrimitive R.primitive)
  refine ⟨P, hPl, hPs, hPe, ?_, ?_⟩
  · rw [hwin] at hcls; exact hcls.trans hRcls.symm
  · intro hend hlm hRlen
    apply hR
    right
    rcases R.right_maximal with h | h
    · omega
    · have e1 := hcopy R.stop (by omega) (by omega)
      have e2 := hcopy (R.stop - d) (by omega) (by omega)
      rw [show v + (R.stop - u) = v + ℓ by omega] at e1
      rw [show v + (R.stop - d - u) = v + ℓ - d by omega] at e2
      rw [← e1, ← e2]; exact h

end Copy

/-! ## Comparing original texts through pieces -/

section PieceCmp

variable [DecidableEq α] {W : Fin k → List α} {d : ℕ}

omit [DecidableEq α] in
/-- Two pieces whose texts agree on `d` letters from the offsets `oP`, `oQ` compare from those
offsets, provided the host piece has at least as much room and either the target piece ends its
word or the rooms are equal and the followers compare. -/
theorem piece_suffixComparison (P Q : Piece W d) {oP oQ : ℕ} (hoP : oP ≤ P.len) (hoQ : oQ ≤ Q.len)
    (hanchor : ∀ t < d,
        t < P.len - oP → (W P.coordinate)[P.start + oP + t]? = (W Q.coordinate)[Q.start + oQ + t]?)
    (hlen : P.len - oP ≤ Q.len - oQ)
    (hfol : P.stop = (W P.coordinate).length ∨ (P.len - oP = Q.len - oQ ∧ SuffixComparison
        (W P.coordinate) P.stop (W Q.coordinate) Q.stop)) :
    SuffixComparison (W P.coordinate) (P.start + oP) (W Q.coordinate) (Q.start + oQ) := by
  classical
  have hd := P.period_pos
  have hPl := P.start_add_len
  have hQl := Q.start_add_len
  intro n hn
  rcases Nat.lt_or_ge n (P.len - oP) with h | h
  · have hmle := Nat.mod_le n d
    have e1 := P.getElem?_eq_of_mod (o₁ := oP + n) (o₂ := oP + n % d) (by omega) (by omega)
      (Nat.add_mod_mod oP n d).symm
    have e2 := hanchor (n % d) (Nat.mod_lt _ hd) (by omega)
    have e3 := Q.getElem?_eq_of_mod (o₁ := oQ + n % d) (o₂ := oQ + n) (by omega) (by omega)
      (Nat.add_mod_mod oQ n d)
    simp only [Nat.add_assoc] at e1 e2 e3 ⊢
    rw [e1, e2, e3]
  · rcases hfol with hE | ⟨heq, hcmp⟩
    · omega
    · have := hcmp (n - (P.len - oP)) (by omega)
      rwa [show P.stop + (n - (P.len - oP)) = P.start + oP + n by omega,
        show Q.stop + (n - (P.len - oP)) = Q.start + oQ + n by omega] at this

omit [DecidableEq α] in
/-- Pieces with equal roots agree on their first `d` letters, as `piece_suffixComparison` requires
at offsets `0`. -/
theorem getElem?_eq_of_root_eq (P Q : Piece W d) (h : P.root = Q.root) :
    ∀ t < d, t < P.len - 0 → (W P.coordinate)[P.start + 0 + t]? =
        (W Q.coordinate)[Q.start + 0 + t]? := by
  intro t ht _
  have hP := P.getElem?_root (o := t) (by have := P.len_ge; omega)
  have hQ := Q.getElem?_root (o := t) (by have := Q.len_ge; omega)
  rw [Nat.add_zero, Nat.add_zero, hP, hQ, h]

end PieceCmp

/-! ## The backward expansion at canonical cuts -/

namespace AdmissibleDeletion

variable [DecidableEq α] {W : Fin k → List α} {ρ : List α} {N : ℕ} {x : Piece W ρ.length → ℕ}

/-- No deleted block of a shortened piece that starts at or before `c'` lies in the window
`(c', c' + m)` of word `l`. -/
def NoInteriorJunction (hx : AdmissibleDeletion W ρ N x) (l : Fin k) (c' m : ℕ) : Prop :=
  ∀ R : Piece W ρ.length, R.coordinate = l → x R ≠ 0 → (hx.imagePiece R).start ≤ c' →
    c' < (hx.imagePiece R).start + Periodic.boundaryMargin N ρ.length → c' + m ≤
        (hx.imagePiece R).start + Periodic.boundaryMargin N ρ.length

variable (hx : AdmissibleDeletion W ρ N x)
include hx

theorem imagePiece_piece_mem {R : Piece W ρ.length} (hxR : x R ≠ 0) :
    hx.imagePiece R ∈ piecesOf (editedTuple W ρ N x) ρ :=
        (hx.imagePiece_mem_iff R).mpr (hx.supp R hxR)

theorem imagePiece_room {R : Piece W ρ.length} (hxR : x R ≠ 0) :
    (hx.imagePiece R).start + 6 * Periodic.boundaryMargin N ρ.length + 2 *
        Periodic.statePeriodModulus N ρ.length ≤ (hx.imagePiece R).stop := by
  have := hx.retainedLength_ge_fixedMargin R hxR; have :=
      hx.imagePiece_stop_eq R; unfold Periodic.fixedMargin at *; omega

/-- For a piece of the edited tuple, `NoInteriorJunction` holds at the cut `|ρ|` letters before its
end, for every window length. -/
theorem nojun_end (P' : Piece (editedTuple W ρ N x) ρ.length) (m : ℕ) :
    hx.NoInteriorJunction P'.coordinate (P'.stop - ρ.length) m := by
  intro R hRl hxR h1 h2
  exfalso
  have hroom := hx.imagePiece_room hxR
  have hdA := Periodic.d_le_boundaryMargin N ρ.length
  have hR'l : (hx.imagePiece R).coordinate = P'.coordinate := hRl
  by_cases hRP : hx.imagePiece R = P'
  · have hs : (hx.imagePiece R).start = P'.start := by rw [hRP]
    have he : (hx.imagePiece R).stop = P'.stop := by rw [hRP]
    omega
  · rcases le_total (hx.imagePiece R).start P'.start with h | h
    · have := Piece.sep hRP hR'l h; have := P'.long; omega
    · have := Piece.sep (Ne.symm hRP) hR'l.symm h; omega

/-- The junction of a shortened host piece that starts strictly inside the compared window gives a
piece of the class in the target at the corresponding cut. -/
theorem target_piece_of_junction (hN : 0 < N) {i j : Fin k} {ct ch : ℕ}
    (hcmp : SuffixComparison (editedTuple W ρ N x j) ct (editedTuple W ρ N x i) ch)
        (R : Piece W ρ.length)
    (hRl : R.coordinate = i) (hxR : x R ≠ 0) (h1 : ch < (hx.imagePiece R).start)
    (h2 : (hx.imagePiece R).start + Periodic.boundaryMargin N ρ.length < ch +
        ((editedTuple W ρ N x j).length - ct)) :
    ∃ P' : Piece (editedTuple W ρ N x) ρ.length, P'.coordinate = j ∧ P' ∈
        piecesOf (editedTuple W ρ N x) ρ ∧
      P'.start = ct + ((hx.imagePiece R).start - ch) := by
  have hroom := hx.imagePiece_room hxR
  have h2d := Periodic.two_d_le_boundaryMargin hN ρ.length
  have hd := (hx.imagePiece R).period_pos
  have hag : ∀ n < (editedTuple W ρ N x j).length - ct,
      (editedTuple W ρ N x i)[ch + n]? = (editedTuple W ρ N x j)[ct + n]? :=
    fun n hn => (hcmp n (by omega)).symm
  obtain ⟨P, hPl, hPs, hProot, _, _⟩ := copy_piece hag (hx.imagePiece R) hRl h1
    (ℓ := Periodic.boundaryMargin N ρ.length + 1) (by omega) (by omega) (by omega)
  refine ⟨P, hPl, ?_, hPs⟩
  rw [mem_piecesOf, hProot, hx.imagePiece_root]
  exact (mem_piecesOf _).mp (hx.supp R hxR)

omit hx in
theorem canonicalCut_le_length {l : Fin k} {c c' : ℕ} (h :
    CanonicalCut (W := W) (ρ := ρ) (N := N) (x := x) l c c') :
    c' ≤ (editedTuple W ρ N x l).length := by
  rw [← h.2.1, length_editedTuple]; exact retainedCount_mono h.1

theorem canonicalCut_start_of_image_eq {P : Piece W ρ.length}
    {P' : Piece (editedTuple W ρ N x) ρ.length}
    (hP : hx.imagePiece P = P') {l : Fin k}
        (hl : P'.coordinate = l) :
            CanonicalCut (W := W) (ρ := ρ) (N := N) (x := x) l P.start P'.start := by
  have hPl : P.coordinate = l := by rw [← hl, ← hP]; rfl
  have := hx.canonicalCut_start P; rw [hP, hPl] at this; exact this

theorem canonicalCut_end_sub_of_image_eq {P : Piece W ρ.length}
    {P' : Piece (editedTuple W ρ N x) ρ.length}
    (hP : hx.imagePiece P = P') {l : Fin k} (hl : P'.coordinate = l) :
    CanonicalCut (W := W) (ρ := ρ) (N := N) (x := x) l (P.stop - ρ.length) (P'.stop - ρ.length)
        := by
  have hPl : P.coordinate = l := by rw [← hl, ← hP]; rfl
  have := hx.canonicalCut_end_sub P; rw [hP, hPl] at this; exact this

/-- No junction of word `l` lies in the window `(c', c' + n)` if `n ≤ m`, the shortened pieces
starting at or before `c'` have no junction in `(c', c' + m)`, and the pieces starting after `c'`
have no junction in `(c', c' + n)`. -/
theorem noJunction_window {l : Fin k} {c' m n : ℕ} (hNJ : hx.NoInteriorJunction l c' m)
    (hn : n ≤ m)
    (hafter : ∀ R : Piece W ρ.length, R.coordinate = l → x R ≠ 0 → c' < (hx.imagePiece R).start →
      (hx.imagePiece R).start + Periodic.boundaryMargin N ρ.length < c' + n → False) :
    ∀ R : Piece W ρ.length, R.coordinate = l → x R ≠ 0 →
      ¬ (c' < (hx.imagePiece R).start + Periodic.boundaryMargin N ρ.length ∧
        (hx.imagePiece R).start + Periodic.boundaryMargin N ρ.length < c' + n) := by
  rintro R hRl hxR ⟨h1, h2⟩
  by_cases hs : (hx.imagePiece R).start ≤ c'
  · have := hNJ R hRl hxR hs h1; omega
  · exact hafter R hRl hxR (by omega) h2

/-- A comparison of edited texts between canonical cuts, with no deleted block of a piece that
starts at or before either cut inside the window, is a comparison of original texts at the
canonical cuts. -/
theorem canonicalCut_suffixComparison (hN : 0 < N) (i j : Fin k) (m : ℕ) :
    ∀ ct' ch', (editedTuple W ρ N x j).length - ct' = m → ct' ≤ (editedTuple W ρ N x j).length →
      SuffixComparison (editedTuple W ρ N x j) ct' (editedTuple W ρ N x i) ch' →
          hx.NoInteriorJunction j ct' m →
      hx.NoInteriorJunction i ch' m → ∀ ct ch,
        CanonicalCut (W := W) (ρ := ρ) (N := N) (x := x) j ct ct' →
        CanonicalCut (W := W) (ρ := ρ) (N := N) (x := x) i ch ch' →
      SuffixComparison (W j) ct (W i) ch := by
  classical
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro ct' ch' hm hct hcmp hNJt hNJh ct ch hctc hchc
  have hdA := Periodic.d_le_boundaryMargin N ρ.length
  have h2d := Periodic.two_d_le_boundaryMargin hN ρ.length
  have hch' := canonicalCut_le_length hchc
  have hag : ∀ n < m, (editedTuple W ρ N x j)[ct' + n]? = (editedTuple W ρ N x i)[ch' + n]? :=
    fun n hn => hcmp n (by omega)
  by_cases hex : ∃ P' : Piece (editedTuple W ρ N x) ρ.length, P'.coordinate = j ∧
      P' ∈ piecesOf (editedTuple W ρ N x) ρ ∧ ct' < P'.start
  · -- the next class piece of the target
    have hexs : ∃ s₀, ∃ P' : Piece (editedTuple W ρ N x) ρ.length, P'.coordinate = j ∧
        P' ∈ piecesOf (editedTuple W ρ N x) ρ ∧ ct' < P'.start ∧ P'.start = s₀ := by
      obtain ⟨P', h1, h2, h3⟩ := hex; exact ⟨P'.start, P', h1, h2, h3, rfl⟩
    obtain ⟨P', hP'l, hP'm, hP's, hP's0⟩ := Nat.find_spec hexs
    have hmin : ∀ P'' : Piece (editedTuple W ρ N x) ρ.length, P''.coordinate = j →
        P'' ∈ piecesOf (editedTuple W ρ N x) ρ → ct' < P''.start → P'.start ≤ P''.start := by
      intro P'' h1 h2 h3; rw [hP's0]; exact Nat.find_min' hexs ⟨P'', h1, h2, h3, rfl⟩
    have hP'e := P'.stop_le_length; rw [hP'l] at hP'e
    have hd := P'.period_pos
    have hP'L := P'.start_add_len
    have hP'g := P'.len_ge
    -- the matched host piece
    obtain ⟨Q', hQ'l, hQ's, hQ'root, hQ'e, hQ'e'⟩ := copy_piece hag P' hP'l hP's
      (ℓ := P'.len) hP'g (by omega) (by omega)
    have hQ'm : Q' ∈ piecesOf (editedTuple W ρ N x) ρ := by
      rw [mem_piecesOf, hQ'root]; exact (mem_piecesOf _).mp hP'm
    obtain ⟨P, hP⟩ := hx.exists_imagePiece P'
    obtain ⟨Q, hQ⟩ := hx.exists_imagePiece Q'
    have hPl : P.coordinate = j := by rw [← hP'l, ← hP]; rfl
    have hQl : Q.coordinate = i := by rw [← hQ'l, ← hQ]; rfl
    have hPm : P ∈ piecesOf W ρ := (hx.imagePiece_mem_iff P).mp (hP ▸ hP'm)
    have hQm : Q ∈ piecesOf W ρ := (hx.imagePiece_mem_iff Q).mp (hQ ▸ hQ'm)
    have hQ'le := Q'.stop_le_length; rw [hQ'l] at hQ'le
    have hQ'L := Q'.start_add_len
    -- the unchanged region before the pieces, on both sides: a later junction of the target
    -- belongs to a class piece starting after `P'`, one of the host gives such a piece
    obtain ⟨hcT, htT⟩ := hx.canonicalCut_add hctc (n := P'.start - ct') (by omega)
      (hx.noJunction_window hNJt (by omega) fun R hRl hxR h1 h2 => by
        have := hmin (hx.imagePiece R) hRl (hx.imagePiece_piece_mem hxR) h1; omega)
    obtain ⟨hcH, htH⟩ := hx.canonicalCut_add hchc (n := P'.start - ct') (by omega)
      (hx.noJunction_window hNJh (by omega) fun R hRl hxR h1 h2 => by
        obtain ⟨P'', h1', h2', h3'⟩ := hx.target_piece_of_junction hN hcmp R hRl hxR h1 (by omega)
        have := hmin P'' h1' h2' (by omega); omega)
    rw [show ct' + (P'.start - ct') = P'.start by omega] at hcT
    rw [show ch' + (P'.start - ct') = Q'.start by omega] at hcH
    have hctr : ct + (P'.start - ct') = P.start :=
        canonicalCut_unique hcT (hx.canonicalCut_start_of_image_eq hP hP'l)
    have hchr : ch + (P'.start - ct') = Q.start :=
        canonicalCut_unique hcH (hx.canonicalCut_start_of_image_eq hQ hQ'l)
    have hreg : ∀ n < P'.start - ct', (W j)[ct + n]? = (W i)[ch + n]? := by
      intro n hn; rw [htT n hn, hag n (by omega), ← htH n hn]
    -- the piece step
    have hnP : retainedLength (N := N) (x := x) P = P'.len := by rw [← hx.imagePiece_len, hP]
    have hnQ : retainedLength (N := N) (x := x) Q = Q'.len := by rw [← hx.imagePiece_len, hQ]
    have hroot : P.root = Q.root := by
      rw [← hx.imagePiece_root P, ← hx.imagePiece_root Q, hP, hQ, hQ'root]
    have hstep : SuffixComparison (W j) P.start (W i) Q.start := by
      by_cases hterm : P'.stop = (editedTuple W ρ N x j).length
      · have hE : P.stop = (W P.coordinate).length := (hx.imagePiece_stop_eq_length_iff P).mp (by
          rw [hP, hterm, hPl])
        have hG : FollowerEdge P Q := Or.inl (by
          unfold Piece.follower; rw [hE, List.drop_length]; exact List.nil_prefix)
        have hle := hx.len_le_of_followerEdge hPm hQm hG (by omega)
        have := piece_suffixComparison P Q (oP := 0) (oQ := 0) (by omega) (by omega)
          (getElem?_eq_of_root_eq P Q hroot) (by omega) (Or.inl hE)
        rwa [hPl, hQl, Nat.add_zero, Nat.add_zero] at this
      · have hQe : Q'.stop = ch' + (P'.stop - ct') := hQ'e' (by omega) (by omega)
        have hfolN := ih ((editedTuple W ρ N x j).length - (P'.stop - ρ.length)) (by omega)
          (P'.stop - ρ.length) (Q'.stop - ρ.length) rfl (by omega)
          (by have := hcmp.shift (P'.stop - ρ.length - ct')
              rwa [show ct' + (P'.stop - ρ.length - ct') = P'.stop - ρ.length by omega,
                show ch' + (P'.stop - ρ.length - ct') = Q'.stop - ρ.length by omega] at this)
          (hP'l ▸ hx.nojun_end P' _) (hQ'l ▸ hx.nojun_end Q' _)
          (P.stop - ρ.length) (Q.stop - ρ.length) (hx.canonicalCut_end_sub_of_image_eq hP hP'l)
          (hx.canonicalCut_end_sub_of_image_eq hQ hQ'l)
        have hPe := P.long; have hQe2 := Q.long
        have hfol : SuffixComparison (W j) P.stop (W i) Q.stop := by
          have := hfolN.shift ρ.length
          rwa [Nat.sub_add_cancel (by omega), Nat.sub_add_cancel (by omega)] at this
        have hG : FollowerEdge P Q := Or.inl (by
          unfold Piece.follower; rw [hPl, hQl]; exact drop_prefix_iff_suffixComparison.mpr hfol)
        have heq := (hx.eq_of_followerEdge hPm hQm hG (by omega)).2
        have := piece_suffixComparison P Q (oP := 0) (oQ := 0) (by omega) (by omega)
          (getElem?_eq_of_root_eq P Q hroot) (by omega)
          (Or.inr ⟨by omega, by rw [hPl, hQl]; exact hfol⟩)
        rwa [hPl, hQl, Nat.add_zero, Nat.add_zero] at this
    exact SuffixComparison.append hreg (by rw [hctr, hchr]; exact hstep)
  · -- no further class piece of the target: the rest is unchanged text on both sides
    push Not at hex
    have hJt := hx.noJunction_window hNJt le_rfl fun R hRl hxR h1 _ =>
      absurd (hex (hx.imagePiece R) hRl (hx.imagePiece_piece_mem hxR)) (by omega)
    have hJh := hx.noJunction_window hNJh le_rfl fun R hRl hxR h1 h2 => by
      obtain ⟨P'', h1', h2', h3'⟩ := hx.target_piece_of_junction hN hcmp R hRl hxR h1 (by omega)
      exact absurd (hex P'' h1' h2') (by omega)
    have hhn : ch' + m ≤ (editedTuple W ρ N x i).length := by
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · omega
      · have := hcmp.lt_length (n := m - 1) (by omega); omega
    obtain ⟨_, hkT, htT⟩ := hx.text_canonicalCut hctc (by omega) hJt
    have htH := (hx.text_canonicalCut hchc hhn hJh).2.2
    intro n hn
    have hnm : n < m := by
      by_contra hge
      have := hx.retainedCount_lt_length (l := j) (c := ct + m) (by omega)
      rw [hkT, ← length_editedTuple] at this; omega
    rw [htT n hnm, hag n hnm, ← htH n hnm]

omit [DecidableEq α] in
/-- Offsets `o` and `p` in pieces of period `d` carry the same states: they are equal, or both are
at least the transient length and agree modulo the state period. -/
def SameStatePhase (N d o p : ℕ) : Prop :=
  o = p ∨ (Periodic.stateTransientLength N d ≤ o ∧ Periodic.stateTransientLength N d ≤ p ∧
    o % Periodic.statePeriodModulus N d = p % Periodic.statePeriodModulus N d)

omit [DecidableEq α] hx in
theorem mod_eq_of_add_mul {a b u v M : ℕ} (h : a + M * u = b + M * v) : a % M = b % M := by
  have h1 : (a + M * u) % M = a % M := Nat.add_mul_mod_self_left a M u
  have h2 : (b + M * v) % M = b % M := Nat.add_mul_mod_self_left b M v
  rw [← h1, ← h2, h]

omit hx in
omit [DecidableEq α] in
theorem mod_d_of_mod_statePeriodModulus {a b : ℕ} (h : SameStatePhase N ρ.length a b) :
    a % ρ.length = b % ρ.length := by
  rcases h with h | ⟨_, _, h⟩
  · rw [h]
  · have hd : ρ.length ∣ Periodic.statePeriodModulus N ρ.length := ⟨_, rfl⟩
    rw [← Nat.mod_mod_of_dvd a hd, ← Nat.mod_mod_of_dvd b hd, h]

/-- A comparison of the edited tuple that starts inside the images of two pieces, at offsets `pT`
and `pS`, lifts to a comparison of the original tuple at offsets `oT` and `oS` with the same
states. -/
theorem lift_in_pieces {S : Type} [Fintype S] (T : Table α S k) (hNS : N = Fintype.card S)
    {i j : Fin k} {P Q : Piece W ρ.length} (hPl : P.coordinate = j) (hQl : Q.coordinate = i)
    {b' a' pT pS oT oS : ℕ} (hb' : b' = (hx.imagePiece P).start + pT)
        (ha' : a' = (hx.imagePiece Q).start + pS)
    (hpT : pT + ρ.length ≤ retainedLength (N := N) (x := x) P)
    (hpS : pS + ρ.length ≤ retainedLength (N := N) (x := x) Q) (hoT : oT ≤ P.len) (hoS : oS ≤ Q.len)
    (hT : SameStatePhase N ρ.length oT pT) (hS : SameStatePhase N ρ.length oS pS)
    (hcmp : SuffixComparison (editedTuple W ρ N x j) b' (editedTuple W ρ N x i) a')
    (hlen : P.len - oT ≤ Q.len - oS)
    (hfol : P.stop = (W j).length ∨ (P.len - oT = Q.len - oS ∧ SuffixComparison (W j) P.stop
        (W i) Q.stop)) :
    SuffixComparison (W j) (P.start + oT) (W i) (Q.start + oS) ∧ T.runPrefix W j (P.start + oT) =
        T.runPrefix (editedTuple W ρ N x) j b' ∧
      T.runPrefix W i (Q.start + oS) = T.runPrefix (editedTuple W ρ N x) i a' := by
  have hLP := retainedLength_le (N := N) (x := x) P
  have hLQ := retainedLength_le (N := N) (x := x) Q
  have hd := P.period_pos
  have hmT := mod_d_of_mod_statePeriodModulus hT
  have hmS := mod_d_of_mod_statePeriodModulus hS
  have hPe : (hx.imagePiece P).stop ≤ (editedTuple W ρ N x j).length := by
    have := (hx.imagePiece P).stop_le_length; rw [imagePiece_coordinate, hPl] at this; exact this
  have hPimg := hx.imagePiece_stop_eq P
  -- states
  have hstate : ∀ (R : Piece W ρ.length) (o p : ℕ) (l : Fin k), R.coordinate = l → o ≤ R.len →
      p ≤ retainedLength (N := N) (x := x) R → SameStatePhase N ρ.length o p →
      T.runPrefix W l (R.start + o) =
          T.runPrefix (editedTuple W ρ N x) l ((hx.imagePiece R).start + p) := by
    intro R o p l hRl ho hp h
    subst hRl
    rw [hx.runPrefix_imagePiece T hNS R hp]
    rcases h with h | ⟨h1, h2, h3⟩
    · rw [h]
    · have := retainedLength_le (N := N) (x := x) R
      subst hNS
      exact R.runPrefix_mod T h1 h2 ho (by omega) h3
  refine ⟨?_, by rw [hb']; exact hstate P oT pT j hPl hoT (by omega) hT,
    by rw [ha']; exact hstate Q oS pS i hQl hoS (by omega) hS⟩
  have hanchor : ∀ t < ρ.length, t < P.len - oT →
      (W P.coordinate)[P.start + oT + t]? = (W Q.coordinate)[Q.start + oS + t]? := by
    intro t ht ht'
    have e1 := P.getElem?_eq_of_mod (o₁ := oT + t) (o₂ := pT + t) (by omega) (by omega)
      (by rw [Nat.add_mod, hmT, ← Nat.add_mod])
    have e2 := hx.getElem?_imagePiece P (o := pT + t) (by omega)
    have e3 := hx.getElem?_imagePiece Q (o := pS + t) (by omega)
    have e4 := Q.getElem?_eq_of_mod (o₁ := pS + t) (o₂ := oS + t) (by omega) (by omega)
      (by rw [Nat.add_mod, ← hmS, ← Nat.add_mod])
    have e5 := hcmp t (by rw [hb']; omega)
    simp only [Nat.add_assoc] at e1 e2 e3 e4 ⊢
    rw [e1, ← e2, hPl, ← Nat.add_assoc, ← hb', e5, ha', ← hQl, Nat.add_assoc, e3, e4]
  have := piece_suffixComparison P Q hoT hoS hanchor hlen (by rw [hPl, hQl]; exact hfol)
  rwa [hPl, hQl] at this

private theorem suffixComparison_lift_of_piece {S : Type} [Fintype S] (T : Table α S k)
    (hNS : N = Fintype.card S)
    (hN : 0 < N) (i j : Fin k) {a' b' : ℕ}
    (hb' : b' ≤ (editedTuple W ρ N x j).length)
    (hcmp : SuffixComparison (editedTuple W ρ N x j) b' (editedTuple W ρ N x i) a')
    (hα : ∃ P' : Piece (editedTuple W ρ N x) ρ.length, P'.coordinate = j ∧
      P' ∈ piecesOf (editedTuple W ρ N x) ρ ∧ P'.start ≤ b' ∧ b' + 2 * ρ.length < P'.stop) :
    ∃ a ≤ (W i).length, ∃ b ≤ (W j).length, SuffixComparison (W j) b (W i) a ∧
      T.runPrefix W i a = T.runPrefix (editedTuple W ρ N x) i a' ∧ T.runPrefix W j b =
          T.runPrefix (editedTuple W ρ N x) j b' := by
  classical
  have hdA := Periodic.d_le_boundaryMargin N ρ.length
  have h2d := Periodic.two_d_le_boundaryMargin hN ρ.length
  have hag : ∀ n < (editedTuple W ρ N x j).length - b',
      (editedTuple W ρ N x j)[b' + n]? = (editedTuple W ρ N x i)[a' + n]? :=
          fun n hn => hcmp n (by omega)
  have hag' : ∀ n < (editedTuple W ρ N x j).length - b',
      (editedTuple W ρ N x i)[a' + n]? = (editedTuple W ρ N x j)[b' + n]? :=
          fun n hn => (hag n hn).symm
  have hKc : Periodic.stateTransientLength N ρ.length + Periodic.statePeriodModulus N ρ.length ≤
      Periodic.comparisonGap N ρ.length := by
    unfold Periodic.comparisonGap Periodic.boundaryMargin; omega
  obtain ⟨P', hP'l, hP'm, hP's, hP'e⟩ := hα
  have hd := P'.period_pos
  have hP'le := P'.stop_le_length; rw [hP'l] at hP'le
  have hP'L := P'.start_add_len
  obtain ⟨P, hP⟩ := hx.exists_imagePiece P'
  have hPl : P.coordinate = j := by rw [← hP'l, ← hP]; rfl
  have hPm : P ∈ piecesOf W ρ := (hx.imagePiece_mem_iff P).mp (hP ▸ hP'm)
  have hnP : retainedLength (N := N) (x := x) P = P'.len := by rw [← hx.imagePiece_len, hP]
  have hPs' : (hx.imagePiece P).start = P'.start := by rw [hP]
  have hLP := hx.len_eq_retainedLength_add P
  obtain ⟨Q', hQ'l, hQ's, hQ'e, hQ'cls, hQ'e'⟩ := copy_stretch hag P' hP'l hP's
    (ℓ := P'.stop - b') (by omega) (by omega) (by omega)
  have hQ'm : Q' ∈ piecesOf (editedTuple W ρ N x) ρ := by
    rw [mem_piecesOf]; exact hQ'cls.trans ((mem_piecesOf _).mp hP'm)
  obtain ⟨Q, hQ⟩ := hx.exists_imagePiece Q'
  have hQl : Q.coordinate = i := by rw [← hQ'l, ← hQ]; rfl
  have hQm : Q ∈ piecesOf W ρ := (hx.imagePiece_mem_iff Q).mp (hQ ▸ hQ'm)
  have hnQ : retainedLength (N := N) (x := x) Q = Q'.len := by rw [← hx.imagePiece_len, hQ]
  have hQs' : (hx.imagePiece Q).start = Q'.start := by rw [hQ]
  have hLQ := hx.len_eq_retainedLength_add Q
  have hQ'L := Q'.start_add_len
  have hQ'le := Q'.stop_le_length; rw [hQ'l] at hQ'le
  have hPsl := P.start_add_len
  have hQsl := Q.start_add_len
  have hPle := P.stop_le_length; rw [hPl] at hPle
  have hQle := Q.stop_le_length; rw [hQl] at hQle
  -- the lift at original offsets `oT`, `oS` with the states and phases of the new offsets
  have lift : ∀ oT oS, oT ≤ P.len → oS ≤ Q.len → SameStatePhase N ρ.length oT (b' - P'.start) →
      SameStatePhase N ρ.length oS (a' - Q'.start) → P.len - oT ≤ Q.len - oS →
      (P.stop = (W j).length ∨
        (P.len - oT = Q.len - oS ∧ SuffixComparison (W j) P.stop (W i) Q.stop)) →
      ∃ a ≤ (W i).length, ∃ b ≤ (W j).length, SuffixComparison (W j) b (W i) a ∧
        T.runPrefix W i a = T.runPrefix (editedTuple W ρ N x) i a' ∧
          T.runPrefix W j b = T.runPrefix (editedTuple W ρ N x) j b' := by
    intro oT oS hoT hoS hT hS hlen hfol
    obtain ⟨hc, hqb, hqa⟩ := hx.lift_in_pieces T hNS hPl hQl (pT := b' - P'.start)
      (pS := a' - Q'.start) (by omega) (by omega) (by omega) (by omega) hoT hoS hT hS hcmp hlen
      hfol
    exact ⟨_, by omega, _, by omega, hc, hqa, hqb⟩
  by_cases hterm : P'.stop = (editedTuple W ρ N x j).length
  · -- the target suffix lies wholly inside its last piece
    have hE : P.stop = (W j).length := by
      rw [← hPl]; exact (hx.imagePiece_stop_eq_length_iff P).mp (by rw [hP, hterm, hPl])
    have hG : FollowerEdge P Q := Or.inl (by
      unfold Piece.follower; rw [hPl, hE, List.drop_length]; exact List.nil_prefix)
    by_cases hA : Periodic.stateTransientLength N ρ.length ≤ b' - P'.start ∨ x P = 0
    · -- end-relative target offset
      refine lift (b' - P'.start + Periodic.statePeriodModulus N ρ.length * x P) _ (by omega)
        (by omega) ?_ (Or.inl rfl) (by omega) (Or.inl hE)
      rcases hA with h | h
      · exact .inr ⟨by omega, h, Nat.add_mul_mod_self_left _ _ _⟩
      · exact .inl (by rw [h]; simp)
    · push Not at hA
      rcases hx.followerEdge_cases hPm hQm hG with hxe | ⟨hf1, hf1'⟩ | ⟨hf2, hf2'⟩
      · exact lift _ _ (by omega) (by omega) (Or.inl rfl) (Or.inl rfl)
          (by rw [hxe] at hLP; omega) (Or.inl hE)
      · by_cases hpS : a' - Q'.start < Periodic.stateTransientLength N ρ.length
        · exact lift _ _ (by omega) (by omega) (Or.inl rfl) (Or.inl rfl) (by omega) (Or.inl hE)
        · have hM : 0 < Periodic.statePeriodModulus N ρ.length := by
            unfold Periodic.statePeriodModulus; positivity
          have hmlt := Nat.mod_lt (a' - Q'.start - Periodic.stateTransientLength N ρ.length) hM
          refine lift (b' - P'.start) (Periodic.stateTransientLength N ρ.length +
              (a' - Q'.start - Periodic.stateTransientLength N ρ.length) %
                Periodic.statePeriodModulus N ρ.length) (by omega) (by omega) (Or.inl rfl)
            (.inr ⟨by omega, by omega, ?_⟩) (by omega) (Or.inl hE)
          rw [Nat.add_mod_mod, show Periodic.stateTransientLength N ρ.length +
            (a' - Q'.start - Periodic.stateTransientLength N ρ.length) = a' - Q'.start by omega]
      · exfalso; omega
  · -- the first (partial) piece is complete: followers and the near/far choice of offsets
    have hQe : Q'.stop = a' + (P'.stop - b') := hQ'e' (by omega) (by omega) (by omega)
    have hfolN :=
        hx.canonicalCut_suffixComparison hN i j
            ((editedTuple W ρ N x j).length - (P'.stop - ρ.length))
      (P'.stop - ρ.length) (Q'.stop - ρ.length) rfl (by omega)
      (by have := hcmp.shift (P'.stop - ρ.length - b')
          rwa [show b' + (P'.stop - ρ.length - b') = P'.stop - ρ.length by omega,
            show a' + (P'.stop - ρ.length - b') = Q'.stop - ρ.length by omega] at this)
      (hP'l ▸ hx.nojun_end P' _) (hQ'l ▸ hx.nojun_end Q' _)
      (P.stop - ρ.length) (Q.stop - ρ.length) (hx.canonicalCut_end_sub_of_image_eq hP hP'l)
      (hx.canonicalCut_end_sub_of_image_eq hQ hQ'l)
    have hPlong := P.long; have hQlong := Q.long
    have hfol : SuffixComparison (W j) P.stop (W i) Q.stop := by
      have := hfolN.shift ρ.length
      rwa [Nat.sub_add_cancel (by omega), Nat.sub_add_cancel (by omega)] at this
    have hG : FollowerEdge P Q := Or.inl (by
      unfold Piece.follower; rw [hPl, hQl]; exact drop_prefix_iff_suffixComparison.mpr hfol)
    rcases hx.followerEdge_cases hPm hQm hG with hxe | ⟨hf1, hf1'⟩ | ⟨hf2, hf2'⟩
    · exact lift _ _ (by omega) (by omega) (Or.inl rfl) (Or.inl rfl)
        (by rw [hxe] at hLP; omega) (Or.inr ⟨by rw [hxe] at hLP; omega, hfol⟩)
    · -- far, target shorter: hold the target offset
      unfold Periodic.comparisonGap Periodic.boundaryMargin at hf1 hf1'
      exact lift (b' - P'.start) (b' - P'.start + (Q.len - P.len)) (by omega) (by omega)
        (Or.inl rfl) (.inr ⟨by omega, by omega, mod_eq_of_add_mul (u := x P) (v := x Q)
          (by omega)⟩) (by omega) (Or.inr ⟨by omega, hfol⟩)
    · -- far, host shorter: hold the host offset
      unfold Periodic.comparisonGap Periodic.boundaryMargin at hf2 hf2'
      exact lift (a' - Q'.start + (P.len - Q.len)) (a' - Q'.start) (by omega) (by omega)
        (.inr ⟨by omega, by omega, mod_eq_of_add_mul (u := x Q) (v := x P) (by omega)⟩)
        (Or.inl rfl) (by omega) (Or.inr ⟨by omega, hfol⟩)

private theorem suffixComparison_lift_of_no_piece {S : Type} [Fintype S] (T : Table α S k)
    (hNS : N = Fintype.card S)
    (hN : 0 < N) (i j : Fin k) {a' b' : ℕ} (ha' : a' ≤ (editedTuple W ρ N x i).length)
    (hb' : b' ≤ (editedTuple W ρ N x j).length)
    (hcmp : SuffixComparison (editedTuple W ρ N x j) b' (editedTuple W ρ N x i) a')
    (hα : ¬ (∃ P' : Piece (editedTuple W ρ N x) ρ.length, P'.coordinate = j ∧
      P' ∈ piecesOf (editedTuple W ρ N x) ρ ∧ P'.start ≤ b' ∧ b' + 2 * ρ.length < P'.stop)) :
    ∃ a ≤ (W i).length, ∃ b ≤ (W j).length, SuffixComparison (W j) b (W i) a ∧
      T.runPrefix W i a = T.runPrefix (editedTuple W ρ N x) i a' ∧ T.runPrefix W j b =
          T.runPrefix (editedTuple W ρ N x) j b' := by
  classical
  have hdA := Periodic.d_le_boundaryMargin N ρ.length
  have h2d := Periodic.two_d_le_boundaryMargin hN ρ.length
  have hag : ∀ n < (editedTuple W ρ N x j).length - b',
      (editedTuple W ρ N x j)[b' + n]? = (editedTuple W ρ N x i)[a' + n]? :=
          fun n hn => hcmp n (by omega)
  have hag' : ∀ n < (editedTuple W ρ N x j).length - b',
      (editedTuple W ρ N x i)[a' + n]? = (editedTuple W ρ N x j)[b' + n]? :=
          fun n hn => (hag n hn).symm
  have hKc : Periodic.stateTransientLength N ρ.length + Periodic.statePeriodModulus N ρ.length ≤
      Periodic.comparisonGap N ρ.length := by
    unfold Periodic.comparisonGap Periodic.boundaryMargin; omega
  push Not at hα
  have hNJt : hx.NoInteriorJunction j b' ((editedTuple W ρ N x j).length - b') := by
    intro R hRl hxR h1 h2
    exfalso
    have := hα (hx.imagePiece R) hRl (hx.imagePiece_piece_mem hxR) h1
    have := hx.imagePiece_room hxR
    omega
  by_cases hNJh : hx.NoInteriorJunction i a' ((editedTuple W ρ N x j).length - b')
  · -- the backward expansion from the canonical cuts
    obtain ⟨b, hbc⟩ := hx.exists_canonicalCut j hb'
    obtain ⟨a, hac⟩ := hx.exists_canonicalCut i ha'
    exact
        ⟨a, hac.1, b, hbc.1,
            hx.canonicalCut_suffixComparison hN i j _ b' a' rfl hb' hcmp hNJt hNJh b a hbc hac,
      (hx.runPrefix_canonicalCut T hNS hac).symm, (hx.runPrefix_canonicalCut T hNS hbc).symm⟩
  · -- a short window inside a shortened host piece
    unfold NoInteriorJunction at hNJh
    push Not at hNJh
    obtain ⟨R, hRl, hxR, h1, h2, h3⟩ := hNJh
    have hroom := hx.imagePiece_room hxR
    have hR'm := hx.imagePiece_piece_mem hxR
    have hd := R.period_pos
    have hR'L := (hx.imagePiece R).start_add_len
    have hRe : a' + ((editedTuple W ρ N x j).length - b') ≤ (hx.imagePiece R).stop := by
      by_contra hlt
      have hRlt : (hx.imagePiece R).stop < (editedTuple W ρ N x i).length := by
        have := hcmp.lt_length (n := (hx.imagePiece R).stop - a') (by omega); omega
      obtain ⟨P'', h1', h2', h3', h4', _⟩ := copy_stretch hag' (hx.imagePiece R) hRl h1
        (ℓ := (hx.imagePiece R).stop - a') (by omega) (by omega) (by omega)
      exact absurd (hα P'' h1' (by rw [mem_piecesOf]; exact h4'.trans ((mem_piecesOf _).mp hR'm))
        h2') (by omega)
    have hn' : (editedTuple W ρ N x j).length - b' ≤ 2 * ρ.length := by
      by_contra hlt
      obtain ⟨P'', h1', h2', h3', h4', _⟩ := copy_stretch hag' (hx.imagePiece R) hRl h1
        (ℓ := (editedTuple W ρ N x j).length - b') (by omega) (by omega) le_rfl
      exact absurd (hα P'' h1' (by rw [mem_piecesOf]; exact h4'.trans ((mem_piecesOf _).mp hR'm))
        h2') (by omega)
    obtain ⟨b, hbc⟩ := hx.exists_canonicalCut j hb'
    obtain ⟨_, hkT, htT⟩ := hx.text_canonicalCut hbc (by omega)
      (hx.noJunction_window hNJt le_rfl fun R₂ hR₂l hxR₂ _ _ => by
        have := hx.imagePiece_room hxR₂
        have := (hx.imagePiece R₂).stop_le_length
        rw [show (hx.imagePiece R₂).coordinate = j from hR₂l] at this
        omega)
    have hpS : a' - (hx.imagePiece R).start ≤ retainedLength (N := N) (x := x) R := by
      have := hx.imagePiece_len R; omega
    have hale : R.start + (a' - (hx.imagePiece R).start) ≤ (W i).length := by
      have h1' := retainedLength_le (N := N) (x := x) R
      have h2' := R.stop_le_length
      have h3' := R.start_add_len
      have h4' := hx.imagePiece_len R
      rw [hRl] at h2'
      omega
    refine ⟨R.start + (a' - (hx.imagePiece R).start), hale, b, hbc.1, ?_, ?_,
      (hx.runPrefix_canonicalCut T hNS hbc).symm⟩
    · intro n hn
      have hnm : n < (editedTuple W ρ N x j).length - b' := by
        by_contra hge
        have :=
            hx.retainedCount_lt_length (l := j) (c := b + ((editedTuple W ρ N x j).length - b'))
                (by omega)
        rw [hkT, ← length_editedTuple] at this; omega
      have e :=
          hx.getElem?_imagePiece R (o := a' - (hx.imagePiece R).start + n)
              (by have := hx.imagePiece_len R; omega)
      rw [hRl, ← Nat.add_assoc, ← Nat.add_assoc,
        show (hx.imagePiece R).start + (a' - (hx.imagePiece R).start) = a' by omega] at e
      rw [htT n hnm, hag n hnm, e]
    · have := hx.runPrefix_imagePiece T hNS R hpS
      rw [hRl,
          show (hx.imagePiece R).start + (a' - (hx.imagePiece R).start) = a' by omega] at this
      exact this.symm

/-- Every comparison of the edited tuple lifts to a comparison of the original tuple whose
start states are the same. -/
theorem suffixComparison_lift {S : Type} [Fintype S] (T : Table α S k) (hNS : N = Fintype.card S)
    (hN : 0 < N) (i j : Fin k) {a' b' : ℕ} (ha' : a' ≤ (editedTuple W ρ N x i).length)
    (hb' : b' ≤ (editedTuple W ρ N x j).length)
    (hcmp : SuffixComparison (editedTuple W ρ N x j) b' (editedTuple W ρ N x i) a') :
    ∃ a ≤ (W i).length, ∃ b ≤ (W j).length, SuffixComparison (W j) b (W i) a ∧
      T.runPrefix W i a = T.runPrefix (editedTuple W ρ N x) i a' ∧ T.runPrefix W j b =
          T.runPrefix (editedTuple W ρ N x) j b' := by
  classical
  by_cases hα : ∃ P' : Piece (editedTuple W ρ N x) ρ.length, P'.coordinate = j ∧
      P' ∈ piecesOf (editedTuple W ρ N x) ρ ∧ P'.start ≤ b' ∧ b' + 2 * ρ.length < P'.stop
  · exact hx.suffixComparison_lift_of_piece T hNS hN i j hb' hcmp hα
  · exact hx.suffixComparison_lift_of_no_piece T hNS hN i j ha' hb' hcmp hα

end AdmissibleDeletion

/-! ## Channel inclusion and domination -/

section Main

variable [DecidableEq α] {S : Type} [Fintype S] [DecidableEq S] {W : Fin k → List α}
  {ρ : List α} {x : Piece W ρ.length → ℕ}

/-- Every channel of the edited tuple, including those from a coordinate to itself and those
with empty target suffixes, is contained in the channel of the original tuple. -/
theorem editedTuple_channel_subset (T : Table α S k)
    (hx : AdmissibleDeletion W ρ (Fintype.card S) x) (i j : Fin k) :
    T.channel (editedTuple W ρ (Fintype.card S) x) i j ⊆ T.channel W i j := by
  intro pq hpq
  obtain ⟨a', ha', b', hb', hpre, rfl⟩ := mem_channel.mp hpq
  have hN : 0 < Fintype.card S := Fintype.card_pos_iff.mpr ⟨T.start i⟩
  obtain ⟨a, ha, b, hb, hcmp, hqa, hqb⟩ :=
    hx.suffixComparison_lift T rfl hN i j ha' hb' (drop_prefix_iff_suffixComparison.mp hpre)
  exact mem_channel.mpr ⟨a, ha, b, hb, drop_prefix_iff_suffixComparison.mpr hcmp, by rw [hqa, hqb]⟩

/-- The edited tuple dominates the original one: equal endpoints, fewer visited states and
smaller channels. -/
theorem editedTuple_dominates (T : Table α S k)
    (hx : AdmissibleDeletion W ρ (Fintype.card S) x) :
    Dominates T (editedTuple W ρ (Fintype.card S) x) W :=
  ⟨fun l => hx.editedTuple_endState T rfl l, fun l => hx.editedTuple_visitedStates T rfl l,
    fun i j => editedTuple_channel_subset T hx i j⟩

end Main

/-! ## First rejection and pieces of other classes -/

section Holes

variable [DecidableEq α] {S : Type} [Fintype S] [DecidableEq S] {W : Fin k → List α}
  {ρ : List α} {x : Piece W ρ.length → ℕ}

/-- The first rejected cut of the edited tuple is the image of the first rejected cut of the
hole. -/
theorem editedTuple_firstRejection (M : StructuralReader α S k) (hW : M.IsHole W)
    (hx : AdmissibleDeletion W ρ (Fintype.card S) x) (l : Fin k) :
    M.firstRejection (editedTuple W ρ (Fintype.card S) x) l =
      keepCut W ρ (Fintype.card S) x l (M.firstRejection W l) :=
  firstRejection_deletePositions M (hW.1 l) rfl
    (fun h => absurd (hx.deletedPositions_lt_length h) (lt_irrefl _))
    (hx.runPrefix_editedTuple_greatestPreimage M.toTable rfl l)

section Site

variable {N dR : ℕ} (hx : AdmissibleDeletion W ρ N x)
include hx

/-- No position of a piece `R` of another class, with period at most `|ρ|` and length at least
`|ρ|` plus its period, is deleted, and neither are the letters just before and after it. -/
theorem deletionSite_retained (hN : 0 < N) (R : Piece W dR)
    (hcls : ¬ IsConjugate R.root ρ) (hd : dR ≤ ρ.length)
    (hlen : ρ.length + dR ≤ R.len) {p : ℕ}
    (hp : R.start ≤ p + 1) (hpe : p ≤ R.stop) : p ∉ deletedPositions W ρ N x R.coordinate := by
  intro hdel
  obtain ⟨P, hP, hl, hstart, hend⟩ := mem_deletedPositions.mp hdel
  have hmove : x P ≠ 0 := by intro hz; rw [hz] at hend; omega
  have hb := hx.site_bound hmove
  have hA := Periodic.two_d_le_boundaryMargin hN ρ.length
  have hdp := P.period_pos
  have hdiff : ¬ IsConjugate P.root R.root := by
    intro hc
    exact hcls (hc.symm.trans ((mem_piecesOf W).mp hP))
  have hf := fw_overlap P R hdiff hd hl
  unfold Piece.len at hlen
  omega

/-- A piece `R` of another class, with period at most `|ρ|` and length at least `|ρ|` plus its
period, survives the deletion: none of its positions and none of the adjacent letters that
end it is deleted, and the edited tuple has a piece with the same coordinate, length and
root. -/
theorem exists_preserved_piece_of_nonconjugate_root (hN : 0 < N) (R : Piece W dR)
    (hcls : ¬ IsConjugate R.root ρ) (hd : dR ≤ ρ.length)
    (hlen : ρ.length + dR ≤ R.len) :
    (∀ p, R.start ≤ p → p < R.stop → p ∉ deletedPositions W ρ N x R.coordinate) ∧
    (R.start ≠ 0 → R.start - 1 ∉ deletedPositions W ρ N x R.coordinate) ∧
    (R.stop < (W R.coordinate).length → R.stop ∉ deletedPositions W ρ N x R.coordinate) ∧
    ∃ R' : Piece (editedTuple W ρ N x) dR,
      R'.coordinate = R.coordinate ∧ R'.len = R.len ∧ R'.root = R.root := by
  have hret : ∀ {p}, R.start ≤ p + 1 → p ≤ R.stop → p ∉ deletedPositions W ρ N x R.coordinate :=
    by intro p; exact deletionSite_retained hx hN R hcls hd hlen (p := p)
  have hin : ∀ p, R.start ≤ p → p < R.stop → p ∉ deletedPositions W ρ N x R.coordinate :=
    fun p hp he => hret (by omega) (by omega)
  have hleft : R.start ≠ 0 → R.start - 1 ∉ deletedPositions W ρ N x R.coordinate :=
    fun hs => hret (by omega) (by have := R.start_lt_stop; omega)
  have hright : R.stop ∉ deletedPositions W ρ N x R.coordinate :=
    hret (by have := R.start_lt_stop; omega) le_rfl
  refine ⟨hin, hleft, fun _ => hright, ?_⟩
  let s := keepCut W ρ N x R.coordinate R.start
  let e := keepCut W ρ N x R.coordinate R.stop
  have hlenR := R.start_add_len
  have hlong := R.len_ge
  have hdpos := R.period_pos
  have hkeep : ∀ o ≤ R.len, keepCut W ρ N x R.coordinate (R.start + o) = s + o := by
    intro o ho
    exact retainedCount_add_of_not_mem (fun i hi => hin _ (by omega) (by omega))
  have he : e = s + R.len := by
    have := hkeep R.len le_rfl
    rwa [hlenR] at this
  have hget : ∀ o < R.len, (editedTuple W ρ N x R.coordinate)[s + o]? =
      (W R.coordinate)[R.start + o]? := by
    intro o ho
    rw [← hkeep o ho.le, editedTuple]
    exact getElem?_deletePositions _ (hin _ (by omega) (by omega))
        (by have := R.stop_le_length; omega)
  have hroot : ((editedTuple W ρ N x R.coordinate).drop s).take dR = R.root := by
    apply List.ext_getElem?
    intro i
    by_cases hi : i < dR
    · rw [List.getElem?_take_of_lt hi, List.getElem?_drop, hget i (by omega),
        Piece.root, List.getElem?_take_of_lt hi, List.getElem?_drop]
    · rw [List.getElem?_eq_none (by simp; omega),
        List.getElem?_eq_none (by rw [R.root_length]; omega)]
  have hmaxL : s = 0 ∨ (editedTuple W ρ N x R.coordinate)[s - 1]? ≠
      (editedTuple W ρ N x R.coordinate)[s - 1 + dR]? := by
    rcases R.left_maximal with hs | hs
    · left; dsimp [s, keepCut]; rw [hs, retainedCount_zero]
    · by_cases hs0 : R.start = 0
      · left; dsimp [s, keepCut]; rw [hs0, retainedCount_zero]
      · right
        have hk := retainedCount_succ_of_not_mem (hleft hs0)
        rw [show R.start - 1 + 1 = R.start by omega] at hk
        change s = retainedCount (deletedPositions W ρ N x R.coordinate) (R.start - 1) + 1 at hk
        have hprev : (editedTuple W ρ N x R.coordinate)[s - 1]? =
            (W R.coordinate)[R.start - 1]? := by
          rw [hk, Nat.add_sub_cancel, editedTuple]
          exact getElem?_deletePositions _ (hleft hs0) (by have := R.stop_le_length; omega)
        rw [hprev, show s - 1 + dR = s + (dR - 1) by omega,
          hget (dR - 1) (by omega), show R.start + (dR - 1) = R.start - 1 + dR by omega]
        exact hs
  have hmaxR : e = (editedTuple W ρ N x R.coordinate).length ∨
      (editedTuple W ρ N x R.coordinate)[e]? ≠ (editedTuple W ρ N x R.coordinate)[e - dR]? := by
    rcases R.right_maximal with hE | hE
    · left; dsimp [e, keepCut]; rw [hE, editedTuple, length_deletePositions]
    · by_cases hend : R.stop = (W R.coordinate).length
      · left; dsimp [e, keepCut]; rw [hend, editedTuple, length_deletePositions]
      · right
        have hlast : (editedTuple W ρ N x R.coordinate)[e]? = (W R.coordinate)[R.stop]? :=
          getElem?_deletePositions _ hright (lt_of_le_of_ne R.stop_le_length hend)
        rw [hlast, he, show s + R.len - dR = s + (R.len - dR) by omega,
          hget (R.len - dR) (by omega), show R.start + (R.len - dR) = R.stop - dR by omega]
        exact hE
  let R' : Piece (editedTuple W ρ N x) dR :=
    { coordinate := R.coordinate
      start := s
      stop := e
      long := by omega
      stop_le_length := by rw [AdmissibleDeletion.length_editedTuple];
                           exact retainedCount_mono R.stop_le_length
      periodic := by
        intro p hp hpe
        have h1 := hget (p - s) (by omega)
        have h2 := hget (p - s + dR) (by omega)
        rw [show s + (p - s) = p by omega] at h1
        rw [show s + (p - s + dR) = p + dR by omega] at h2
        rw [h1, h2]
        simpa only [Nat.add_assoc] using R.periodic (R.start + (p - s)) (by omega) (by omega)
      primitive := hroot ▸ R.primitive
      left_maximal := hmaxL
      right_maximal := hmaxR }
  exact ⟨R', rfl, by change e - s = R.len; omega, hroot⟩

end Site

end Holes

end DeciSigma1.Holes.Periodic
