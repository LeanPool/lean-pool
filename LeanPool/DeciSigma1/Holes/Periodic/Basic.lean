/-
Copyright (c) 2026 Yaoyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaoyu Zhao
-/

module

public import LeanPool.DeciSigma1.Readers.Basic
public import LeanPool.DeciSigma1.Words.Periods
import Mathlib.Order.SuccPred.Nat

/-! Ported to Lean Pool’s module system and pinned Lean and Mathlib.

 # Periodic pieces

A *piece* of period `d` in a tuple `W` is a maximal interval `[start, stop)` of one word that
has period `d`, length at least `2d` and a primitive factor of length `d` at its start, its
*root*; these are the runs of combinatorics on words with exponent at least `2`. Two pieces of
the same period that overlap in at least `d` letters coincide (`piece_eq_of_overlap`), so the
pieces of a tuple form a finite set (`allPieces`). The pieces whose roots are conjugate to a
primitive word `ρ` form its class `piecesOf W ρ`, and by Fine–Wilf pieces of different classes
overlap in fewer letters than the sum of their periods (`fw_overlap`).

The shortening of periodic factors deletes blocks from the pieces of one class. The text after
a piece is its *follower*. Two pieces whose followers are comparable in the prefix order are
joined by a `FollowerEdge`: their suffixes can be compared by a channel, so the deletion must
shorten them consistently. Paths in this graph control the retained lengths of pieces.

## Main declarations

- `Piece`, `Piece.root`, `Piece.follower`: pieces, their roots and followers.
- `IsPeriodicPiece`, `allPieces`, `piecesOf`: the piece conditions and the finite sets of
  pieces.
- `piece_eq_of_overlap`, `piece_ends_sep`: overlapping pieces of one period coincide.
- `exists_piece_of_stretch`, `long_factor_in_piece`: long periodic factors lie in pieces.
- `fw_overlap`: pieces of different classes overlap in fewer letters than the sum of their
  periods.
- `FollowerEdge`: the follower graph of pieces.
-/

@[expose] public section


namespace DeciSigma1.Holes.Periodic

open DeciSigma1.Readers DeciSigma1.Words

variable {α : Type} {k : ℕ}

/-- A piece of period `d` in the tuple `W`: a maximal interval `[start, stop)` of the word of
`coordinate` with period `d`, length at least `2d` and a primitive root of length `d`. -/
structure Piece (W : Fin k → List α) (d : ℕ) where
  /-- Coordinate whose word contains the periodic interval. -/
  coordinate : Fin k
  /-- First position of the periodic interval. -/
  start : ℕ
  /-- Position immediately after the periodic interval. -/
  stop : ℕ
  long : start + 2 * d ≤ stop
  stop_le_length : stop ≤ (W coordinate).length
  periodic : ∀ p, start ≤ p → p + d < stop → (W coordinate)[p]? = (W coordinate)[p + d]?
  primitive : IsPrimitive (((W coordinate).drop start).take d)
  left_maximal : start = 0 ∨ (W coordinate)[start - 1]? ≠ (W coordinate)[start - 1 + d]?
  right_maximal : stop = (W coordinate).length ∨ (W coordinate)[stop]? ≠ (W coordinate)[stop - d]?

namespace Piece

variable {W : Fin k → List α} {d : ℕ}

theorem ext_coordinates {P Q : Piece W d} (hl : P.coordinate = Q.coordinate)
    (hs : P.start = Q.start) (he : P.stop = Q.stop) : P = Q := by
  cases P; cases Q; simp only at hl hs he; subst hl hs he; rfl

theorem ext_iff_coordinates {P Q : Piece W d} :
    P = Q ↔ P.coordinate = Q.coordinate ∧ P.start = Q.start ∧ P.stop = Q.stop :=
  ⟨fun h => h ▸ ⟨rfl, rfl, rfl⟩, fun ⟨a, b, c⟩ => ext_coordinates a b c⟩

instance : DecidableEq (Piece W d) := fun _ _ => decidable_of_iff _ ext_iff_coordinates.symm

/-- The length of a piece. -/
def len (P : Piece W d) : ℕ := P.stop - P.start

/-- The root of a piece: its first `d` letters. -/
def root (P : Piece W d) : List α := ((W P.coordinate).drop P.start).take d

/-- The text after the piece, to the end of its word. -/
def follower (P : Piece W d) : List α := (W P.coordinate).drop P.stop

theorem periodicOn (P : Piece W d) : PeriodicOn (W P.coordinate) d P.start P.stop := P.periodic

theorem period_pos (P : Piece W d) : 0 < d := by
  rcases Nat.eq_zero_or_pos d with h | h
  · exact absurd (by simp [h]) P.primitive.ne_nil
  · exact h

theorem len_ge (P : Piece W d) : 2 * d ≤ P.len := by unfold len; have := P.long; omega

theorem start_lt_stop (P : Piece W d) :
    P.start < P.stop := by have := P.long; have := P.period_pos; omega

theorem root_length (P : Piece W d) : P.root.length = d := by
  unfold root; simp; have := P.long; have := P.stop_le_length; omega

/-- Letters of a piece at offsets congruent modulo `d` agree. -/
theorem getElem?_eq_of_mod (P : Piece W d) {o₁ o₂ : ℕ} (h₁ : o₁ < P.len) (h₂ : o₂ < P.len)
    (h : o₁ % d = o₂ % d) : (W P.coordinate)[P.start + o₁]? = (W P.coordinate)[P.start + o₂]? := by
  unfold len at h₁ h₂
  apply P.periodicOn.eq_of_mod (by omega) (by omega) (by omega) (by omega)
  rw [Nat.add_mod, h, ← Nat.add_mod]

theorem getElem?_root (P : Piece W d) {o : ℕ} (h : o < P.len) :
    (W P.coordinate)[P.start + o]? = P.root[o % d]? := by
  have hd := P.period_pos
  rw [P.getElem?_eq_of_mod h (by have := P.len_ge; have := Nat.mod_lt o hd; omega)
    (Nat.mod_mod o d).symm]
  unfold root
  rw [List.getElem?_take_of_lt (Nat.mod_lt _ hd), List.getElem?_drop]

/-- Every `d`-window of a piece is in the class of its root. -/
theorem window_isConjugate (P : Piece W d) {z : ℕ} (hz : P.start ≤ z) (hze : z + d ≤ P.stop) :
    IsConjugate P.root (((W P.coordinate).drop z).take d) :=
  ⟨_, P.periodicOn.window_rotate P.stop_le_length hz hze⟩

/-- In a piece of primitive period `d`, a second period `δ` on a stretch of length `≥ d + δ`
from inside the piece to its end is a multiple of `d`. -/
theorem dvd_of_periodicOn
    (P : Piece W d) {x δ : ℕ}
    (hx : P.start ≤ x) (hδ : PeriodicOn (W P.coordinate) δ x P.stop)
        (hlen : x + d + δ ≤ P.stop) : d ∣ δ := by
  have hd := P.period_pos
  have hg := period_extend_gcd (by omega) P.stop_le_length (P.periodicOn.mono hx le_rfl) hδ
    (by have := Nat.gcd_le_left δ hd; omega)
  have hgpos : 0 < d.gcd δ := Nat.gcd_pos_of_pos_left _ hd
  have hgle : d.gcd δ ≤ d := Nat.gcd_le_left _ hd
  have hwin := P.window_isConjugate hx (by omega)
  have hprim := hwin.isPrimitive P.primitive
  have hwlen : (((W P.coordinate).drop x).take d).length = d := by
    have := P.stop_le_length; simp; omega
  have hgd : d.gcd δ = d := by
    by_contra hne
    rw [isPrimitive_iff_period] at hprim
    apply hprim.2 (d.gcd δ) hgpos (by rw [hwlen]; omega) (by rw [hwlen]; exact Nat.gcd_dvd_left _ _)
    have := (periodicOn_iff_hasPeriod (w := W P.coordinate) (s := x) (e := x + d) (by omega)
      (by have := P.stop_le_length; omega)).mp (hg.mono le_rfl (by omega))
    rwa [show x + d - x = d by omega] at this
  rw [← hgd]
  exact Nat.gcd_dvd_right _ _

end Piece

/-! ## Finitely many pieces -/

section Fin

variable [DecidableEq α] (W : Fin k → List α) (d : ℕ)

/-- The conditions for the interval `[s, e)` of word `l` to be a piece of period `d`, in a form
that is decidable. -/
def IsPeriodicPiece (l : Fin k) (s e : ℕ) : Prop :=
  s + 2 * d ≤ e ∧ e ≤ (W l).length ∧ (∀ p < e, s ≤ p → p + d < e → (W l)[p]? = (W l)[p + d]?) ∧
    IsPrimitive (((W l).drop s).take d) ∧ (s = 0 ∨ (W l)[s - 1]? ≠ (W l)[s - 1 + d]?) ∧
    (e = (W l).length ∨ (W l)[e]? ≠ (W l)[e - d]?)

instance (l : Fin k) (s e : ℕ) : Decidable (IsPeriodicPiece W d l s e) := by
  unfold IsPeriodicPiece; infer_instance

/-- The piece given by a triple that satisfies the piece conditions. -/
def Piece.ofIsPeriodicPiece {U : Fin k → List α} {d : ℕ}
    {l : Fin k} {s e : ℕ}
    (h : IsPeriodicPiece U d l s e) : Piece U d :=
  ⟨l, s, e, h.1, h.2.1, fun p hp hpe => h.2.2.1 p (by omega) hp hpe, h.2.2.2.1, h.2.2.2.2.1,
    h.2.2.2.2.2⟩

omit [DecidableEq α] in
/-- A piece satisfies the piece conditions. -/
theorem Piece.isPeriodicPiece {U : Fin k → List α} {d : ℕ}
    (P : Piece U d) :
    IsPeriodicPiece U d P.coordinate P.start P.stop :=
  ⟨P.long, P.stop_le_length, fun p _ hp hpe => P.periodic p hp hpe, P.primitive, P.left_maximal,
      P.right_maximal⟩

/-- The piece with a given triple, if the triple satisfies the piece conditions. -/
def mkPiece? (t : Fin k × ℕ × ℕ) : Option (Piece W d) :=
  if h : IsPeriodicPiece W d t.1 t.2.1 t.2.2 then some (Piece.ofIsPeriodicPiece h) else none

theorem mkPiece?_spec {t : Fin k × ℕ × ℕ} {P : Piece W d} (h : P ∈ mkPiece? W d t) :
    t = (P.coordinate, P.start, P.stop) := by
  unfold mkPiece? at h
  split_ifs at h with h1
  · simp only [Option.mem_def, Option.some.injEq] at h; subst h; rfl
  · simp at h

theorem mkPiece?_inj (t t' : Fin k × ℕ × ℕ) (P : Piece W d) (h : P ∈ mkPiece? W d t)
    (h' : P ∈ mkPiece? W d t') : t = t' :=
  (mkPiece?_spec W d h).trans (mkPiece?_spec W d h').symm

/-- All pieces of period `d` in `W`. -/
def allPieces : Finset (Piece W d) :=
  (Finset.univ ×ˢ (Finset.range (totalLength W + 1) ×ˢ Finset.range (totalLength W + 1))).filterMap
    (mkPiece? W d) (mkPiece?_inj W d)

theorem mem_allPieces (P : Piece W d) : P ∈ allPieces W d := by
  unfold allPieces
  rw [Finset.mem_filterMap]
  have hle := (P.stop_le_length).trans (length_le_totalLength W P.coordinate)
  refine ⟨(P.coordinate, P.start, P.stop), by simp; have := P.long; omega, ?_⟩
  unfold mkPiece?
  rw [dite_eq_left P.isPeriodicPiece]
  rfl

instance : Fintype (Piece W d) := ⟨allPieces W d, mem_allPieces W d⟩

/-- The pieces whose root is in the rotation class of `ρ`. -/
def piecesOf (ρ : List α) : Finset (Piece W ρ.length) :=
  Finset.univ.filter (fun P => IsConjugate P.root ρ)

theorem mem_piecesOf {ρ : List α} {P : Piece W ρ.length} :
    P ∈ piecesOf W ρ ↔ IsConjugate P.root ρ := by
  simp [piecesOf]

end Fin

/-- Two pieces are joined in the follower graph if their followers are comparable in the prefix
order. -/
def FollowerEdge {W : Fin k → List α} {d : ℕ} (P Q : Piece W d) : Prop :=
  P.follower <+: Q.follower ∨ Q.follower <+: P.follower

instance [DecidableEq α] {W : Fin k → List α} {d : ℕ} (P Q : Piece W d) :
    Decidable (FollowerEdge P Q) := by
  unfold FollowerEdge; infer_instance

theorem FollowerEdge.symm {W : Fin k → List α} {d : ℕ} {P Q : Piece W d} (h : FollowerEdge P Q) :
    FollowerEdge Q P :=
  Or.symm h

/-! ## Overlap and separation -/

section Overlap

variable {W : Fin k → List α} {d : ℕ}

/-- Two pieces of the same period in the same word that overlap in at least `d` letters are
equal. -/
theorem piece_eq_of_overlap {P Q : Piece W d} (hl : P.coordinate = Q.coordinate)
    (h₁ : P.start + d ≤ Q.stop)
    (h₂ : Q.start + d ≤ P.stop) : P = Q := by
  have hQper : PeriodicOn (W P.coordinate) d Q.start Q.stop := hl ▸ Q.periodic
  have hQle : Q.stop ≤ (W P.coordinate).length := hl ▸ Q.stop_le_length
  have hQL : Q.start = 0 ∨ (W P.coordinate)[Q.start - 1]? ≠ (W P.coordinate)[Q.start - 1 + d]? :=
      hl ▸ Q.left_maximal
  have hQR : Q.stop = (W P.coordinate).length ∨ (W P.coordinate)[Q.stop]? ≠
      (W P.coordinate)[Q.stop - d]? := hl ▸ Q.right_maximal
  have hP := P.long; have hQ := Q.long
  -- the union of the two stretches is periodic
  have hU : PeriodicOn (W P.coordinate) d (min P.start Q.start) (max P.stop Q.stop) := by
    rcases le_total P.start Q.start with h | h
    · rw [min_eq_left h]; exact P.periodicOn.union hQper h₂
    · rw [min_eq_right h, max_comm]; exact hQper.union P.periodicOn h₁
  have he : P.stop = Q.stop := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · rcases P.right_maximal with h | h
      · omega
      · apply h
        have := hU (P.stop - d) (by omega) (by omega)
        rw [show P.stop - d + d = P.stop by omega] at this
        exact this.symm
    · rcases hQR with h | h
      · have := P.stop_le_length; omega
      · apply h
        have := hU (Q.stop - d) (by omega) (by omega)
        rw [show Q.stop - d + d = Q.stop by omega] at this
        exact this.symm
  have hs : P.start = Q.start := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · rcases hQL with h | h
      · omega
      · exact h (hU (Q.start - 1) (by omega) (by omega))
    · rcases P.left_maximal with h | h
      · omega
      · exact h (hU (P.start - 1) (by omega) (by omega))
  exact Piece.ext_coordinates hl hs he

/-- Distinct pieces of one word: the earlier one ends less than `d` letters after the later
one starts, so starts and ends are ordered alike. -/
theorem Piece.sep {P Q : Piece W d} (hne : P ≠ Q) (hl : P.coordinate = Q.coordinate)
    (hs : P.start ≤ Q.start) :
    P.start < Q.start ∧ P.stop < Q.start + d ∧ P.stop + d < Q.stop := by
  have hP := P.long; have hQ := Q.long; have hd := P.period_pos
  have h1 : ¬ (P.start + d ≤ Q.stop ∧ Q.start + d ≤ P.stop) :=
      fun h => hne (piece_eq_of_overlap hl h.1 h.2)
  have h2 : P.stop < Q.start + d := by
    by_contra h; exact h1 ⟨by omega, by omega⟩
  exact ⟨by omega, h2, by omega⟩

/-- The ends of distinct pieces of period `d` in one word are more than `d` apart. -/
theorem piece_ends_sep {P Q : Piece W d} (hne : P ≠ Q) (hl : P.coordinate = Q.coordinate) :
    d < (P.stop : ℤ) - Q.stop ∨ d < (Q.stop : ℤ) - P.stop := by
  rcases le_total P.start Q.start with h | h
  · have := Piece.sep hne hl h; right; omega
  · have := Piece.sep (Ne.symm hne) hl.symm h; left; omega

/-- A position of a piece outside its first and last `d` letters lies in no other piece of
the same word. -/
theorem Piece.not_mem_other {P Q : Piece W d} (hne : P ≠ Q) (hl : P.coordinate = Q.coordinate)
    {p : ℕ}
    (hp1 : P.start + d ≤ p) (hp2 : p + d < P.stop) : ¬ (Q.start ≤ p ∧ p < Q.stop) := by
  rintro ⟨hq1, hq2⟩
  rcases le_total P.start Q.start with h | h
  · have := Piece.sep hne hl h; omega
  · have := Piece.sep (Ne.symm hne) hl.symm h; omega

end Overlap

/-! ## Pieces from periodic stretches -/

/-- A periodic stretch of length `≥ 2d` with a primitive window lies in a piece; a left
(right) break at the stretch fixes the piece start (end). -/
theorem exists_piece_of_stretch (W : Fin k → List α) (l : Fin k) {d x y : ℕ}
    (hxy : x + 2 * d ≤ y) (hy : y ≤ (W l).length) (hper : PeriodicOn (W l) d x y)
    (hprim : IsPrimitive (((W l).drop x).take d)) :
    ∃ P : Piece W d, P.coordinate = l ∧ P.start ≤ x ∧ y ≤ P.stop ∧
      IsConjugate P.root (((W l).drop x).take d) ∧
      ((x = 0 ∨ (W l)[x - 1]? ≠ (W l)[x - 1 + d]?) → P.start = x) ∧
      ((y = (W l).length ∨ (W l)[y]? ≠ (W l)[y - d]?) → P.stop = y) := by
  classical
  have hd : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · exact absurd (by simp [h]) hprim.ne_nil
    · exact h
  have hexS : ∃ s, s ≤ x ∧ PeriodicOn (W l) d s y := ⟨x, le_rfl, hper⟩
  set s := Nat.find hexS with hs_def
  obtain ⟨hsx, hsper⟩ : s ≤ x ∧ PeriodicOn (W l) d s y := Nat.find_spec hexS
  set e := Nat.findGreatest (fun e => PeriodicOn (W l) d x e) (W l).length with he_def
  have hye : y ≤ e := Nat.le_findGreatest hy hper
  have heper : PeriodicOn (W l) d x e := Nat.findGreatest_spec hy hper
  have hele : e ≤ (W l).length := Nat.findGreatest_le _
  have hper' : PeriodicOn (W l) d s e := by
    have := hsper.union heper (by omega); rwa [max_eq_right hye] at this
  have hwin : (((W l).drop x).take d) = (((W l).drop s).take d).rotate ((x - s) % d) :=
    hper'.window_rotate hele hsx (by omega)
  have hcls : IsConjugate (((W l).drop s).take d) (((W l).drop x).take d) := ⟨_, hwin⟩
  have hmaxL : s = 0 ∨ (W l)[s - 1]? ≠ (W l)[s - 1 + d]? := by
    by_contra hcon
    push Not at hcon
    have h1 : PeriodicOn (W l) d (s - 1) y := by
      intro p hp hpy
      by_cases hps : p = s - 1
      · subst hps; exact hcon.2
      · exact hsper p (by omega) hpy
    have := Nat.find_min' hexS ⟨by omega, h1⟩
    omega
  have hmaxR : e = (W l).length ∨ (W l)[e]? ≠ (W l)[e - d]? := by
    by_contra hcon
    push Not at hcon
    have h1 : PeriodicOn (W l) d x (e + 1) := by
      intro p hp hpe
      by_cases hpe' : p + d < e
      · exact heper p hp hpe'
      · have : p = e - d := by omega
        subst this
        rw [show e - d + d = e by omega]; exact hcon.2.symm
    exact Nat.findGreatest_is_greatest (Nat.lt_succ_self e)
      (by have := hcon.1; omega) h1
  refine ⟨⟨l, s, e, by omega, hele, hper', hcls.symm.isPrimitive hprim, hmaxL, hmaxR⟩,
    rfl, hsx, hye, hcls, ?_, ?_⟩
  · intro hbrk
    change s = x
    by_contra hne
    rcases hbrk with h | h
    · omega
    · exact h (hsper (x - 1) (by omega) (by omega))
  · intro hbrk
    change e = y
    by_contra hne
    rcases hbrk with h | h
    · omega
    · apply h
      have := heper (y - d) (by omega) (by omega)
      rw [show y - d + d = y by omega] at this
      exact this.symm

/-! ## Long periodic factors and pieces of different classes -/

/-- An interval of length at least `2p` with period `p` lies in a piece whose period is the
least period `d` of the interval, and `d ∣ p`. -/
theorem long_factor_in_piece [DecidableEq α] (W : Fin k → List α) (l : Fin k) {p x y : ℕ}
    (hp : 0 < p) (hy : y ≤ (W l).length) (hlen : x + 2 * p ≤ y) (hper : PeriodicOn (W l) p x y) :
    ∃ P : Piece W (leastPeriod (((W l).drop x).take (y - x))), P.coordinate = l ∧ P.start ≤ x ∧ y ≤
        P.stop ∧
      leastPeriod (((W l).drop x).take (y - x)) ∣ p := by
  set f := ((W l).drop x).take (y - x) with hf
  have hflen : f.length = y - x := by simp [hf]; omega
  have hfp : f.HasPeriod p := (periodicOn_iff_hasPeriod (by omega) hy).mp hper
  have hdvd : leastPeriod f ∣ p := leastPeriod_dvd hfp (by omega)
  have hdle : leastPeriod f ≤ p := Nat.le_of_dvd hp hdvd
  have hdper : PeriodicOn (W l) (leastPeriod f) x y :=
    (periodicOn_iff_hasPeriod (by omega) hy).mpr (hasPeriod_leastPeriod f)
  have hprim : IsPrimitive (((W l).drop x).take (leastPeriod f)) := by
    have h := primitive_take_leastPeriod (w := f) (by omega)
    have e : f.take (leastPeriod f) = ((W l).drop x).take (leastPeriod f) := by
      change (((W l).drop x).take (y - x)).take (leastPeriod f) = _
      rw [List.take_take, min_eq_left (by omega)]
    rwa [e] at h
  obtain ⟨P, hPl, hPs, hPe, _⟩ := exists_piece_of_stretch W l (by omega) hy hdper hprim
  exact ⟨P, hPl, hPs, hPe, hdvd⟩

/-- Pieces of different classes with periods `dR ≤ dP` overlap in fewer than `dP + dR` letters
(Fine–Wilf). -/
theorem fw_overlap {W : Fin k → List α} {dP dR : ℕ} (P : Piece W dP) (R : Piece W dR)
    (hcls : ¬ IsConjugate P.root R.root) (hd : dR ≤ dP) (hl : P.coordinate = R.coordinate) :
    min P.stop R.stop - max P.start R.start < dP + dR := by
  by_contra hge
  push Not at hge
  have hP := P.period_pos; have hR := R.period_pos
  set s := max P.start R.start
  set e := min P.stop R.stop
  have hRper : PeriodicOn (W P.coordinate) dR R.start R.stop := hl ▸ R.periodic
  have hRle : R.stop ≤ (W P.coordinate).length := hl ▸ R.stop_le_length
  have h1 : PeriodicOn (W P.coordinate) dP s e :=
      P.periodicOn.mono (le_max_left _ _) (min_le_left _ _)
  have h2 : PeriodicOn (W P.coordinate) dR s e := hRper.mono (le_max_right _ _) (min_le_right _ _)
  have hse : s ≤ e := by omega
  have he : e ≤ (W P.coordinate).length := (min_le_left _ _).trans P.stop_le_length
  have hg := period_extend_gcd hse he h1 h2 (by omega)
  have hgpos : 0 < dP.gcd dR := Nat.gcd_pos_of_pos_left _ hP
  -- the `dP`-window at `s` is a rotation of `P.root`, hence primitive
  have hwin : IsConjugate P.root (((W P.coordinate).drop s).take dP) :=
    P.window_isConjugate (le_max_left _ _) (by omega)
  have hwprim := hwin.isPrimitive P.primitive
  have hwlen : (((W P.coordinate).drop s).take dP).length = dP := by simp; omega
  have hgdP : dP.gcd dR = dP := by
    by_contra hne
    have hlt : dP.gcd dR < dP := lt_of_le_of_ne (Nat.gcd_le_left _ hP) hne
    rw [isPrimitive_iff_period] at hwprim
    apply hwprim.2 (dP.gcd dR) hgpos (by rw [hwlen]; exact hlt)
        (by rw [hwlen]; exact Nat.gcd_dvd_left _ _)
    have :=
        (periodicOn_iff_hasPeriod (w := W P.coordinate) (s := s) (e := s + dP) (by omega)
            (by omega)).mp
      (hg.mono le_rfl (by omega))
    rwa [show s + dP - s = dP by omega] at this
  have hdR : dR = dP := by
    have : dP ∣ dR := hgdP ▸ Nat.gcd_dvd_right dP dR
    exact le_antisymm hd (Nat.le_of_dvd hR this)
  subst hdR
  have hwinR : IsConjugate R.root (((W R.coordinate).drop s).take dR) :=
    R.window_isConjugate (le_max_right _ _) (by omega)
  rw [← hl] at hwinR
  exact hcls (hwin.trans hwinR.symm)

end DeciSigma1.Holes.Periodic
