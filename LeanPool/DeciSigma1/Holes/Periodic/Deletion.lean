/-
Copyright (c) 2026 Yaoyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaoyu Zhao
-/

module

public import LeanPool.DeciSigma1.Holes.Periodic.Basic
public import LeanPool.DeciSigma1.Words.Deletion

/-! Ported to Lean Pool’s module system and pinned Lean and Mathlib.

 # Admissible deletions in periodic pieces

Inside a piece of period `d`, the run of a table with `N` states is periodic with period
`statePeriodModulus N d = d · N!` after `stateTransientLength N d = N · d` letters
(`Arithmetic.runFrom_take_periodic`). Deleting blocks of `statePeriodModulus N d` letters from the
middle of a piece therefore keeps the states at all later cuts. An `AdmissibleDeletion` of the class
of a primitive word `ρ` deletes `x P` such blocks from every piece `P` of the class, starting
`boundaryMargin N d` letters after the start of the piece. The counts vanish on pieces shorter than
`fixedMargin N d`, leave at least `fixedMargin N d` letters of every piece they shorten, and treat
pieces joined by a follower edge consistently: pieces whose lengths differ by less than
`comparisonGap N d` lose the same number of blocks, and a piece shorter than another by at least
`comparisonGap N d` stays shorter by at least that much. These conditions make the deletion preserve
the comparisons recorded by channels (`Holes.Periodic.Transport`). The deletion of positions and its
cut map are those of `Words.Deletion`.

## Main declarations

- `stateTransientLength`, `statePeriodModulus`, `boundaryMargin`, `comparisonGap`,
  `fixedMargin`, `pieceLengthBound`: the constants of the deletion.
- `AdmissibleDeletion`, `editedTuple`, `keepCut`: admissible deletions, the edited tuple and
  its cut map.
-/

@[expose] public section


namespace DeciSigma1.Holes.Periodic

open DeciSigma1.Readers DeciSigma1.Words

variable {α S : Type} {k : ℕ}

/-! ## The constants of the deletion -/

section Constants

/-- The number `N · d` of letters after which the run along a word of period `d` is
periodic. -/
def stateTransientLength (N d : ℕ) : ℕ := N * d

/-- The length `d · N!` of a deleted block: a period of the run along a word of period `d`. -/
def statePeriodModulus (N d : ℕ) : ℕ := d * N.factorial

/-- The offset `N · d + d · N!` of the deleted blocks from the start of a piece. -/
def boundaryMargin (N d : ℕ) : ℕ := stateTransientLength N d + statePeriodModulus N d

/-- The length difference `2 · boundaryMargin + statePeriodModulus` below which two comparable
pieces lose the same number of blocks. -/
def comparisonGap (N d : ℕ) : ℕ := 2 * boundaryMargin N d + statePeriodModulus N d

/-- The length `6 · boundaryMargin + 2 · statePeriodModulus` below which a piece is not
shortened. -/
def fixedMargin (N d : ℕ) : ℕ := 6 * boundaryMargin N d + 2 * statePeriodModulus N d

/-- The retained-length cap for head height `h` and at most `t` tail pieces. -/
def pieceLengthBound (N d h t : ℕ) : ℕ :=
  fixedMargin N d + statePeriodModulus N d + ((t + 1) * 2 ^ h - 1) *
    (comparisonGap N d + statePeriodModulus N d)

theorem d_le_statePeriodModulus (N d : ℕ) :
    d ≤ statePeriodModulus N d := Nat.le_mul_of_pos_right d (Nat.factorial_pos N)

theorem d_le_boundaryMargin (N d : ℕ) : d ≤ boundaryMargin N d := by
  have := d_le_statePeriodModulus N d; unfold boundaryMargin stateTransientLength; omega

theorem two_d_le_boundaryMargin {N : ℕ} (hN : 0 < N) (d : ℕ) : 2 * d ≤ boundaryMargin N d := by
  have := d_le_statePeriodModulus N d; unfold boundaryMargin stateTransientLength
  have : d ≤ N * d := Nat.le_mul_of_pos_left d hN
  omega

end Constants

/-! ## Admissible deletions and the edited tuple -/

section Edit

variable [DecidableEq α]

/-- An admissible deletion of the class of `ρ` for `N` states: `x P` blocks of length
`statePeriodModulus` are deleted from each piece `P`. The counts vanish outside the class, leave at
least `fixedMargin` letters of every piece they shorten (so they vanish on shorter pieces), are
equal on comparable pieces of nearly equal length (`near`), and keep the order and a gap of
`comparisonGap` between comparable pieces of different lengths (`far`). -/
structure AdmissibleDeletion (W : Fin k → List α) (ρ : List α) (N : ℕ) (x : Piece W ρ.length → ℕ) :
    Prop where
  supp : ∀ P, x P ≠ 0 → P ∈ piecesOf W ρ
  long : ∀ P ∈ piecesOf W ρ, x P ≠ 0 → Periodic.fixedMargin N ρ.length +
      Periodic.statePeriodModulus N ρ.length * x P ≤ P.len
  near : ∀ P ∈ piecesOf W ρ, ∀ Q ∈ piecesOf W ρ, FollowerEdge P Q →
    P.len < Q.len + Periodic.comparisonGap N ρ.length → Q.len < P.len +
        Periodic.comparisonGap N ρ.length → x P = x Q
  far : ∀ P ∈ piecesOf W ρ, ∀ Q ∈ piecesOf W ρ, FollowerEdge P Q → P.len +
      Periodic.comparisonGap N ρ.length ≤ Q.len →
    P.len - Periodic.statePeriodModulus N ρ.length * x P + Periodic.comparisonGap N ρ.length ≤
        Q.len - Periodic.statePeriodModulus N ρ.length * x Q

variable (W : Fin k → List α) (ρ : List α) (N : ℕ) (x : Piece W ρ.length → ℕ)

/-- The deleted positions of a piece: `statePeriodModulus · x P` positions from offset
`boundaryMargin`. -/
def pieceDeletionSites (P : Piece W ρ.length) : Finset ℕ :=
  Finset.Ico (P.start + Periodic.boundaryMargin N ρ.length)
      (P.start + Periodic.boundaryMargin N ρ.length + Periodic.statePeriodModulus N ρ.length * x P)

/-- All deleted positions of word `l`. -/
def deletedPositions (l : Fin k) : Finset ℕ :=
  ((piecesOf W ρ).filter (fun P => P.coordinate = l)).biUnion (pieceDeletionSites W ρ N x)

/-- The edited tuple. -/
def editedTuple : Fin k → List α := fun l => deletePositions (W l) (deletedPositions W ρ N x l)

/-- The retained-cut map of word `l`. -/
def keepCut (l : Fin k) (a : ℕ) : ℕ := retainedCount (deletedPositions W ρ N x l) a

variable {W ρ N x}

theorem mem_deletedPositions {l : Fin k} {p : ℕ} : p ∈ deletedPositions W ρ N x l ↔
    ∃ P ∈ piecesOf W ρ, P.coordinate = l ∧ P.start + Periodic.boundaryMargin N ρ.length ≤ p ∧
      p < P.start + Periodic.boundaryMargin N ρ.length + Periodic.statePeriodModulus N ρ.length *
          x P := by
  simp only
      [deletedPositions, pieceDeletionSites, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_Ico]
  constructor
  · rintro ⟨P, ⟨hP, hl⟩, h⟩; exact ⟨P, hP, hl, h⟩
  · rintro ⟨P, hP, hl, h⟩; exact ⟨P, ⟨hP, hl⟩, h⟩

/-- The deleted positions of a shortened piece lie in its middle: after `boundaryMargin`
letters, and at least `5 · boundaryMargin + 2 · statePeriodModulus` letters before its end. -/
theorem AdmissibleDeletion.site_bound (hx : AdmissibleDeletion W ρ N x) {P : Piece W ρ.length}
    (hP : x P ≠ 0) :
    P.start + Periodic.boundaryMargin N ρ.length + Periodic.statePeriodModulus N ρ.length * x P +
        (5 * Periodic.boundaryMargin N ρ.length +
      2 * Periodic.statePeriodModulus N ρ.length) ≤ P.stop := by
  have := hx.long P (hx.supp P hP) hP
  have := P.long
  unfold Piece.len Periodic.fixedMargin at *
  omega

/-- A deleted position lies in the site of every piece of its word that contains it (sites
are deep inside their pieces, and distinct pieces overlap in fewer than `d` letters). -/
theorem AdmissibleDeletion.site_deep (hx : AdmissibleDeletion W ρ N x) {l : Fin k} {p : ℕ}
    (hp : p ∈ deletedPositions W ρ N x l) (Q : Piece W ρ.length) (hQl : Q.coordinate = l)
        (hQ1 : Q.start ≤ p)
    (hQ2 : p < Q.stop) : Q ∈ piecesOf W ρ ∧ x Q ≠ 0 ∧ Q.start + Periodic.boundaryMargin N ρ.length ≤
        p ∧
      p < Q.start + Periodic.boundaryMargin N ρ.length + Periodic.statePeriodModulus N ρ.length *
          x Q := by
  obtain ⟨P, hP, hPl, h1, h2⟩ := mem_deletedPositions.mp hp
  have hxP : x P ≠ 0 := by intro h0; rw [h0] at h2; omega
  have hb := hx.site_bound hxP
  have hdA := Periodic.d_le_boundaryMargin N ρ.length
  have hPQ : P = Q := by
    by_contra hne
    exact Piece.not_mem_other hne (hPl.trans hQl.symm) (p := p) (by omega) (by omega)
      ⟨hQ1, hQ2⟩
  subst hPQ
  exact ⟨hP, hxP, h1, h2⟩

theorem AdmissibleDeletion.not_mem_deletedPositions (hx : AdmissibleDeletion W ρ N x) {l : Fin k}
    {p : ℕ}
    (Q : Piece W ρ.length) (hQl : Q.coordinate = l) (hQ1 : Q.start ≤ p) (hQ2 : p < Q.stop)
    (hns : p < Q.start + Periodic.boundaryMargin N ρ.length ∨ Q.start + Periodic.boundaryMargin N
        ρ.length + Periodic.statePeriodModulus N ρ.length * x Q ≤ p) :
    p ∉ deletedPositions W ρ N x l := by
  intro hp
  have := hx.site_deep hp Q hQl hQ1 hQ2
  omega

theorem AdmissibleDeletion.deletedPositions_lt_length (hx : AdmissibleDeletion W ρ N x) {l : Fin k}
    {p : ℕ}
    (hp : p ∈ deletedPositions W ρ N x l) : p < (W l).length := by
  obtain ⟨P, _, hPl, _, h2⟩ := mem_deletedPositions.mp hp
  have hxP : x P ≠ 0 := by intro h0; rw [h0] at h2; omega
  have := hx.site_bound hxP
  have := P.stop_le_length
  subst hPl
  omega

end Edit

end DeciSigma1.Holes.Periodic
